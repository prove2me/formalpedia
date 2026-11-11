-- Prove2me | Definitions.Def_QTolTest1673_Unified_Classes
-- name    : QTolTest1673_Unified_Classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:20:50.248217+00:00
-- url     : https://prove2.me/theorems/5f360f94-ffc5-45bc-bba4-d0ef9480492b
-- title:
--   The classes $L_{n,k}$, $J_{n,k}$, the block-constant classes $C_V$, correlation and the candidate families $\mathcal V_k^{\dim}$, $\mathcal V_k^{\mathrm{junta}}$
-- statement:
--   Write $V_n=\mathbb F_2^n$ and consider Boolean functions $f:\mathbb F_2^n\to\{\pm1\}$, with distance $\operatorname{dist}(f,g)=\Pr_x[f(x)\ne g(x)]$ under the uniform distribution and $\operatorname{dist}(f,\mathcal C)=\min_{g\in\mathcal C}\operatorname{dist}(f,g)$.
--
--   1. The class of functions of **Fourier dimension at most $k$** is defined, as in the source, by
--   $$L_{n,k}=\{x\mapsto h(Ax): A\in\mathbb F_2^{k\times n},\ h:\mathbb F_2^k\to\{\pm1\}\},$$
--   where $A$ need not have full rank.
--   2. The class $J_{n,k}$ of **$k$-juntas** consists of the functions for which some set $T$ of at most $k$ coordinates exists such that any two inputs agreeing on $T$ have the same value.
--   3. For a linear subspace $V\le\mathbb F_2^n$, the **block-constant class** $C_V$ consists of the Boolean functions constant on every coset $x+V^\perp$, where $V^\perp=\{z:u\cdot z=0\text{ for all }u\in V\}$.
--   4. For $T\subseteq[n]$, the **coordinate subspace** is $V_T=\{u:\operatorname{supp}(u)\subseteq T\}$ with $\operatorname{supp}(u)=\{i:u_i=1\}$.
--   5. The **candidate families** are $\mathcal V_k^{\dim}=\{V\le\mathbb F_2^n:\dim V\le k\}$ and $\mathcal V_k^{\mathrm{junta}}=\{V_T:|T|\le k\}$.
--   6. The **correlation** is $\operatorname{corr}(f,g)=\mathbb E_x[f(x)g(x)]$ and $\operatorname{corr}(f,\mathcal C)=\max_{g\in\mathcal C}\operatorname{corr}(f,g)$.
--   7. A family of subspaces is viewed as a family of subsets of $\Omega=\mathbb F_2^n$ through the indicator functions $u\mapsto\mathbf 1[u\in V]$, so that shattering and VC dimension (Definition 3.1) apply to it.
--
--   These are the objects of the unified tester: $L_{n,k}$ and $J_{n,k}$ are the tested properties, each is a union of block-constant classes over its candidate family, and the VC dimension of the candidate families controls the number of Fourier samples.
--
--   **Formalization Note** Functions are recorded by their bit $b_f$ with $f=(-1)^{b_f}$, as in the published model `FourierDimTesting102.Quantum.Model`, which also supplies $V^\perp$ (`perp`), the distance to a set (`distToSet`) and the Fourier mass. The classes are defined combinatorially, not through Fourier support, so the source's characterizations are not true by definition. Coordinates are indexed by `Fin n`. The maximum defining $\operatorname{corr}(f,\mathcal C)$ is a supremum of finitely many values; the file proves that the constant functions lie in $L_{n,k}$, $J_{n,k}$ and every $C_V$, so the supremum and the distance infimum are attained over nonempty sets.
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), source.pdf SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, §2.1 (p. 13), §2.3 (pp. 14–15), Definition 3.1 (p. 18)

import Definitions.Def_FourierDimTesting102_Quantum_Model
import Definitions.Def_UnderstandingML_VC

/-!
# The classes `L_{n,k}`, `J_{n,k}`, the block-constant classes `C_V` and the candidate families

Zekun Ye, Jialin Zhang, *Quantum Tolerant Testing of Fourier Dimensionality and Juntas*,
STOC 2027 submission #1673 (October 2026), §2.1 (p. 13), §2.3 (pp. 14–15), §3.1 (p. 18).

Boolean functions `f : F₂ⁿ → {±1}` are recorded by their bit `b_f` with `f = (-1)^{b_f}`
(`FourierDimTesting102.Quantum.BoolFn`, `toSign`); the published model supplies the characters
`chi`, the Fourier coefficients `coeff` (`f̂(u) = E_x f(x) χ_u(x)`), the distance `boolDist`,
the distance to a set `distToSet`, the Fourier mass `wtIn` (`W_V`), the annihilator `perp`
(`V^⊥`) and the coset average `cosetAverage` (`m_V`). Coordinates are indexed by `Fin n`
(the source's `[n] = {1,…,n}`).

The classes are defined combinatorially, as in the source: `L_{n,k}` as the functions `h(Ax)`,
`J_{n,k}` by the coordinates a function depends on, and `C_V` as the functions constant on every
coset of `V^⊥`. None of them is defined through Fourier support, so the §2.3 display and
Lemma 2.4 are not true by definition.
-/

namespace QTolTest1673.Unified

open FourierDimTesting102.Quantum

/-- §2.1, p. 13: `L_{n,k} = {x ↦ h(Ax) : A ∈ F₂^{k×n}, h : F₂^k → {±1}}`; the matrix `A`
need not have full rank. `h` is recorded by its bit function. -/
def linJunta (n k : ℕ) : Set (BoolFn n) :=
  {f | ∃ (A : Matrix (Fin k) (Fin n) (ZMod 2)) (h : (Fin k → ZMod 2) → Bool),
    ∀ x, f x = h (A.mulVec x)}

/-- §2.1, p. 13: `J_{n,k}`, the functions depending on at most `k` coordinates: there is a set
`T` of at most `k` coordinates such that inputs agreeing on `T` have equal values. -/
def junta (n k : ℕ) : Set (BoolFn n) :=
  {f | ∃ T : Finset (Fin n), T.card ≤ k ∧ ∀ x y : V n, (∀ i ∈ T, x i = y i) → f x = f y}

/-- §2.3, p. 15: `C_V`, the Boolean functions constant on every coset `x + V^⊥` (block). -/
def blockConst {n : ℕ} (W : Submodule (ZMod 2) (V n)) : Set (BoolFn n) :=
  {f | ∀ x z : V n, z ∈ perp W → f (x + z) = f x}

/-- §2.3, p. 15: the coordinate subspace `V_T = {u : supp(u) ⊆ T}`, where
`supp(u) = {i : u_i = 1}` (over `F₂`, `u_i = 1` iff `u_i ≠ 0`). -/
def coordSubspace {n : ℕ} (T : Finset (Fin n)) : Submodule (ZMod 2) (V n) where
  carrier := {u | ∀ i, u i ≠ 0 → i ∈ T}
  add_mem' := by
    intro a b ha hb i hi
    by_cases hai : a i = 0
    · apply hb i
      intro hbi
      apply hi
      simp [hai, hbi]
    · exact ha i hai
  zero_mem' := by
    intro i hi
    exact absurd rfl hi
  smul_mem' := by
    intro c u hu i hi
    apply hu i
    intro hui
    apply hi
    simp [hui]

/-- §2.3, p. 15: `V_k^dim = {V ≤ F₂ⁿ : dim V ≤ k}`. -/
def famDim (n k : ℕ) : Set (Submodule (ZMod 2) (V n)) :=
  {W | Module.finrank (ZMod 2) W ≤ k}

/-- §2.3, p. 15: `V_k^junta = {V_T : T ⊆ [n], |T| ≤ k}`. -/
def famJunta (n k : ℕ) : Set (Submodule (ZMod 2) (V n)) :=
  {W | ∃ T : Finset (Fin n), T.card ≤ k ∧ W = coordSubspace T}

/-- §2.1, p. 13: `corr(f, g) = E_x[f(x) g(x)]`, `x` uniform on `F₂ⁿ`, for the `{±1}`-valued
functions. -/
noncomputable def corr {n : ℕ} (f g : BoolFn n) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x : V n, toSign f x * toSign g x

/-- §2.1, p. 13: `corr(f, C) = max_{g ∈ C} corr(f, g)` for a nonempty class `C`. Every set of
Boolean functions is finite, so on a nonempty set this supremum is attained
(`exists_corr_eq_corrToSet`); every class used in this mission contains the constant functions. -/
noncomputable def corrToSet {n : ℕ} (f : BoolFn n) (S : Set (BoolFn n)) : ℝ :=
  sSup (corr f '' S)

open Classical in
/-- Definition 3.1, p. 18: a family of subsets of `Ω = F₂ⁿ` (here, of subspaces) as the family of
their indicator functions, so that `UnderstandingML.Shatters` / `UnderstandingML.vcDim` are the
source's shattering and VC dimension. -/
noncomputable def indicatorFamily {n : ℕ} (F : Set (Submodule (ZMod 2) (V n))) :
    Set (V n → Bool) :=
  (fun W u => decide (u ∈ W)) '' F

/-! ### Structural facts: the classes contain the constants, so distances are minima -/

theorem const_mem_linJunta (n k : ℕ) (b : Bool) : (fun _ => b : BoolFn n) ∈ linJunta n k :=
  ⟨0, fun _ => b, fun _ => rfl⟩

theorem const_mem_junta (n k : ℕ) (b : Bool) : (fun _ => b : BoolFn n) ∈ junta n k :=
  ⟨∅, by simp, fun _ _ _ => rfl⟩

theorem const_mem_blockConst {n : ℕ} (W : Submodule (ZMod 2) (V n)) (b : Bool) :
    (fun _ => b : BoolFn n) ∈ blockConst W :=
  fun _ _ _ => rfl

theorem linJunta_nonempty (n k : ℕ) : (linJunta n k).Nonempty := ⟨_, const_mem_linJunta n k false⟩

theorem junta_nonempty (n k : ℕ) : (junta n k).Nonempty := ⟨_, const_mem_junta n k false⟩

theorem blockConst_nonempty {n : ℕ} (W : Submodule (ZMod 2) (V n)) : (blockConst W).Nonempty :=
  ⟨_, const_mem_blockConst W false⟩

theorem exists_corr_eq_corrToSet {n : ℕ} (f : BoolFn n) {S : Set (BoolFn n)}
    (hS : S.Nonempty) : ∃ g ∈ S, corr f g = corrToSet f S := by
  have h := (hS.image (corr f)).csSup_mem ((Set.toFinite S).image _)
  obtain ⟨g, hg, hgd⟩ := h
  exact ⟨g, hg, hgd⟩

theorem mem_coordSubspace {n : ℕ} (T : Finset (Fin n)) (u : V n) :
    u ∈ coordSubspace T ↔ ∀ i, u i ≠ 0 → i ∈ T := Iff.rfl

end QTolTest1673.Unified


