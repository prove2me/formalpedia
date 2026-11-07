-- Prove2me | Definitions.Def_PackingLPAccel_Residual
-- name    : PackingLPAccel_Residual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:52.181041+00:00
-- url     : https://prove2.me/theorems/d21519d4-6047-4dfb-84b4-04ffcf998c49
-- title:
--   The packing residual problem, its signed reformulation and the geometric grid
-- statement:
--   An instance of Problem 1.3 has $A\ge0$, $0\le x^{\mathrm{curr}}\le u$, convex $\psi_j$ on $[0,u_j]$, an integer $p\ge2$, weights $v^{(2)},v^{(p)}\ge0$, centered convex $c_{i,j}$ and centered convex nonnegative $\phi_{i,j}$. The problem is to minimize over $\Delta\in\prod_j[-x^{\mathrm{curr}}_j,u_j-x^{\mathrm{curr}}_j]$ the function
--
--   $$F(\Delta)=\sum_j\bigl(\psi_j(x^{\mathrm{curr}}_j+\Delta_j)-\psi_j(x^{\mathrm{curr}}_j)\bigr)+\sum_{i,j}c_{i,j}(A_{i,j}\Delta_j)+\sum_iv^{(2)}_i\Bigl(\sum_j\phi_{i,j}(A_{i,j}\Delta_j)\Bigr)^2+\sum_iv^{(p)}_i\Bigl(\sum_j\phi_{i,j}(A_{i,j}\Delta_j)\Bigr)^p.$$
--
--   The module defines the separable part $\chi_j$, the signed reformulation $H(z)$ on $[0,\tilde u]$ with $f^\pm_j(z)=-\chi_j(\pm z)$ and $g^\pm_{ij}(z)=\phi_{ij}(\pm A_{ij}z)$, the geometric grid with $\alpha_j=\delta d^{-1}\tilde u_j(1+\tilde u_jL_j)^{-1}$ and points $\min\{2^{k-1}\alpha_j,\tilde u_j\}$, its retained prefix, and the regression instance built from the chord slopes. It also defines the value oracle, the numeric part of Assumption 3.6 with $\exp(\widetilde O(1))=\exp(\mathsf{lg}(m+n)^b)$, and the input layout.
--
--   **Formalization Note** "$\psi_j+\sum_ic_{i,j}$ is $L_j$-Lipschitz" of Assumption 3.6 is about $\chi_j$, because of the argument $A_{ij}t_j$. When $\tilde u_j=0$ the grid is $\{0\}$ and $K_j=0$. The signed copies are indexed by $\mathrm{Fin}\,n\oplus\mathrm{Fin}\,n$, and $d=2n$.
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Problem 1.3, pp.4, 12 (pdf 5, 13); Assumption 3.6, p.12 (pdf 13); §4.1, pp.13–15 (pdf 14–16)

import Mathlib
import Definitions.Def_PackingLPAccel_Regression

namespace PackingLPAccel

/-!
# The packing residual problem, its signed reformulation and its grid

Chen, Chen, Graur, Sidford, *Accelerated Parallel Algorithms for Packing Linear Programming*,
STOC 2027 submission (manuscript sha256 1dac7711…), Problem 1.3 (pp.4, 12), Assumption 3.6 (p.12), and
§4.1 (pp.13–15).

**Formalization Note.**
* `ψ_j` is a total function on `ℝ`; only its values on `[0, u_j]` matter.
* "`ψ_j + ∑ c_{i,j}` is `L_j`-Lipschitz" of Assumption 3.6 is about `χ_j` of p.13, because of the
  argument `A_ij t_j`.
* The grid: `0`, then `min{2^{k-1} α_j, ũ_j}` for `k ≥ 1` until reaching `ũ_j`, then the prefix of
  intervals on which the chord slope of `f_j` is positive. `Nat.findGreatest` selects that prefix; when
  `ũ_j = 0` the grid is `{0}` and `K_j = 0`. `sInf` on `ℕ` finds the first `k` reaching `ũ_j`.
* `d = 2n`, and the signed copies are indexed by `Fin n ⊕ Fin n` (`inl` for `+`, `inr` for `-`).
* Value-oracle block: `∆` from cell `0`, then `χ_j(∆_j)` from cell `n`, and `ϕ_ij(A_ij ∆_j)` at the
  `N` enumerated nonzeros from cell `2n`.
* Input layout: `I` holds `m, n, N, p` and then positions; `M` holds `ε`, `x^curr`, `u`, `L`, `v^{(2)}`,
  `v^{(p)}` and then the values of `A`. The output `∆̂` starts at `M (1 + 3n + 2m + N)`.
-/

variable {m n : ℕ}

/-- The data of Problem 1.3. -/
structure ResidualInstance (m n : ℕ) where
  /-- The matrix `A`. -/
  A : Matrix (Fin m) (Fin n) ℝ
  /-- The current point `x^curr`. -/
  x : Fin n → ℝ
  /-- The upper bounds `u`. -/
  u : Fin n → ℝ
  /-- The composite functions `ψ_j`. -/
  ψ : Fin n → ℝ → ℝ
  /-- The exponent `p`. -/
  p : ℕ
  /-- The weights `v^{(2)}`. -/
  v₂ : Fin m → ℝ
  /-- The weights `v^{(p)}`. -/
  vₚ : Fin m → ℝ
  /-- The centered convex functions `c_{i,j}`. -/
  c : Fin m → Fin n → ℝ → ℝ
  /-- The centered convex nonnegative functions `ϕ_{i,j}`. -/
  ϕ : Fin m → Fin n → ℝ → ℝ

namespace ResidualInstance

/-- The conditions of Problem 1.3. -/
def IsValid (R : ResidualInstance m n) : Prop :=
  (∀ i j, 0 ≤ R.A i j) ∧ (∀ j, 0 ≤ R.x j ∧ R.x j ≤ R.u j) ∧
  (∀ j, ConvexOn ℝ (Set.Icc 0 (R.u j)) (R.ψ j)) ∧ 2 ≤ R.p ∧
  (∀ i, 0 ≤ R.v₂ i ∧ 0 ≤ R.vₚ i) ∧
  (∀ i j, ConvexOn ℝ Set.univ (R.c i j) ∧ R.c i j 0 = 0) ∧
  (∀ i j, ConvexOn ℝ Set.univ (R.ϕ i j) ∧ R.ϕ i j 0 = 0 ∧ ∀ t, 0 ≤ R.ϕ i j t)

/-- `∆ ∈ I_1 × ⋯ × I_n`, with `I_j = [-x^curr_j, u_j - x^curr_j]`. -/
def InBox (R : ResidualInstance m n) (Δ : Fin n → ℝ) : Prop :=
  ∀ j, -R.x j ≤ Δ j ∧ Δ j ≤ R.u j - R.x j

/-- The objective `F(∆)` of (3)–(4). -/
noncomputable def F (R : ResidualInstance m n) (Δ : Fin n → ℝ) : ℝ :=
  ∑ j, (R.ψ j (R.x j + Δ j) - R.ψ j (R.x j)) + ∑ i, ∑ j, R.c i j (R.A i j * Δ j) +
    ∑ i, R.v₂ i * (∑ j, R.ϕ i j (R.A i j * Δ j)) ^ 2 +
    ∑ i, R.vₚ i * (∑ j, R.ϕ i j (R.A i j * Δ j)) ^ R.p

/-- `χ_j(t) = ψ_j(x^curr_j + t) - ψ_j(x^curr_j) + ∑_i c_ij(A_ij t)`, p.13. -/
noncomputable def chi (R : ResidualInstance m n) (j : Fin n) (t : ℝ) : ℝ :=
  R.ψ j (R.x j + t) - R.ψ j (R.x j) + ∑ i, R.c i j (R.A i j * t)

/-- `χ_j` is `L_j`-Lipschitz on `I_j`. -/
def ChiLipschitz (R : ResidualInstance m n) (L : Fin n → ℝ) : Prop :=
  ∀ j, 0 ≤ L j ∧ ∀ s ∈ Set.Icc (-R.x j) (R.u j - R.x j), ∀ t ∈ Set.Icc (-R.x j) (R.u j - R.x j),
    |R.chi j s - R.chi j t| ≤ L j * |s - t|

/-- The numeric part of Assumption 3.6, with `Õ(1) = lg(m+n)^b`, and `p ≤ Õ(1)` of Theorem 4.1. -/
def IsQuasiPolyBounded (R : ResidualInstance m n) (L : Fin n → ℝ) (b : ℕ) : Prop :=
  let B : ℝ := Real.exp ((lg (m + n) : ℝ) ^ b)
  R.ChiLipschitz L ∧ (∀ j, R.u j ≤ B ∧ L j ≤ B) ∧ (∀ i, R.v₂ i ≤ B ∧ R.vₚ i ≤ B) ∧
    (∀ i j, ∀ t ∈ Set.Icc (-R.x j) (R.u j - R.x j), R.ϕ i j (R.A i j * t) ≤ B) ∧
    (R.p : ℝ) ≤ (lg (m + n) : ℝ) ^ b

/-- The upper bounds `ũ` of the signed copies. -/
def uT (R : ResidualInstance m n) : Fin n ⊕ Fin n → ℝ := Sum.elim (fun j => R.u j - R.x j) R.x

/-- The functions `f^±_j(z) = -χ_j(±z)`. -/
noncomputable def fT (R : ResidualInstance m n) : Fin n ⊕ Fin n → ℝ → ℝ :=
  Sum.elim (fun j t => -R.chi j t) (fun j t => -R.chi j (-t))

/-- The functions `g^±_ij(z) = ϕ_ij(±A_ij z)`. -/
def gT (R : ResidualInstance m n) (i : Fin m) : Fin n ⊕ Fin n → ℝ → ℝ :=
  Sum.elim (fun j t => R.ϕ i j (R.A i j * t)) (fun j t => R.ϕ i j (-(R.A i j * t)))

/-- `H(z)`, p.13. -/
noncomputable def H (R : ResidualInstance m n) (z : Fin n ⊕ Fin n → ℝ) : ℝ :=
  ∑ s, R.fT s (z s) - ∑ i, R.v₂ i * (∑ s, R.gT i s (z s)) ^ 2 -
    ∑ i, R.vₚ i * (∑ s, R.gT i s (z s)) ^ R.p

/-- `z ∈ [0, ũ]`. -/
def InBoxT (R : ResidualInstance m n) (z : Fin n ⊕ Fin n → ℝ) : Prop :=
  ∀ s, 0 ≤ z s ∧ z s ≤ R.uT s

/-- The signed update `∆ = z⁺ - z⁻`. -/
def zToDelta (z : Fin n ⊕ Fin n → ℝ) : Fin n → ℝ := fun j => z (Sum.inl j) - z (Sum.inr j)

/-- `α_s = δ d⁻¹ ũ_s (1 + ũ_s L_s)⁻¹`, `d = 2n`. -/
noncomputable def gridAlpha (R : ResidualInstance m n) (L : Fin n → ℝ) (δ : ℝ)
    (s : Fin n ⊕ Fin n) : ℝ :=
  δ * (2 * (n : ℝ))⁻¹ * R.uT s * (1 + R.uT s * Sum.elim L L s)⁻¹

/-- The full geometric grid: `0`, then `min{2^{k-1} α_s, ũ_s}`. -/
noncomputable def gridPt (R : ResidualInstance m n) (L : Fin n → ℝ) (δ : ℝ) (s : Fin n ⊕ Fin n) :
    ℕ → ℝ
  | 0 => 0
  | k + 1 => min (2 ^ k * R.gridAlpha L δ s) (R.uT s)

/-- The first index at which the grid reaches `ũ_s`. -/
noncomputable def gridFull (R : ResidualInstance m n) (L : Fin n → ℝ) (δ : ℝ)
    (s : Fin n ⊕ Fin n) : ℕ :=
  sInf {k | R.gridPt L δ s k = R.uT s}

open Classical in
/-- `K_s`: the length of the retained prefix of intervals with positive chord slope of `f_s`. -/
noncomputable def gridK (R : ResidualInstance m n) (L : Fin n → ℝ) (δ : ℝ) (s : Fin n ⊕ Fin n) :
    ℕ :=
  Nat.findGreatest
    (fun k => ∀ h < k, R.fT s (R.gridPt L δ s h) < R.fT s (R.gridPt L δ s (h + 1)))
    (R.gridFull L δ s)

/-- The grid variables `(s, k)`, `k < K_s`. -/
abbrev GridIdx (R : ResidualInstance m n) (L : Fin n → ℝ) (δ : ℝ) : Type :=
  Σ s : Fin n ⊕ Fin n, Fin (R.gridK L δ s)

/-- `ℓ_{s,k} = t_{s,k+1} - t_{s,k}`. -/
noncomputable def gridLen (R : ResidualInstance m n) (L : Fin n → ℝ) (δ : ℝ) (v : R.GridIdx L δ) :
    ℝ :=
  R.gridPt L δ v.1 ((v.2 : ℕ) + 1) - R.gridPt L δ v.1 (v.2 : ℕ)

/-- The chord slope of `g_is` on the interval `v`. -/
noncomputable def gridSlope (R : ResidualInstance m n) (L : Fin n → ℝ) (δ : ℝ) (i : Fin m)
    (v : R.GridIdx L δ) : ℝ :=
  (R.gridLen L δ v)⁻¹ *
    (R.gT i v.1 (R.gridPt L δ v.1 ((v.2 : ℕ) + 1)) - R.gT i v.1 (R.gridPt L δ v.1 (v.2 : ℕ)))

/-- The regression instance of §4.1 (p.14): `a_{j,k}`, `ℓ`, `(B^{(2)})_{i,(j,k)}`, `(B^{(p)})_{i,(j,k)}`. -/
noncomputable def gridInstance (R : ResidualInstance m n) (L : Fin n → ℝ) (δ : ℝ) :
    RegInstance (R.GridIdx L δ) m m where
  a v := (R.gridLen L δ v)⁻¹ *
    (R.fT v.1 (R.gridPt L δ v.1 ((v.2 : ℕ) + 1)) - R.fT v.1 (R.gridPt L δ v.1 (v.2 : ℕ)))
  u v := R.gridLen L δ v
  B₂ i v := Real.sqrt (R.v₂ i) * R.gridSlope L δ i v
  Bₚ i v := R.vₚ i ^ ((1 : ℝ) / R.p) * R.gridSlope L δ i v
  p := R.p

/-- `z_s = ∑_k y_{s,k}`. -/
noncomputable def yToZ (R : ResidualInstance m n) (L : Fin n → ℝ) (δ : ℝ) (y : R.GridIdx L δ → ℝ) :
    Fin n ⊕ Fin n → ℝ :=
  fun s => ∑ k : Fin (R.gridK L δ s), y ⟨s, k⟩

/-- The value oracle of Theorem 4.1: on `∆ ∈ ∏_j I_j` it writes all `χ_j(∆_j)` and all
`ϕ_ij(A_ij ∆_j)` at the enumerated nonzeros; every other query has no answer. -/
def IsValueOracle {N : ℕ} (R : ResidualInstance m n) (e : Fin N → Fin m × Fin n)
    (O : OracleModel) : Prop :=
  ∀ st : State,
    let Δ : Fin n → ℝ := readBlock st.M 0
    (R.InBox Δ → O.answer st =
      some (writeBlock
        (writeBlock st.M n n (fun k => if h : k < n then R.chi ⟨k, h⟩ (Δ ⟨k, h⟩) else 0)) (2 * n) N
        (fun t => if h : t < N then
          R.ϕ (e ⟨t, h⟩).1 (e ⟨t, h⟩).2 (R.A (e ⟨t, h⟩).1 (e ⟨t, h⟩).2 * Δ (e ⟨t, h⟩).2) else 0),
        st.I)) ∧
    (¬ R.InBox Δ → O.answer st = none)

/-- The integer list of a residual instance. -/
def resInts {N : ℕ} (R : ResidualInstance m n) (e : Fin N → Fin m × Fin n) : List ℤ :=
  [(m : ℤ), (n : ℤ), (N : ℤ), (R.p : ℤ)] ++ sparseIdx e

/-- The real list of a residual instance, with the accuracy in front. -/
noncomputable def resReals {N : ℕ} (ε : ℝ) (R : ResidualInstance m n) (L : Fin n → ℝ)
    (e : Fin N → Fin m × Fin n) : List ℝ :=
  ε :: (List.ofFn R.x ++ List.ofFn R.u ++ List.ofFn L ++ List.ofFn R.v₂ ++ List.ofFn R.vₚ ++
    sparseVals R.A e)

/-- The initial state of a residual program. -/
noncomputable def resInit {N : ℕ} (ε : ℝ) (R : ResidualInstance m n) (L : Fin n → ℝ)
    (e : Fin N → Fin m × Fin n) : State :=
  initState (resReals ε R L e) (R.resInts e)

/-- The output of a residual program. -/
def resOutput (m n N : ℕ) (s : State) : Fin n → ℝ :=
  fun j => s.M (1 + 3 * (n : ℤ) + 2 * (m : ℤ) + (N : ℤ) + ((j : ℕ) : ℤ))

end ResidualInstance

end PackingLPAccel


