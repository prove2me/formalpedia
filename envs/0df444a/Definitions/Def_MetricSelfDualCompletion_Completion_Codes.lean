-- Prove2me | Definitions.Def_MetricSelfDualCompletion_Completion_Codes
-- name    : MetricSelfDualCompletion_Completion_Codes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T06:45:39.756775+00:00
-- url     : https://prove2.me/theorems/935e6549-2a89-440d-953a-229cc8ac1eff
-- title:
--   Binary codes for metric self-dual completion: self-duality, distance to a code, the repetition embedding $\tau$, the completion $K, A$, the prefix-sum code
-- statement:
--   All vectors are over $\mathbb F_2$; a vector of $\mathbb F_2^n$ is a function $\{0,\dots,n-1\}\to\mathbb F_2$, and a **code** is an arbitrary linear subspace $C\le\mathbb F_2^n$ (the zero code and the whole space are allowed). The **weight** $\mathrm{wt}(x)$ is the number of nonzero coordinates of $x$, the dual $C^\perp=\{y : c^\top y=0\ \forall c\in C\}$ is taken with the ordinary dot product, and $d(C)=\min_{0\ne c\in C}\mathrm{wt}(c)$ with $d(0)=+\infty$ (these two are the published `QAlgorithms.codeDual` and `QAlgorithms.minDistCode`). This file defines:
--
--   1. $C$ is **self-orthogonal** if $C\le C^\perp$ and **self-dual** if $C=C^\perp$.
--   2. The **distance from a point to a code**, $\mathrm{dist}(y,C)=\min_{c\in C}\mathrm{wt}(y+c)$, a natural number (the minimum is over a nonempty set, since $0\in C$).
--   3. A $k\times n$ matrix $B$ is a **row basis** of $C$ if its rows are linearly independent and span $C$ ($k=0$ for the zero code).
--   4. The **Shpilka–Guruswami lengths** $n_j=42\cdot 8^{j+1}$ and the **all-ones vector** $\mathbf 1_n$.
--   5. The **repetition embedding** $\tau:\mathbb F_2^m\to\mathbb F_2^N$,
--   $$\tau(x)=(x,\,x,\,0^{N-2m}),$$
--   the linear map copying $x$ into the first two blocks of $m$ coordinates and padding with zeros (used with $2m\le N$).
--   6. For a host code $M\le\mathbb F_2^N$ and a source code $C\le\mathbb F_2^m$, the **completion**
--   $$K=M\cap\tau(C)^\perp,\qquad A=K+\tau(C).$$
--   7. The **prefix sums** $s_0(w)=0$, $s_t(w)=\sum_{j=1}^{t}w_j$, the **prefix-sum map** $\Phi:\mathbb F_2^n\times\mathbb F_2^n\to\mathbb F_2^{2n}$ whose $i$-th output pair ($1\le i\le n$) is
--   $$\Phi_i(c,w)=\bigl(c_i+s_{i-1}(w),\;c_i+s_i(w)\bigr),$$
--   and, for a code $E\le\mathbb F_2^n$, the **prefix-sum code** $P=\Phi(E\times E^\perp)\le\mathbb F_2^{2n}$.
--
--   These are the objects of §2.1, §3.1 and §5.2 of the paper; every theorem of the mission is stated in terms of them.
--
--   **Formalization Note** Coordinates are 0-based: $\tau(x)_i=x_i$ for $i<m$, $x_{i-m}$ for $m\le i<2m$, $0$ otherwise; the output pair of index $i$ of $\Phi$ occupies positions $2i,2i+1$, and position $k$ carries $c_{\lfloor k/2\rfloor}+s_{\lfloor k/2\rfloor+(k\bmod 2)}(w)$. $\Phi$ is defined on all of $\mathbb F_2^n\times\mathbb F_2^n$; the paper's $\Phi$ on $E\times E^\perp$ is its restriction. The weight is Mathlib's `hammingNorm`.
-- source:
--   Rafail Ostrovsky, STOC 2027 submission #5 (October 2026), §2.1, printed p. 5 (PDF p. 7); §3.1, printed pp. 6–7 (PDF pp. 8–9); §5.2, printed p. 11 (PDF p. 13); Theorem 11, printed p. 10 (PDF p. 12). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/5.pdf

import Mathlib
import Definitions.Def_QAlgorithms_Defs_TensorCode

/-!
# Metric self-dual completion: binary codes, the repetition embedding, the completion, prefix sums

Rafail Ostrovsky, *Metric Self-Dual Completion and Optimal Additive Hardness for Quantum and
Graph-State Distance*, STOC 2027 submission #5 (October 2026), §2.1 (printed p. 5, PDF p. 7),
§3.1 (printed pp. 6–7, PDF pp. 8–9), §5.2 (printed p. 11, PDF p. 13).

Conventions (§2.1). Vectors of `F₂ⁿ` are functions `Fin n → ZMod 2`; a code is an arbitrary
`Submodule (ZMod 2) (Fin n → ZMod 2)` (the zero code and the full space included). The weight
`wt(x)` is Mathlib's `hammingNorm x`. The dual `C^⊥` and the minimum distance `d(C)` (valued in
`ℕ∞`, with `d(0) = ∞`) are the published `QAlgorithms.codeDual` and `QAlgorithms.minDistCode`.
-/

namespace MetricSelfDualCompletion.Completion

open QAlgorithms

/-- §2.1: a code `C` is **self-orthogonal** if `C ⩽ C^⊥`. -/
def IsSelfOrthogonal {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2)) : Prop :=
  C ≤ codeDual C

/-- §2.1: a code `C` is **self-dual** if `C = C^⊥`. -/
def IsSelfDual {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2)) : Prop :=
  codeDual C = C

/-- §2.1: `dist(y, C) = min_{c ∈ C} wt(y + c)`. The set of weights is nonempty (`0 ∈ C`), so the
`ℕ`-infimum is the attained minimum (no junk value). -/
noncomputable def distToCode {n : ℕ} (y : Fin n → ZMod 2)
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) : ℕ :=
  sInf ((fun c => hammingNorm (y + c)) '' (C : Set (Fin n → ZMod 2)))

/-- §2.1 ("Codes are specified by bases. Generator matrices have basis rows."): the rows
`B 0, …, B (k−1)` of a `k × n` matrix form a basis of the code `C`: they are linearly independent
and span `C`. `k = 0` (the zero code) is allowed. -/
def IsRowBasis {k n : ℕ} (B : Fin k → Fin n → ZMod 2)
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) : Prop :=
  LinearIndependent (ZMod 2) B ∧ Submodule.span (ZMod 2) (Set.range B) = C

/-- §5, Theorem 11 (printed p. 10, PDF p. 12): the Shpilka–Guruswami lengths
`n_j = 42 · 8^{j+1}`. -/
def sgLength (j : ℕ) : ℕ := 42 * 8 ^ (j + 1)

/-- §5: the all-ones vector `1ₙ ∈ F₂ⁿ`. -/
def allOnes (n : ℕ) : Fin n → ZMod 2 := fun _ => 1

/-- §3.1 (printed p. 6, PDF p. 8): the repetition embedding `τ(x) = (x, x, 0^{N−2m})` of `F₂ᵐ`
into `F₂ᴺ`: coordinate `i` (0-based) is `x_i` for `i < m`, `x_{i−m}` for `m ⩽ i < 2m`, and `0`
for `i ⩾ 2m`. The statements using it always have `2m ⩽ N`, so no coordinate of `(x, x)` is
cut off. -/
def repEmbed (m N : ℕ) : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin N → ZMod 2) where
  toFun x i :=
    if h : i.val < m then x ⟨i.val, h⟩
    else if h' : i.val < 2 * m then x ⟨i.val - m, by omega⟩ else 0
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

/-- §3.1 (printed p. 7, PDF p. 9): `K = M ∩ τ(C)^⊥`, the host words orthogonal to the embedded
copy of `C`. -/
def completionK {m N : ℕ} (M : Submodule (ZMod 2) (Fin N → ZMod 2))
    (C : Submodule (ZMod 2) (Fin m → ZMod 2)) : Submodule (ZMod 2) (Fin N → ZMod 2) :=
  M ⊓ codeDual (C.map (repEmbed m N))

/-- §3.1 (printed p. 7, PDF p. 9): the completion `A = K + τ(C)`. -/
def completionA {m N : ℕ} (M : Submodule (ZMod 2) (Fin N → ZMod 2))
    (C : Submodule (ZMod 2) (Fin m → ZMod 2)) : Submodule (ZMod 2) (Fin N → ZMod 2) :=
  completionK M C ⊔ C.map (repEmbed m N)

/-- §5.2 (printed p. 11, PDF p. 13): the prefix sum `s_t(w) = ∑_{j=1}^{t} w_j` (1-based), i.e.
the sum of the coordinates of `w` with 0-based index `< t`; `s₀(w) = 0`. -/
def prefixSum {n : ℕ} (w : Fin n → ZMod 2) (t : ℕ) : ZMod 2 :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < t), w j

/-- §5.2 (printed p. 11, PDF p. 13): the prefix-sum map `Φ : F₂ⁿ × F₂ⁿ → F₂^{2n}`,
`Φ(c, w) = (Φ₁(c, w), …, Φₙ(c, w))` with `Φᵢ(c, w) = (cᵢ + s_{i−1}(w), cᵢ + sᵢ(w))` (1-based).
In 0-based coordinates the pair of index `i < n` occupies positions `2i` and `2i + 1`; position
`k` carries `c_{⌊k/2⌋} + s_{⌊k/2⌋ + (k mod 2)}(w)`. The paper applies `Φ` on `E × E^⊥`; here it is
the restriction of this linear map. -/
def prefixSumMap (n : ℕ) :
    ((Fin n → ZMod 2) × (Fin n → ZMod 2)) →ₗ[ZMod 2] (Fin (2 * n) → ZMod 2) where
  toFun p k := p.1 ⟨k.val / 2, by omega⟩ + prefixSum p.2 (k.val / 2 + k.val % 2)
  map_add' p q := by
    funext k
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, prefixSum, Finset.sum_add_distrib]
    ring
  map_smul' a p := by
    funext k
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      prefixSum, ← Finset.mul_sum]
    ring

/-- §5.2 (printed p. 11, PDF p. 13): the prefix-sum code `P = Φ(E, E^⊥) ⩽ F₂^{2n}`. -/
def prefixSumCode {n : ℕ} (E : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Submodule (ZMod 2) (Fin (2 * n) → ZMod 2) :=
  (E.prod (codeDual E)).map (prefixSumMap n)

/-! ### Sanity checks -/

example : repEmbed 2 5 ![1, 0] = ![1, 0, 1, 0, 0] := by
  funext i; fin_cases i <;> rfl

example : prefixSumMap 2 (![1, 1], ![1, 1]) = ![1, 0, 0, 1] := by
  funext k; fin_cases k <;> decide

example {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (y : Fin n → ZMod 2) :
    distToCode y C ≤ hammingNorm y := by
  apply Nat.sInf_le
  exact ⟨0, C.zero_mem, by simp⟩

end MetricSelfDualCompletion.Completion


