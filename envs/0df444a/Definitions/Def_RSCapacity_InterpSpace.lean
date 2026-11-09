-- Prove2me | Definitions.Def_RSCapacity_InterpSpace
-- name    : RSCapacity_InterpSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:46.179967+00:00
-- url     : https://prove2.me/theorems/d3044e8c-c7b0-4c96-89f6-67edeeecaa6f
-- title:
--   The interpolation space $\mathcal Q(A,K,r,m,c,s)$ and the tail counts $|\mathcal T|$, $\Lambda$
-- statement:
--   Fix integers $A,K,r,m$ (the theorems assume $1\le r<K\le A$) and reals $c,s$ (the theorems assume $1<c<s<A/(K-1)$). For $v=(v_2,\dots,v_r)\in\mathbb Z_{\ge0}^{r-1}$ put
--   $$\omega(v)=\sum_{j=2}^r (j-1)v_j,\qquad |v|=\sum_{j=2}^r v_j,\qquad Y^v=\prod_{j=2}^r Y_j^{v_j}.$$
--   With the natural logarithm, set
--   $$W=\Bigl\lfloor \frac{crm}{\log(er)}\Bigr\rfloor,\qquad \mathcal T=\{v:\ \omega(v)\le W,\ |v|\le\lceil sm\rceil\},\qquad B=\Bigl\lceil\frac{mA}{K-1}\Bigr\rceil .$$
--   The **interpolation space** $\mathcal Q$ is the $F$-span of the monomials $X^aY_0^{b_0}Y_1^{b_1}Y^v$ with $a,b_0,b_1\ge0$, $v\in\mathcal T$ and
--   1. $b_1\le m$,
--   2. $b_0+b_1+|v|\le B$,
--   3. $a+(K-1)(b_0+b_1+|v|)<mA$.
--
--   For real $z\ge0$, $\Lambda(z)=|\{v\in\mathbb Z_{\ge0}^{r-1}:\omega(v)\le z\}|$.
--
--   The interpolant of the decoder is a nonzero element of $\mathcal Q$; the dimension of $\mathcal Q$ is compared with the number of local constraints.
--
--   **Formalization Note** A tail $v$ is a function `Fin (r - 1) → ℕ` with $v_i$ standing for $v_{i+2}$; its variable $Y_{i+2}$ is variable $i+3$ of `MvPolynomial (Fin (r + 2)) F`. $W$, $\lceil sm\rceil$ and $B$ are natural numbers (`Nat.floor`, `Nat.ceil`). $|\mathcal T|$ and $\Lambda$ are `Set.ncard` of finite sets.
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), §4.1, p.13 (PDF 15), Equations (15)–(21); Equation (27), p.15 (PDF 17)

import Mathlib

set_option autoImplicit false

namespace RSCapacity

/-!
# The interpolation space 𝒬 = 𝒬(A, K, r, m, c, s) and the tail counts |𝒯|, Λ

Jeronimo, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…): §4.1, p.13
(PDF 15), Equations (15)–(21); Equation (27), p.15 (PDF 17).

"Fix integers A, K, r, m with 1 ≤ r < K ≤ A and write u := A/(K − 1). Choose real numbers
1 < c < s < u. For v = (v_2, …, v_r) ∈ ℤ_{≥0}^{r−1}, define ω(v) := ∑_{j=2}^{r} (j − 1)v_j,
|v| := ∑_{j=2}^{r} v_j, Y^v := ∏_{j=2}^{r} Y_j^{v_j}. Set W := ⌊crm / log(er)⌋ (15) and
𝒯 := {v ∈ ℤ_{≥0}^{r−1} : ω(v) ≤ W, |v| ≤ ⌈sm⌉} (16). Finally put B := ⌈mA/(K − 1)⌉ (17) and let
𝒬 be the span of all monomials X^a Y_0^{b_0} Y_1^{b_1} Y^v (18) with a, b_0, b_1 ∈ ℤ_{≥0},
v ∈ 𝒯, b_1 ≤ m (19), b_0 + b_1 + |v| ≤ B (20), a + (K − 1)(b_0 + b_1 + |v|) < mA (21)."

**Formalization Note.**
* A tail v = (v_2, …, v_r) is a function `v : Fin (r - 1) → ℕ` with `v i = v_{i+2}`; so
  ω(v) = ∑_i (i + 1) v_i and |v| = ∑_i v_i. Its variable Y_{i+2} is variable `i + 3` of
  `MvPolynomial (Fin (r + 2)) F` (X = 0, Y_0 = 1, Y_1 = 2, Y_j = j + 1).
* log is the natural logarithm `Real.log` (p.10). W, ⌈sm⌉ and B are natural numbers
  (`Nat.floor`, `Nat.ceil`); their arguments are nonnegative under the standing hypotheses.
* The definitions take any natural numbers and reals; the standing hypotheses
  1 ≤ r < K ≤ A, 1 < c < s < A/(K − 1) are hypotheses of the theorems that use them.
* Λ(z) := |{v ∈ ℤ_{≥0}^{r−1} : ω(v) ≤ z}| (27) is `Set.ncard` of a finite set (every weight
  j − 1 is at least 1).
-/

/-- ω(v) = ∑_{j=2}^{r} (j − 1) v_j, with `v i = v_{i+2}`. -/
def omegaW {r : ℕ} (v : Fin (r - 1) → ℕ) : ℕ := ∑ i : Fin (r - 1), ((i : ℕ) + 1) * v i

/-- |v| = ∑_{j=2}^{r} v_j. -/
def absV {r : ℕ} (v : Fin (r - 1) → ℕ) : ℕ := ∑ i, v i

/-- W = ⌊c r m / log(e r)⌋ (Equation (15)), natural logarithm. -/
noncomputable def Wcut (r m : ℕ) (c : ℝ) : ℕ :=
  ⌊c * r * m / Real.log (Real.exp 1 * r)⌋₊

/-- B = ⌈m A / (K − 1)⌉ (Equation (17)). -/
noncomputable def Bdeg (m A K : ℕ) : ℕ := ⌈(m * A : ℝ) / ((K : ℝ) - 1)⌉₊

/-- 𝒯 = {v ∈ ℤ_{≥0}^{r−1} : ω(v) ≤ W, |v| ≤ ⌈s m⌉} (Equation (16)). -/
noncomputable def tailSet (r m : ℕ) (c s : ℝ) : Set (Fin (r - 1) → ℕ) :=
  {v | omegaW v ≤ Wcut r m c ∧ absV v ≤ ⌈s * m⌉₊}

/-- Λ(z) = |{v ∈ ℤ_{≥0}^{r−1} : ω(v) ≤ z}| (Equation (27)). -/
noncomputable def Lambda (r : ℕ) (z : ℝ) : ℕ :=
  {v : Fin (r - 1) → ℕ | (omegaW v : ℝ) ≤ z}.ncard

/-- The variable Y_{i+2} of `MvPolynomial (Fin (r + 2)) F`, i.e. variable number `i + 3`. -/
def tailIdx (r : ℕ) (i : Fin (r - 1)) : Fin (r + 2) :=
  ⟨(i : ℕ) + 3, by have := i.isLt; omega⟩

/-- The monomial X^a Y_0^{b_0} Y_1^{b_1} Y^v (Equation (18)). -/
noncomputable def interpMonomial {F : Type*} [Field F] {r : ℕ} (a b₀ b₁ : ℕ)
    (v : Fin (r - 1) → ℕ) : MvPolynomial (Fin (r + 2)) F :=
  MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b₀ * MvPolynomial.X 2 ^ b₁ *
    ∏ i, MvPolynomial.X (tailIdx r i) ^ v i

/-- The interpolation space 𝒬: the span of the monomials (18) satisfying (19)–(21). -/
noncomputable def interpSpace (F : Type*) [Field F] (A K r m : ℕ) (c s : ℝ) :
    Submodule F (MvPolynomial (Fin (r + 2)) F) :=
  Submodule.span F
    {Q | ∃ (a b₀ b₁ : ℕ) (v : Fin (r - 1) → ℕ), v ∈ tailSet r m c s ∧ b₁ ≤ m ∧
      b₀ + b₁ + absV v ≤ Bdeg m A K ∧ a + (K - 1) * (b₀ + b₁ + absV v) < m * A ∧
      Q = interpMonomial a b₀ b₁ v}

end RSCapacity


