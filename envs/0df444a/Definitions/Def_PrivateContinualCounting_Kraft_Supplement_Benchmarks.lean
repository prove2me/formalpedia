-- Prove2me | Definitions.Def_PrivateContinualCounting_Kraft_Supplement_Benchmarks
-- name    : PrivateContinualCounting_Kraft_Supplement_Benchmarks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:27:15.706209+00:00
-- url     : https://prove2.me/theorems/2d78f6c1-0695-493a-a43b-0c580b41d7f1
-- title:
--   Square-root coefficients, ordinary gamma-two and finite inner factors
-- statement:
--   Define the square-root coefficients, their energy and the prefix matrix by
--   $$c_j=4^{-j}\binom{2j}{j},\qquad S(n)=\sum_{j<n}c_j^2,\quad S(0)=0,\qquad (A_n)_{ij}=\mathbf1_{j\le i}.$$
--   The square-root family has decoder coefficients $\sqrt{S(n)}c_j$ and strategy coefficients $c_j/\sqrt{S(n)}$ for positive horizons. For an arbitrary finite real matrix $M$, the ordinary factorization norm is
--   $$\gamma_2(M)=\inf_{k,L,R:\,LR=M}\left(\max_i\|L_{i,\cdot}\|_2\right)\left(\max_j\|R_{\cdot,j}\|_2\right),$$
--   with every finite inner dimension $k$ allowed. This is not a Toeplitz-restricted infimum. The factorization set contains $M$ times the identity; all costs are nonnegative. Empty row or column maxima are assigned zero. The running maximum is $\bar v_t=\max_{0\le s\le t}v_s$; every counter used here has $v_0=0$, so it equals the source's positive-time maximum, and $\bar v_0=0$.
--
--   A raw inner family consists only of horizon-dependent decoder and strategy coefficient sequences. Its accuracy predicate asks for exact prefix convolution, strategy columns normalized with first-column squared norm one, and every decoder prefix squared norm at most $(S(n)+\eta)^2$. A buffered sequence is specified by an actual finite linear state filter: $c_0=\tau+v^\top u$ and $c_{j+1}=v^\top A^{j+1}u$. The existence of accurate buffered families and of their implementations is a conclusion of the clock theorem, not input data. This distinguishes finite filter state dimension from scalar recurrence order.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 7, PDF p. 9, Section 2.4; pp. 23–24, PDF pp. 25–26, Appendix E.3

import Definitions.Def_PrivateContinualCounting_Kraft_Supplement_Privacy

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft.Supplement

noncomputable def sqrtCoeff (j : ℕ) : ℝ := (Nat.choose (2*j) j : ℝ) / (4:ℝ)^j
noncomputable def squareEnergy (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, (sqrtCoeff j)^2

def prefixMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => if j ≤ i then 1 else 0

/-- Ordinary finite-dimensional gamma₂: arbitrary inner dimension and arbitrary factors.
For every matrix the feasible set is nonempty (M times identity); costs are nonnegative.
Finite suprema include 0 to define the empty row/column case. -/
noncomputable def matrixGamma2 {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sInf {v : ℝ | ∃ k : ℕ, ∃ L : Matrix (Fin m) (Fin k) ℝ,
    ∃ R : Matrix (Fin k) (Fin n) ℝ, L * R = M ∧
      v = (Finset.univ.sup' (by simp) (fun i : Option (Fin m) =>
        match i with | none => 0 | some i => Real.sqrt (∑ j, (L i j)^2))) *
        (Finset.univ.sup' (by simp) (fun j : Option (Fin n) =>
        match j with | none => 0 | some j => Real.sqrt (∑ i, (R i j)^2)))}

noncomputable def runningMax (v : ℕ → ℝ) (t : ℕ) : ℝ :=
  (Finset.range (t+1)).sup' (by simp) v

/-- Raw horizon-dependent Toeplitz coefficient pairs, with no product or norm data. -/
structure InnerFamily where
  decoder : ℕ → ℕ → ℝ
  strategy : ℕ → ℕ → ℝ

noncomputable def squareRootFamily : InnerFamily where
  decoder n j := Real.sqrt (squareEnergy n) * sqrtCoeff j
  strategy n j := sqrtCoeff j / Real.sqrt (squareEnergy n)

/-- The normalized finite factors required in Appendix E.3. These are obligations
for an existential family, not hypotheses of the clock theorem. -/
def InnerAccuracy (F : InnerFamily) (η : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n →
    (∀ s : ℕ, s < n →
      (∑ j ∈ Finset.range (s+1), F.decoder n j * F.strategy n (s-j)) = 1) ∧
    (∑ j ∈ Finset.range n, (F.strategy n j)^2) = 1 ∧
    (∀ s : ℕ, s ≤ n → (∑ j ∈ Finset.range s, (F.strategy n j)^2) ≤ 1) ∧
    (∀ s : ℕ, s ≤ n →
      (∑ j ∈ Finset.range s, (F.decoder n j)^2) ≤ (squareEnergy n + η)^2)

/-- A finite linear filter with feedthrough; both Toeplitz symbols admit this form.
The state dimension is not misidentified with the order of its scalar recurrence. -/
def IsBuffered (c : ℕ → ℝ) : Prop :=
  ∃ d : ℕ, ∃ A : Matrix (Fin d) (Fin d) ℝ, ∃ u v : Fin d → ℝ, ∃ τ : ℝ,
    c 0 = τ + (v ⬝ᵥ u) ∧
    ∀ j : ℕ, c (j+1) = dotProduct v (Matrix.mulVec (A^(j+1)) u)

def BufferedFamily (F : InnerFamily) : Prop :=
  ∀ n : ℕ, 0 < n → IsBuffered (F.decoder n) ∧ IsBuffered (F.strategy n)

end PrivateContinualCounting.Kraft.Supplement


