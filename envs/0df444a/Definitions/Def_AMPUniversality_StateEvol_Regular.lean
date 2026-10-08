-- Prove2me | Definitions.Def_AMPUniversality_StateEvol_Regular
-- name    : AMPUniversality_StateEvol_Regular
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T05:28:37.705854+00:00
-- url     : https://prove2.me/theorems/4b2a5671-915f-47d4-8a26-ea690874b9e9
-- title:
--   (C,d)-regular polynomial AMP sequences, Definition 4
-- statement:
--   A random AMP sequence is $(C,d)$-regular when $C>0$: each matrix is symmetric with zero diagonal; its upper-triangular entries are independent, centered, and sub-Gaussian with variance proxy $C/N$; the polynomial coefficients are bounded by $C$ and independent of the matrix and initial condition; and the initial squared Euclidean norms satisfy the exponential bound
--
--   $$\sum_{i=1}^{N}\exp(\|x_i^{0,N}\|_2^2/C)\le NC.$$
--
--   Measurability is explicit. This is the common random-matrix and initial-data hypothesis used by the state-evolution results.
--
--   **Formalization Note** The sub-Gaussian moment-generating bound is imposed for all real arguments; the paper's displayed scale-factor formula conflicts with its stated $C/N$ scale. The initial bound is imposed almost surely for each $N$, as the proof uses it deterministically in expectation estimates. These readings are recorded in the moderation notes.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 7, (1.7), Definition 4

import Definitions.Def_AMPUniversality_StateEvol_Orbit

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace AMPUniversality.StateEvol

/-- Definition 4, with the paper's sub-Gaussian scale and the almost-sure reading
of its initial exponential bound. -/
def IsRegular {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (C : ℝ) (d q : ℕ)
    (A : ∀ N : ℕ, Ω → Matrix (Fin N) (Fin N) ℝ)
    (c : ∀ N : ℕ, Ω → Fin N → ℕ → Fin q → (Fin q → Fin (d + 1)) → ℝ)
    (x0 : ∀ N : ℕ, Ω → Fin N → Fin q → ℝ) : Prop :=
  0 < C ∧
  (∀ N ω, (A N ω).IsSymm ∧ ∀ i, A N ω i i = 0) ∧
  (∀ N, iIndepFun
    (fun p : {p : Fin N × Fin N // p.1 < p.2} =>
      fun ω => A N ω p.1.1 p.1.2) P) ∧
  (∀ N (i j : Fin N), i < j →
    (∫ ω, A N ω i j ∂P) = 0 ∧
    HasSubgaussianMGF (fun ω => A N ω i j)
      ⟨max 0 (C / (N : ℝ)), le_max_left _ _⟩ P) ∧
  (∀ N ω i t r m, |c N ω i t r m| ≤ C) ∧
  (∀ N, IndepFun (fun ω => fun (i j : Fin N) => A N ω i j)
      (fun ω => (c N ω, x0 N ω)) P ∧
    IndepFun (c N) (x0 N) P) ∧
  (∀ N, (∀ (i j : Fin N), Measurable (fun ω => A N ω i j)) ∧
    Measurable (c N) ∧ Measurable (x0 N)) ∧
  (∀ N, ∀ᵐ ω ∂P,
    (∑ i, Real.exp ((∑ s, (x0 N ω i s) ^ 2) / C)) ≤ (N : ℝ) * C)

end AMPUniversality.StateEvol


