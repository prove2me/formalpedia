-- Prove2me | Definitions.Def_HighDimProb_DvoretzkyMilman_IsGaussianMatrix
-- name    : HighDimProb_DvoretzkyMilman_IsGaussianMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:13:24.668974+00:00
-- url     : https://prove2.me/theorems/721716f7-2a75-4bb1-82e2-778fca79e488
-- title:
--   A Gaussian random matrix with i.i.d. $N(0,1)$ entries
-- statement:
--   A random $m\times n$ matrix $A$ on a probability space is a **Gaussian random matrix with
--   i.i.d. $N(0,1)$ entries** if every entry has law $N(0,1)$ and the whole family of entries is
--   jointly independent — the measurement matrix of the goal theorem.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 276, Theorem 11.3.3 (hypothesis)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace HighDimProb.DvoretzkyMilman

/-- **`IsGaussianMatrix P A`**: the random `m × n` matrix `A` on the probability space `(Ω,P)` is a
**Gaussian random matrix with i.i.d. `N(0,1)` entries**. Vershynin, *High-Dimensional Probability*
(2018), Theorem 11.3.3: "Let `A` be an `m × n` Gaussian random matrix with i.i.d. `N(0,1)`
entries." Formalized entrywise: every entry `(i,j)` has law `N(0,1)` (Mathlib's `gaussianReal 0
1`), and the whole family of entries, indexed by `Fin m × Fin n`, is (jointly) independent — the
standard meaning of "i.i.d. entries" (identical marginal laws, joint independence, not merely
pairwise). -/
def IsGaussianMatrix {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {m n : ℕ}
    (A : Ω → Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (∀ p : Fin m × Fin n, Measure.map (fun ω => A ω p.1 p.2) P = gaussianReal 0 1) ∧
  iIndepFun (fun p : Fin m × Fin n => fun ω => A ω p.1 p.2) P

end HighDimProb.DvoretzkyMilman


