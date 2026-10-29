-- Prove2me | Definitions.Def_PutermanMDP_SemiMarkov_Deviation
-- name    : PutermanMDP_SemiMarkov_Deviation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:49.71296+00:00
-- url     : https://prove2.me/theorems/0e65fddb-a098-48b3-b394-5758fb035cd9
-- title:
--   Deviation matrix and the constructed stationary bias
-- statement:
--   For a finite state space, let $M_d$ be the embedded transition matrix of a stationary randomized rule and let $M_d^*$ be its Cesaro matrix. Define the deviation matrix and stationary bias by
--   $$H_d=(I-M_d+M_d^*)^{-1}(I-M_d^*),\qquad h^{d^\infty}=H_d\bigl(r_d-g^{d^\infty}y_d\bigr).$$
--   The product with $g^{d^\infty}$ is componentwise. This constructs the particular bias named in Theorem 11.4.3, rather than treating the bias as an arbitrary solution.
--
--   **Formalization Note** Matrix inversion is Lean's total nonsingular inverse. Extended gains are converted to real numbers in this definition; the finite evaluation theorem separately asserts that every gain equals one common real number, so the conversion cannot hide an infinite value in that theorem. Outside its hypotheses, the definitions retain their total-function defaults.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, https://doi.org/10.1002/9780470316887, p. 552 (PDF 568), Theorem 11.4.3

import Definitions.Def_PutermanMDP_SemiMarkov_Stationary

open scoped Matrix

namespace PutermanMDP.SemiMarkov

variable {S : Type*} [Fintype S] [DecidableEq S]

noncomputable def transitionMatrix (M : Model S) (d : Rule M) : Matrix S S ℝ :=
  fun s j => (embedded M d s j).toReal

noncomputable def cesaroMatrix (M : Model S) (d : Rule M) : Matrix S S ℝ :=
  fun s j => limitingMatrix M d s j

/-- H_d = (I - M_d + M_d*)⁻¹ (I - M_d*), the source's normalized deviation matrix. -/
noncomputable def deviation (M : Model S) (d : Rule M) : Matrix S S ℝ :=
  (1 - transitionMatrix M d + cesaroMatrix M d)⁻¹ * (1 - cesaroMatrix M d)

/-- The bias constructed by Theorem 11.4.3, not an arbitrary solution. -/
noncomputable def stationaryBias (M : Model S) (d : Rule M) : S → ℝ :=
  (deviation M d).mulVec
    (fun s => ruleReward M d s - (gain M d s).toReal * ruleTime M d s)

end PutermanMDP.SemiMarkov


