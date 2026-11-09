-- Prove2me | Definitions.Def_GevreyGibbsSep_finalState
-- name    : GevreyGibbsSep_finalState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:43:38.605132+00:00
-- url     : https://prove2.me/theorems/ad0bf815-4202-467b-b98c-ecef4c0e75a2
-- title:
--   Final state $U_T O^{\pm}\cdots U_1 O^{\pm} U_0|\psi_0\rangle$
-- statement:
--   The final state of a first-order quantum algorithm run with the oracle of $E$:
--   $$|\psi_T\rangle=U_T\,O^{\pm}_{\nabla E}\,U_{T-1}\cdots U_1\,O^{\pm}_{\nabla E}\,U_0|\psi_0\rangle ,$$
--   where each $O^{\pm}$ is the oracle or its inverse as the algorithm prescribes.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eq. (7), p.6

import Mathlib
import Definitions.Def_GevreyGibbsSep_oracle
import Definitions.Def_GevreyGibbsSep_QH
import Definitions.Def_GevreyGibbsSep_gradOracle
import Definitions.Def_GevreyGibbsSep_FirstOrderQAlg

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The state `U_T O^{±} U_{T−1} ⋯ U_1 O^{±} U_0 |start⟩` of a first-order quantum algorithm
run with the gradient oracle of `E` (arXiv:2608.24527 (sha256 d4fd40eb…), Eq. (7), p.6). -/
noncomputable def finalState {d : ℕ} {W : Type} {T : ℕ} (A : FirstOrderQAlg d W T)
    (E : (Fin d → ℝ) → ℝ) : QH d W :=
  (List.finRange T).foldl
    (fun ψ i => A.U i.succ (if A.useInv i then (gradOracle E).symm ψ else gradOracle E ψ))
    (A.U 0 A.start)

end GevreyGibbsSep


