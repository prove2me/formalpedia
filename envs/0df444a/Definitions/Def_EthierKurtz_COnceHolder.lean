-- Prove2me | Definitions.Def_EthierKurtz_COnceHolder
-- name    : EthierKurtz_COnceHolder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:12:03.023643+00:00
-- url     : https://prove2.me/theorems/976bae7a-b489-4a09-a6ea-493f9b751e0b
-- title:
--   Interior C¹,μ regularity
-- statement:
--   A continuously differentiable scalar function whose first partial derivatives satisfy the componentwise local Hölder condition.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, equations (1.13)–(1.14), printed p. 368 (PDF p. 377).

import Definitions.Def_EthierKurtz_ComponentHolder

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- C^{1,μ} with the component oscillation convention (1.13)–(1.14). -/
def COnceHolder {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (μ : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiffOn ℝ 1 f D ∧ ∀ i : Fin d,
    ComponentHolder D μ (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))

end EthierKurtz


