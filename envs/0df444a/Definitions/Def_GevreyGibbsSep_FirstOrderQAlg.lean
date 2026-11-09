-- Prove2me | Definitions.Def_GevreyGibbsSep_FirstOrderQAlg
-- name    : GevreyGibbsSep_FirstOrderQAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:42:32.699424+00:00
-- url     : https://prove2.me/theorems/9c1c9f2a-a6bd-495a-b55f-57d9649d66cf
-- title:
--   First-order quantum algorithm with $T$ oracle calls
-- statement:
--   A **first-order quantum algorithm** accesses the instance only through the gradient oracle (7) and its inverse. With $T$ oracle calls it consists of
--
--   1. a unit start vector $|\psi_0\rangle$;
--   2. unitaries $U_0,U_1,\dots,U_T$;
--   3. for each of the $T$ calls, the choice of $O_{\nabla E}$ or $O_{\nabla E}^\dagger$;
--   4. a classical post-processing rule that turns the outcome of a final measurement in the computational basis into a point of $\mathbb T^d$ (a probability distribution for each outcome).
--
--   None of these depends on the instance $E$; $E$ enters only through the oracle.
--
--   **Formalization Note** The paper does not define its quantum model; this is the reading recorded for the mission. Intermediate measurements, heralded success and restarts are covered by deferred measurement.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), p.6 (definition of a first-order quantum algorithm); Theorem 2, pp.10–11

import Mathlib
import Definitions.Def_GevreyGibbsSep_Torus
import Definitions.Def_GevreyGibbsSep_oracle
import Definitions.Def_GevreyGibbsSep_QReg
import Definitions.Def_GevreyGibbsSep_QH

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- A first-order quantum algorithm with `T` queries (arXiv:2608.24527 (sha256 d4fd40eb…), p.6:
an algorithm that accesses the instance only through the gradient oracle (7) and its inverse).
It consists of a unit start vector, unitaries `U_0, …, U_T`, for each of the `T` oracle calls a
choice of `O_∇E` or its inverse, and a classical post-processing kernel applied to the outcome of
a final computational-basis measurement. None of these depends on the instance `E`.

**Formalization Note** The paper does not define its quantum model; this is the reading recorded
for the mission (paper.md R1). Intermediate measurements and restarts are covered by deferred
measurement. -/
structure FirstOrderQAlg (d : ℕ) (W : Type) (T : ℕ) where
  /-- The initial state. -/
  start : QH d W
  norm_start : ‖start‖ = 1
  /-- The instance-independent unitaries `U_0, …, U_T`. -/
  U : Fin (T + 1) → (QH d W ≃ₗᵢ[ℂ] QH d W)
  /-- Whether the `i`-th oracle call is `O_∇E^†` (`true`) or `O_∇E` (`false`). -/
  useInv : Fin T → Bool
  /-- Classical post-processing of the measured basis label into a point of `T^d`. -/
  post : QReg d W → ProbabilityMeasure (Torus d)

end GevreyGibbsSep


