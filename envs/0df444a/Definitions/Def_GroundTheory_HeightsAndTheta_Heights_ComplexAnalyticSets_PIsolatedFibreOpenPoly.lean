-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenPoly
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenPoly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:07.364584+00:00
-- url     : https://prove2.me/theorems/0c5ccc5b-d6a6-4f60-be92-60a3d65a237d
-- title:
--   PIsolated Fibre Open Poly
-- statement:
--   Definitions and structural lemmas for PIsolated Fibre Open Poly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpenPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Topology Filter Matrix ComplexSets
noncomputable section
namespace IsolatedFibreOpenPoly
variable {n d : ℕ}
def graphSubst (p : Fin d → MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin (n + d)) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (Fin.append X p)
def graphIdeal (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) :
    Ideal (MvPolynomial (Fin (n + d)) ℂ) :=
  P.comap (graphSubst p)
def graphPt (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin (n + d) → ℂ :=
  Fin.append x fun i => eval x (p i)
def firstPart (z : Fin (n + d) → ℂ) : Fin n → ℂ :=
  fun j => z (Fin.castAdd d j)
def lastRows (n d : ℕ) : Matrix (Fin d) (Fin (n + d)) ℂ :=
  fun i j => if j = Fin.natAdd n i then 1 else 0
end IsolatedFibreOpenPoly
end
end GroundTheory.Heights₂.Heights


