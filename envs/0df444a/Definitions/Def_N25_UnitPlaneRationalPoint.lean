-- Prove2me | Definitions.Def_N25_UnitPlaneRationalPoint
-- name    : N25_UnitPlaneRationalPoint
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:47.519193+00:00
-- url     : https://prove2.me/theorems/f65e725c-dd45-4f83-9c20-2b8991821833
-- title:
--   Local algebra of a rational point on the unit-plane curve
-- statement:
--   For a rational solution $(u,v)$ of $R(u,v)=0$, the file defines the evaluation map $A→ℚ$, its maximal kernel $m_{u,v}$, the local ring $A_{m_{u,v}}$, and an $ℚ$-algebra equivalence between its residue field and $ℚ$. This is the local-algebraic package underlying the place attached to a rational plane point.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitPlaneRing
import Definitions.Def_Algebra_LocalizationAtPrimeResidue
noncomputable section
namespace N25

/-- Evaluation of the actual plane coordinate ring at a rational plane point. -/
def unitPlaneEvaluation25 (u v : ℚ) (hr : planeRelation u v = 0) :
    UnitPlaneRing →ₐ[ℚ] ℚ :=
  AdjoinRoot.liftAlgHom unitPlanePolynomial (Polynomial.aeval u) v (by
    simpa [unitPlanePolynomial, planeRelation, Polynomial.eval₂_pow] using hr)

/-- The maximal ideal of an actual rational point on the plane relation. -/
def unitPlanePointIdeal25 (u v : ℚ) (hr : planeRelation u v = 0) :
    Ideal UnitPlaneRing := RingHom.ker (unitPlaneEvaluation25 u v hr).toRingHom

instance unitPlanePointIdeal25_isMaximal (u v : ℚ) (hr : planeRelation u v = 0) :
    (unitPlanePointIdeal25 u v hr).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun a =>
    ⟨algebraMap ℚ UnitPlaneRing a, (unitPlaneEvaluation25 u v hr).commutes a⟩)

/-- The local ring at the evaluation kernel of a rational plane point. -/
abbrev UnitPlanePointLocalRing25 (u v : ℚ) (hr : planeRelation u v = 0) :=
  Localization.AtPrime (unitPlanePointIdeal25 u v hr)

/-- The local ring has rational residue field with its actual constant action. -/
def unitPlanePointResidueAlgEquiv25 (u v : ℚ) (hr : planeRelation u v = 0) :
    IsLocalRing.ResidueField (UnitPlanePointLocalRing25 u v hr) ≃ₐ[ℚ] ℚ :=
  IsLocalization.AtPrime.rationalPointResidueAlgEquiv
    (unitPlaneEvaluation25 u v hr) (unitPlanePointIdeal25 u v hr) rfl

end N25


