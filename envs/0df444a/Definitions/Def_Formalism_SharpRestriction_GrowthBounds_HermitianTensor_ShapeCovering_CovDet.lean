-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_HermitianTensor_ShapeCovering_CovDet
-- name    : Formalism_SharpRestriction_GrowthBounds_HermitianTensor_ShapeCovering_CovDet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:43.199939+00:00
-- url     : https://prove2.me/theorems/1fed3b4a-dd40-45ef-8e5d-6b7ffb12e4fb
-- title:
--   Cov Det
-- statement:
--   Definitions and structural lemmas for Cov Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/HermitianTensor/ShapeCovering/CovDet.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_HermitianTensor_ShapeCovering_StatementY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
open MvPolynomial Formalism.GradedWeylDivisibility
def cvdM (K : Type) [Field K] (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :=
  fun a b => Fin.cases 0 (fun b' : Fin m => X (a, b'.castSucc)) b
def cvdN {F : Type*} [Field F] {k : ℕ} (z : Fin (k + 2) → F) : Matrix (Fin (k + 2)) (Fin (k + 2)) F :=
  fun i j => if i = 0 then z j else if i = j then (if i = 1 then (z 0)⁻¹ else 1) else 0
end Formalism.MainNotions.flipOneThree.Pf.ShapeCovering


