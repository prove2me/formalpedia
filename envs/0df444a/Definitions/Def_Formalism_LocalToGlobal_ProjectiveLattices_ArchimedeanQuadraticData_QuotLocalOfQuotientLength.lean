-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_QuotLocalOfQuotientLength
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_QuotLocalOfQuotientLength
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:17:29.746919+00:00
-- url     : https://prove2.me/theorems/af22ba93-c441-4ef6-bc29-794cb9049c40
-- title:
--   Quot Local Of Quotient Length
-- statement:
--   Definitions and structural lemmas for Quot Local Of Quotient Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/QuotLocalOfQuotientLength.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.Pj.QAt
namespace TieQL
open Module
variable {O Q : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [AddCommGroup Q] [Module O Q] {ρ : ℕ}
noncomputable def coordK (b : Basis (Fin ρ) O Q) : Q →ₗ[O] (Fin ρ → FractionRing O) where
  toFun q k := algebraMap O (FractionRing O) (b.repr q k)
  map_add' x y := by ext k; simp
  map_smul' r x := by ext k; simp [Algebra.smul_def]
noncomputable def matA (b : Basis (Fin ρ) O Q) (c : Fin ρ → (Q →ₗ[O] O)) :
    Matrix (Fin ρ) (Fin ρ) O :=
  Matrix.of fun i k => c i (b k)
noncomputable def cK (b : Basis (Fin ρ) O Q) (c : Fin ρ → (Q →ₗ[O] O)) :
    (Fin ρ → FractionRing O) →ₗ[FractionRing O] (Fin ρ → FractionRing O) :=
  Matrix.toLin' ((matA b c).map (algebraMap O (FractionRing O)))
end TieQL
end Formalism.L2.Pj.QAt


