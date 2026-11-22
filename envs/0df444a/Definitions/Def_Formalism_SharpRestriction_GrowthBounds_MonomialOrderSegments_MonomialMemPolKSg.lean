-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:27:18.754584+00:00
-- url     : https://prove2.me/theorems/cacd3ed3-1297-4dbf-ab70-8bed454644a3
-- title:
--   Monomial Mem Pol KSg
-- statement:
--   Definitions and structural lemmas for Monomial Mem Pol KSg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
namespace TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
def outSeg (i : D.ML) : Prop := ¬ ∃ k, D.e0 j k = i
instance : DecidablePred (D.outSeg j) := Classical.decPred _
instance : DecidablePred (D.SegL j) := Classical.decPred _
def pullE (ζ : D.EM) : Fin (D.nB j + D.r) × Fin D.r →₀ ℕ :=
  Finsupp.comapDomain (Prod.map (D.e0 j) id) ζ
    (((D.index_embedding_injective j).prodMap (Function.injective_id (α := Fin D.r))).injOn)
variable {ι : Type} [Fintype ι]
def TT (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K) :
    MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K :=
  lsup fun lam => ∑ b, cc lam b • PP b
def Th (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K) :
    MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K :=
  lsup fun ζ => monomial (eOut (D.outSeg j) ζ) 1 * D.TT j cc PP (monomial (D.pullE j ζ) 1)
variable (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)
end TwistData
end Formalism.MainNotions.PlaneGram


