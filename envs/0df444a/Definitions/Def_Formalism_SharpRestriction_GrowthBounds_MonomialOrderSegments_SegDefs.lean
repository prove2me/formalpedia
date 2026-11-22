-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:49:20.426646+00:00
-- url     : https://prove2.me/theorems/0ea8be83-89cb-444a-b2b3-3158d68d2bc1
-- title:
--   Seg Defs
-- statement:
--   Definitions and structural lemmas for Seg Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SegDefs.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
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
variable {K : Type} [Field K] (D : TwistData K)
def TLset (j : Fin D.J) (m : Fin D.r) : Finset D.ML :=
  (D.LLj j).image D.mb ∪ (univ.filter fun m' : Fin D.r => m < m').image fun m' => D.mlab (j, m')
def YPset (j : Fin D.J) (m : Fin D.r) : Finset D.ML :=
  (D.LLj j).image D.mb ∪ (univ.filter fun m' : Fin D.r => m < m').image fun m' => D.mtp (j, m')
def SegL (j : Fin D.J) (i : D.ML) : Prop :=
  (∃ b, D.seg b = j ∧ i = D.mb b) ∨ (∃ m, i = D.mlab (j, m)) ∨ (∃ m, i = D.mtp (j, m))
def PreE (j : Fin D.J) (ζ : D.EM) : Prop :=
  (∀ b, D.seg b = j → ldeg ζ (D.mb b) = D.dB b) ∧ (∀ m, ldeg ζ (D.mlab (j, m)) = D.dT (j, m)) ∧
  (∀ m a, ζ (D.mtp (j, m), a) = 0)
def PostE (j : Fin D.J) (ζ : D.EM) : Prop :=
  (∀ b, D.seg b = j → ldeg ζ (D.mb b) = D.dB b) ∧
  (∀ m, ldeg ζ (D.mlab (j, m)) + ldeg ζ (D.mtp (j, m)) = D.dT (j, m)) ∧
  (∀ m, ldeg ζ (D.mtp (j, m)) ≤ D.dLL j) ∧
  (∀ m : Fin D.r, m.val = 0 → ∀ a, ζ (D.mtp (j, m), a) = 0)
end TwistData
def SegStep (K : Type) [Field K] [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ) : Prop :=
  DVRHyp v p → ∀ D : TwistData K, 0 < D.r → 0 < D.J → ∀ j : Fin D.J,
    ∃ Th : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K,
      (∀ ζ : D.EM, D.PreE j ζ → Integral v (Th (monomial ζ 1))) ∧
      (∀ ζ : D.EM, D.PreE j ζ → D.ph p (Th (monomial ζ 1)) = D.ph p (monomial ζ 1)) ∧
      (∀ ζ : D.EM, D.PreE j ζ → ∀ ζ' ∈ (Th (monomial ζ 1)).support,
        D.PostE j ζ' ∧ ∀ i, ¬ D.SegL j i → ∀ a, ζ' (i, a) = ζ (i, a)) ∧
      (∀ Z : MvPolynomial (D.ML × Fin D.r) K, Integral v Z → (∀ ζ ∈ Z.support, D.PreE j ζ) →
        ∀ (m : Fin D.r) (θ : ℝ), m.val + 2 ≤ D.r →
          vala D.msg (D.TLset j m) θ Z → vala D.msg (D.YPset j m) θ (Th Z)) ∧
      (∀ S : Finset D.ML, (∀ i ∈ S, ¬ D.SegL j i) → ∀ Z : MvPolynomial (D.ML × Fin D.r) K,
        valS D.msg S Z ≤ valS D.msg S (Th Z))
end Formalism.MainNotions.PlaneGram


