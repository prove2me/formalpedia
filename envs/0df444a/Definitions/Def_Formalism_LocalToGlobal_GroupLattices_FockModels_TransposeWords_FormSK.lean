-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FormSK
-- name    : Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FormSK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:41.699843+00:00
-- url     : https://prove2.me/theorems/6c132daf-8a10-4827-8ba3-fd97e00ef39b
-- title:
--   Form SK
-- statement:
--   Definitions and structural lemmas for Form SK, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/FormSK.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_DualWeylIn
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.L2.G.Model.TS
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility
def nabO (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (ν : Fin (m + 1) → ℕ) :
    Submodule O (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :=
  Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap (dualWeyl O (m + 1) (m + 1) ν)
def expN (p m : ℕ) (lam : Fin (m + 1) → ℤ) : ℕ :=
  if ellWt lam = 0 then 0 else N0 (m + 1) * deF p (m + 1) (ellWt lam)
def FormCoreSK : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
    ∃ B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] Kf,
      (∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf),
        B (rowAct Kf g P) Q = B P (rowAct Kf g.transpose Q)) ∧
      (∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam),
        (∀ P ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam), B P Q = 0) → Q = 0) ∧
      (∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam),
        (∀ P ∈ nabO O Kf m (nuOf lam), B P Q ∈ Set.range (algebraMap O Kf)) → Q ∈ nabO O Kf m (nuOf lam)) ∧
      (∀ Q ∈ nabO O Kf m (nuOf lam), ∀ P ∈ nabO O Kf m (nuOf lam),
        B P (((p : Kf) ^ expN p m lam) • Q) ∈ Set.range (algebraMap O Kf))
end Formalism.L2.G.Model.TS


