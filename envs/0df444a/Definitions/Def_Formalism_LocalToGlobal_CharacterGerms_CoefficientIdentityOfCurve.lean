-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoefficientIdentityOfCurve
-- name    : Formalism_LocalToGlobal_CharacterGerms_CoefficientIdentityOfCurve
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:19.211866+00:00
-- url     : https://prove2.me/theorems/7fb6a7fa-75fd-4d2c-af2c-88e5d622d5e9
-- title:
--   Coefficient Identity Of Curve
-- statement:
--   Definitions and structural lemmas for Coefficient Identity Of Curve, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoefficientIdentityOfCurve.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
section Closed
variable {C : Type} [Field C]
def PsiCurveFBSt : Prop :=
  AllFB fun C _ V _ I _ dd X => X.RankHyp → ∀ _H : ∀ g, X.CartHyp V g, X.AltC → ∀ g,
    ∃ M : JJ I g → JJ I g → C, (∀ q' q, V.Ge 0 (M q' q)) ∧
      ∀ x ∈ X.TySet V g, ∀ (γ : Fin dd → PowerSeries C) (lam : JJ I g → PowerSeries C),
        IsCv V γ → IsCv V lam →
        (∀ i, alongCv γ (X.lg i) =
          ∑ c : I g, X.u g c i • tyS V.l (fun s => Vpow 1 (Fs V.l x) s (Sum.inl c))) →
        (∀ q : JJ I g, tyS V.l (fun s => Vpow 1 (Fs V.l x) s (Sum.inr q)) =
          lam q - alongCv γ (X.sg (X.u (1 - g) q)) +
            ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
              X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => Vpow 1 (Fs V.l x) s (Sum.inl c)) else 0) →
        (∀ i, ∀ m < V.l ^ 2, PowerSeries.coeff m (γ i) = 0) →
        (∀ i, V.MM (PowerSeries.coeff (V.l ^ 2) (γ i))) →
        ∀ q, V.MM (PowerSeries.coeff V.l (lam q) ^ V.l -
          ∑ q', PowerSeries.coeff (V.l ^ 2) (lam q') * M q' q)
end Closed
end Formalism.L2.FormalSeriesBounds


