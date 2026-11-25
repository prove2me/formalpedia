-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T03:03:59.94464+00:00
-- url     : https://prove2.me/theorems/d320a989-d728-4f02-9ba7-5b8d84d8acf3
-- title:
--   NZType E
-- statement:
--   Definitions and structural lemmas for NZType E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeE.lean

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_eSum_central_56b4ffc8a854
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_eSum_coeff_c97526e39ca4
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms NumberField IsDedekindDomain
variable {R : Ranks} {H : Host R}
theorem neZero_g (k : Fin 2) : NeZero (H.g k) := by
  exact ⟨(H.g_prime k).ne_zero⟩
theorem fact_g (k : Fin 2) : Fact (H.g k).Prime := by
  exact ⟨H.g_prime k⟩
attribute [local instance] neZero_g fact_g Classical.propDecidable
variable {what₂ : Rows.Data R} (N : NData R H what₂)
abbrev Ix : Type := Σ k : Fin 2, N.PlG k
def GoodT (f : ∀ k, N.PlG k → (ZMod (H.g k))[X]) : Prop :=
  ∀ k, haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (f k) (N.chiT k) ∧
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (f k) (fun v j => (N.chiT k v j)⁻¹)
variable {K : Type} [Field K]
def e0F (es : ∀ k, (ZMod (H.g k))[X] → MonoidAlgebra K (GL (Fin R.r) (ZMod (H.g k)))) :
    MonoidAlgebra K (G0g N) :=
  eSum (I := Ix N) (G := fun kv => GL (Fin R.r) (ZMod (H.g kv.1)))
    (L := fun kv => Fin R.r → ZMod (H.g kv.1)) (fun kv a => es kv.1 (monicOf a))
    (fun a => GoodT N fun k v => monicOf (a ⟨k, v⟩))
variable (es : ∀ k, (ZMod (H.g k))[X] → MonoidAlgebra K (GL (Fin R.r) (ZMod (H.g k))))
  (hidem : ∀ k f, es k f * es k f = es k f) (hcen : ∀ k f a, es k f * a = a * es k f)
  (horth : ∀ k f f', f ≠ f' → es k f * es k f' = 0)
include hcen in
theorem seriesIdempotent_central (a : MonoidAlgebra K (G0g N)) : e0F N es * a = a * e0F N es := by
  unfold e0F
  apply eSum_central
  intro i x b
  exact hcen i.1 (monicOf x) b
variable {N}
theorem e0_eq {A : NAut N} (X : NTypes A) : X.e0 = e0F N X.eSer := by
  apply MonoidAlgebra.ext
  ext g
  rw [e0F, eSum_coeff]
  simp only [Formalism.BasicNotions.NTypes.e0, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
  rw [finsum_eq_sum_of_fintype]
  rfl
theorem idempotent_mem_center {A : NAut N} (X : NTypes A) :
    X.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) := by
  rw [e0_eq X, Subalgebra.mem_center_iff]
  intro b
  exact (seriesIdempotent_central N X.eSer X.eSer_central b).symm
end Formalism.BasicNotions.Examples₂.NZ


