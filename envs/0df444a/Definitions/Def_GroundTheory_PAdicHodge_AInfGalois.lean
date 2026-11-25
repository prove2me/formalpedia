-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
-- name    : GroundTheory_PAdicHodge_AInfGalois
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:33:00.076693+00:00
-- url     : https://prove2.me/theorems/1aed7107-6444-4188-b36a-145b8b670f3a
-- title:
--   AInf Galois
-- statement:
--   Definitions and structural lemmas for AInf Galois, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfGalois.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Theorems.Thm_GroundTheory_PAdicHodge_galCp_mul
import Theorems.Thm_GroundTheory_PAdicHodge_galCp_one
import Theorems.Thm_GroundTheory_PAdicHodge_norm_galCp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
namespace AInf
section Functor
variable {K L M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [NontriviallyNormedField M]
  [IsUltrametricDist M]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
  [IsPerfectoidField M p]
variable (p) in

def map (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) : AInf K p →+* AInf L p :=
  WittVector.map (preTiltMap p φ hφ)
theorem map_coeff (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (x : AInf K p) (n : ℕ) :
    (map p φ hφ x).coeff n = preTiltMap p φ hφ (x.coeff n) :=
  WittVector.map_coeff _ _ _
theorem map_congr {φ ψ : K →+* L} (h : φ = ψ) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) :
    map p φ hφ = map p ψ hψ := by
  subst h; rfl
theorem map_comp (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (ψ : L →+* M) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) :
    map p (ψ.comp φ) (norm_comp_eq hφ hψ) = (map p ψ hψ).comp (map p φ hφ) := by
  refine RingHom.ext fun x => WittVector.ext fun n => ?_
  rw [RingHom.comp_apply, map_coeff, map_coeff, map_coeff, preTiltMap_comp, RingHom.comp_apply]
theorem preTiltMap_id (x : PreTilt (normInteger K) p) :
    preTiltMap p (RingHom.id K) (fun _ => rfl) x = x := by
  refine Perfection.ext fun n => ?_
  rw [coeff_preTiltMap]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (Perfection.coeff (ModP (normInteger K) p) p n x)
  rw [← ha, modPMap_mk]
  congr 1
theorem map_id : map p (RingHom.id K) (fun _ => rfl) = RingHom.id (AInf K p) := by
  refine RingHom.ext fun x => WittVector.ext fun n => ?_
  rw [map_coeff, preTiltMap_id, RingHom.id_apply]
omit [IsUltrametricDist K] in

theorem norm_toRingHom_apply (σ : K ≃+* K) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (x : K) :
    ‖(σ : K →+* K) x‖ = ‖x‖ :=
  hσ x
omit [IsUltrametricDist K] in

theorem norm_symm_toRingHom_apply (σ : K ≃+* K) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (x : K) :
    ‖(σ.symm : K →+* K) x‖ = ‖x‖ := by
  change ‖σ.symm x‖ = ‖x‖
  rw [← hσ, RingEquiv.apply_symm_apply]
variable (p) in

def mapEquiv (σ : K ≃+* K) (hσ : ∀ x, ‖σ x‖ = ‖x‖) : AInf K p ≃+* AInf K p :=
  RingEquiv.ofRingHom (map p (σ : K →+* K) (norm_toRingHom_apply σ hσ))
    (map p (σ.symm : K →+* K) (norm_symm_toRingHom_apply σ hσ))
    (by
      rw [← map_comp, ← map_id]
      exact map_congr (RingHom.ext fun x => σ.apply_symm_apply x) _ _)
    (by
      rw [← map_comp, ← map_id]
      exact map_congr (RingHom.ext fun x => σ.symm_apply_apply x) _ _)
end Functor
section Galois
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
theorem norm_galCp_toRingHom (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    ‖(galCp σ : ℂ_[p] →+* ℂ_[p]) x‖ = ‖x‖ :=
  norm_galCp σ x
def galMap (σ : Gal(PadicAlgCl p/K)) : AInf ℂ_[p] p →+* AInf ℂ_[p] p :=
  map p (galCp σ : ℂ_[p] →+* ℂ_[p]) (norm_galCp_toRingHom σ)
theorem galMap_one : galMap (1 : Gal(PadicAlgCl p/K)) = RingHom.id _ := by
  rw [galMap, ← map_id]
  exact map_congr (RingHom.ext fun x => by rw [galCp_one]; rfl) _ _
theorem galMap_mul (σ τ : Gal(PadicAlgCl p/K)) : galMap (σ * τ) = (galMap σ).comp (galMap τ) := by
  rw [galMap, galMap, galMap, ← map_comp]
  exact map_congr (RingHom.ext fun x => by rw [galCp_mul]; rfl) _ _
instance instMulSemiringActionGal : MulSemiringAction Gal(PadicAlgCl p/K) (AInf ℂ_[p] p) where
  smul σ x := galMap σ x
  one_smul x := by
    change galMap 1 x = x
    rw [galMap_one, RingHom.id_apply]
  mul_smul σ τ x := by
    change galMap (σ * τ) x = galMap σ (galMap τ x)
    rw [galMap_mul, RingHom.comp_apply]
  smul_zero σ := map_zero (galMap σ)
  smul_add σ := map_add (galMap σ)
  smul_one σ := map_one (galMap σ)
  smul_mul σ := map_mul (galMap σ)
end Galois
end AInf
end GroundTheory.PAdicHodge


