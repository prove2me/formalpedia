-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmC
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:56.410215+00:00
-- url     : https://prove2.me/theorems/1487ea9a-7376-4ed4-91f7-363e769de469
-- title:
--   Det Adm C
-- statement:
--   Definitions and structural lemmas for Det Adm C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DetAdmC.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_continuous_crd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW.DeterminantAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabW.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabW
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported
section Crd
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) {a M : ℕ}
def crdH (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    (Fin a → Fin M → R ⊗[F] E) ≃ₜ (Fin a × Fin M × Fin d → R) where
  toFun X c := crd b R (X c.1 c.2.1) c.2.2
  invFun Y x i := (Algebra.TensorProduct.basis R b).equivFun.symm (fun k => Y (x, i, k))
  left_inv X := by
    funext x i
    show (Algebra.TensorProduct.basis R b).equivFun.symm (fun k => crd b R (X x i) k) = X x i
    have e : (fun k => crd b R (X x i) k) = (Algebra.TensorProduct.basis R b).equivFun (X x i) := by
      funext k
      simp [crd, Module.Basis.equivFun_apply]
    rw [e, LinearEquiv.symm_apply_apply]
  right_inv Y := by
    funext c
    show crd b R ((Algebra.TensorProduct.basis R b).equivFun.symm (fun k => Y (c.1, c.2.1, k))) c.2.2
      = Y c
    have e : ∀ y, crd b R y c.2.2 = (Algebra.TensorProduct.basis R b).equivFun y c.2.2 := fun y => by
      simp [crd, Module.Basis.equivFun_apply]
    rw [e, LinearEquiv.apply_symm_apply]
  continuous_toFun := continuous_pi fun c =>
    (continuous_crd b R c.2.2).comp ((continuous_apply c.2.1).comp (continuous_apply c.1))
  continuous_invFun := continuous_pi fun x => continuous_pi fun i =>
    (IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap).comp
      (continuous_pi fun k => continuous_apply _)
end Crd
section Split
variable (F : Type) [Field F] [NumberField F]
def splitH (ι : Type) : (ι → AF F) ≃ₜ (ι → Ainf F) × (ι → Af F) where
  toFun Y := (fun c => fstA F (Y c), fun c => sndA F (Y c))
  invFun p c := pairA F (p.1 c) (p.2 c)
  left_inv Y := rfl
  right_inv p := rfl
  continuous_toFun := by
    refine (continuous_pi fun c => ?_).prodMk (continuous_pi fun c => ?_)
    · exact continuous_fst.comp (continuous_apply c)
    · exact continuous_snd.comp (continuous_apply c)
  continuous_invFun := continuous_pi fun c =>
    ((continuous_apply c).comp continuous_fst).prodMk ((continuous_apply c).comp continuous_snd)
end Split
section admitted
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {a M : ℕ}
def locBox (D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fin a → Fin M → Fv F v ⊗[F] E) :=
  (crdH b (Fv F v)) ⁻¹' (Set.pi univ fun c => D c v)
variable {b}
end admitted
section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {a M : ℕ}
variable (F E a M) in

def psiH : (Fin a → Fin M → AF F ⊗[F] E) ≃ₜ
    (Fin a × Fin M × Fin (Module.finrank F E) → Ainf F) ×
      (Fin a × Fin M × Fin (Module.finrank F E) → Af F) :=
  (crdH (Module.finBasis F E) (AF F)).trans (splitH F _)
end Main
end PI.VolStabW.DeterminantAdmissible


