-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_ExistsSdWSdHerm
-- name    : Development_AutomorphicSpectrum_Proofs_HermitianForms_ExistsSdWSdHerm
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T13:39:40.9848+00:00
-- url     : https://prove2.me/theorems/43b9169b-ed45-4be8-8d0e-3a696f0bcc31
-- title:
--   Exists Sd WSd Herm
-- statement:
--   Definitions and structural lemmas for Exists Sd WSd Herm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/ExistsSdWSdHerm.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_IndicatorInSchrodingerSpanStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_AdelicCharacterLocalNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AdditiveCharConductorExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk


set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU Topology
open scoped TensorProduct
namespace GlobalTheory.CompanionTheory.SdFin
section Lat
open GlobalTheory.JR.DualLattice
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [LocallyCompactSpace K]
end Lat
section Local
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
end Local
section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
theorem sigR_smul (c : R) (z : R ⊗[F] E) : sigR R σ (c • z) = c • sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul a e => rfl
variable {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
noncomputable def bilinW (n : ℕ) : LinearMap.BilinForm R (Fin n → Fin M → R ⊗[F] E) :=
  LinearMap.mk₂ R (BR R σ J)
    (fun x x' y => by
      simp [BR, hR, hform, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp [BR, hR, hform, sigR_smul, Finset.mul_sum])
    (fun x y y' => by
      simp [BR, hR, hform, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp [BR, hR, hform, Finset.mul_sum])
@[reducible] def hermSMul (n : ℕ) : SMul R (HermR R σ n) :=
  ⟨fun c S => ⟨c • S.1, fun a b => by
    rw [Matrix.smul_apply, Matrix.smul_apply, sigR_smul, S.2 a b]⟩⟩
@[reducible] def hermModule (n : ℕ) : Module R (HermR R σ n) :=
  letI := hermSMul R σ n
  Function.Injective.module R (HermR R σ n).subtype Subtype.val_injective (fun _ _ => rfl)
noncomputable def bilinH (n : ℕ) :
    letI := hermModule R σ n
    LinearMap.BilinForm R (HermR R σ n) :=
  letI := hermModule R σ n
  LinearMap.mk₂ R (pairHerm R σ n)
    (fun x x' y => by
      simp [pairHerm, add_mul, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      change pairHerm R σ n ⟨c • x.1, _⟩ y = _
      simp [pairHerm, Finset.mul_sum, mul_left_comm c])
    (fun x y y' => by
      simp [pairHerm, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      change pairHerm R σ n x ⟨c • y.1, _⟩ = _
      simp [pairHerm, Finset.mul_sum, mul_left_comm c])
end Alg
noncomputable def psiChar {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) : AddChar (Fv F v) ℂ where
  toFun := psiV F ψ v
  map_zero_eq_one' := by
    classical
    have : pairA F 0 (singleV F v 0) = 0 :=
      Prod.ext rfl (Subtype.ext (Pi.single_zero v))
    rw [psiV, this, AddChar.map_zero_eq_one]
  map_add_eq_mul' a b := by
    classical
    have : pairA F 0 (singleV F v (a + b)) = pairA F 0 (singleV F v a) + pairA F 0 (singleV F v b) :=
      Prod.ext (add_zero 0).symm (Subtype.ext (Pi.single_add v a b))
    rw [psiV, this, AddChar.map_add_eq_mul]; rfl
end GlobalTheory.CompanionTheory.SdFin


