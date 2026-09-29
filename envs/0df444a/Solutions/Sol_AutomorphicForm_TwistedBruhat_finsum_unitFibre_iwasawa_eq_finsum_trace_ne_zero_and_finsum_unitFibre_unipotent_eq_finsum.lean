-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.finsum_unitFibre_iwasawa_eq_finsum_trace_ne_zero_and_finsum_unitFibre_unipotent_eq_finsum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/8caf8fef-1222-51c5-94c9-188aca62f484

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Theorems.Thm_LT_TwistedNorm_exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mul_eq_mul_map_and_trace_ne_zero_of_apply_one_zero_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_finsum_unitFibre_iwasawa_eq_finsum_trace_ne_zero_and_finsum_unitFibre_unipotent_eq_finsum

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.AdelicTracePushforward

set_option linter.unusedSectionVars false

namespace XMerge

theorem map_scalar' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (s : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) s)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) s) := by
  apply Units.ext
  ext i j
  show f ((Matrix.scalar (Fin 2) (s : R)) i j) = (Matrix.scalar (Fin 2) (f (s : R))) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem unipotentGL2_inv' {L : Type} [Field L] [NumberField L] (q : AdeleRing (𝓞 L) L) :
    (AutomorphicForm.unipotentGL2 q : AutomorphicForm.AdelicGL2 (𝓞 L) L)⁻¹ = AutomorphicForm.unipotentGL2 (-q) :=
  Units.ext rfl

theorem centralScalar_mul_comm' {L : Type} [Field L] [NumberField L] (z : (AdeleRing (𝓞 L) L)ˣ)
    (h : AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.centralScalar (𝓞 L) L z * h = h * AutomorphicForm.centralScalar (𝓞 L) L z := by
  have hcoe : ((AutomorphicForm.centralScalar (𝓞 L) L z : AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) := rfl
  ext i j
  have hc := (Matrix.scalar_commute (z : AdeleRing (𝓞 L) L) (fun r => Commute.all _ r)
    ((h : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq
  rw [Units.val_mul, Units.val_mul, hcoe, hc]

theorem globalPoints_unipotentGL2' {L : Type} [Field L] [NumberField L] (k : L) :
    AutomorphicForm.globalPoints (𝓞 L) L (AutomorphicForm.unipotentGL2 k) =
      AutomorphicForm.unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) k) := by
  ext i j
  rw [AutomorphicForm.globalPoints_apply, AutomorphicForm.unipotentGL2_coe, AutomorphicForm.unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

end XMerge

namespace XMerge

open AutomorphicForm.TwistedBruhat

section Algebra

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

local notation "𝔸" => AdeleRing (𝓞 L) L

theorem sigmaAdelicAct_centralScalar (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (a : (𝔸)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L a) =
      centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ a) := by
  show Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) _
  rw [map_scalar']
  rfl

theorem sigmaAdelicAct_unipotentGL2 (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (q : 𝔸) :
    sigmaAdelicAct K L D σ (unipotentGL2 q) = unipotentGL2 (D.act σ q) := by
  refine Units.ext ?_
  ext i j
  show ((D.act σ : RingAut 𝔸).toRingHom : 𝔸 → 𝔸) ((unipotentGL2 q : AdelicGL2 (𝓞 L) L).val i j) =
    (unipotentGL2 (D.act σ q) : AdelicGL2 (𝓞 L) L).val i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem sigmaAdelicAct_diagOne (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (t : (𝔸)ˣ) :
    sigmaAdelicAct K L D σ (diagOne t) = diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t) := by
  refine Units.ext ?_
  ext i j
  show ((D.act σ : RingAut 𝔸).toRingHom : 𝔸 → 𝔸) ((diagOne t : AdelicGL2 (𝓞 L) L).val i j) =
    (diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t) : AdelicGL2 (𝓞 L) L).val i j
  rw [diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

theorem diag2 (p q : 𝔸) : Matrix.diagonal ![p, q] = !![p, 0; 0, q] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem scalar2 (c : 𝔸) : Matrix.scalar (Fin 2) c = !![c, 0; 0, c] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem mid_identity (x b x' : 𝔸) (t t' ζ' : (𝔸)ˣ) :
    (diagOne t)⁻¹ * (unipotentGL2 x)⁻¹ * unipotentGL2 b * centralScalar (𝓞 L) L ζ' * unipotentGL2 x' * diagOne t' =
      (unipotentGL2 ((b + (x' - x)) * ((t⁻¹ : (𝔸)ˣ) : 𝔸)) * diagOne (t' * t⁻¹) * centralScalar (𝓞 L) L ζ' :
        AdelicGL2 (𝓞 L) L) := by
  rw [← map_inv, unipotentGL2_inv']
  refine Units.ext ?_
  show Matrix.diagonal ![((t⁻¹ : (𝔸)ˣ) : 𝔸), 1] * !![(1 : 𝔸), -x; 0, 1] * !![(1 : 𝔸), b; 0, 1] *
      Matrix.scalar (Fin 2) (ζ' : 𝔸) * !![(1 : 𝔸), x'; 0, 1] * Matrix.diagonal ![((t' : (𝔸)ˣ) : 𝔸), 1] =
    !![(1 : 𝔸), (b + (x' - x)) * ((t⁻¹ : (𝔸)ˣ) : 𝔸); 0, 1] * Matrix.diagonal ![((t' * t⁻¹ : (𝔸)ˣ) : 𝔸), 1] *
      Matrix.scalar (Fin 2) (ζ' : 𝔸)
  simp only [diag2, scalar2, Matrix.mul_fin_two, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem arg_unipotent (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (x q b : 𝔸) (t ζ : (𝔸)ˣ) (k : AdelicGL2 (𝓞 L) L) :
    (unipotentGL2 x * diagOne t * k)⁻¹ * unipotentGL2 b *
        sigmaAdelicAct K L D σ (unipotentGL2 q * (centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * k))) =
      k⁻¹ * unipotentGL2 ((b + D.act σ q + actSubId K L D σ x) * ((t⁻¹ : (𝔸)ˣ) : 𝔸)) *
        diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
        centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) * sigmaAdelicAct K L D σ k := by
  have H : (diagOne t)⁻¹ * (unipotentGL2 x)⁻¹ * (unipotentGL2 b * unipotentGL2 (D.act σ q)) *
        centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) * unipotentGL2 (D.act σ x) *
        diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t) =
      (unipotentGL2 ((b + D.act σ q + actSubId K L D σ x) * ((t⁻¹ : (𝔸)ˣ) : 𝔸)) *
        diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
        centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) : AdelicGL2 (𝓞 L) L) := by
    rw [← unipotentGL2_add]
    exact mid_identity L x (b + D.act σ q) (D.act σ x) t _ _
  calc _ = k⁻¹ * ((diagOne t)⁻¹ * (unipotentGL2 x)⁻¹ * (unipotentGL2 b * unipotentGL2 (D.act σ q)) *
          centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
          unipotentGL2 (D.act σ x) * diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t)) * sigmaAdelicAct K L D σ k := by
        simp only [map_mul, mul_inv_rev, sigmaAdelicAct_centralScalar, sigmaAdelicAct_unipotentGL2, sigmaAdelicAct_diagOne]
        group
    _ = _ := by rw [H]; group

variable [IsGalois K L]

theorem forall_apply_eq_of_apply_eq (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {r : L} (hr : σ r = r) (τ : L ≃ₐ[K] L) : τ r = r := by
  have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (L ≃ₐ[K] L) r := by
    rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
    exact hr
  exact (MulAction.mem_stabilizer_iff).1 (hle (hgen τ))

theorem unipotentGL2_mem_normUnipotentSet_iff (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (b : L) : (unipotentGL2 b : GL (Fin 2) L) ∈ normUnipotentSet K L σ hgen ↔ Algebra.trace K L b ≠ 0 := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have h10 : ((unipotentGL2 b : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by simp
  have h00 : ((unipotentGL2 b : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 := by simp
  have h11 : ((unipotentGL2 b : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by simp
  have h01 : ((unipotentGL2 b : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = b := by simp
  have h := LT.TwistedNorm.exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mul_eq_mul_map_and_trace_ne_zero_of_apply_one_zero_eq_zero
    hgen (unipotentGL2 b : GL (Fin 2) L) h10
  rw [h00, h11, h01] at h
  show (∃ γ : Matrix.GeneralLinearGroup (Fin 2) K, γ ∈ AutomorphicForm.unipotentCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ (unipotentGL2 b)) = ConjClasses.mk γ) ↔ _
  rw [h]
  simp only [one_mul, div_one]
  constructor
  · rintro ⟨r, hr0, hrσ, htr⟩
    have hfix : ∀ τ : L ≃ₐ[K] L, τ r = r := forall_apply_eq_of_apply_eq K L σ hgen hrσ.symm
    have key : algebraMap K L (Algebra.trace K L (r * b)) = r * algebraMap K L (Algebra.trace K L b) := by
      rw [trace_eq_sum_automorphisms, trace_eq_sum_automorphisms, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [map_mul, hfix τ]
    intro hb
    apply htr
    have : algebraMap K L (Algebra.trace K L (r * b)) = 0 := by rw [key, hb, map_zero, mul_zero]
    exact (algebraMap K L).injective (this.trans (map_zero _).symm)
  · intro hb
    exact ⟨1, one_ne_zero, by simp, by simpa using hb⟩

end Algebra

end XMerge

namespace XMerge

open AutomorphicForm.TwistedBruhat

section Fibre

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

local notation "𝔸" => AdeleRing (𝓞 L) L

theorem eq_unipotentGL2_of_entries {δ : GL (Fin 2) L}
    (h10 : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h11 : (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1)
    (h00 : (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1) :
    δ = unipotentGL2 ((δ : Matrix (Fin 2) (Fin 2) L) 0 1) := by
  refine Units.ext ?_
  ext i j
  rw [unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [h10, h11, h00]

theorem arg_unipotent₀ (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (x b : 𝔸) (t ζ : (𝔸)ˣ) (k : AdelicGL2 (𝓞 L) L) :
    (unipotentGL2 x * diagOne t * k)⁻¹ * unipotentGL2 b *
        sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * k)) =
      k⁻¹ * unipotentGL2 ((b + actSubId K L D σ x) * ((t⁻¹ : (𝔸)ˣ) : 𝔸)) *
        diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
        centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) * sigmaAdelicAct K L D σ k := by
  have h := arg_unipotent K L D σ x 0 b t ζ k
  rw [unipotentGL2_zero, one_mul, map_zero, add_zero] at h
  exact h

variable [IsGalois K L]

theorem finsum_unitFibre_eq (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (x : 𝔸) (t ζ : (𝔸)ˣ) (k : AdelicGL2 (𝓞 L) L) :
    (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
        (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
        (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
        φ ((unipotentGL2 x * diagOne t * k)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * k)))) =
      ∑ᶠ b ∈ {b : L | Algebra.trace K L b ≠ 0},
        φ (k⁻¹ * unipotentGL2 ((algebraMap L 𝔸 b + actSubId K L D σ x) * ((t⁻¹ : (𝔸)ˣ) : 𝔸)) *
          diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
          centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
          AutomorphicForm.sigmaAdelicAct K L D σ k) := by
  symm
  refine finsum_mem_eq_of_bijOn (fun b : L => (unipotentGL2 b : GL (Fin 2) L)) ⟨?_, ?_, ?_⟩ ?_
  · intro b hb
    refine ⟨(unipotentGL2_mem_normUnipotentSet_iff K L σ hgen b).2 hb, ?_, ?_, ?_⟩ <;> simp
  · intro b _ b' _ h
    have := congrArg (fun δ : GL (Fin 2) L => (δ : Matrix (Fin 2) (Fin 2) L) 0 1) h
    simpa using this
  · intro δ hδ
    obtain ⟨hN, h10, h11, h00⟩ := hδ
    refine ⟨(δ : Matrix (Fin 2) (Fin 2) L) 0 1, ?_, (eq_unipotentGL2_of_entries L h10 h11 h00).symm⟩
    show Algebra.trace K L ((δ : Matrix (Fin 2) (Fin 2) L) 0 1) ≠ 0
    rw [← unipotentGL2_mem_normUnipotentSet_iff K L σ hgen, ← eq_unipotentGL2_of_entries L h10 h11 h00]
    exact hN
  · intro b _
    rw [globalPoints_unipotentGL2', arg_unipotent₀]

theorem finsum_unitFibre_box_eq (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (x q : 𝔸) (t ζ : (𝔸)ˣ) (k : AdelicGL2 (𝓞 L) L) :
    (∑ᶠ δ ∈ {δ : GL (Fin 2) L |
        (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
        (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
        φ ((unipotentGL2 x * diagOne t * k)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (unipotentGL2 q * (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * k))))) =
      ∑ᶠ b : L,
        φ (k⁻¹ * unipotentGL2 ((algebraMap L 𝔸 b + D.act σ q + actSubId K L D σ x) * ((t⁻¹ : (𝔸)ˣ) : 𝔸)) *
          diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
          centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
          AutomorphicForm.sigmaAdelicAct K L D σ k) := by
  symm
  rw [← finsum_mem_univ]
  refine finsum_mem_eq_of_bijOn (fun b : L => (unipotentGL2 b : GL (Fin 2) L)) ⟨?_, ?_, ?_⟩ ?_
  · intro b _
    refine ⟨?_, ?_, ?_⟩ <;> simp
  · intro b _ b' _ h
    have := congrArg (fun δ : GL (Fin 2) L => (δ : Matrix (Fin 2) (Fin 2) L) 0 1) h
    simpa using this
  · intro δ hδ
    obtain ⟨h10, h11, h00⟩ := hδ
    exact ⟨(δ : Matrix (Fin 2) (Fin 2) L) 0 1, Set.mem_univ _, (eq_unipotentGL2_of_entries L h10 h11 h00).symm⟩
  · intro b _
    rw [globalPoints_unipotentGL2', arg_unipotent]

end Fibre

end XMerge

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (x q : AdeleRing (𝓞 L) L) (t ζ : (AdeleRing (𝓞 L) L)ˣ) (k : AdelicGL2 (𝓞 L) L) :
    (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
        (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
        (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
        φ ((unipotentGL2 x * diagOne t * k)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * k))) =
      ∑ᶠ b ∈ {b : L | Algebra.trace K L b ≠ 0},
        φ (k⁻¹ *
          unipotentGL2 ((algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) *
            ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
          diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
          centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
          AutomorphicForm.sigmaAdelicAct K L D σ k)) ∧
    (∑ᶠ δ ∈ {δ : GL (Fin 2) L |
        (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
        (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
        φ ((unipotentGL2 x * diagOne t * k)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (unipotentGL2 q * (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * k)))) =
      ∑ᶠ b : L,
        φ (k⁻¹ *
          unipotentGL2 ((algebraMap L (AdeleRing (𝓞 L) L) b + D.act σ q + actSubId K L D σ x) *
            ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
          diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
          centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
          AutomorphicForm.sigmaAdelicAct K L D σ k)) :=
  ⟨XMerge.finsum_unitFibre_eq K L D σ hgen φ x t ζ k, XMerge.finsum_unitFibre_box_eq K L D σ φ x q t ζ k⟩

end S_AutomorphicForm_TwistedBruhat_finsum_unitFibre_iwasawa_eq_finsum_trace_ne_zero_and_finsum_unitFibre_unipotent_eq_finsum
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_finsum_unitFibre_iwasawa_eq_finsum_trace_ne_zero_and_finsum_unitFibre_unipotent_eq_finsum (solution)
