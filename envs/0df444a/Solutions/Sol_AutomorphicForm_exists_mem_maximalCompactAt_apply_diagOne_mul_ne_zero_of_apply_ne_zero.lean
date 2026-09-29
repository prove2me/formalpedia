-- Prove2me | solution 1 for AutomorphicForm.exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ac91a872-eaf5-56d6-bd20-64f296e72c81

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero
p2m_attr_erase "instance" "HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain
open AutomorphicForm.WindowedSiegel

namespace NondegKit

open AdelicDock

variable {F : Type} [Field F] [NumberField F]

private noncomputable def atPlace (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (v.adicCompletion F)) :
    AdelicGL2 (𝓞 F) F :=
  finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v g)

private theorem glArch_atPlace (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (v.adicCompletion F)) :
    glArch (𝓞 F) F (atPlace v g) = 1 := glArch_finEmbed _ _ _

private theorem finComponent_atPlace_self (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (v.adicCompletion F)) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (atPlace v g)) = g := by
  rw [atPlace, glFin_finEmbed, finComponent_localEmbed_self]

private theorem finComponent_atPlace_of_ne (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (v.adicCompletion F))
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F (atPlace v g)) = 1 := by
  rw [atPlace, glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]

private theorem localEmbed_entries_integral (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (v.adicCompletion F))
    (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F)
    (i j : Fin 2) :
    ((localEmbed (𝓞 F) F v g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j ∈ integralFiniteAdeles (𝓞 F) F := by
  intro w
  rw [coe_localEmbed]
  by_cases hw : w = v
  · subst hw
    rw [localMat_apply_self]
    exact hg i j
  · rw [localMat_apply_of_ne _ _ _ _ i j hw, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

private theorem atPlace_mem (v : HeightOneSpectrum (𝓞 F)) {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ adelicMaximalCompact F) :
    atPlace v (finComponent (𝓞 F) F v (glFin (𝓞 F) F k)) ∈ adelicMaximalCompact F := by
  set g := finComponent (𝓞 F) F v (glFin (𝓞 F) F k) with hgdef
  have hkf := mem_finiteIntegralGL2_iff.mp hk.1
  have hint : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
    intro i j
    rw [hgdef, finComponent_apply]
    exact hkf.1 i j v
  have hint' : ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
      ∈ v.adicCompletionIntegers F := by
    intro i j
    rw [hgdef, ← map_inv, ← map_inv, finComponent_apply]
    exact (mem_finiteIntegralGL2_iff.mp ((adelicMaximalCompact F).inv_mem hk).1).1 i j v
  refine ⟨?_, fun w => ?_⟩
  · rw [atPlace, glFin_finEmbed, mem_finiteIntegralGL2_iff]
    refine ⟨localEmbed_entries_integral v g hint, ?_⟩
    intro i j
    rw [← map_inv]
    exact localEmbed_entries_integral v g⁻¹ hint' i j
  · rw [glArch_atPlace, map_one]
    exact isRowIsometry_one

private theorem exists_truncation (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ adelicMaximalCompact F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ m : AdelicGL2 (𝓞 F) F, m ∈ adelicMaximalCompact F ∧ glArch (𝓞 F) F m = 1 ∧
      (∀ v ∈ T, finComponent (𝓞 F) F v (glFin (𝓞 F) F m) = finComponent (𝓞 F) F v (glFin (𝓞 F) F k)) ∧
      (∀ v ∉ T, finComponent (𝓞 F) F v (glFin (𝓞 F) F m) = 1) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact ⟨1, one_mem _, map_one _, fun v hv => absurd hv (Finset.notMem_empty v),
      fun v _ => by rw [map_one, map_one]⟩
  | insert u T hu ih =>
    obtain ⟨m, hmK, hma, hmon, hmoff⟩ := ih
    refine ⟨m * atPlace u (finComponent (𝓞 F) F u (glFin (𝓞 F) F k)), mul_mem hmK (atPlace_mem u hk), ?_, ?_, ?_⟩
    · rw [map_mul, hma, glArch_atPlace, one_mul]
    · intro v hv
      rw [map_mul, map_mul]
      rcases Finset.mem_insert.1 hv with rfl | hvT
      · rw [hmoff v hu, finComponent_atPlace_self, one_mul]
      · have hvu : v ≠ u := fun h => hu (h ▸ hvT)
        rw [hmon v hvT, finComponent_atPlace_of_ne _ _ hvu, mul_one]
    · intro v hv
      have hvu : v ≠ u := fun h => hv (h ▸ Finset.mem_insert_self u T)
      have hvT : v ∉ T := fun h => hv (Finset.mem_insert_of_mem h)
      rw [map_mul, map_mul, hmoff v hvT, finComponent_atPlace_of_ne _ _ hvu, one_mul]

end NondegKit

open AdelicDock in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (W : AdelicGL2 (𝓞 F) F → ℂ)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), W (unipotentGL2 u * g) = ψ u * W g)
    (hZ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      W (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ i j : Fin 2,
      ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
        ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v)
    (hW : W g₀ ≠ 0) :
    ∃ (t : (AdeleRing (𝓞 F) F)ˣ) (k : AdelicGL2 (𝓞 F) F),
      k ∈ maximalCompactAt F S ∧
      (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1) ∧
      W (diagOne t * k) ≠ 0 := by
  classical

  obtain ⟨b, k₁, hb, hk1f, hk1a, hg0⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g₀
  have hk1K : k₁ ∈ adelicMaximalCompact F := ⟨hk1f, hk1a⟩

  have hg0v : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → finComponent (𝓞 F) F v (glFin (𝓞 F) F g₀) = 1 := by
    intro v hv
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [finComponent_apply, glFin_apply, hg₀ v hv i j]
    change ((finComponent (𝓞 F) F v (glFin (𝓞 F) F 1) : GL (Fin 2) (v.adicCompletion F)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j = _
    rw [map_one, map_one]

  obtain ⟨m, hmK, hma, hmon, hmoff⟩ := NondegKit.exists_truncation k₁ hk1K S
  set kf : AdelicGL2 (𝓞 F) F := finEmbed (𝓞 F) F (glFin (𝓞 F) F k₁) with hkf
  have hkfK : kf ∈ adelicMaximalCompact F :=
    ⟨by rw [hkf, glFin_finEmbed]; exact hk1f,
     fun w => by rw [hkf, glArch_finEmbed, map_one]; exact isRowIsometry_one⟩
  set k : AdelicGL2 (𝓞 F) F := k₁ * kf⁻¹ * m with hkdef
  have hkK : k ∈ adelicMaximalCompact F := mul_mem (mul_mem hk1K (inv_mem hkfK)) hmK
  have hka : glArch (𝓞 F) F k = glArch (𝓞 F) F k₁ := by
    rw [hkdef, map_mul, map_mul, map_inv, hkf, glArch_finEmbed, inv_one, mul_one, hma, mul_one]
  have hkS : ∀ v ∈ S, finComponent (𝓞 F) F v (glFin (𝓞 F) F k) = finComponent (𝓞 F) F v (glFin (𝓞 F) F k₁) := by
    intro v hv
    simp only [hkdef, map_mul, map_inv, hkf, glFin_finEmbed, mul_inv_cancel, one_mul]
    exact hmon v hv
  have hkoff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → finComponent (𝓞 F) F v (glFin (𝓞 F) F k) = 1 := by
    intro v hv
    simp only [hkdef, map_mul, map_inv, hkf, glFin_finEmbed, mul_inv_cancel, one_mul]
    exact hmoff v hv
  have hkmem : k ∈ maximalCompactAt F S := mem_maximalCompactAt_iff.2 ⟨hkK, hkoff⟩

  set b' : AdelicGL2 (𝓞 F) F := g₀ * k⁻¹ with hb'def
  have hb'S : ∀ v ∈ S, finComponent (𝓞 F) F v (glFin (𝓞 F) F b') = finComponent (𝓞 F) F v (glFin (𝓞 F) F b) := by
    intro v hv
    rw [hb'def, map_mul, map_mul, map_inv, map_inv, hkS v hv, hg0, map_mul, map_mul, mul_inv_cancel_right]
  have hb'off : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → finComponent (𝓞 F) F v (glFin (𝓞 F) F b') = 1 := by
    intro v hv
    rw [hb'def, map_mul, map_mul, map_inv, map_inv, hkoff v hv, hg0v v hv, inv_one, mul_one]
  have hb'a : glArch (𝓞 F) F b' = glArch (𝓞 F) F b := by
    rw [hb'def, map_mul, map_inv, hka, hg0, map_mul, mul_inv_cancel_right]
  have hb10 : ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 := hb
  have hb' : b' ∈ adelicBorel (𝓞 F) F := by
    show ((b' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0
    apply Prod.ext
    · change ((glArch (𝓞 F) F b' : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 0 = 0
      rw [hb'a]
      change (((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).1 = 0
      rw [hb10]
      rfl
    · apply Subtype.ext
      funext v
      change ((finComponent (𝓞 F) F v (glFin (𝓞 F) F b') : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0
      by_cases hv : v ∈ S
      · rw [hb'S v hv]
        change (((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2 v = 0
        rw [hb10]
        rfl
      · rw [hb'off v hv, Units.val_one, Matrix.one_apply_ne (by decide)]

  set Bel : ↥(adelicBorel (𝓞 F) F) := ⟨b', hb'⟩ with hBel
  set t₁ : (AdeleRing (𝓞 F) F)ˣ := borelDiagFst Bel with ht₁
  set t₂ : (AdeleRing (𝓞 F) F)ˣ := borelDiagSnd Bel with ht₂
  set β : AdeleRing (𝓞 F) F :=
    ((b' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 * ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
    with hβ
  have h00 : ((b' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = (t₁ : AdeleRing (𝓞 F) F) := rfl
  have h11 : ((b' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = (t₂ : AdeleRing (𝓞 F) F) := rfl
  have hb'10 : ((b' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 := hb'
  have ht2inv : ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * (t₂ : AdeleRing (𝓞 F) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcs : ((centralScalar (𝓞 F) F t₂ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(t₂ : AdeleRing (𝓞 F) F), 0; 0, (t₂ : AdeleRing (𝓞 F) F)] := by
    change Matrix.scalar (Fin 2) (t₂ : AdeleRing (𝓞 F) F) = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hdo : ((diagOne (t₁ * t₂⁻¹) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(t₁ : AdeleRing (𝓞 F) F) * ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 0; 0, 1] := by
    change Matrix.diagonal ![((t₁ * t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1] = _
    rw [Units.val_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hx00 : (t₂ : AdeleRing (𝓞 F) F) * ((t₁ : AdeleRing (𝓞 F) F) * ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
      = (t₁ : AdeleRing (𝓞 F) F) := by
    rw [mul_left_comm, Units.mul_inv, mul_one]
  have hβ01 : β * (t₂ : AdeleRing (𝓞 F) F)
      = ((b' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 := by
    rw [hβ, mul_assoc, ht2inv, mul_one]
  have hR : ((unipotentGL2 β : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((centralScalar (𝓞 F) F t₂ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((diagOne (t₁ * t₂⁻¹) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(t₁ : AdeleRing (𝓞 F) F), β * (t₂ : AdeleRing (𝓞 F) F); 0, (t₂ : AdeleRing (𝓞 F) F)] := by
    rw [hcs, hdo, unipotentGL2_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hx00]
  have hdecomp : b' = unipotentGL2 β * centralScalar (𝓞 F) F t₂ * diagOne (t₁ * t₂⁻¹) := by
    apply Units.ext
    change ((b' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = ((unipotentGL2 β : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((centralScalar (𝓞 F) F t₂ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((diagOne (t₁ * t₂⁻¹) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    rw [hR, hβ01]
    conv_lhs => rw [Matrix.eta_fin_two ((b' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))]
    rw [h00, h11, hb'10]

  have hg0' : g₀ = b' * k := by rw [hb'def, inv_mul_cancel_right]
  have hWval : W g₀ = ψ β * ((((ω t₂ : ℂˣ) : ℂ)) * W (diagOne (t₁ * t₂⁻¹) * k)) := by
    rw [hg0', hdecomp, mul_assoc, mul_assoc, hN, hZ]
  refine ⟨t₁ * t₂⁻¹, k, hkmem, fun v hv => ?_, fun h0 => hW ?_⟩
  ·
    have h1 : ((t₁ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
      change ((finComponent (𝓞 F) F v (glFin (𝓞 F) F b') : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 = 1
      rw [hb'off v hv, Units.val_one, Matrix.one_apply_eq]
    have h2 : ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
      change ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (b'⁻¹)) : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = 1
      rw [map_inv, map_inv, hb'off v hv, inv_one, Units.val_one, Matrix.one_apply_eq]
    rw [Units.val_mul]
    change ((t₁ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v * ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1
    rw [h1, h2, mul_one]
  · rw [hWval, h0, mul_zero, mul_zero]

end S_AutomorphicForm_exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero (solution)
