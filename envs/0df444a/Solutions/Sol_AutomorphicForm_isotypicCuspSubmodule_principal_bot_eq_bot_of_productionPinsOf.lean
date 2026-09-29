-- Prove2me | solution 1 for AutomorphicForm.isotypicCuspSubmodule_principal_bot_eq_bot_of_productionPinsOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/504da5cb-b91d-50ad-932a-5fc60c40e829

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isotypicCuspSubmodule_principal_bot_eq_bot_of_productionPinsOf

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm

namespace R3PrincipalLevelBot

private theorem _root_.R3PrincipalLevelBot.exists_notMem_finset (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ T := by
  have hinj : ∀ p : Nat.Primes, ∃ v : HeightOneSpectrum (𝓞 K), v.asIdeal.under ℤ = Ideal.span {(p.1 : ℤ)} := by
    intro p
    haveI hpr : (Ideal.span {(p.1 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr (Nat.prime_iff_prime_int.mp p.2)
    have hp0 : Ideal.span {(p.1 : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero
    obtain ⟨⟨Q, hQ⟩⟩ := (inferInstance : Nonempty ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K)))
    exact ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver hp0 hQ⟩, hQ.2.over.symm⟩
  choose g hg using hinj
  have hginj : Function.Injective g := by
    intro p q hpq
    have h := hg p
    rw [hpq, hg q] at h
    have h' := Int.associated_iff_natAbs.mp (Ideal.span_singleton_eq_span_singleton.mp h)
    simp only [Int.natAbs_natCast] at h'
    exact Subtype.ext h'.symm
  haveI : Infinite (HeightOneSpectrum (𝓞 K)) := Infinite.of_injective g hginj
  exact Infinite.exists_notMem_finset T

p2m_export "R3PrincipalLevelBot" "exists_notMem_finset"

section LevelBot

variable {F : Type} [Field F] [NumberField F]

theorem eq_zero_of_mem_idealBall_bot {x : FiniteAdeleRing (𝓞 F) F} (hx : x ∈ idealBall (𝓞 F) F ⊥) : x = 0 := by
  refine FiniteAdeleRing.ext F fun v => ?_
  have hv : Valued.v (x v) ≤ idealBound (𝓞 F) (⊥ : Ideal (𝓞 F)) v := hx v
  rw [idealBound_bot] at hv
  have h0 : Valued.v (x v) = 0 := le_antisymm hv zero_le'
  exact (Valuation.zero_iff _).mp h0

theorem glFin_lower_of_mem_levelOne_bot {g : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hg : g ∈ levelOne (𝓞 F) F (⊥ : Ideal (𝓞 F))) :
    (glFin (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 = 0 ∧
      (glFin (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 = 1 := by
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hg
  refine ⟨eq_zero_of_mem_idealBall_bot hg.1.toIsLevelZeroMatrix.lowerLeft, ?_⟩
  exact sub_eq_zero.mp (eq_zero_of_mem_idealBall_bot hg.1.lowerRight)

theorem glFin_weyl_val_apply (i j : Fin 2) :
    (glFin (𝓞 F) F (weyl (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j =
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j := by
  rw [glFin_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem glFin_weyl_val :
    (glFin (𝓞 F) F (weyl (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) = !![0, 1; 1, 0] :=
  Matrix.ext glFin_weyl_val_apply

theorem weyl_inv : (weyl (𝓞 F) F)⁻¹ = weyl (𝓞 F) F := by
  refine Units.ext ?_
  rfl

theorem principalLevel_bot_inf_finiteAdelicGL2Subgroup_eq_bot :
    principalLevel (𝓞 F) F (⊥ : Ideal (𝓞 F)) ⊓ finiteAdelicGL2Subgroup F = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
  obtain ⟨hgP, hgA⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨hg1, hg2⟩ := (mem_principalLevel_iff (𝓞 F) F ⊥).mp hgP

  have hg2' : (weyl (𝓞 F) F)⁻¹ * g * weyl (𝓞 F) F ∈ levelOne (𝓞 F) F (⊥ : Ideal (𝓞 F)) := by
    have := (Subgroup.mem_map_equiv (f := MulAut.conj (weyl (𝓞 F) F)) (K := levelOne (𝓞 F) F ⊥) (x := g)).mp hg2
    rwa [MulAut.conj_symm_apply] at this

  set m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
    ((glFin (𝓞 F) F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) with hm
  have hlow := glFin_lower_of_mem_levelOne_bot hg1
  have hup := glFin_lower_of_mem_levelOne_bot hg2'
  have hconj : ((glFin (𝓞 F) F ((weyl (𝓞 F) F)⁻¹ * g * weyl (𝓞 F) F) : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) = !![0, 1; 1, 0] * m * !![0, 1; 1, 0] := by
    rw [map_mul, map_mul, weyl_inv, Units.val_mul, Units.val_mul, glFin_weyl_val]
  rw [hconj] at hup
  have e10 : (!![0, 1; 1, 0] * m * !![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 = m 0 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp
  have e11 : (!![0, 1; 1, 0] * m * !![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 = m 0 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp
  rw [e10] at hup
  rw [e11] at hup
  have hfin : glFin (𝓞 F) F g = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    show m i j = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
    fin_cases i <;> fin_cases j
    · simpa using hup.2
    · simpa using hup.1
    · simpa using hlow.1
    · simpa using hlow.2
  have harch : glArch (𝓞 F) F g = 1 := (mem_finiteAdelicGL2Subgroup_iff F g).mp hgA

  refine Subgroup.mem_bot.mpr (Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_))
  · have h1 : ((glArch (𝓞 F) F g : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j
        = ((1 : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j := by
      rw [harch]
    rw [glArch_apply] at h1
    rw [h1, Units.val_one, Units.val_one]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq]; rfl
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij]; rfl
  · have h2 : ((glFin (𝓞 F) F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
        = ((1 : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j := by
      rw [hfin]
    rw [glFin_apply] at h2
    rw [h2, Units.val_one, Units.val_one]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq]; rfl
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij]; rfl

end LevelBot

section IsotypicBot

variable (F : Type) [Field F] [NumberField F]

theorem not_isIsotypicCuspFormAt_principal_bot (D : Set (AdelicGL2 (𝓞 F) F)) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    ¬ IsIsotypicCuspFormAt F (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ ⊥ S Ψ φ := by
  intro h
  obtain ⟨v, hv⟩ := exists_notMem_finset F S
  have h' : SmoothCusp.IsHeckeCosetEigenfunctionAt F
      (principalLevel (𝓞 F) F (⊥ : Ideal (𝓞 F)) ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v) v φ (Ψ.a v) :=
    h.hecke_eigen v hv
  rw [principalLevel_bot_inf_finiteAdelicGL2Subgroup_eq_bot] at h'
  exact SmoothCusp.not_isHeckeCosetEigenfunctionAt_bot F _ v _ _ h'

theorem isotypicCuspSubmodule_principal_bot_eq_bot (D : Set (AdelicGL2 (𝓞 F) F)) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ) :
    isotypicCuspSubmodule F (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ ⊥ S Ψ = ⊥ :=
  (isotypicCuspSubmodule_eq_bot_iff F _ ξ ⊥ S Ψ).mpr fun φ hφ =>
    absurd hφ (not_isIsotypicCuspFormAt_principal_bot F D B ξ S Ψ φ)

end IsotypicBot

end R3PrincipalLevelBot

theorem solution
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ) :
    isotypicCuspSubmodule F (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ ⊥ S Ψ = ⊥ :=
  R3PrincipalLevelBot.isotypicCuspSubmodule_principal_bot_eq_bot F D B ξ S Ψ

end S_AutomorphicForm_isotypicCuspSubmodule_principal_bot_eq_bot_of_productionPinsOf
end P2MW
export P2MW.S_AutomorphicForm_isotypicCuspSubmodule_principal_bot_eq_bot_of_productionPinsOf (solution)
