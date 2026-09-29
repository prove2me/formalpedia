-- Prove2me | solution 1 for AutomorphicForm.exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f4bae4b6-1044-5fa3-b30f-b97d35d419f8

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm
open AutomorphicForm.WindowedSiegel

namespace SplitKit

open AdelicDock

variable {F : Type} [Field F] [NumberField F]

theorem finEntry_eq {g h : AdelicGL2 (𝓞 F) F}
    (h₂ : ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F g) = finComponent (𝓞 F) F w (glFin (𝓞 F) F h))
    (i j : Fin 2) :
    ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
      = ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 := by
  apply Subtype.ext
  funext w
  have := congrArg (fun m : GL (Fin 2) (w.adicCompletion F) =>
    (m : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j) (h₂ w)
  simp [finComponent_apply, glFin_apply] at this
  exact this

theorem adelicGL2_ext {g h : AdelicGL2 (𝓞 F) F}
    (h₁ : glArch (𝓞 F) F g = glArch (𝓞 F) F h)
    (h₂ : ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F g) = finComponent (𝓞 F) F w (glFin (𝓞 F) F h)) :
    g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply Prod.ext
  · have := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) =>
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
    simpa [glArch_apply] using this
  · exact finEntry_eq h₂ i j

noncomputable def atPlace (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (v.adicCompletion F)) :
    AdelicGL2 (𝓞 F) F :=
  finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v g)

theorem glArch_atPlace (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (v.adicCompletion F)) :
    glArch (𝓞 F) F (atPlace v g) = 1 := glArch_finEmbed _ _ _

theorem finComponent_atPlace_self (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (v.adicCompletion F)) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (atPlace v g)) = g := by
  rw [atPlace, glFin_finEmbed, finComponent_localEmbed_self]

theorem finComponent_atPlace_of_ne (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (v.adicCompletion F))
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F (atPlace v g)) = 1 := by
  rw [atPlace, glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]

theorem localEmbed_entries_integral (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (v.adicCompletion F))
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

theorem atPlace_mem (v : HeightOneSpectrum (𝓞 F)) {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ adelicMaximalCompact F) :
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

theorem mul_atPlace_comm (v : HeightOneSpectrum (𝓞 F)) (k : AdelicGL2 (𝓞 F) F) :
    k * atPlace v (finComponent (𝓞 F) F v (glFin (𝓞 F) F k))
      = atPlace v (finComponent (𝓞 F) F v (glFin (𝓞 F) F k)) * k := by
  apply adelicGL2_ext
  · rw [map_mul, map_mul, glArch_atPlace, mul_one, one_mul]
  · intro w
    rw [map_mul, map_mul, map_mul, map_mul]
    by_cases hw : w = v
    · subst hw
      rw [finComponent_atPlace_self]
    · rw [finComponent_atPlace_of_ne _ _ hw, mul_one, one_mul]

end SplitKit

open SplitKit AdelicDock

open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (k : AdelicGL2 (𝓞 F) F) (_hk : k ∈ adelicMaximalCompact F) :
    ∃ k₁ k₂ : AdelicGL2 (𝓞 F) F, k₁ ∈ maximalCompactAt F S ∧ k₂ ∈ maximalCompactAway F S ∧ k = k₁ * k₂ := by
  have hk := _hk
  induction S using Finset.induction_on with
  | empty =>

    set kf : AdelicGL2 (𝓞 F) F := finEmbed (𝓞 F) F (glFin (𝓞 F) F k) with hkf
    have hkfK : kf ∈ adelicMaximalCompact F := by
      refine ⟨?_, fun w => ?_⟩
      · rw [hkf, glFin_finEmbed]; exact hk.1
      · rw [hkf, glArch_finEmbed, map_one]; exact isRowIsometry_one
    refine ⟨k * kf⁻¹, kf, ?_, ?_, by rw [inv_mul_cancel_right]⟩
    · rw [mem_maximalCompactAt_iff]
      refine ⟨(adelicMaximalCompact F).mul_mem hk ((adelicMaximalCompact F).inv_mem hkfK), fun w _ => ?_⟩
      rw [map_mul, map_inv, hkf, glFin_finEmbed, mul_inv_cancel, map_one]
    · rw [mem_maximalCompactAway_iff]
      refine ⟨hkfK, by rw [hkf, glArch_finEmbed], fun w hw => ?_⟩
      simp at hw
  | insert v S hv IH =>
    obtain ⟨k₁, k₂, hk₁, hk₂, rfl⟩ := IH
    rw [mem_maximalCompactAt_iff] at hk₁
    rw [mem_maximalCompactAway_iff] at hk₂
    obtain ⟨hk₁K, hk₁S⟩ := hk₁
    obtain ⟨hk₂K, hk₂arch, hk₂S⟩ := hk₂
    set g := finComponent (𝓞 F) F v (glFin (𝓞 F) F k₂) with hgdef
    set kv : AdelicGL2 (𝓞 F) F := atPlace v g with hkvdef
    have hkvK : kv ∈ adelicMaximalCompact F := atPlace_mem v hk₂K
    have hcomm : k₂ * kv = kv * k₂ := mul_atPlace_comm v k₂
    refine ⟨k₁ * kv, kv⁻¹ * k₂, ?_, ?_, ?_⟩
    · rw [mem_maximalCompactAt_iff]
      refine ⟨(adelicMaximalCompact F).mul_mem hk₁K hkvK, fun w hw => ?_⟩
      rw [Finset.mem_insert, not_or] at hw
      rw [map_mul, map_mul, hk₁S w hw.2, hkvdef, finComponent_atPlace_of_ne _ _ hw.1, mul_one]
    · rw [mem_maximalCompactAway_iff]
      refine ⟨(adelicMaximalCompact F).mul_mem ((adelicMaximalCompact F).inv_mem hkvK) hk₂K, ?_, fun w hw => ?_⟩
      · rw [map_mul, map_inv, hkvdef, glArch_atPlace, inv_one, one_mul, hk₂arch]
      · rw [map_mul, map_mul, map_inv, map_inv]
        rcases Finset.mem_insert.mp hw with rfl | hwS
        · rw [hkvdef, finComponent_atPlace_self, hgdef, inv_mul_cancel]
        · have hwv : w ≠ v := fun h => hv (h ▸ hwS)
          rw [hk₂S w hwS, hkvdef, finComponent_atPlace_of_ne _ _ hwv, inv_one, mul_one]
    ·
      rw [mul_assoc, ← mul_assoc kv, mul_inv_cancel, one_mul]

end S_AutomorphicForm_exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq
end P2MW
export P2MW.S_AutomorphicForm_exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq (solution)
