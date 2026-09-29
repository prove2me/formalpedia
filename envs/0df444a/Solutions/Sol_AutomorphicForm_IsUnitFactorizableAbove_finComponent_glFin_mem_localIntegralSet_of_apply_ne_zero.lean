-- Prove2me | solution 1 for AutomorphicForm.IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/01e4963b-8994-5956-9ce3-59bf7666e4e5

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_IsUnitFactorizableAbove_finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm
open scoped TensorProduct

noncomputable section

namespace RS11UP

variable {K : Type} [Field K] [NumberField K]

theorem under_self (v : HeightOneSpectrum (𝓞 K)) : v.under (𝓞 K) = v := by
  apply HeightOneSpectrum.ext
  show Ideal.comap (algebraMap (𝓞 K) (𝓞 K)) v.asIdeal = v.asIdeal
  have h : algebraMap (𝓞 K) (𝓞 K) = RingHom.id (𝓞 K) := by
    ext x
    rfl
  rw [h, Ideal.comap_id]

def selfExt (v : HeightOneSpectrum (𝓞 K)) : v.Extension (𝓞 K) := ⟨v, under_self v⟩

theorem semiLocalHomeomorph_apply (v : HeightOneSpectrum (𝓞 K)) (y : K ⊗[K] v.adicCompletion K) :
    semiLocalHomeomorph K K v y = HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K K (𝓞 K) v y := rfl

theorem semiLocalEval_apply (v : HeightOneSpectrum (𝓞 K)) (x : FiniteAdeleRing (𝓞 K) K) :
    semiLocalEval K K v x = (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K K (𝓞 K) v).symm
      (fun w : v.Extension (𝓞 K) => x w.1) := rfl

theorem mem_adicCompletionIntegers_of_semiLocalEval_mem (v : HeightOneSpectrum (𝓞 K)) (x : FiniteAdeleRing (𝓞 K) K)
    (hx : semiLocalEval K K v x ∈ semiLocalIntegers K K v) : x v ∈ v.adicCompletionIntegers K := by
  rw [semiLocalIntegers_eq_preimage] at hx
  rw [Set.mem_preimage, semiLocalHomeomorph_apply, semiLocalEval_apply, AlgEquiv.apply_symm_apply] at hx
  have h := hx (selfExt v) (Set.mem_univ _)
  exact h

theorem entry_semiLocalComponent (v : HeightOneSpectrum (𝓞 K)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) (i j : Fin 2) :
    (semiLocalComponent K K v h : Matrix (Fin 2) (Fin 2) (K ⊗[K] v.adicCompletion K)) i j =
      semiLocalEval K K v ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) := rfl

theorem finComponent_mem_localIntegralSet_of_semiLocal (v : HeightOneSpectrum (𝓞 K))
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) (hh : semiLocalComponent K K v h ∈ semiLocalIntegralSet K K v) :
    finComponent (𝓞 K) K v h ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet]
  have hh' := (mem_integralUnitsSet.mp hh)
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [finComponent_apply]
    apply mem_adicCompletionIntegers_of_semiLocalEval_mem
    rw [← entry_semiLocalComponent]
    exact hh'.1 i j
  · rw [← map_inv, finComponent_apply]
    apply mem_adicCompletionIntegers_of_semiLocalEval_mem
    rw [← entry_semiLocalComponent, map_inv]
    exact hh'.2 i j

end RS11UP

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : IsUnitFactorizableAbove K K U S f)
    (z : GL (Fin 2) (AdeleRing (𝓞 K) K)) (hz : f z ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v := by
  obtain ⟨-, φa, φf, φS, -, -, -, -, hvanish, hfac⟩ := hf
  have hφf : φf (glFin (𝓞 K) K z) ≠ 0 := by
    intro h0
    apply hz
    rw [hfac z, h0, mul_zero]
  have hint : semiLocalComponent K K v (glFin (𝓞 K) K z) ∈ semiLocalIntegralSet K K v := by
    by_contra hnot
    exact hφf (hvanish _ ⟨v, hv, hnot⟩)
  exact RS11UP.finComponent_mem_localIntegralSet_of_semiLocal v _ hint

end S_AutomorphicForm_IsUnitFactorizableAbove_finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_IsUnitFactorizableAbove_finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero (solution)
