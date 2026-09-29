-- Prove2me | solution 1 for AutomorphicForm.exists_forall_mem_of_isOpen_of_congruence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/12723d2a-ac1f-55ba-a88b-3a5f1328312f

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_mem_of_isOpen_of_congruence

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hU : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ)))) :
    ∃ b : ℕ, ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      (∀ i j : Fin 2, Valued.v ((((k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) - 1) i j) ≤
        WithZero.exp (-(b : ℤ))) → k ∈ U := by
  classical
  by_contra hcon
  push_neg at hcon
  choose k hkK hkv hkU using hcon

  have hinv_int : ∀ (b : ℕ) (i j : Fin 2),
      Valued.v ((((k b)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j) ≤ 1 :=
    fun b i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp
      (((AdelicDock.mem_localLevelOne_iff (𝓞 ℚ) ℚ p (k b)).mp (hkK b)).2.integral i j)

  have hkv' : ∀ (b : ℕ) (i j : Fin 2),
      Valued.v (((((k b)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) - 1) i j) ≤
        WithZero.exp (-(b : ℤ)) := by
    intro b i j
    have hmat : (((k b)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) - 1 =
        -((((k b)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          (((k b : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) - 1)) := by
      rw [mul_sub, mul_one, Units.inv_mul, neg_sub]
    rw [hmat, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [Valuation.map_mul]
    calc _ ≤ 1 * WithZero.exp (-(b : ℤ)) := mul_le_mul' (hinv_int b i l) (hkv b l j)
      _ = WithZero.exp (-(b : ℤ)) := one_mul _

  have hscal : ∀ (a : ℕ → p.adicCompletion ℚ) (x : p.adicCompletion ℚ),
      (∀ b : ℕ, Valued.v (a b - x) ≤ WithZero.exp (-(b : ℤ))) → Filter.Tendsto a Filter.atTop (nhds x) := by
    intro a x ha
    rw [Filter.tendsto_def]
    intro s hs
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
    rw [Filter.mem_atTop_sets]
    set δ : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hδ
    have hδ0 : δ ≠ 0 :=
      (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding :
        MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v (R := p.adicCompletion ℚ))) →*₀ WithZero (Multiplicative ℤ)).toMonoidHom
        γ).ne_zero
    refine ⟨(-(WithZero.log δ)).toNat + 1, fun b hb => hγ ?_⟩
    show Valued.v.restrict (a b - x) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding]
    refine lt_of_le_of_lt (ha b) ?_
    show WithZero.exp (-(b : ℤ)) < δ
    rw [← WithZero.exp_log hδ0, WithZero.exp_lt_exp]
    have := Int.self_le_toNat (-(WithZero.log δ))
    omega

  have hM : Filter.Tendsto (fun b => ((k b : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))
      Filter.atTop (nhds 1) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hscal _ _ fun b => by
      have := hkv b i j; rwa [Matrix.sub_apply] at this
  have hMinv : Filter.Tendsto
      (fun b => (((k b)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))
      Filter.atTop (nhds 1) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hscal _ _ fun b => by
      have := hkv' b i j; rwa [Matrix.sub_apply] at this

  have hGL : Filter.Tendsto k Filter.atTop (nhds 1) := by
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    simp only [Function.comp_def, Units.embedProduct_apply, Units.val_one, inv_one, MulOpposite.op_one]
    exact hM.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hMinv)
  obtain ⟨b, hb⟩ := (hGL.eventually_mem (hU.mem_nhds U.one_mem)).exists
  exact hkU b hb

end S_AutomorphicForm_exists_forall_mem_of_isOpen_of_congruence
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_mem_of_isOpen_of_congruence (solution)
