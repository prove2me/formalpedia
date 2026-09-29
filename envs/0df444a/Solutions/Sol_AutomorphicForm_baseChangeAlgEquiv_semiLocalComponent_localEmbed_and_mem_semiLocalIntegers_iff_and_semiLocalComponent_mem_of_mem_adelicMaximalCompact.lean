-- Prove2me | solution 1 for AutomorphicForm.baseChangeAlgEquiv_semiLocalComponent_localEmbed_and_mem_semiLocalIntegers_iff_and_semiLocalComponent_mem_of_mem_adelicMaximalCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9bbce7bd-0f45-5e45-aa20-dbfc36738fb4

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_baseChangeAlgEquiv_semiLocalComponent_localEmbed_and_mem_semiLocalIntegers_iff_and_semiLocalComponent_mem_of_mem_adelicMaximalCompact

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace S0EMBED

theorem coord_semiLocalEval (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (a : FiniteAdeleRing (𝓞 L) L) (w : v.Extension (𝓞 L)) :
    HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v (AutomorphicForm.semiLocalEval K L v a) w =
      a w.1 := by
  show HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
      ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w' : v.Extension (𝓞 L) => NumberField.AdelicLevel.finAdeleEval (𝓞 L) L w'.1 a)) w = a w.1
  rw [AlgEquiv.apply_symm_apply]
  rfl

theorem entry_semiLocalComponent (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2) :
    ((AutomorphicForm.semiLocalComponent K L v x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j =
      AutomorphicForm.semiLocalEval K L v ((x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) :=
  rfl

theorem mem_semiLocalIntegers_iff (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (y : L ⊗[K] v.adicCompletion K) :
    y ∈ AutomorphicForm.semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L),
        HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v y w ∈ w.1.adicCompletionIntegers L := by
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage, AutomorphicForm.piIntegers, Set.mem_univ_pi]
  exact Iff.rfl

theorem semiLocalEval_mem_of_integral (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (a : FiniteAdeleRing (𝓞 L) L)
    (ha : a ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 L) L) :
    AutomorphicForm.semiLocalEval K L v a ∈ AutomorphicForm.semiLocalIntegers K L v := by
  rw [mem_semiLocalIntegers_iff]
  intro w
  rw [coord_semiLocalEval]
  exact ha w.1

end S0EMBED

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    (∀ (w₀ : v.Extension (𝓞 L)) (g : GL (Fin 2) (w₀.1.adicCompletion L)) (i j : Fin 2),
      HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
          (((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₀.1 g) :
            GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j) w₀ =
        (g : Matrix (Fin 2) (Fin 2) (w₀.1.adicCompletion L)) i j ∧
      ∀ w : v.Extension (𝓞 L), w ≠ w₀ →
        HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
            (((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₀.1 g) :
              GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j) w =
          (1 : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j) ∧
    (∀ y : L ⊗[K] v.adicCompletion K,
      y ∈ AutomorphicForm.semiLocalIntegers K L v ↔
        ∀ w : v.Extension (𝓞 L),
          HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v y w ∈ w.1.adicCompletionIntegers L) ∧
    (∀ k : AutomorphicForm.AdelicGL2 (𝓞 L) L, k ∈ AutomorphicForm.adelicMaximalCompact L →
      AutomorphicForm.semiLocalComponent K L v (NumberField.AdelicLevel.glFin (𝓞 L) L k) ∈
        AutomorphicForm.semiLocalIntegralSet K L v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w₀ g i j
    refine ⟨?_, fun w hw => ?_⟩
    · rw [S0EMBED.entry_semiLocalComponent, S0EMBED.coord_semiLocalEval]
      exact AdelicDock.localMat_apply_self (𝓞 L) L w₀.1 _ i j
    · rw [S0EMBED.entry_semiLocalComponent, S0EMBED.coord_semiLocalEval]
      have hw' : w.1 ≠ w₀.1 := fun h => hw (Subtype.ext h)
      exact AdelicDock.localMat_apply_of_ne (𝓞 L) L w₀.1 _ i j hw'
  · intro y
    exact S0EMBED.mem_semiLocalIntegers_iff K L v y
  · intro k hk
    have hfin := (NumberField.AdelicLevel.mem_finiteIntegralGL2_iff).1 (AutomorphicForm.mem_adelicMaximalCompact_iff.1 hk).1
    refine (AutomorphicForm.mem_integralUnitsSet).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [S0EMBED.entry_semiLocalComponent]
      exact S0EMBED.semiLocalEval_mem_of_integral K L v _ (hfin.1 i j)
    · rw [← map_inv, S0EMBED.entry_semiLocalComponent]
      exact S0EMBED.semiLocalEval_mem_of_integral K L v _ (hfin.2 i j)

end S_AutomorphicForm_baseChangeAlgEquiv_semiLocalComponent_localEmbed_and_mem_semiLocalIntegers_iff_and_semiLocalComponent_mem_of_mem_adelicMaximalCompact
end P2MW
export P2MW.S_AutomorphicForm_baseChangeAlgEquiv_semiLocalComponent_localEmbed_and_mem_semiLocalIntegers_iff_and_semiLocalComponent_mem_of_mem_adelicMaximalCompact (solution)
