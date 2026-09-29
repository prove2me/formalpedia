-- Prove2me | solution 1 for AutomorphicForm.isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c8b30518-1ba5-5bdb-a04d-c6200be9d198

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (rT : Fin n → GL (Fin 2) (v.adicCompletion K)) (z : GL (Fin 2) (v.adicCompletion K)) (k j : ℕ) :
    AutomorphicForm.IsLocalTestFn K v (fun x : GL (Fin 2) (v.adicCompletion K) =>
      ∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * x))  := by
  classical

  have hmul : ∀ (g : GL (Fin 2) (v.adicCompletion K)) {f : GL (Fin 2) (v.adicCompletion K) → ℂ},
      AutomorphicForm.IsLocalTestFn K v f → AutomorphicForm.IsLocalTestFn K v (fun x => f (g * x)) :=
    fun g f h => ⟨h.1.comp_continuous (continuous_const_mul g), h.2.comp_homeomorph (Homeomorph.mulLeft g)⟩
  have hadd : ∀ {f g : GL (Fin 2) (v.adicCompletion K) → ℂ}, AutomorphicForm.IsLocalTestFn K v f →
      AutomorphicForm.IsLocalTestFn K v g → AutomorphicForm.IsLocalTestFn K v (fun x => f x + g x) :=
    fun hf hg => ⟨(hf.1.prodMk hg.1).comp (fun p : ℂ × ℂ => p.1 + p.2), hf.2.add hg.2⟩
  have hsum : ∀ (s : Finset (Fin k → Fin n)),
      AutomorphicForm.IsLocalTestFn K v (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ ι ∈ s, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
          (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * x)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using AutomorphicForm.isLocalTestFn_zero K v
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact hadd (hmul _ (AutomorphicForm.isLocalTestFn_indicator_localIntegralSet K v)) ih
  exact hsum Finset.univ

end S_AutomorphicForm_isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul
end P2MW
export P2MW.S_AutomorphicForm_isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul (solution)
