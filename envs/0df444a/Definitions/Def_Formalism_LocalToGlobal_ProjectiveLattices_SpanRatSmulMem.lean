-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:12:46.975801+00:00
-- url     : https://prove2.me/theorems/764022c4-2689-4bf4-901a-396f1bc26aca
-- title:
--   Span Rat Smul Mem
-- statement:
--   Definitions and structural lemmas for Span Rat Smul Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Theorems.Thm_Formalism_L2_Pj_FJ_FnVia_smul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.FD
namespace Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
def trBE (n : ℕ) : LinearMap.BilinForm ℚ (Fin n → E) :=
  LinearMap.mk₂ ℚ (fun l x => Algebra.trace ℚ E (∑ i, l i * x i))
    (fun l₁ l₂ x => by
      rw [← map_add]; congr 1; simp [add_mul, Finset.sum_add_distrib])
    (fun c l x => by
      rw [← map_smul]; congr 1; simp [Finset.smul_sum])
    (fun l x₁ x₂ => by
      rw [← map_add]; congr 1; simp [mul_add, Finset.sum_add_distrib])
    (fun c l x => by
      rw [← map_smul]; congr 1; simp [Finset.smul_sum])
def dualZSubE {n : ℕ} (Xs : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := dualZE Xs
  zero_mem' := fun x _ => ⟨0, by simp⟩
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨u, hu⟩ := ha x hx
    obtain ⟨v, hv⟩ := hb x hx
    have h : ∑ i, (a + b) i * x i = ∑ i, a i * x i + ∑ i, b i * x i := by
      simp [add_mul, Finset.sum_add_distrib]
    exact ⟨u + v, by rw [h, map_add, ← hu, ← hv, Int.cast_add]⟩
  smul_mem' := by
    intro c a ha x hx
    obtain ⟨u, hu⟩ := ha (c • x) (Xs.smul_mem c hx)
    have h : ∑ i, (c • a) i * x i = ∑ i, a i * (c • x) i := by
      simp only [Pi.smul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def]; ring
    exact ⟨u, by rw [h]; exact hu⟩
end Formalism.L2.Pj.FJ


