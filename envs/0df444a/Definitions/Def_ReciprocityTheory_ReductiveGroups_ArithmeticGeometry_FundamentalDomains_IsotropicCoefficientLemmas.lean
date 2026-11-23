-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientLemmas
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:11.104104+00:00
-- url     : https://prove2.me/theorems/b3bfeadf-8271-4583-baf4-d9650cd12c4b
-- title:
--   Isotropic Coefficient Lemmas
-- statement:
--   Definitions and structural lemmas for Isotropic Coefficient Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicCoefficientLemmas.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace IsotropicCoefficientLemmas
lemma smul_O {r : ℕ} (β : 𝓞 E) (v : Fin r → E) : β • v = (β : E) • v := by
  rfl
lemma herm_add_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G (x + y) z = herm G x z + herm G y z := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
lemma herm_smul_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (e : E) (x z : Fin r → E) :
    herm G (e • x) z = e * herm G x z := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
def Mp {r : ℕ} (X : Data E r) (ξ : Fin r → E) : Submodule (𝓞 E) (Fin r → E) where
  carrier := {μ | μ ∈ X.Λ ∧ herm X.Gm μ ξ = 0}
  add_mem' := fun ha hb => ⟨X.Λ.add_mem ha.1 hb.1, by rw [herm_add_left, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨X.Λ.zero_mem, by simp [herm]⟩
  smul_mem' := fun β μ h => ⟨X.Λ.smul_mem β h.1, by
    rw [smul_O, herm_smul_left, h.2, mul_zero]⟩
def Nx {r : ℕ} (X : Data E r) (ξ : Fin r → E) : Submodule (𝓞 E) (Mp X ξ) where
  carrier := {m | ∃ e : E, (m : Fin r → E) = e • ξ}
  add_mem' := by
    rintro m m' ⟨e, he⟩ ⟨e', he'⟩
    exact ⟨e + e', by rw [Submodule.coe_add, he, he', add_smul]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro β m ⟨e, he⟩
    exact ⟨(β : E) * e, by rw [Submodule.coe_smul, smul_O, he, smul_smul]⟩
end IsotropicCoefficientLemmas
end ReciprocityTheory.ChartRestriction.G.FD


