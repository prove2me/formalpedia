-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinA
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:22.219829+00:00
-- url     : https://prove2.me/theorems/b63b792e-92a2-4054-99e8-a458af36ba56
-- title:
--   Phi CMin A
-- statement:
--   Definitions and structural lemmas for Phi CMin A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PhiCMinA.lean

import Mathlib
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
theorem emb_nonempty : Nonempty (E →+* ℂ) := by
  exact ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩
theorem eq_of_emb {a b : E} (h : ∀ σ : E →+* ℂ, σ a = σ b) : a = b := by
  obtain ⟨σ⟩ := emb_nonempty (E := E)
  exact σ.injective (h σ)
section Conj
variable {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
include hcj
theorem cj_add (a b : E) : cj (a + b) = cj a + cj b := eq_of_emb fun φ => by rw [hcj, map_add, star_add, map_add, hcj, hcj]
theorem cj_mul (a b : E) : cj (a * b) = cj a * cj b := eq_of_emb fun φ => by rw [hcj, map_mul, star_mul', map_mul, hcj, hcj]
theorem cj_one : cj 1 = 1 := eq_of_emb fun φ => by rw [hcj, map_one, star_one]
theorem cj_zero : cj 0 = 0 := eq_of_emb fun φ => by rw [hcj, map_zero, star_zero]
def cjR : E →+* E where
  toFun := cj
  map_one' := cj_one hcj
  map_mul' := cj_mul hcj
  map_zero' := cj_zero hcj
  map_add' := cj_add hcj
end Conj
def ed (E : Type) [Field E] [NumberField E] : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E)
abbrev Dinv (E : Type) [Field E] [NumberField E] : FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)
end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin


