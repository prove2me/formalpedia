-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareEqDiagOfQuadraticEven
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_SquareEqDiagOfQuadraticEven
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:11:10.402567+00:00
-- url     : https://prove2.me/theorems/27824949-c70c-444d-9bc8-4b0dd4d3b12b
-- title:
--   Square Eq Diag Of Quadratic Even
-- statement:
--   Definitions and structural lemmas for Square Eq Diag Of Quadratic Even, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SquareEqDiagOfQuadraticEven.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SignsFromTrianglesSquares
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
open Formalism.HermitianLattices.WeilRepresentation Formalism.HermitianLattices.IntegralLatticeDensity
example : ∀ a b : ZMod 2, a.val % 2 = b.val % 2 →
    (∑ _r : Unit, (1 : ZMod 5) * 1) = if a = b then 1 else 0 := by decide
example (p : ℕ) (hp : p.Prime) : ∀ a ∈ (algebraMap ℤ ℚ).range, ∃ b ∈ (algebraMap ℤ ℚ).range,
    (RingHom.id ℚ) a - a ^ p = (p : ℚ) * b := by
  rintro _ ⟨n, rfl⟩
  haveI := Fact.mk hp
  have : (p : ℤ) ∣ n - n ^ p := by
    rw [← (ZMod.intCast_zmod_eq_zero_iff_dvd _ p)]; push_cast; rw [ZMod.pow_card]; ring
  obtain ⟨k, hk⟩ := this
  refine ⟨k, ⟨k, rfl⟩, ?_⟩
  have := congrArg (fun z : ℤ => (z : ℚ)) hk
  simpa using this
section
variable {V : Type} [AddCommGroup V] {H : V → V → ℂ}
end
example : ∀ a : Fin 3 → ZMod 3, (∑ j, a j) ^ 2 =
    (∑ j, (a j) ^ 2) + ∑ j, ∑ j' ∈ univ.filter (fun j' => j < j'), cob (fun x : ZMod 3 => x ^ 2) (a j) (a j') := by
  decide +kernel
end Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
namespace Formalism.HermitianLattices.WeilRepresentation
end Formalism.HermitianLattices.WeilRepresentation


