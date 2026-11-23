-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:46.784615+00:00
-- url     : https://prove2.me/theorems/d8c34e5e-f0ed-4256-a840-27486d986b4b
-- title:
--   Zero Mem Sol Set
-- statement:
--   Definitions and structural lemmas for Zero Mem Sol Set, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ZeroMemSolSet.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllReg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ZetaZeros.D.EllReg
open scoped BoundedContinuousFunction
namespace GlobalTheory.HCA
variable {d : ℕ}
def apOp (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (u : E d → ℂ) (x : E d) : ℂ :=
  ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d, a n w x * dw (List.ofFn w) u x
def symb (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (x ξ : E d) : ℂ :=
  ∑ w : Fin m → Fin d, a m w x * ∏ l, ((ξ (w l) : ℝ) : ℂ)
def oneSys (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) : Sys d Unit := ⟨fun _ => m, fun _ => a⟩
open Classical in

def ext0 (U : Set (E d)) (u : U → ℂ) (x : E d) : ℂ := if hx : x ∈ U then u ⟨x, hx⟩ else 0
def solSet {ι : Type} (P : Sys d ι) (U : Set (E d)) : Set (U →ᵇ ℂ) := {u | WeakSol P U (ext0 U u)}
end GlobalTheory.HCA
end


