-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:38:53.10081+00:00
-- url     : https://prove2.me/theorems/0328dcb5-43f3-4d45-a00e-4dfca5828f9e
-- title:
--   Local Frame Preserves Orthogonal
-- statement:
--   Definitions and structural lemmas for Local Frame Preserves Orthogonal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
namespace PI.ScPiBuildW.Loc
open PI.ScPiExists
section Basic
variable {n : ℕ} (ε : Fin n → Bool)
end Basic
structure LocFrame (n r k : ℕ) (ε : Fin n → Bool) where
  e : Fin r → Fin n → ℂ
  f : Fin r → Fin n → ℂ
  z : Fin n → ℂ
  w : Fin k → Fin n → ℂ
  hn : n = 2 * r + k + 1
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0
  ez : ∀ a, hJ ε (e a) z = 0
  fz : ∀ a, hJ ε (f a) z = 0
  zz : hJ ε z z ≠ 0
  ww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0
  ew : ∀ c a, hJ ε (e c) (w a) = 0
  fw : ∀ c a, hJ ε (f c) (w a) = 0
  zw : ∀ a, hJ ε z (w a) = 0
namespace LocFrame
variable {n r k : ℕ} {ε : Fin n → Bool} (L : LocFrame n r k ε)
def fam : (Fin r ⊕ Fin r) ⊕ (Unit ⊕ Fin k) → Fin n → ℂ :=
  Sum.elim (Sum.elim L.e L.f) (Sum.elim (fun _ => L.z) L.w)
abbrev X : Submodule ℂ (Fin n → ℂ) := spanLt L.e r
section Grp
variable {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g)
include hg hS
end Grp
def M (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun a b => hJ ε (L.w a) (g *ᵥ L.w b)
end LocFrame
end PI.ScPiBuildW.Loc


