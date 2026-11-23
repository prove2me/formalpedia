-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:01.465558+00:00
-- url     : https://prove2.me/theorems/acf8a2c8-edb2-483d-a8b6-e2bf27d74d01
-- title:
--   PFour Sq
-- statement:
--   Definitions and structural lemmas for PFour Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PFourSq.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K]
def qM (p q r s : K) : Matrix (Fin 4) (Fin 4) K :=
  !![p, -q, -r, -s; q, p, -s, r; r, s, p, -q; s, -r, q, p]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (c : K →+* K) (h : V → V → K)
structure Herm4 : Prop where
  add_left : ∀ x x' y, h (x + x') y = h x y + h x' y
  smul_left : ∀ (k : K) x y, h (k • x) y = k * h x y
  symm : ∀ x y, h y x = c (h x y)
  pos : ∀ x, x ≠ 0 → h x x ≠ 0 ∧ ∃ p q r s : K, c p = p ∧ c q = q ∧ c r = r ∧ c s = s ∧
    h x x = p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2
variable {c h}
def Herm4.hl (H : Herm4 c h) (y : V) : V →ₗ[K] K where
  toFun x := h x y
  map_add' x x' := H.add_left x x' y
  map_smul' k x := H.smul_left k x y
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
end


