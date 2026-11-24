-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_LaurentCoeffZero
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_LaurentCoeffZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:09.259264+00:00
-- url     : https://prove2.me/theorems/f8e07f33-bdc7-4218-a323-00ad62fcb789
-- title:
--   Laurent Coeff Zero
-- statement:
--   Definitions and structural lemmas for Laurent Coeff Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/ModulusBounds/LaurentCoeffZero.lean

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
open Matrix Module Polynomial
namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound
namespace LaurentWeightBound
variable {k : Type} [Field k] {n : ℕ}
def gt (P : GL (Fin n) k) (w : Fin n → ℤ) (t : kˣ) : Matrix (Fin n) (Fin n) k :=
  P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
def cut (w : Fin n → ℤ) (m : ℤ) (u : Fin n → k) : Fin n → k := fun i => if w i = m then u i else 0
def prj (P : GL (Fin n) k) (w : Fin n → ℤ) (m : ℤ) (y : Fin n → k) : Fin n → k :=
  P.val *ᵥ cut w m (P⁻¹.val *ᵥ y)
end LaurentWeightBound
open LaurentWeightBound
variable {k : Type} [Field k] [CharZero k] {n : ℕ}
end PositivityTheory.RgUd.T.Nil.Orb.BModbound


