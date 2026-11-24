-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Columns_GoodXgE
-- name    : Formalism_LocalToGlobal_Columns_GoodXgE
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T10:31:37.910191+00:00
-- url     : https://prove2.me/theorems/24e6ceb3-9eeb-420a-8022-76e4ae7a0afb
-- title:
--   Good Xg E
-- statement:
--   Definitions and structural lemmas for Good Xg E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GoodXgE.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GoodXgFin
import Theorems.Thm_Formalism_L2_Col_absIrrChar_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Col
open Formalism.L2.DIV
section E
variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [CharZero K]
def XgESet (σ : K →+* ℂ) (e : MonoidAlgebra ℂ G) : Set (G → K) :=
  {χ | IsAbsIrrChar χ ∧ ∑ g : G, e.coeff g * σ (χ g) = σ (χ 1)}
theorem XgESet_finite (σ : K →+* ℂ) (e : MonoidAlgebra ℂ G) : (XgESet σ e).Finite :=
  (absIrrChar_finite (G := G) (K := K)).subset fun _ h => h.1
def XgE (σ : K →+* ℂ) (e : MonoidAlgebra ℂ G) : Finset (G → K) := (XgESet_finite σ e).toFinset
end E
end Formalism.L2.Col


