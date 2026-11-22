-- Prove2me | Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GaussV
-- name    : Formalism_FormalGroupWitt_FormalGroupWittProofs_GaussV
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:40.569231+00:00
-- url     : https://prove2.me/theorems/d6ee3471-cad8-4aee-9c27-b85dc8dcfab2
-- title:
--   Gauss V
-- statement:
--   Definitions and structural lemmas for Gauss V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GaussV.lean

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
namespace Formalism.FG.BernoulliBounds
open MvPowerSeries Formalism.G Formalism.FG.SolveVAux
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
def BndLe {ι : Type*} (c : ℝ) (M : ℕ) (f : MvPowerSeries ι K) (B : ℝ) : Prop :=
  ∀ t : ι →₀ ℕ, t.degree ≤ M → ‖coeff t f‖ * c ^ t.degree ≤ B
variable [CharZero K]
def shiftPoly (K : Type u) [Field K] (l m : ℕ) (j : ZMod m) (N : ℕ) : MvPowerSeries (ZMod m) K :=
  ∑ e ∈ Finset.range (N + 1), ((l : K) ^ e)⁻¹ • (X (j - (e : ZMod m)) ^ ((l ^ 2) ^ e))
end Formalism.FG.BernoulliBounds
namespace Formalism.FG
end Formalism.FG


