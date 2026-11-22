-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:14:30.837826+00:00
-- url     : https://prove2.me/theorems/bf1bb08f-842c-48b7-b485-45d21a2d4a6c
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/Imports.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux
def fS {p m : ℕ} (s : Fin (p + 2) → ℝ) (x : Xp (p + 1) m) : ℝ≥0∞ :=
  ∏ l, ENNReal.ofReal (de x l ^ (-s l))
def rho (t : ℝ) : ℂ := (1 + t * Complex.I) ^ 2 / ((1 + t ^ 2 : ℝ) : ℂ)
def rot {p m : ℕ} (t : ℝ) (x : Xp p m) : Xp p m :=
  (fun j => rho t * x.1 j, fun j => rho t * x.2.1 j, fun i => rho t * x.2.2.1 i, x.2.2.2)
def scl {p m : ℕ} (τ : ℝ) (x : Xp (p + 1) m) : Xp (p + 1) m :=
  (Function.update x.1 0 (τ * x.1 0), Function.update x.2.1 0 (x.2.1 0 / τ), x.2.2.1, x.2.2.2)
end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi


