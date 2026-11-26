-- Prove2me | Definitions.Def_Eden_ExteriorMaximalGrowth
-- name    : Eden_ExteriorMaximalGrowth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:32:33.363236+00:00
-- url     : https://prove2.me/theorems/e4f30895-33b1-4fb3-ac84-38a06c2bbd6d
-- title:
--   Exterior Maximal Growth
-- statement:
--   Definitions and structural lemmas for Exterior Maximal Growth, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean

import Definitions.Def_Eden_ExteriorLimits
import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_KaplanYorke
import Mathlib.Topology.Order.LiminfLimsup
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
namespace Eden
def exteriorGrowthRate (k : ℕ) (c : ℝ) (p : PhaseSpace) (v : ExteriorSpace k) : ℝ :=
  limUnder atTop (fun t => Real.log ‖exteriorEvolution k c t p v‖ / t)
def initialExteriorBasisVector (k : ℕ) (p : PhaseSpace) (s : ExteriorIndex k) : ExteriorSpace k :=
  exteriorPower.map k (radialFrame p).toLinearMap (exteriorBasis k s)
end Eden


