-- Prove2me | Definitions.Def_B1s_fried_counterexample_main
-- name    : B1s_fried_counterexample_main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:42:02.547837+00:00
-- url     : https://prove2.me/theorems/178986e8-10e9-49d4-8083-6755f0d23986
-- title:
--   fried counterexample main
-- statement:
--   Definitions and structural lemmas for fried counterexample main, from Ben Lawton (blawton/fried-conj-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Resonance-cluster conditional reduction for a proposed counterexample to Fried's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_counterexample_main.lean

import Definitions.Def_B1s_cluster_from_resolvent_9_11
set_option autoImplicit true
set_option linter.style.header false
namespace FriedCrossing
open Filter Topology TwinRate FirstVariation Hadamard PureZeros Capstone OrderCount TorsionCore
  Derived Regularity Ledger Branch
end FriedCrossing


