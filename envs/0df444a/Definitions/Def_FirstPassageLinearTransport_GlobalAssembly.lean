-- Prove2me | Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
-- name    : FirstPassageLinearTransport_GlobalAssembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:14:37.9458+00:00
-- url     : https://prove2.me/theorems/0c18ebf4-a0fd-46a2-88e4-2df69b7f49b9
-- title:
--   Global Assembly
-- statement:
--   Definitions and structural lemmas for Global Assembly, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/GlobalAssembly.lean

import Definitions.Def_FirstPassageLinearTransport_HeadlineParameters
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real Topology
noncomputable section
def shellBootstrap {r eta : ℝ} (p : StageSetup r eta)
    (omega : ℝ) (M : ℕ) : Set ℕ :=
  bootstrapSet p (stageCount omega M)
def assembledBootstrap {r eta : ℝ} (p : StageSetup r eta)
    (omega : ℝ) : Set ℕ :=
  assembleDyadic (shellBootstrap p omega)
end
end FirstPassageLinearTransport


