-- Prove2me | Definitions.Def_Eight_ViaGrouping_AlgDefs
-- name    : Eight_ViaGrouping_AlgDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:58:11.182808+00:00
-- url     : https://prove2.me/theorems/2e3e568f-a370-4e64-ba5c-1d628d7bc8e2
-- title:
--   Alg Defs
-- statement:
--   Definitions and structural lemmas for Alg Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/AlgDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_GridPsiDefs
import Definitions.Def_Eight_ViaGrouping_SatPsiDefs
set_option autoImplicit false
section
section
namespace Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Eight.SecNetworks
def CLIQUEp : ℕ → CliqueAlgorithm
  | 0 => bruteE (levelK 0)
  | ℓ + 1 => levelAlgP (levelG ℓ) (gridPsi (levelG ℓ) false) (gridPsi (levelG ℓ) true) (netAlg (levelK ℓ) (levelG ℓ) (CLIQUEp ℓ))
def NETWORKp (ℓ : ℕ) : NetAlg := netAlg (levelK ℓ) (levelG ℓ) (CLIQUEp ℓ)
def COUNTp (ℓ : ℕ) : StepMachine Formula ℤ := (NETWORKp ℓ).app (satProcs (levelG ℓ) 3)
end Eight.ViaGrouping


