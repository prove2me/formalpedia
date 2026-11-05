-- Prove2me | Definitions.Def_PaddedDescent_F_ArithGlob
-- name    : PaddedDescent_F_ArithGlob
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:46:05.467839+00:00
-- url     : https://prove2.me/theorems/0cdf3e10-0f76-4c5c-bad2-950ff592c5e8
-- title:
--   Arith Glob
-- statement:
--   Definitions and structural lemmas for Arith Glob, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithGlob.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Threshold
import Definitions.Def_PaddedDescent_F_ArithInv
set_option autoImplicit false
section
section
namespace PaddedDescent.F.Arith
def Xof (s n : ℕ) : ℕ := n / 2 ^ s + 1
def Zof (s : ℕ) : ℕ := Ytop s ^ 2
def Ubof (k s n : ℕ) : ℕ := Ub k (gtop s) n (n + 2) (betaOf s) (layersOf s + 2)
def Pbof (Δ s n : ℕ) : ℕ := Pb (gtop s) n (betaOf s) Δ
def Qmof (k s n : ℕ) : ℕ := Ubof k s n + Xof s n + Zof s
def Wmof (k s n : ℕ) : ℕ := 17 * Qmof k s n * Ktop s ^ 3
def Lof (s n : ℕ) : ℕ := 6 * s + 24 + Nat.size n
end PaddedDescent.F.Arith


