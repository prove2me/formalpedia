-- Prove2me | Definitions.Def_VariableBound_Paper_Decide
-- name    : VariableBound_Paper_Decide
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:22:50.716204+00:00
-- url     : https://prove2.me/theorems/e3d10d2b-a7df-482a-b2ff-dd6ae2877828
-- title:
--   Decide
-- statement:
--   Definitions and structural lemmas for Decide, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Decide.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInKStatement
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_UniformInK_Top_End
import Definitions.Def_ClauseBound_Both_End
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace SatM
open Turing
open Sat3 (CNF)
end SatM
namespace VariableBound.Decide
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSatRate
structure Alg (rn rm : ℕ → ℝ) (A : List Bool × U → List Bool) (e : List Bool → ℕ) : Prop where
  /-- A is polynomial-time -/
  polyA : PolyT A
  /-- e is polynomial-time -/
  polyE : PolyT e
  /-- on the code of (k, φ), k ≥ 1, φ a k-CNF, with a pad of at least 2^(e x) units, A is the number
  of satisfying assignments in n + 1 bits -/
  correct : ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ e (SatM.enc k φ) ≤ pad.length → A (SatM.enc k φ, pad) = SatK.binary n (SatK.numSat φ)
  /-- for n ≥ 1 the number of steps of the padding machine is within the bound in n, for every q,
  with a constant that does not depend on k -/
  timeN : ∀ q : ℕ, ∃ D : ℕ, ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ →
    q * ((SatM.enc k φ).length + 2 ^ e (SatM.enc k φ) + 1) ^ q ≤ SatM.boundNK rn D k n
  /-- if all variables occur and m ≥ 1, it is within the bound in m, for every q, with a constant
  that does not depend on k -/
  timeM : ∀ q : ℕ, ∃ D : ℕ, ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ →
    q * ((SatM.enc k φ).length + 2 ^ e (SatM.enc k φ) + 1) ^ q ≤ SatM.bound rm D k φ.length
def bitOf (w : List Bool) : List Bool := [w.any id]
end VariableBound.Decide
end
section
@[expose] section
namespace VariableBound.Decide
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Both.End UniformInK.End
end VariableBound.Decide


