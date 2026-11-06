-- Prove2me | Definitions.Def_CountedRecursion_RowFactorRun
-- name    : CountedRecursion_RowFactorRun
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:04:55.742815+00:00
-- url     : https://prove2.me/theorems/8342ff99-2ebd-4985-9a87-bb30c7b88ea2
-- title:
--   Row Factor Run
-- statement:
--   Definitions and structural lemmas for Row Factor Run, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowFactorRun.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowPairRun
import Mathlib.Tactic
set_option autoImplicit false
section
section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
def factorDigit (D : PiecesCounted.Data) (c g : ℕ) (tr : Bool) (lam y : ℕ) (q : FQ) (j : ℕ) : ℕ := digG (piecesOf D c) g tr 0 lam y (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2)) (tri (j / g) (j % g))
def factorChunk (D : PiecesCounted.Data) (c g : ℕ) (tr : Bool) (lam y : ℕ) (q : FQ) (j : ℕ) : List Bool :=
  chunkAt (lenG (piecesOf D c) g tr 0 lam y (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2))) (tri (j / g) (j % g)) (q.2.2.drop (g * lam))
def factorItem (D : PiecesCounted.Data) (c g : ℕ) (tr : Bool) (lam y : ℕ) (q : FQ) (j : ℕ) : ℤ :=
  if j / g < j % g then D.fn lam tr (!decide (q.1.1 < q.1.2)) (indexAt D lam (factorDigit D c g tr lam y q j))
    (PiecesCounted.toBits lam (heG g g lam q.2.1 (j / g) (nodeG g tr q.1.2 (j % g))), PiecesCounted.toBits lam (heG g g lam q.2.1 (j % g) (nodeG g tr q.1.2 (j / g)))) (factorChunk D c g tr lam y q j)
  else 1
end ExplicitCost


