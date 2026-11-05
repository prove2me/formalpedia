-- Prove2me | Definitions.Def_GraphProblems_Defs
-- name    : GraphProblems_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:49:35.311892+00:00
-- url     : https://prove2.me/theorems/f4873c93-bd11-44fc-9219-39240ef7f556
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblemsStatement
import Definitions.Def_CountKSat_Defs
set_option autoImplicit false
section
section
namespace GraphProblems
open Groundwork Groundwork.Prog CountKSat
def ones (x : List Bool) : ℕ := (x.takeWhile id).length
def rest (x : List Bool) : List Bool := (x.dropWhile id).tail
def read1 (x : List Bool) : List Unit × List Bool := (List.replicate (ones x) (), rest x)
def read2 (x : List Bool) : List Unit × ℕ × List Bool := (List.replicate (ones x) (), ones (rest x), rest (rest x))
def adjB (n : ℕ) (m : List Bool) (u v : ℕ) : Bool := m.getD (u * n + v) false
def pairs (n : ℕ) : List (ℕ × ℕ) := List.range n ×ˢ List.range n
def cntS (n s : ℕ) (ψ : Fml) : ℕ :=
  (Finset.univ.filter fun a : Fin n → Bool => (∀ C ∈ ψ, ∃ l ∈ C, ext a l.1 = l.2) ∧ (Finset.univ.filter fun i => a i = true).card = s).card
def indepF (n : ℕ) (m : List Bool) : Fml := ((pairs n).filter fun p => adjB n m p.1 p.2).map fun p => [(p.1, false), (p.2, false)]
def cliqueF (n : ℕ) (m : List Bool) : Fml :=
  ((pairs n).filter fun p => p.1 != p.2 && !adjB n m p.1 p.2).map fun p => [(p.1, false), (p.2, false)]
def coverF (n : ℕ) (m : List Bool) : Fml := ((pairs n).filter fun p => adjB n m p.1 p.2).map fun p => [(p.1, true), (p.2, true)]
def nbhd (n : ℕ) (m : List Bool) : List (List ℕ) := (List.range n).map fun v => v :: (List.range n).filter fun u => u != v && adjB n m v u
def posC (D : List ℕ) : List (ℕ × Bool) := D.map fun u => (u, true)
def domF (n : ℕ) (m : List Bool) : Fml := (nbhd n m).map posC
def colorF (k n : ℕ) (m : List Bool) : Fml :=
  ((List.range n).map fun v => (List.range k).map fun c => (v * k + c, true)) ++
  ((List.range n).flatMap fun v => ((pairs k).filter fun q => decide (q.1 < q.2)).map fun q => [(v * k + q.1, false), (v * k + q.2, false)]) ++
  (((pairs n).filter fun p => adjB n m p.1 p.2).flatMap fun p => (List.range k).map fun c => [(p.1 * k + c, false), (p.2 * k + c, false)])
def pats : ℕ → List (List Bool)
  | 0 => [[]]
  | b + 1 => (pats b).flatMap fun p => [false :: p, true :: p]
def nBlocks (b n : ℕ) : ℕ := n / b + 1
def digit (b y i : ℕ) : ℕ := y / (b + 1) ^ i % (b + 1)
def blockCl (b i d : ℕ) : Fml :=
  ((pats b).filter fun p => p.count true != d).map fun p => (List.range b).map fun j => (i * b + j, !(p.getD j false))
def blockF (b n s y : ℕ) (ψ : Fml) : Fml :=
  if ((List.range (nBlocks b n)).map (digit b y)).sum = s then
    ψ ++ (((List.range (b * nBlocks b n)).filter fun i => decide (n ≤ i)).map fun i => [(i, false)]) ++
      (List.range (nBlocks b n)).flatMap fun i => blockCl b i (digit b y i)
  else [[]]
abbrev DNode : Type := (List Unit × ℕ) × (List (List ℕ) × Fml)
def stepD (w : ℕ) (x : DNode) : Option (DNode × DNode) :=
  (x.2.1.find? fun C => decide (w < C.length)).map fun C =>
    ((x.1, (x.2.1.filter fun D => D != C, posC (C.take w) :: x.2.2)),
     (x.1, (x.2.1.map fun D => D.filter fun u => !(C.take w).contains u, ((C.take w).map fun u => [(u, false)]) ++ x.2.2)))
def rootD (a : List Unit × ℕ × List Bool) : DNode := ((a.1, a.2.1), (nbhd a.1.length a.2.2, []))
def leafD (x : DNode) : List Unit × ℕ × Fml := (x.1.1, x.1.2, x.2.1.map posC ++ x.2.2)
end GraphProblems


