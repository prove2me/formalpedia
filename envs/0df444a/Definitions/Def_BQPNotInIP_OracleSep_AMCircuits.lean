-- Prove2me | Definitions.Def_BQPNotInIP_OracleSep_AMCircuits
-- name    : BQPNotInIP_OracleSep_AMCircuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:45:43.352472+00:00
-- url     : https://prove2.me/theorems/0d89e5d8-d66a-4d2a-a3c4-f36532c75ed0
-- title:
--   Definition 1 — affine-leaf average–maximum circuits
-- statement:
--   An average–maximum tree on $m$ real coordinates has affine leaves $c+\sum_i u_i x_i$ and internal nodes computing either the average or maximum of a nonempty finite child list. An $(m,d,L)$ circuit is such a tree with depth at most $d$, fan-in at most $2^L$, and
--   $$
--   \sum_{i=1}^m |u_i|\le L
--   $$
--   at every leaf. A leaf has depth zero. Evaluation recursively computes a real function $C:\mathbb R^m\to\mathbb R$.
--
--   A head child and tail list encode nonempty fan-in, so averages and maxima are always defined. The definition contains no smoothing theorem or assumed derivative bound; it gives the circuit class used by the structural and indistinguishability results.
--
--   Differences from the source:
--   - encoding: nonempty gate fan-in and natural depth/communication bounds → head-plus-tail child lists and natural numbers d,L; reason: empty averages and maxima are excluded; the same trees and depth convention are represented
-- source:
--   Adam Bouland, Andrew Huang, Anand Natarajan, Itay Shalit, Avishay Tal, BQP ⊆ IP Does Not Relativize, STOC 2027 submission #156 (October 2026), Definition 1, PDF p. 12 (printed p. 10). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/156.pdf#page=12

import Mathlib

set_option autoImplicit false

namespace BQPNotInIP.OracleSep

/-- Nonempty child lists are represented by one head and an arbitrary tail. -/
inductive AMTree (m : ℕ) where
  | leaf (c : ℝ) (u : Fin m → ℝ)
  | avg (first : AMTree m) (rest : List (AMTree m))
  | max (first : AMTree m) (rest : List (AMTree m))

def AMTree.depth {m : ℕ} : AMTree m → ℕ
  | .leaf _ _ => 0
  | .avg f fs | .max f fs => 1 + (fs.map AMTree.depth).foldl Nat.max f.depth

def AMTree.admissible {m : ℕ} (L : ℕ) : AMTree m → Prop
  | .leaf _ u => (∑ i, |u i|) ≤ (L : ℝ)
  | .avg f fs | .max f fs =>
    fs.length + 1 ≤ 2^L ∧ f.admissible L ∧ ∀ g ∈ fs, g.admissible L

noncomputable def AMTree.eval {m : ℕ} : AMTree m → (Fin m → ℝ) → ℝ
  | .leaf c u, x => c + ∑ i, u i * x i
  | .avg f fs, x => (f.eval x + (fs.map (fun g => g.eval x)).sum) / (fs.length + 1 : ℕ)
  | .max f fs, x => (fs.map (fun g => g.eval x)).foldl (fun a b => Max.max a b) (f.eval x)

structure AMCircuit (m d L : ℕ) where
  tree : AMTree m
  depth_le : tree.depth ≤ d
  admissible : tree.admissible L

noncomputable def AMCircuit.eval {m d L : ℕ} (C : AMCircuit m d L) : (Fin m → ℝ) → ℝ :=
  C.tree.eval

end BQPNotInIP.OracleSep


