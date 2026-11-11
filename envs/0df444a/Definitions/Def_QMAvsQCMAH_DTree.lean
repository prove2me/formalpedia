-- Prove2me | Definitions.Def_QMAvsQCMAH_DTree
-- name    : QMAvsQCMAH_DTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:06.964342+00:00
-- url     : https://prove2.me/theorems/21d575b3-8efa-400a-9fb4-39b453d01894
-- title:
--   Deterministic classical query algorithms (decision trees)
-- statement:
--   A **deterministic classical query algorithm** on a finite domain $\mathcal X$ is a decision tree: each internal node queries the oracle at an input $u\in\mathcal X$ and branches on the answer; each leaf holds the output (a bit, or for a simulator the probability that the final randomized oracle-free computation outputs $1$). Its number of queries is the depth; its queried inputs on an oracle are the labels on the path followed.
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Theorem 5, p.31; Theorem 6, p.35; Definition 22, p.35; Theorem 7, p.36

import Mathlib

set_option autoImplicit false

namespace QMAvsQCMAH

/-- A **deterministic classical query algorithm** on a finite oracle domain `X`, as a decision
tree: `node u k` queries the oracle at `u` and continues with `k (O u)`; `leaf o` stops with
output `o`. With `L = Bool` the output is a bit; with `L = ℝ` the leaf holds the acceptance
probability of a final randomized oracle-free computation.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Theorem 5, p.31 (PDF p.34): "a deterministic-classical-query simulator Sim making at most
Qsim queries, followed by a randomized oracle-free computation producing one bit. Its description
and local computation may be unrestricted"; Theorem 6, p.35; Definition 22, p.35; Theorem 7, p.36.

**Formalization Note.** Local computation is unrestricted (any tree). Each query may depend on
all earlier answers. The number of queries on a path is its length (paper.md decision 15). -/
inductive DTree (X : Type) (L : Type) where
  | leaf (o : L)
  | node (u : X) (next : Bool → DTree X L)

namespace DTree

/-- The output of the algorithm run with oracle `O`. -/
def eval {X L : Type} (O : X → Bool) : DTree X L → L
  | leaf o => o
  | node u k => eval O (k (O u))

/-- The worst-case number of queries (the depth of the tree). -/
def depth {X L : Type} : DTree X L → ℕ
  | leaf _ => 0
  | node _ k => max (depth (k false)) (depth (k true)) + 1

/-- Every query input of the tree lies in `P`. -/
def LabelsIn {X L : Type} (P : Set X) : DTree X L → Prop
  | leaf _ => True
  | node u k => u ∈ P ∧ LabelsIn P (k false) ∧ LabelsIn P (k true)

/-- Every output of the tree lies in `A`. -/
def LeavesIn {X L : Type} (A : Set L) : DTree X L → Prop
  | leaf o => o ∈ A
  | node _ k => LeavesIn A (k false) ∧ LeavesIn A (k true)

/-- The set `𝒬^O` of inputs queried when the algorithm runs with oracle `O`. -/
def queried {X L : Type} [DecidableEq X] (O : X → Bool) : DTree X L → Finset X
  | leaf _ => ∅
  | node u k => insert u (queried O (k (O u)))

/-- All root-to-leaf paths: the queried inputs with their answers, and the leaf value. -/
def paths {X L : Type} : DTree X L → List (List (X × Bool) × L)
  | leaf o => [([], o)]
  | node u k => ((paths (k false)).map fun p => ((u, false) :: p.1, p.2)) ++
      ((paths (k true)).map fun p => ((u, true) :: p.1, p.2))

end DTree

end QMAvsQCMAH


