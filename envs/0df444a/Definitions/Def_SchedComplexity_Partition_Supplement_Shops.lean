-- Prove2me | Definitions.Def_SchedComplexity_Partition_Supplement_Shops
-- name    : SchedComplexity_Partition_Supplement_Shops
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:25:29.153021+00:00
-- url     : https://prove2.me/theorems/91663638-381b-4e36-9b07-a312871f6919
-- title:
--   Section 3 — fixed and variable machine counts, F/P/G/I shops
-- statement:
--   The machine count is either a positive fixed constant or a positive number supplied in the instance. A flow shop has one operation per machine in the order $M_1,\ldots,M_m$. A permutation shop is a flow shop whose schedule uses one common job permutation on every machine. A general job shop allows an arbitrary operation list for each job, including repeated machines. In an identical parallel-machine shop each job has a single operation; the schedule chooses its machine.
--
--   $$F:\ \mu_j=(M_1,\ldots,M_m),\qquad P:\ F\text{ with a common job order},\qquad I:\ m_j=1.$$
--
--   At $m=1$, the shop label is absent in the source: each label denotes the single-machine, one-operation model. The variable-count family includes this boundary under that convention. The common-order condition compares operations of earlier and later jobs on the same machine. Identical-machine inputs carry canonical machine tag zero, and a schedule assignment builds the published shop instance with the actual chosen machine for each job.
--
--   This is the structural layer shared by all classification results. **Formalization Note** Counts and indices use natural numbers, jobs are `Fin n`, and zero operations are allowed in the general job shop when $m>1$. The processing times, releases and precedence of the published instance are unchanged when realizing a machine assignment.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), Sections 2–3, pp. 4, 6–7

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Supplement_Data

namespace SchedComplexity.Partition.Supplement

/-- Section 3: a fixed machine count, or a count supplied with the instance. -/
inductive MachineCount where
  | fixed (m : ℕ)
  | variable
  deriving DecidableEq

/-- The count is a positive constant or is variable. -/
def MachineCount.Valid : MachineCount → Prop
  | .fixed m => 0 < m
  | .variable => True

/-- Machine counts are positive; the single-machine case is included. -/
def MachineCount.Allows : MachineCount → ℕ → Prop
  | .fixed c, m => 0 < m ∧ m = c
  | .variable, m => 0 < m

/-- Section 3, p. 6: F, P, G, I. At one machine ℓ is absent, and all four names denote
the one-operation single-machine model. Variable m includes m=1 under this convention. -/
inductive ShopKind where
  | flow
  | permutation
  | general
  | identical
  deriving DecidableEq

/-- Flow-shop machine order: each job visits every machine once, in index order. -/
def IsFlow {n m : ℕ} (I : Instance n m) : Prop :=
  ∀ j, (I.shop.ops j).map Prod.fst = List.ofFn (fun i : Fin m => i)

/-- An identical-machine input stores one operation per job with canonical machine tag zero.
Its actual assigned machine is chosen by the schedule, not supplied in the instance. -/
def IsIdenticalInput {n m : ℕ} (I : Instance n m) : Prop :=
  (∀ j, (I.shop.ops j).length = 1) ∧
  (∀ j, ∀ e ∈ I.shop.ops j, e.1.val = 0)

/-- Structural membership in ℓ. At m=1, the paper omits ℓ and every job has one operation.
At larger m, G permits any operation list, including repetitions and the empty list. -/
def HasShape {n m : ℕ} (ell : ShopKind) (I : Instance n m) : Prop :=
  if m = 1 then ∀ j, (I.shop.ops j).length = 1 else
    match ell with
    | .flow | .permutation => IsFlow I
    | .general => True
    | .identical => IsIdenticalInput I

/-- Build the published ShopInstance for a chosen identical-machine assignment. For the other
shop types the input's machine orders are retained. The assignment is a witness, not input data. -/
def realize {n m : ℕ} (ell : ShopKind) (I : Instance n m) (a : Fin n → Fin m) :
    SchedComplexity.Shops.ShopInstance n m :=
  if ell = .identical then
    { I.shop with ops := fun j => (I.shop.ops j).map (fun e => (a j, e.2)) }
  else I.shop

/-- P means one common permutation of jobs on every machine (p. 6). Order positions,
job indices and machine indices are all 0-based. This includes operations of duration zero. -/
def CommonOrder {n m : ℕ} (Q : SchedComplexity.Shops.ShopInstance n m)
    (S : Q.Op → ℕ) : Prop :=
  ∃ π : Equiv.Perm (Fin n), ∀ (a b : Fin n) (o o' : Q.Op),
    a < b → o.1 = π a → o'.1 = π b → Q.mach o = Q.mach o' →
      S o + Q.proc o ≤ S o'

end SchedComplexity.Partition.Supplement


