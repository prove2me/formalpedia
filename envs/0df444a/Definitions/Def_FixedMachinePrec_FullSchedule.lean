-- Prove2me | Definitions.Def_FixedMachinePrec_FullSchedule
-- name    : FixedMachinePrec_FullSchedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:06.387947+00:00
-- url     : https://prove2.me/theorems/0153a861-e0dd-4d4c-a5bb-93c7b7355860
-- title:
--   Full schedules, ideals, antichains and the cones $P_A, D_A, \hat P_A, \hat D_A$ on a padded job set
-- statement:
--   Let $J=\{1,\dots,N\}$ be a finite job set with a strict partial order $\prec$ (the transitive precedence of the padded instance). Every subset $W\subseteq J$ inherits the restriction of $\prec$, even when a path establishing $x\prec y$ leaves $W$.
--
--   1. A **full schedule** of $W$ is an ordered partition $(S_1,\dots,S_q)$ of $W$ into antichains of exactly $m$ jobs respecting the induced order: $x\in S_i$, $y\in S_j$, $x\prec y$ imply $i<j$. It has $q=|W|/m$ slots; the empty set has the empty full schedule.
--   2. $U\subseteq W$ is an **ideal** of $W$ if $y\in U$, $x\in W$ and $x\prec y$ imply $x\in U$ (a global ideal when $W=J$). A set is an **antichain** if no two of its jobs are comparable.
--   3. For $A\subseteq J$ the **cones** are
--   $$P_A=\{x\in J:\exists a\in A,\ x\prec a\},\qquad D_A=\{x\in J:\exists a\in A,\ a\prec x\},\qquad \hat P_A=P_A\cup A,\quad \hat D_A=D_A\cup A.$$
--   4. For a list of slots, $\bigcup_{a<t<b}S_t$ is the block of slots strictly between positions $a$ and $b$; the local time $\tau(x)=t$ for $x\in S_t$.
--
--   These objects describe the full-slot subproblems that the algorithm stores, the state tests, and the cones used as atoms and in the structural proof.
--
--   **Formalization Note** $J$ is `Fin N` with 0-based labels; slots are list positions, slot $t$ (1-based as printed) being the list entry $t-1$. A strict partial order is irreflexive and transitive.
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Definition 2.1, p.4; §2.2, p.4; §7.1, pp.27–29

import Mathlib

namespace FixedMachinePrec

/-- **Full schedules, ideals, antichains, cones and slot blocks on a padded job set.**
Jansen, *Precedence Constraint Scheduling on a Fixed Number of Machines* (manuscript, sha256
08cdf3e1…), Definition 2.1, p.4: "A full schedule of W ⊆ J is an ordered partition of W into
antichains of exactly m jobs that respects the induced order on W. It has |W|/m slots. The empty
set has the empty full schedule. A set U ⊆ W is an ideal of W if y ∈ U, x ∈ W, and x ≺ y imply
x ∈ U. A set is an antichain if no two of its jobs are comparable."

`IsFullSchedule prec m W S` says that the list of slots `S = (S₁, …, S_q)` is a full schedule of
`W`: every slot has exactly `m` jobs and is an antichain, the slots are pairwise disjoint with
union `W`, and `x ≺ y` with `x ∈ S_i`, `y ∈ S_j` forces `i < j`.

**Formalization Note** The padded job set `J` is `Fin N` (0-based labels; the paper's job `j` is
`j - 1`) and `prec x y` is the global strict order `x ≺ y` on `J`; a subset `W` inherits its
restriction, so a precedence remains even if its path leaves `W` (p.4). Slots are list positions,
slot `t` (1-based, as printed) being `S[t-1]`. -/
def IsFullSchedule {N : ℕ} (prec : Fin N → Fin N → Prop) (m : ℕ) (W : Finset (Fin N))
    (S : List (Finset (Fin N))) : Prop :=
  (∀ A ∈ S, A.card = m ∧ ∀ x ∈ A, ∀ y ∈ A, ¬ prec x y) ∧
  S.Pairwise Disjoint ∧
  S.foldr (· ∪ ·) ∅ = W ∧
  ∀ (i j : ℕ) (hi : i < S.length) (hj : j < S.length) (x y : Fin N),
    x ∈ S[i] → y ∈ S[j] → prec x y → i < j

/-- `U` is an **ideal** of `W` (Definition 2.1, p.4): `U ⊆ W`, and `y ∈ U`, `x ∈ W`, `x ≺ y`
imply `x ∈ U`. With `W = univ` this is a global ideal. -/
def IsIdealIn {N : ℕ} (prec : Fin N → Fin N → Prop) (W U : Finset (Fin N)) : Prop :=
  U ⊆ W ∧ ∀ y ∈ U, ∀ x ∈ W, prec x y → x ∈ U

/-- `A` is an **antichain**: no two of its jobs are comparable. -/
def IsAntichainSet {N : ℕ} (prec : Fin N → Fin N → Prop) (A : Finset (Fin N)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ¬ prec x y

/-- The strict predecessor cone `P_A = {x ∈ J : ∃ a ∈ A, x ≺ a}` (§2.2, p.4). -/
def predCone {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec] (A : Finset (Fin N)) :
    Finset (Fin N) :=
  Finset.univ.filter fun x => ∃ a ∈ A, prec x a

/-- The strict successor cone `D_A = {x ∈ J : ∃ a ∈ A, a ≺ x}` (§2.2, p.4). -/
def succCone {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec] (A : Finset (Fin N)) :
    Finset (Fin N) :=
  Finset.univ.filter fun x => ∃ a ∈ A, prec a x

/-- The weak predecessor cone `P̂_A = P_A ∪ A` (§2.2, p.4). -/
def weakPredCone {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec] (A : Finset (Fin N)) :
    Finset (Fin N) :=
  predCone prec A ∪ A

/-- The weak successor cone `D̂_A = D_A ∪ A` (§2.2, p.4). -/
def weakSuccCone {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec] (A : Finset (Fin N)) :
    Finset (Fin N) :=
  succCone prec A ∪ A

/-- The jobs of the slots strictly between positions `a` and `b`: `⋃_{a < t < b} S_t`
(1-based slots, an empty union being `∅`). This is the open gap `A_i` of Definition 5.7 (p.15)
for `a = t_i`, `b = t_{i+1}`, the prefix `L_i = ⋃_{t < t_i} S_t` for `a = 0`, and the temporal
open interval `(a, b)` of §7.1 (p.29). -/
def slotsBetween {N : ℕ} (S : List (Finset (Fin N))) (a b : ℕ) : Finset (Fin N) :=
  ((Finset.range S.length).filter fun i => a < i + 1 ∧ i + 1 < b).biUnion fun i => S.getD i ∅

/-- The union of all slots of a schedule. -/
def unionSlots {N : ℕ} (S : List (Finset (Fin N))) : Finset (Fin N) :=
  S.foldr (· ∪ ·) ∅

/-- The local time `τ(x) = t` when `x ∈ S_t` (1-based); `S.length + 1` if `x` is in no slot. -/
def localTime {N : ℕ} (S : List (Finset (Fin N))) (x : Fin N) : ℕ :=
  S.findIdx (fun A => decide (x ∈ A)) + 1

/-- `prec` is a **strict partial order** (irreflexive and transitive), as the transitive
precedence `≺` of a directed acyclic graph is (§7.1, p.27). -/
def IsStrictOrder' {N : ℕ} (prec : Fin N → Fin N → Prop) : Prop :=
  (∀ x, ¬ prec x x) ∧ ∀ x y z, prec x y → prec y z → prec x z

end FixedMachinePrec


