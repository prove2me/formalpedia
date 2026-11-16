-- Prove2me | Definitions.Def_PolymatroidCover_Supplement_PushRelabelStep
-- name    : PolymatroidCover_Supplement_PushRelabelStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:51:11.970445+00:00
-- url     : https://prove2.me/theorems/1b5f534f-8ed7-4f32-b833-eef681d2239f
-- title:
--   Algorithm 2 (push-relabel): one while-loop iteration, as a relation
-- statement:
--   Algorithm 2 colors the ground set $E$ of a $d$-polymatroid $f$ with $k \ge (4d-2)\cdot\chi^\circ(f)$ colors. Its state at the head of the while-loop consists of color classes $S_1,\dots,S_k$ (pairwise disjoint independent sets, initially empty), positive integer levels $p(e)$ (initially $1$), and, for the analysis, the numbers of pushes and relabels performed so far. Write $p(X) := \sum_{e\in X} p(e)$.
--
--   One iteration picks an uncolored element $a$ and tries the colors $j = 1, \dots, k$ in order. The attempt of $a$ with color $j$:
--
--   1. sets $T \leftarrow \{a\}$ and orders $S_j = \{e_1,\dots,e_m\}$ so that $p(e_1) \ge \dots \ge p(e_m)$, breaking ties arbitrarily;
--   2. for $i = 1,\dots,m$, adds $e_i$ to $T$ if $T \cup \{e_i\}$ is independent;
--   3. sets the blocking set $B \leftarrow S_j \setminus T$, and succeeds if $p(a) \ge 2\, p(B)$.
--
--   At the first color whose attempt succeeds, a **push** is performed: $S_j \leftarrow T$ (the elements of $B$ become uncolored) and the iteration ends. If every color fails, a **relabel** is performed: $p(a) \leftarrow p(a) + 1$. The algorithm stops when every element is colored.
--
--   This definition records that one iteration as a relation between states, together with the initial state. The analysis of Theorem 4.1 is about every state reachable from the initial state.
--
--   **Formalization Note** The relation is nondeterministic exactly where the algorithm is: in the choice of the uncolored element and in the tie-breaking of each ordering. Colors are 0-based (`S j` is $S_{j+1}$). The independence test is the published `IsIndep`. The orderings chosen for colors after the pushed one are never used by the algorithm and influence nothing.
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §4, Algorithm 2, p.21 (PDF p.23); p(X), p.20 (PDF p.22)

import Mathlib
import Definitions.Def_PolymatroidCover_IsIndep

namespace PolymatroidCover.Supplement

open PolymatroidCover

/-- A state of Algorithm 2 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §4, printed p.21 = PDF p.23) at the head of its while-loop:
the color classes `S j` (`S j` is the paper's `S_{j+1}`), the levels `p : E → ℤ_{>0}`, and the
numbers of push and relabel operations performed so far. -/
structure PRState (n k : ℕ) where
  /-- the color classes `S_1, …, S_k` (0-based) -/
  S : Fin k → Finset (Fin n)
  /-- the levels `p(e)` -/
  p : Fin n → ℕ
  /-- pushes performed so far -/
  pushes : ℕ
  /-- relabels performed so far -/
  relabels : ℕ

/-- The initial state (lines 1–2 of Algorithm 2): every `S_j = ∅`, every level `p(e) = 1`, no
operation performed. -/
def prInit (n k : ℕ) : PRState n k := ⟨fun _ => ∅, fun _ => 1, 0, 0⟩

/-- `p(X) := ∑_{e∈X} p(e)` (printed p.20 = PDF p.22). -/
def levelSum {n : ℕ} (p : Fin n → ℕ) (X : Finset (Fin n)) : ℕ := ∑ e ∈ X, p e

/-- An element is uncolored if it lies in no color class. -/
def IsUncolored {n k : ℕ} (σ : PRState n k) (a : Fin n) : Prop := ∀ j : Fin k, a ∉ σ.S j

/-- Line 6: `l` lists the elements of `X` once each, in non-increasing order of level (ties broken
arbitrarily). -/
def IsLevelOrder {n : ℕ} (p : Fin n → ℕ) (X : Finset (Fin n)) (l : List (Fin n)) : Prop :=
  l.Nodup ∧ l.toFinset = X ∧ l.Pairwise (fun x y => p y ≤ p x)

/-- Lines 5–9: starting from `T = {a}`, scan the list `l = (e_1, …, e_m)` and add `e_i` to `T`
whenever `T ∪ {e_i}` is independent. -/
noncomputable def greedyClass {n : ℕ} (f : Finset (Fin n) → ℕ) (a : Fin n) (l : List (Fin n)) :
    Finset (Fin n) := by
  classical
  exact l.foldl (fun T e => if IsIndep f (insert e T) then insert e T else T) {a}

/-- Lines 10–11: the attempt of `a` with the color class `Sj`, scanned in the order `l`, succeeds
if `p(a) ≥ 2 · p(B)` for the blocking set `B := Sj \ T`. -/
def PushSucceeds {n : ℕ} (f : Finset (Fin n) → ℕ) (p : Fin n → ℕ) (a : Fin n)
    (Sj : Finset (Fin n)) (l : List (Fin n)) : Prop :=
  2 * levelSum p (Sj \ greedyClass f a l) ≤ p a

/-- One iteration of the while-loop of Algorithm 2 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §4, printed p.21 = PDF p.23), as a
relation between loop-head states. Verbatim: "3: while there exists an uncolored element a do
4: for j = 1, . . . , k do 5: T ← {a}. 6: Order Sj = {e1, . . . , em} so that p(e1) ≥ · · · ≥ p(em),
breaking ties arbitrarily. 7: for i = 1, . . . , m do 8: if T ∪ {ei} ∈ If then 9: T ← T ∪ {ei}.
10: B ← Sj \ T. 11: if p(a) ≥ 2 · p(B) then 12: Sj ← T and break 13: if a is uncolored then
14: p(a) ← p(a) + 1."
* `push`: `a` is uncolored; for every color an ordering `ord j` of `S_j` by non-increasing level
  is chosen; the colors are tried in the order `0, 1, …, k − 1`; `j` is the first color whose
  attempt succeeds; then `S_j ← T` (the elements of the blocking set become uncolored) and the
  push counter increases by one;
* `relabel`: `a` is uncolored and the attempts with all `k` colors fail; then `p(a)` increases by
  one and the relabel counter increases by one.

**Formalization Note** The relation is nondeterministic exactly where the algorithm is: in the
choice of the uncolored element `a` (line 3) and in the tie-breaking of each ordering (line 6).
The independence test of line 8 is the published `IsIndep`. Attempts with colors after the pushed
one are not performed by the algorithm; their orderings `ord j` are unconstrained choices that
influence nothing. The algorithm stops (no step) when no element is uncolored. -/
inductive PushRelabelStep {n k : ℕ} (f : Finset (Fin n) → ℕ) : PRState n k → PRState n k → Prop
  | push (σ : PRState n k) (a : Fin n) (ha : IsUncolored σ a) (ord : Fin k → List (Fin n))
      (hord : ∀ j : Fin k, IsLevelOrder σ.p (σ.S j) (ord j)) (j : Fin k)
      (hfail : ∀ j' : Fin k, j' < j → ¬ PushSucceeds f σ.p a (σ.S j') (ord j'))
      (hj : PushSucceeds f σ.p a (σ.S j) (ord j)) :
      PushRelabelStep f σ
        ⟨Function.update σ.S j (greedyClass f a (ord j)), σ.p, σ.pushes + 1, σ.relabels⟩
  | relabel (σ : PRState n k) (a : Fin n) (ha : IsUncolored σ a) (ord : Fin k → List (Fin n))
      (hord : ∀ j : Fin k, IsLevelOrder σ.p (σ.S j) (ord j))
      (hfail : ∀ j : Fin k, ¬ PushSucceeds f σ.p a (σ.S j) (ord j)) :
      PushRelabelStep f σ
        ⟨σ.S, Function.update σ.p a (σ.p a + 1), σ.pushes, σ.relabels + 1⟩

end PolymatroidCover.Supplement


