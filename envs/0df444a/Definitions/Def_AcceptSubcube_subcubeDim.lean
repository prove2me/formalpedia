-- Prove2me | Definitions.Def_AcceptSubcube_subcubeDim
-- name    : AcceptSubcube_subcubeDim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:26.40423+00:00
-- url     : https://prove2.me/theorems/3ef49bd2-89a1-4728-b063-c1b7ce5523c5
-- title:
--   Accepting-subcube dimension $h(P)$, pinning property $\mathsf P_t$, the class $\mathcal C_{k,h}$
-- statement:
--   A **coordinate subcube** of $\{0,1\}^k$ is $Q(S,a)=\{x: x_S=a\}$ for $S\subseteq[k]$ and $a\in\{0,1\}^S$; it has dimension $k-|S|$. It is **accepting** for a predicate $P$ if $Q(S,a)\subseteq P^{-1}(1)$. The **accepting-subcube dimension** of a nontrivial predicate is
--   $$h(P)=\max\{\dim Q: Q\subseteq P^{-1}(1)\text{ a coordinate subcube}\}\in\{0,\dots,k-1\}.$$
--
--   A predicate has the **pinning property** $\mathsf P_t$ if for every $t$-set $S$ of coordinates and every $a\in\{0,1\}^S$ some completion $z$ has $P(a,z)=0$ (Definition 2.1); an instance has $\mathsf P_t$ when every predicate does.
--
--   For $0\le h\le k-1$, **$\mathcal C_{k,h}$** is the class of complete Boolean $k$-CSPs with nontrivial predicates in which every predicate has $h(P)\le h$.
--
--   Parity on three variables has $h=0$, signed NAE$_3$ has $h=1$, and a 3-clause has $h=2$ (Figure 1); the class $\mathcal C_{k,h}$ is the one Theorem 1.1 is about.
--
--   **Formalization Note** $a$ is a full vector of which only $a_S$ is read. $h$ is defined for every table as a maximum over a finite set; a table with no accepting pattern gets $0$, but the class and Lemma 2.2 only apply $h$ to nontrivial predicates, where an accepting pattern is a $0$-dimensional accepting subcube and the value is the paper's.
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), §1.2.1, p.3 (Q(S,a), h(P), C_{k,h}); Definition 2.1, p.10 (P_t)

import Mathlib
import Definitions.Def_AcceptSubcube_GInst

namespace AcceptSubcube

/-- The `k`-ary predicate given by a truth table (pattern `y` at index `Σ_i 2^i·y_i`). -/
def tabPred (k : ℕ) (tab : List Bool) : (Fin k → Bool) → Bool :=
  fun y => tab.getD (patIdx (List.ofFn y)) false

/-- The local predicate of a constraint, on the coordinates `0, …, |scope|−1` of its scope. -/
def consPred (c : List ℕ × List Bool) : (Fin c.1.length → Bool) → Bool :=
  tabPred c.1.length c.2

/-- The coordinate subcube `Q(S, a) = {y : y_S = a_S}` is accepting for `P` (contained in
`P^{−1}(1)`). Only the values of `a` on `S` matter. -/
def AcceptsSubcube {k : ℕ} (P : (Fin k → Bool) → Bool) (S : Finset (Fin k)) (a : Fin k → Bool) :
    Prop :=
  ∀ y : Fin k → Bool, (∀ i ∈ S, y i = a i) → P y = true

instance {k : ℕ} (P : (Fin k → Bool) → Bool) (S : Finset (Fin k)) (a : Fin k → Bool) :
    Decidable (AcceptsSubcube P S a) := by
  unfold AcceptsSubcube; infer_instance

/-- **Accepting-subcube dimension** `h(P)`.

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), §1.2.1, p.3: "A coordinate subcube of {0,1}^k
is a set Q(S, a) = {x ∈ {0,1}^k : x_S = a}, S ⊆ [k], a ∈ {0,1}^S … it fixes the coordinates in S
and has dimension k − |S|. An accepting subcube of a predicate P is a coordinate subcube contained
in P^{−1}(1). For a nontrivial predicate P, define its accepting-subcube dimension by
h(P) = max{dim Q : Q ⊆ P^{−1}(1) is a coordinate subcube}."

The maximum of `k − |S|` over all pairs `(S, a)` whose subcube is accepting.

**Formalization Note.** `a ∈ {0,1}^S` is a full vector `a : Fin k → Bool` of which only `a_S` is
read. The definition is total: a predicate with no accepting pattern has no accepting subcube and
gets the value `0` (empty `Finset.sup`). The paper defines `h` only for nontrivial predicates, and
every use in the mission (`InClass`, Lemma 2.2) assumes nontriviality, where an accepting pattern
is a subcube of dimension `0` and the value is the paper's maximum. -/
def subcubeDim {k : ℕ} (P : (Fin k → Bool) → Bool) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin k) × (Fin k → Bool))).filter
    (fun p => AcceptsSubcube P p.1 p.2)).sup (fun p => k - p.1.card)

/-- `P` is nontrivial: it accepts some pattern and rejects some pattern (p.2, p.3). -/
def PredNontrivial {k : ℕ} (P : (Fin k → Bool) → Bool) : Prop :=
  (∃ y, P y = true) ∧ ∃ y, P y = false

/-- **Pinning property `P_t`** (Definition 2.1, p.10): "a predicate P on scope E has property P_t
if ∀S ∈ (E choose t) ∀a ∈ {0,1}^S ∃z ∈ {0,1}^{E∖S} : P(a, z) = 0."

**Formalization Note.** `a ∈ {0,1}^S` is a full vector of which only `a_S` is read; the rejected
completion is the pattern `y` agreeing with `a` on `S`. -/
def HasPt {k : ℕ} (t : ℕ) (P : (Fin k → Bool) → Bool) : Prop :=
  ∀ S : Finset (Fin k), S.card = t → ∀ a : Fin k → Bool,
    ∃ y : Fin k → Bool, (∀ i ∈ S, y i = a i) ∧ P y = false

/-- An instance has `P_t` when every predicate does (Definition 2.1, p.10). -/
def InstPt (t : ℕ) (I : GInst) : Prop :=
  ∀ c ∈ I.cons, HasPt t (consPred c)

/-- **The class `𝒞_{k,h}`** (§1.2, p.3): "the class of complete Boolean k-CSPs in which every
predicate has accepting-subcube dimension at most h".

**Formalization Note.** Complete (`GInst.IsComplete k`), every predicate nontrivial (p.2, p.9), and
`h(P_E) ≤ h` for every constraint. -/
def InClass (k h : ℕ) (I : GInst) : Prop :=
  I.IsComplete k ∧ I.Nontrivial ∧ ∀ c ∈ I.cons, subcubeDim (consPred c) ≤ h

end AcceptSubcube


