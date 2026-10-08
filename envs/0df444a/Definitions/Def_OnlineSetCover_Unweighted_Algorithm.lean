-- Prove2me | Definitions.Def_OnlineSetCover_Unweighted_Algorithm
-- name    : OnlineSetCover_Unweighted_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:46:57.429349+00:00
-- url     : https://prove2.me/theorems/ba836c7c-ea28-457f-9acb-d9f1e8f326c1
-- title:
--   The unweighted online set-cover algorithm of Alon et al.: weights, potential $\Phi=\sum_{j\notin C} n^{2w_j}$, iterations and runs (Section 2)
-- statement:
--   This file defines the deterministic online algorithm for **unweighted online set cover** of Section 2 of Alon, Awerbuch, Azar, Buchbinder and Naor (2009), as a relation on its states.
--
--   Fix a set-cover instance: a finite ground set $X$ of $n$ elements, a finite family $\mathcal S$ of $m$ sets, and for every element $j$ the collection $\mathcal S_j\subseteq\mathcal S$ of sets containing $j$. The instance is known to the algorithm in advance; elements of $X$ arrive one at a time. All sets have unit cost (the cost field of the instance is not used).
--
--   1. **State.** A state consists of a weight $w_S\in\mathbb R$ for every set $S\in\mathcal S$ and the current cover $\mathcal C\subseteq\mathcal S$. The weight of an element is $w_j=\sum_{S\in\mathcal S_j}w_S$, and $C$ denotes the set of elements covered by members of $\mathcal C$.
--   2. **Initial state.** $w_S=1/(2m)$ for every $S$, and $\mathcal C=\emptyset$.
--   3. **Potential.**
--   $$\Phi(w,\mathcal C)=\sum_{j\notin C} n^{2w_j}.$$
--   4. **Augmentation exponent.** For $x<1$, $k$ is the minimal integer with $2^k x>1$; it is a positive integer when $0<x<1$.
--   5. **One iteration**, when the adversary gives element $j$:
--      - if $w_j\ge1$, the state is unchanged (no weight augmentation);
--      - otherwise ($w_j<1$) a **weight augmentation** is performed: with $k$ the minimal integer such that $2^k w_j>1$, every $S\in\mathcal S_j$ gets the weight $2^k w_S$ (the other weights are unchanged), and a family $F\subseteq\mathcal S_j$ with $|F|\le\lceil 4\ln n\rceil$ is added to the cover, subject to the condition that the potential after the iteration (new weights, cover $\mathcal C\cup F$) does not exceed the potential before it.
--   6. **Runs.** A run on an arrival list $\sigma=(j_1,\dots,j_T)$ is a sequence of iterations starting from the initial state, one for each arriving element in order; it records its final state and the number of iterations in which a weight augmentation was performed.
--
--   The paper leaves the choice of $F$ in step 2(c) open (Lemma 2.2 shows that an admissible choice exists, and its proof describes one by derandomizing a random experiment). The algorithm is therefore modelled as a relation: every admissible choice gives an iteration, and a theorem about "the algorithm" must hold for every run.
--
--   **Formalization Note** The instance is the published `SetCoverInstance` (elements `E`, set indices `T`, incidence `elemSets`), with element weight `elementWeight` and covering predicate `coveredBy`. $n=|E|$, $m=|T|$, and $n^{2w_j}$ is the real power `Real.rpow`. The paper's "$4\log n$" is read with the natural logarithm and rounded up, `⌈4 * Real.log n⌉₊`, because its proof repeats a random choice $4\log n$ times and needs $(1-\delta/2)^{4\log n}\le n^{-2\delta}$. The exponent $k$ ranges over natural numbers; for $w_j<1$ the minimal integer with $2^k w_j>1$ is a natural number, so nothing is lost. Arrival lists may repeat elements.
-- source:
--   Alon, Awerbuch, Azar, Buchbinder, Naor, The Online Set Cover Problem, SIAM J. Comput. 39(2) (2009), p. 363, Section 2 (algorithm, potential Φ, steps 1, 2(a)–(c)); model pp. 361–362

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy

namespace OnlineSetCover.Unweighted

open OnlinePrimalDual.OnlineSetCover

/-- The state of the unweighted algorithm of Alon et al. (2009, §2, p. 363): the current weight
`w S` of every set `S` and the current cover `𝒞` (a finite family of set indices). -/
structure State (T : Type*) where
  /-- the weight `w_S` of each set -/
  w : T → ℝ
  /-- the family `𝒞` of sets chosen so far -/
  cover : Finset T

/-- The initial state (p. 363): `w_S = 1/(2m)` for every set `S`, where `m = |T|` is the number
of sets, and the empty cover `𝒞 = ∅`. -/
noncomputable def initState (T : Type*) [Fintype T] : State T where
  w := fun _ => 1 / (2 * (Fintype.card T : ℝ))
  cover := ∅

open Classical in
/-- The potential `Φ = ∑_{j ∉ C} n^{2 w_j}` (p. 363), where `n = |E|` is the number of
elements, `C` is the set of elements covered by the family `cover`, and `w_j = ∑_{S ∋ j} w_S`
is the element weight. -/
noncomputable def potential {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (w : T → ℝ) (cover : Finset T) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => ¬ coveredBy inst cover j),
    (Fintype.card E : ℝ) ^ (2 * elementWeight inst w j)

/-- Step 2(a) (p. 363): `k` is the minimal integer with `2^k · x > 1`. It is a natural number
whenever `x < 1` (the only case in which the algorithm uses it), since then `2^k · x ≤ x < 1`
for every integer `k ≤ 0`. -/
def IsAugExponent (x : ℝ) (k : ℕ) : Prop :=
  1 < (2 : ℝ) ^ k * x ∧ ∀ k' : ℕ, k' < k → (2 : ℝ) ^ k' * x ≤ 1

/-- Step 2(b) (p. 363): every set `S ∈ 𝒮_j` (a set containing the arriving element `j`) has
its weight multiplied by `2^k`; the other weights are unchanged. -/
def augment {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (w : T → ℝ) (j : E) (k : ℕ) : T → ℝ :=
  fun S => if S ∈ inst.elemSets j then (2 : ℝ) ^ k * w S else w S

/-- The bound "`4 log n`" on the number of sets added in step 2(c) (p. 363), with the natural
logarithm, rounded up to an integer: `⌈4 ln n⌉`. -/
noncomputable def setCap (n : ℕ) : ℕ := ⌈4 * Real.log n⌉₊

/-- One iteration of the algorithm (p. 363) when the adversary gives element `j`, taking state
`s` to state `s'`; the flag `aug` records whether a weight augmentation is performed.
1. If `w_j ≥ 1`, nothing changes.
2. Otherwise (`w_j < 1`): with `k` the minimal integer such that `2^k w_j > 1`, multiply the
   weight of every set containing `j` by `2^k`, and add to the cover a family `F` of at most
   `⌈4 ln n⌉` sets containing `j`, chosen so that the potential after the iteration does not
   exceed the potential before it. The choice of `F` is not determined by the paper, so this is
   a relation: every admissible choice is a step. -/
inductive Step {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) : State T → E → State T → Bool → Prop
  | noAug (s : State T) (j : E) (h : 1 ≤ elementWeight inst s.w j) :
      Step inst s j s false
  | aug (s : State T) (j : E) (k : ℕ) (F : Finset T)
      (hlt : elementWeight inst s.w j < 1)
      (hk : IsAugExponent (elementWeight inst s.w j) k)
      (hF : F ⊆ inst.elemSets j)
      (hcard : F.card ≤ setCap (Fintype.card E))
      (hΦ : potential inst (augment inst s.w j k) (s.cover ∪ F) ≤ potential inst s.w s.cover) :
      Step inst s j ⟨augment inst s.w j k, s.cover ∪ F⟩ true

/-- `RunFrom inst s σ s' a`: processing the arrival list `σ` (in order) from state `s`, one
`Step` per arrival, the algorithm can end in state `s'` having performed exactly `a` weight
augmentations. -/
inductive RunFrom {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) : State T → List E → State T → ℕ → Prop
  | nil (s : State T) : RunFrom inst s [] s 0
  | cons {s s' s'' : State T} {j : E} {σ : List E} {b : Bool} {a : ℕ} :
      Step inst s j s' b → RunFrom inst s' σ s'' a →
      RunFrom inst s (j :: σ) s'' ((if b then 1 else 0) + a)

/-- `Run inst σ s a`: a run of the algorithm from its initial state on the arrival list `σ`
ends in state `s` after exactly `a` weight augmentations. -/
def Run {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (σ : List E) (s : State T) (a : ℕ) : Prop :=
  RunFrom inst (initState T) σ s a

end OnlineSetCover.Unweighted


