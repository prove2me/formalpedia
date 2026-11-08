-- Prove2me | Definitions.Def_NNPartTree_GreedyTree
-- name    : NNPartTree_GreedyTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:40.932202+00:00
-- url     : https://prove2.me/theorems/c7382eb1-09dc-46d9-8e80-ac3a0b8a90e3
-- title:
--   The balanced cut oracle (corrected), TestMass, and runs of GreedyTree
-- statement:
--   An oracle $O$ maps a law on pairs to a function $\mathbb R^d\to\mathbb R$. It is a **$(\beta_1,\beta_0,R,J,\varepsilon_c)$-balanced cut oracle** with constant $C_O$ if on every probability law $\mathcal D'$:
--
--   1. $O(\mathcal D')$ is a cut;
--   2. if some $(R,J)$-halfspace function has balance at least $\beta_0$, then $\mathrm{bal}_{\mathcal D'}(O(\mathcal D'))\ge\beta_1$;
--   3. for every $(R,J)$-halfspace function $h$ with $\mathrm{bal}_{\mathcal D'}(h)\ge\beta_0$, $\mathrm{err}_{\mathcal D'}(O(\mathcal D'))\le C_O\sqrt{\mathrm{err}_{\mathcal D'}(h)}+\varepsilon_c$.
--
--   **TestMass** on $m$ samples outputs Large if the empirical fraction in the region exceeds $1.5\gamma$, otherwise Small. A **run of GreedyTree** on independent sample blocks $\omega_u$, one per address, is a tree in which at each node $u$: Small makes $u$ a leaf, and Large makes $u$ internal with the cut $O(\mathcal D^{(R_T(u))})$. A run exists exactly when GreedyTree terminates, and on a fixed $\omega$ it is unique.
--
--   **Formalization Note** Condition 2 corrects Definition 6.5, whose first bullet asks for balance $\beta_1$ on every $\mathcal D'$. When the second marginal of $\mathcal D'$ is a point mass every function has balance $0$, so no oracle would exist. As printed the oracle is a function of the distribution, with no failure probability. Blocks indexed by address have the law of fresh samples per call, since each address is tested at most once.
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Definition 6.5, p.23; TestMass, Lemma 6.2, pp.24, 47–48; GreedyTree, p.24

import Mathlib
import Definitions.Def_NNPartTree_CutTree

open MeasureTheory

namespace NNPartTree

/-!
# The balanced cut oracle, TestMass and runs of GreedyTree

S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*,
arXiv:2607.09909 (STOC 2027 submission), held copy of 2026-11-03, sha256 d32992f2…,
Definition 6.5 (p.23), the algorithm GreedyTree (p.24), TestMass (Lemma 6.2, p.24; proof pp.47–48).

**Formalization Note.**
* **Correction of Definition 6.5.** Its first bullet asks `bal_{D′}(g) ≥ β₁` on every `D′`. When the second
  marginal of `D′` is a point mass every `g` has balance `0`, so no oracle would exist and Claim 6.3 and
  Lemma 6.4 would be vacuous. `IsBalancedCutOracle` asks for the balance on the `D′` that have an
  `(R, J)`-halfspace function of balance at least `β₀`. This is what Theorem 3 can deliver.
* As printed, the oracle is a function of the distribution, with no failure probability.
* The randomness of TestMass is one independent block of `m` samples of `D_nn` per address. Each address
  is tested at most once, so this has the same law as fresh samples per call.
* A run is defined as a tree satisfying the recursion. It exists exactly when GreedyTree terminates,
  and it is unique for a fixed `ω`.
-/

variable {d : ℕ}

/-- `O` is a `(β₁, β₀, R, J, ε_c)`-balanced cut oracle (Definition 6.5, p.23, corrected), `C_O` being the
constant of its `O(·)`. On a probability law `D′` it returns a cut; if some `(R, J)`-halfspace function has
balance at least `β₀` under `D′` then the cut has balance at least `β₁`; and for every such function `h`,
`err_{D′}(g) ≤ C_O √(err_{D′}(h)) + ε_c`. -/
structure IsBalancedCutOracle (O : Measure (Pt d × Pt d) → Pt d → ℝ) (β₁ β₀ : ℝ) (R J : ℕ)
    (ε_c C_O : ℝ) : Prop where
  cut : ∀ (D' : Measure (Pt d × Pt d)) [IsProbabilityMeasure D'], IsCut (O D')
  balance : ∀ (D' : Measure (Pt d × Pt d)) [IsProbabilityMeasure D'],
    (∃ h : Pt d → ℝ, IsRJFunction R J h ∧ β₀ ≤ bal D' h) → β₁ ≤ bal D' (O D')
  error : ∀ (D' : Measure (Pt d × Pt d)) [IsProbabilityMeasure D'] (h : Pt d → ℝ),
    IsRJFunction R J h → β₀ ≤ bal D' h → err D' (O D') ≤ C_O * Real.sqrt (err D' h) + ε_c

open Classical in
/-- The empirical fraction of the samples `s` that lie in `W`: `μ̂` of TestMass (p.48). -/
noncomputable def empiricalFraction {m : ℕ} (W : Set (Pt d)) (s : Fin m → Pt d) : ℝ :=
  ((Finset.univ.filter fun i => s i ∈ W).card : ℝ) / m

/-- TestMass outputs Large on the samples `s` iff `μ̂ > 1.5 γ` (p.48); otherwise it outputs Small. -/
def TestLarge {m : ℕ} (γ : ℝ) (W : Set (Pt d)) (s : Fin m → Pt d) : Prop :=
  1.5 * γ < empiricalFraction W s

/-- A run of GreedyTree (p.24) on the sample blocks `ω`: a tree `T` such that at each of its nodes `u`,
if the test on the block of `u` says Small then `u` is a leaf, and if it says Large then `u` is internal
with the cut `O(D^{(u)})`. -/
def IsGreedyRun (O : Measure (Pt d × Pt d) → Pt d → ℝ) (D : Measure (Pt d × Pt d)) (γ : ℝ) {m : ℕ}
    (ω : List Bool → Fin m → Pt d) (T : CutTree d) : Prop :=
  ∀ u, T.IsNode u →
    (TestLarge γ (T.region u) (ω u) → T.IsInternal u (O (condMix D (T.region u)))) ∧
    (¬ TestLarge γ (T.region u) (ω u) → T.IsLeaf u)

/-- The tests on the nodes of `T` satisfy the guarantees of Lemma 6.2: mass at most `γ` gives Small and
mass at least `2γ` gives Large. -/
def TestsCorrect (D : Measure (Pt d × Pt d)) (γ : ℝ) {m : ℕ}
    (ω : List Bool → Fin m → Pt d) (T : CutTree d) : Prop :=
  ∀ u, T.IsNode u →
    (marginalY D (T.region u) ≤ ENNReal.ofReal γ → ¬ TestLarge γ (T.region u) (ω u)) ∧
    (ENNReal.ofReal (2 * γ) ≤ marginalY D (T.region u) → TestLarge γ (T.region u) (ω u))

/-- The law of the sample blocks: for each address an independent block of `m` samples of `D_nn`. -/
noncomputable def blockLaw (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D] (m : ℕ) :
    Measure (List Bool → Fin m → Pt d) :=
  Measure.infinitePi fun _ => Measure.pi fun _ => marginalY D

end NNPartTree


