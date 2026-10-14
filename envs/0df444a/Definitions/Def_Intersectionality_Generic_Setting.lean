-- Prove2me | Definitions.Def_Intersectionality_Generic_Setting
-- name    : Intersectionality_Generic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:25:34.903601+00:00
-- url     : https://prove2.me/theorems/dea8ff6a-ebc4-46d4-82dc-9f9a35b4a4cb
-- title:
--   pp. 7–10, 22 — scores, identities, the space P of distributions, rich commutative policy families, thresholds, capacity, nonintersectional and representative outcomes
-- statement:
--   This file fixes the model of Carvalho, Pradelski and Williams (§2).
--
--   **Scores and identities.** Every applicant has a score $x$ in an interval $X \subset \mathbb{R}$ and an identity $g = (g_1,\dots,g_n) \in G = \{0,1\}^n$. Category $i$ is the set of identities with $g_i = 1$. The identity $g$ is the sum $g' + g''$ of two identities when $g_i = g'_i + g''_i$ for every $i$, as integer vectors. $\mathbf 0$ and $\mathbf 1$ are the vectors of zeros and of ones, and $e_i$ is the $i$-th standard basis vector.
--
--   **Distributions.** A distribution is a Borel probability measure $p$ on $X \times G$. Here $X$ carries the topology it inherits from $\mathbb{R}$ and $G$ is discrete. The space of probability measures carries the topology of weak convergence, the paper's weak$^*$ topology. The marginal mass of a group is $p(g) = p(X \times \{g\})$. The space $P$ consists of those $p$ for which every group $g$ with $p(g) > 0$ has a continuous conditional score law with full support on $X$:
--
--   $$p(\{y\} \times \{g\}) = 0 \ \text{ for every } y \in X, \qquad p\big((a,b) \times \{g\}\big) > 0 \ \text{ for all } a < b \text{ in } X.$$
--
--   $P$ carries the relative topology.
--
--   **Policies.** A family $Q$ of maps $X \to X$ is a *rich and commutative family of increasing bijections* when three conditions hold:
--   1. each $q \in Q$ is a strictly increasing bijection of $X$;
--   2. for all $x, y \in X$ some $q \in Q$ has $q(x) = y$;
--   3. $q \circ q' = q' \circ q$ for all $q, q' \in Q$.
--
--   A policy is a family $q = (q_g)_{g \in G}$ of maps $X \to X$. Given a threshold $x^* \in X$, applicants with $q_g(x) \ge x^*$ are accepted. The accepted mass of group $g$ is $A_g = p(\{(x,g) : q_g(x) \ge x^*\}) = \Pr(q_g(x) \ge x^* \mid g)\,p(g)$, and the capacity constraint at level $\alpha$ is
--
--   $$\sum_{g \in G} A_g = \alpha .$$
--
--   The share of $g$ among the accepted is $\hat p(g) = A_g / \sum_{g'} A_{g'}$.
--
--   **Definition 1.** A policy is *nonintersectional* if $g = g' + g''$ implies $q_g = q_{g'} \circ q_{g''}$, and *intersectional* otherwise.
--
--   **Definition 2.** The outcome of $(q, x^*)$ is *representative* (at capacity $\alpha$) if the capacity constraint holds and $\hat p(g) = p(g)$ for all $g \in G$.
--
--   **Auxiliary objects for the proof of Theorem 1.** These are used only by the milestones:
--   - the conditional CDF $F_g(y) = p(\{(x,g) : x \le y\})/p(g)$;
--   - the quantile $\beta_g = F_g^{-1}(1-\alpha)$, a score $y$ with $F_g(y) = 1-\alpha$;
--   - the transport map, the element of $Q$ sending $x$ to $y$ (Lemma 1(b)).
--
--   These objects are the vocabulary of Theorem 1 and its supporting lemmas.
--
--   **Formalization Note.** Scores live in the subtype $\uparrow X$.
--   - Convention C1: groups with $p(g) = 0$ are unconstrained in $P$. The page is silent on them, and the paper's proofs use such $p$.
--   - "Increasing" is strict monotonicity; for a bijection the two readings coincide.
--   - Conditional probabilities are replaced by the joint masses $A_g$, which avoids division by $p(g)$.
--   - The quantile is chosen with `Classical.epsilon` and is junk when $p(g) = 0$.
--   - `transport` returns the identity when no element of $Q$ sends $x$ to $y$, which richness rules out.
--   - $\hat p$ uses Lean division, which gives $0$ when the denominator is $0$. Representativeness always comes with the capacity constraint, whose denominator is $\alpha > 0$.
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, pp. 7–10 (PDF 8–11), §2, Definitions 1–2, footnote 2; proof of Theorem 1, p. 10 (PDF 11); Lemma 1(b), p. 22 (PDF 23)

import Mathlib

namespace Intersectionality.Generic

open MeasureTheory

/-- Identities `g ∈ G = {0,1}ⁿ`, as Boolean vectors; category `i` is `{g | g i = true}` (p. 7). -/
abbrev Grp (n : ℕ) : Type := Fin n → Bool

/-- `g = g' + g''` as integer vectors with `0/1` entries (Definition 1, p. 8). -/
def IsGroupSum {n : ℕ} (g g' g'' : Grp n) : Prop :=
  ∀ i, (g i).toNat = (g' i).toNat + (g'' i).toNat

/-- The vector of zeros `𝟎`. -/
def zeroGrp (n : ℕ) : Grp n := fun _ => false

/-- The vector of ones `𝟏`. -/
def oneGrp (n : ℕ) : Grp n := fun _ => true

/-- The standard basis vector `eᵢ` (index base `0`: the paper's `e_{i+1}`). -/
def unitGrp {n : ℕ} (i : Fin n) : Grp n := fun j => decide (j = i)

/-- The sample space `X × G` of (score, identity) pairs; `↥X` carries the subspace topology, `G` is
discrete, and the space carries its Borel σ-algebra. -/
abbrev ScoreGrp (X : Set ℝ) (n : ℕ) : Type := ↥X × Grp n

/-- The marginal `p(g) = p(X × {g})`. -/
noncomputable def groupMass {X : Set ℝ} {n : ℕ} (p : ProbabilityMeasure (ScoreGrp X n))
    (g : Grp n) : ℝ :=
  (p : Measure (ScoreGrp X n)).real {z | z.2 = g}

/-- Membership in `P` (p. 7): for every group of positive mass, the conditional score law
`F_g = p(· | g)` is continuous (no atoms) and has full support on the interval `X` (every nonempty
open subinterval has positive mass). Groups with `p(g) = 0` are unconstrained (convention C1). -/
def InP {X : Set ℝ} {n : ℕ} (p : ProbabilityMeasure (ScoreGrp X n)) : Prop :=
  ∀ g : Grp n, 0 < groupMass p g →
    (∀ y : ↥X, (p : Measure (ScoreGrp X n)).real {z | z.1 = y ∧ z.2 = g} = 0) ∧
    (∀ a b : ↥X, a < b →
      0 < (p : Measure (ScoreGrp X n)).real {z | a < z.1 ∧ z.1 < b ∧ z.2 = g})

/-- The space `P ⊂ Δ(X × G)`, with the relative weak(-*) topology (p. 7, fn. 2). -/
abbrev DistSpace (X : Set ℝ) (n : ℕ) : Type :=
  {p : ProbabilityMeasure (ScoreGrp X n) // InP p}

/-- A rich and commutative family `Q ⊂ X^X` of increasing bijections (p. 8). -/
structure IsPolicyFamily {X : Set ℝ} (Q : Set (↥X → ↥X)) : Prop where
  strictMono : ∀ q ∈ Q, StrictMono q
  bijective : ∀ q ∈ Q, Function.Bijective q
  rich : ∀ x y : ↥X, ∃ q ∈ Q, q x = y
  comm : ∀ q ∈ Q, ∀ q' ∈ Q, q ∘ q' = q' ∘ q

/-- Accepted mass of group `g` under policy `q` and threshold `x*`:
`Pr(q_g(x) ≥ x* | g) p(g)` (p. 8). -/
noncomputable def accMass {X : Set ℝ} {n : ℕ} (p : ProbabilityMeasure (ScoreGrp X n))
    (q : Grp n → (↥X → ↥X)) (xs : ↥X) (g : Grp n) : ℝ :=
  (p : Measure (ScoreGrp X n)).real {z | z.2 = g ∧ xs ≤ q g z.1}

/-- The capacity constraint `∑_g Pr(q_g(x) ≥ x* | g) p(g) = α` (p. 8). -/
def SatisfiesCapacity {X : Set ℝ} {n : ℕ} (p : ProbabilityMeasure (ScoreGrp X n)) (α : ℝ)
    (q : Grp n → (↥X → ↥X)) (xs : ↥X) : Prop :=
  ∑ g, accMass p q xs g = α

/-- The share `p̂(g)` of group `g` among the accepted (p. 9). -/
noncomputable def share {X : Set ℝ} {n : ℕ} (p : ProbabilityMeasure (ScoreGrp X n))
    (q : Grp n → (↥X → ↥X)) (xs : ↥X) (g : Grp n) : ℝ :=
  accMass p q xs g / ∑ g', accMass p q xs g'

/-- Definition 1 (p. 8): `q` is nonintersectional if `g = g' + g''` implies `q_g = q_{g'} ∘ q_{g''}`;
otherwise it is intersectional. -/
def IsNonintersectional {X : Set ℝ} {n : ℕ} (q : Grp n → (↥X → ↥X)) : Prop :=
  ∀ g g' g'' : Grp n, IsGroupSum g g' g'' → q g = q g' ∘ q g''

/-- Definition 2 (p. 9), with the capacity constraint of p. 8: threshold `x*` meets capacity `α`
and `p̂(g) = p(g)` for all `g`. -/
def IsRepresentative {X : Set ℝ} {n : ℕ} (p : ProbabilityMeasure (ScoreGrp X n)) (α : ℝ)
    (q : Grp n → (↥X → ↥X)) (xs : ↥X) : Prop :=
  SatisfiesCapacity p α q xs ∧ ∀ g, share p q xs g = groupMass p g

/-- The conditional CDF `F_g(y) = p(score ≤ y | g)` (p. 10). Junk (`0`) when `p(g) = 0`. -/
noncomputable def condCDF {X : Set ℝ} {n : ℕ} (p : ProbabilityMeasure (ScoreGrp X n))
    (g : Grp n) (y : ↥X) : ℝ :=
  (p : Measure (ScoreGrp X n)).real {z | z.1 ≤ y ∧ z.2 = g} / groupMass p g

/-- The `(1 − α)`-th score quantile `β_g = F_g⁻¹(1 − α)` (p. 10): a score `y` with
`F_g(y) = 1 − α`. Meaningful only for `p ∈ P` with `p(g) > 0`, where that score is unique. -/
noncomputable def quantile {X : Set ℝ} [Nonempty ↥X] {n : ℕ}
    (p : ProbabilityMeasure (ScoreGrp X n)) (α : ℝ) (g : Grp n) : ↥X :=
  Classical.epsilon (fun y : ↥X => condCDF p g y = 1 - α)

open Classical in
/-- "The function mapping `x` to `y`" in `Q` (Lemma 1(b), p. 22); `id` if there is none. -/
noncomputable def transport {X : Set ℝ} (Q : Set (↥X → ↥X)) (x y : ↥X) : ↥X → ↥X :=
  if h : ∃ q ∈ Q, q x = y then Classical.choose h else id

end Intersectionality.Generic


