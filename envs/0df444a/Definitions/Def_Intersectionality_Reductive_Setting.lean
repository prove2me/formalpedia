-- Prove2me | Definitions.Def_Intersectionality_Reductive_Setting
-- name    : Intersectionality_Reductive_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:10.585155+00:00
-- url     : https://prove2.me/theorems/2c0c96a3-c999-4ecf-85b6-8972679fe26c
-- title:
--   pp. 7–9, 15, 24–25 — scores, identities, the space P, policy families, capacity, (reductive) representation, and the Appendix D parameterization
-- statement:
--   This file fixes the model of Carvalho, Pradelski and Williams (§2) together with the objects needed for Proposition 3 (Definition 7 and Appendix D).
--
--   **Applicants.** A decision maker accepts a share $\alpha \in (0,1)$ of a unit-mass applicant pool. Each applicant has a score $x$ in an interval $X \subset \mathbb{R}$ and an identity $g \in G = \{0,1\}^n$. All applicants with $g_i = 1$ form *category* $i$. Groups combine as integer vectors: $g = g' + g''$ means $g_i = g'_i + g''_i$ for every coordinate. Special groups are $\mathbf 0$, $\mathbf 1$ and the unit vectors $e_i$.
--
--   **Distributions.** The joint law $p$ of (score, identity) is a probability measure on $X \times G$. The space $P$ consists of those $p$ for which, for every group $g$ with $p(g) = p(X \times \{g\}) > 0$, the conditional score law $F_g = p(\cdot \mid g)$ has no atoms and gives positive mass to every nonempty open subinterval of $X$ (continuity and full support). $P$ carries the relative weak topology.
--
--   **Policies.** $Q$ is a family of maps $X \to X$ that are strictly increasing bijections, *rich* (for all $x, y \in X$ some $q \in Q$ has $q(x) = y$) and *commutative* ($q \circ q' = q' \circ q$). A policy assigns to each group $g$ a map $q_g$; together with a threshold $x^* \in X$ it accepts exactly the applicants with $q_g(x) \ge x^*$. Write
--   $$A_g = \Pr(q_g(x) \ge x^* \mid g)\, p(g)$$
--   for the accepted mass of group $g$. The *capacity constraint* is $\sum_g A_g = \alpha$, and the accepted share of $g$ is $\hat p(g) = A_g / \sum_{g'} A_{g'}$.
--
--   1. A policy is *nonintersectional* (Definition 1) if $g = g' + g''$ implies $q_g = q_{g'} \circ q_{g''}$.
--   2. The outcome of $(q, x^*)$ is *representative* (Definition 2) if the capacity constraint holds and $\hat p(g) = p(g)$ for all $g$.
--   3. With $p(g_i)$ the population share of category $i$ and $\hat p(g_i) = \sum_{g : g_i = 1} \hat p(g)$ its accepted share, the outcome is *reductive representative* (Definition 7) if the capacity constraint holds and $\hat p(g_i) = p(g_i)$ for every $i$.
--
--   **Appendix D objects.** Fix a base score $x_0 \in X$. Let $r(\cdot \mid \theta)$ be the map in $Q$ sending $x_0$ to $\theta$. For $\theta \in X^n$ and a group $g$, let
--   $$r_g(\cdot \mid \theta) = r(\cdot \mid \theta_1 g_1 + (1-g_1) x_0) \circ \cdots \circ r(\cdot \mid \theta_n g_n + (1-g_n) x_0),$$
--   where $\theta_i g_i + (1 - g_i) x_0$ means $\theta_i$ if $g_i = 1$ and $x_0$ otherwise. Under the policy $r_g(\cdot \mid \theta)$ and threshold $x^*$:
--
--   - $R_i(\theta, x^*)$ is the acceptance rate of category $i$, the accepted mass of category $i$ divided by $p(g_i)$;
--   - $S(\theta, x^*)$ is the total acceptance rate;
--   - $t(\theta)$ is a threshold with $S(\theta, t(\theta)) = \alpha$.
--
--   For $a, b \in X^n$, *condition (5)* says that for every $i$ and every $\theta_{-i} \in \times_{j \ne i} [a_j, b_j]$,
--   $$R_i(a_i, \theta_{-i}, t(a_i, \theta_{-i})) < \alpha < R_i(b_i, \theta_{-i}, t(b_i, \theta_{-i})).$$
--
--   These are the objects every statement of the mission is about: Proposition 3 uses the model and Definition 7, and the milestones use the Appendix D parameterization.
--
--   **Formalization Note.** Scores live in the subtype $\uparrow X$, identities are `Fin n → Bool` (0-based: the paper's dimension $i$ is index $i-1$), and $X \times G$ has the product topology and its Borel σ-algebra. $P$ is a subtype of `ProbabilityMeasure`, whose topology is the weak topology. A group with $p(g) = 0$ is unconstrained in $P$; the paper is silent there, and its proofs use such distributions. Accepted masses are measures of sets rather than conditional probabilities times $p(g)$, which is the same number and avoids dividing by $p(g)$. Both representation notions include the capacity constraint; without it they would only ask that all groups (categories) be accepted at a common rate. $r(\cdot \mid \theta)$ is a chosen element of $Q$ (unique by Lemma 1(b)), and $t(\theta)$ is a chosen solution of $S(\theta, \cdot) = \alpha$ (Hilbert's ε), meaningful when a solution exists. $R_i$ divides by $p(g_i)$ and is $0$ when $p(g_i) = 0$ (Lean's $x/0 = 0$).
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, pp. 7–9 (PDF 8–10), §2, Definitions 1–2; p. 15 (PDF 16), Definition 7; pp. 24–25 (PDF 25–26), Appendix D, display (5)

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting

namespace Intersectionality.Reductive

open MeasureTheory

/-- The type of applicants `X × G`: a score in the subtype `↥X` and an identity. It carries the
product topology (`↥X` with the subspace topology, `G` discrete) and its Borel σ-algebra. -/
abbrev Omega (X : Set ℝ) (n : ℕ) : Type := ↥X × Intersectionality.Generic.Grp n

noncomputable instance (X : Set ℝ) (n : ℕ) : TopologicalSpace (Intersectionality.Generic.DistSpace X n) :=
  inferInstanceAs (TopologicalSpace {p : ProbabilityMeasure (Omega X n) // Intersectionality.Generic.InP p})

/-- `p(gᵢ)`, the population share of category `i` (all `g` with `gᵢ = 1`). -/
noncomputable def catMass {X : Set ℝ} {n : ℕ} (p : ProbabilityMeasure (Omega X n)) (i : Fin n) : ℝ :=
  (p : Measure (Omega X n)).real {z | z.2 i = true}

/-- `p̂(gᵢ) = ∑_{g : gᵢ = 1} p̂(g)`, the share of category `i` among the accepted. -/
noncomputable def catShare {X : Set ℝ} {n : ℕ} (p : ProbabilityMeasure (Omega X n))
    (q : Intersectionality.Generic.Grp n → (↥X → ↥X)) (xs : ↥X) (i : Fin n) : ℝ :=
  ∑ g ∈ Finset.univ.filter (fun g : Intersectionality.Generic.Grp n => g i = true), Intersectionality.Generic.share p q xs g

/-- Definition 7 (p. 15), with the capacity constraint of p. 8: the outcome of `(q, x*)` is
reductive representative, `p̂(gᵢ) = p(gᵢ)` for each dimension `i`. -/
def IsReductiveRepresentative {X : Set ℝ} {n : ℕ} (p : ProbabilityMeasure (Omega X n)) (α : ℝ)
    (q : Intersectionality.Generic.Grp n → (↥X → ↥X)) (xs : ↥X) : Prop :=
  Intersectionality.Generic.SatisfiesCapacity p α q xs ∧ ∀ i, catShare p q xs i = catMass p i

/-- `r(· | θ)` (Appendix D, p. 24): the function `q ∈ Q` with `q(x₀) = θ`. -/
noncomputable def param {X : Set ℝ} (Q : Set (↥X → ↥X)) (x0 θ : ↥X) : ↥X → ↥X :=
  Intersectionality.Generic.transport Q x0 θ

/-- `r_g(· | θ) = r(· | θ₁g₁ + (1 - g₁)x₀) ∘ ⋯ ∘ r(· | θₙgₙ + (1 - gₙ)x₀)` (Appendix D, p. 24):
the nonintersectional policy determined by `θ ∈ Xⁿ`. -/
noncomputable def grpMap {X : Set ℝ} {n : ℕ} (Q : Set (↥X → ↥X)) (x0 : ↥X) (θ : Fin n → ↥X)
    (g : Intersectionality.Generic.Grp n) : ↥X → ↥X :=
  (List.finRange n).foldr (fun i f => param Q x0 (if g i then θ i else x0) ∘ f) id

/-- `Rᵢ(θ, x*) = ∑_g (1 - F_g(r_g⁻¹(x* | θ))) p(g | gᵢ = 1)` (Appendix D, p. 24): the acceptance
rate of category `i` under the policy `r(· | θ)` and the threshold `xs`. -/
noncomputable def catRate {X : Set ℝ} {n : ℕ} (p : ProbabilityMeasure (Omega X n))
    (Q : Set (↥X → ↥X)) (x0 : ↥X) (θ : Fin n → ↥X) (xs : ↥X) (i : Fin n) : ℝ :=
  (∑ g ∈ Finset.univ.filter (fun g : Intersectionality.Generic.Grp n => g i = true), Intersectionality.Generic.accMass p (grpMap Q x0 θ) xs g) /
    catMass p i

/-- `S(θ, x*) = ∑_g (1 - F_g(r_g⁻¹(x* | θ))) p(g)` (Appendix D, p. 24): the total acceptance rate. -/
noncomputable def totalRate {X : Set ℝ} {n : ℕ} (p : ProbabilityMeasure (Omega X n))
    (Q : Set (↥X → ↥X)) (x0 : ↥X) (θ : Fin n → ↥X) (xs : ↥X) : ℝ :=
  ∑ g, Intersectionality.Generic.accMass p (grpMap Q x0 θ) xs g

/-- `t(θ)` (Appendix D, p. 25): a threshold with `S(θ, t(θ)) = α` (chosen; unique for `p ∈ P`). -/
noncomputable def thr {X : Set ℝ} [Nonempty ↥X] {n : ℕ} (p : ProbabilityMeasure (Omega X n))
    (Q : Set (↥X → ↥X)) (x0 : ↥X) (α : ℝ) (θ : Fin n → ↥X) : ↥X :=
  Classical.epsilon (fun xs : ↥X => totalRate p Q x0 θ xs = α)

/-- Condition (5) (Appendix D, p. 25): for every `i` and every `θ₋ᵢ ∈ ×_{j ≠ i} [aⱼ, bⱼ]`,
`Rᵢ(aᵢ, θ₋ᵢ, t(aᵢ, θ₋ᵢ)) < α < Rᵢ(bᵢ, θ₋ᵢ, t(bᵢ, θ₋ᵢ))`. -/
def Cond5 {X : Set ℝ} [Nonempty ↥X] {n : ℕ} (p : ProbabilityMeasure (Omega X n))
    (Q : Set (↥X → ↥X)) (x0 : ↥X) (α : ℝ) (a b : Fin n → ↥X) : Prop :=
  ∀ i : Fin n, ∀ θ : Fin n → ↥X, (∀ j, j ≠ i → a j ≤ θ j ∧ θ j ≤ b j) →
    catRate p Q x0 (Function.update θ i (a i)) (thr p Q x0 α (Function.update θ i (a i))) i < α ∧
    α < catRate p Q x0 (Function.update θ i (b i)) (thr p Q x0 α (Function.update θ i (b i))) i

end Intersectionality.Reductive


