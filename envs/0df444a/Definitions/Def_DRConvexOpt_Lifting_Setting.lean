-- Prove2me | Definitions.Def_DRConvexOpt_Lifting_Setting
-- name    : DRConvexOpt_Lifting_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:30:51.361983+00:00
-- url     : https://prove2.me/theorems/c86aedfe-7455-4205-9039-68518e30a9ed
-- title:
--   Theorem 5 and Notation, pp. 7, 15 — proper cones, the moment set 𝒫′, the lifted set 𝒫 and the marginal operator Π_z̃
-- statement:
--   This file fixes the objects of the Lifting Theorem of Wiesemann, Kuhn and Sim.
--
--   1. **Proper cone.** A set $\mathcal K \subseteq \mathbb R^M$ is a *proper cone* if it is a closed convex cone (it contains $0$, is closed under addition and under multiplication by nonnegative scalars) that is pointed ($x \in \mathcal K$ and $-x \in \mathcal K$ imply $x = 0$) and has nonempty interior. For $x, y \in \mathbb R^M$ one writes $x \preccurlyeq_{\mathcal K} y$ when $y - x \in \mathcal K$.
--
--   2. **The moment set.** Let $g : \mathbb R^P \to \mathbb R^M$, $f \in \mathbb R^M$, a proper cone $\mathcal K \subseteq \mathbb R^M$, sets $\mathcal C_i \subseteq \mathbb R^P$ and bounds $\underline p_i, \overline p_i$ for $i \in \mathcal I$. The set $\mathcal P'$ consists of the probability distributions $\mathbb Q$ on $\mathbb R^P$ such that $g(\tilde z)$ has a finite expectation under $\mathbb Q$ and
--   $$
--   \mathbb E_{\mathbb Q}[g(\tilde z)] \preccurlyeq_{\mathcal K} f, \qquad \mathbb Q[\tilde z \in \mathcal C_i] \in [\underline p_i, \overline p_i] \quad \forall i \in \mathcal I.
--   $$
--
--   3. **The lifted set.** With an auxiliary random vector $\tilde u \in \mathbb R^M$, the set $\mathcal P$ consists of the probability distributions $\mathbb P$ on $\mathbb R^P \times \mathbb R^M$ under which $\tilde u$ and $g(\tilde z)$ have finite expectations and
--   $$
--   \mathbb E_{\mathbb P}[\tilde u] = f, \qquad \mathbb P[g(\tilde z) \preccurlyeq_{\mathcal K} \tilde u] = 1, \qquad \mathbb P[\tilde z \in \mathcal C_i] \in [\underline p_i, \overline p_i] \quad \forall i \in \mathcal I.
--   $$
--
--   4. **Marginals.** For a set $\mathcal S$ of distributions on a product space, $\Pi_{\tilde z}\mathcal S = \bigcup_{\mathbb P \in \mathcal S} \{\Pi_{\tilde z}\mathbb P\}$ is the set of the first-coordinate marginals of its members.
--
--   These are the two ambiguity sets compared by the Lifting Theorem, which shows that the lifted set describes exactly the distributions satisfying a conic bound on $\mathbb E[g(\tilde z)]$.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`; the index set $\mathcal I$ is `Fin nI` (0-based). Probabilities of events are `μ.real`. The integrability of $g(\tilde z)$ in both sets reads "the expectation exists": Lean's integral of a non-integrable map is $0$, so without these clauses the moment set would contain every distribution with $f \in \mathcal K$ whose $g(\tilde z)$ has no expectation. The integrability of $g(\tilde z)$ in the lifted set is an addition to the page, needed for the theorem (see Theorem 5 (i)). The event $\{g(\tilde z) \preccurlyeq_{\mathcal K} \tilde u\}$ is written $\{\omega : \omega_2 - g(\omega_1) \in \mathcal K\}$.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 7, Notation (proper cone, ≼_K, Π_z̃); p. 15, Theorem 5 (the sets 𝒫′ and 𝒫)

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting

namespace DRConvexOpt.Lifting

open MeasureTheory

/-- Theorem 5, p. 15: the ambiguity set 𝒫′ of probability distributions ν of z̃ ∈ ℝ^P with
E_ν[g(z̃)] ≼_K f (the expectation exists, and f − E_ν[g(z̃)] ∈ K) and ν[z̃ ∈ C_i] ∈ [p̲_i, p̄_i]
for every i. -/
def momentSet {nP nM nI : ℕ} (g : (Fin nP → ℝ) → (Fin nM → ℝ)) (f : Fin nM → ℝ)
    (K : Set (Fin nM → ℝ)) (C : Fin nI → Set (Fin nP → ℝ)) (plo phi : Fin nI → ℝ) :
    Set (Measure (Fin nP → ℝ)) :=
  {ν | IsProbabilityMeasure ν ∧ Integrable g ν ∧ f - ∫ z, g z ∂ν ∈ K ∧
       ∀ i, ν.real (C i) ∈ Set.Icc (plo i) (phi i)}

/-- Theorem 5, p. 15: the lifted ambiguity set 𝒫 of joint distributions μ of (z̃, ũ) ∈ ℝ^P × ℝ^M
with E_μ[ũ] = f, μ[g(z̃) ≼_K ũ] = 1 and μ[z̃ ∈ C_i] ∈ [p̲_i, p̄_i] for every i. The clause that
g(z̃) is μ-integrable is the disclosed addition of the mission (see the theorems). -/
def liftedSet {nP nM nI : ℕ} (g : (Fin nP → ℝ) → (Fin nM → ℝ)) (f : Fin nM → ℝ)
    (K : Set (Fin nM → ℝ)) (C : Fin nI → Set (Fin nP → ℝ)) (plo phi : Fin nI → ℝ) :
    Set (Measure ((Fin nP → ℝ) × (Fin nM → ℝ))) :=
  {μ | IsProbabilityMeasure μ ∧ Integrable (fun ω => ω.2) μ ∧ Integrable (fun ω => g ω.1) μ ∧
       ∫ ω, ω.2 ∂μ = f ∧ μ {ω | ω.2 - g ω.1 ∈ K} = 1 ∧
       ∀ i, μ.real (Prod.fst ⁻¹' C i) ∈ Set.Icc (plo i) (phi i)}

/-- Notation, p. 7: Π_z̃𝒫 = ⋃_{μ ∈ 𝒫} {Π_z̃ μ}, the set of first-coordinate marginals of the
members of an ambiguity set S of joint distributions. -/
def marginal {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (S : Set (Measure (α × β))) : Set (Measure α) :=
  (fun μ => μ.map Prod.fst) '' S

end DRConvexOpt.Lifting


