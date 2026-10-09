-- Prove2me | Definitions.Def_LinearMDPRL_Linear_LinearMDP
-- name    : LinearMDPRL_Linear_LinearMDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:57.298893+00:00
-- url     : https://prove2.me/theorems/fa09da37-4755-46c3-b103-1ed907bc3b9b
-- title:
--   Assumption A, p. 5 — linear MDP with feature map φ, signed measures µ_h and vectors θ_h; ‖φ‖ ≤ 1, ‖θ_h‖ ≤ √d, total-variation normalization of µ_h
-- statement:
--   This is **Assumption A** (linear MDP, p. 5), with the normalization of the measures stated through their total variations.
--
--   An episodic MDP of horizon $H$ is a **linear MDP** with feature map $\phi:\mathcal S\times\mathcal A\to\mathbb R^d$ if $\|\phi(x,a)\|\le1$ for all $(x,a)$, each $\phi(\cdot,a)$ is measurable, and for every step $h\in[H]$ there exist $d$ finite signed measures $\boldsymbol\mu_h=(\mu_h^{(1)},\dots,\mu_h^{(d)})$ on $\mathcal S$ and a vector $\theta_h\in\mathbb R^d$ such that for all $(x,a)$ and all measurable $B\subseteq\mathcal S$
--   $$
--   \mathbb P_h(B\mid x,a)=\langle\phi(x,a),\boldsymbol\mu_h(B)\rangle=\sum_{i=1}^d\phi_i(x,a)\,\mu_h^{(i)}(B),\qquad r_h(x,a)=\langle\phi(x,a),\theta_h\rangle,
--   $$
--   and
--   $$
--   \|\theta_h\|\le\sqrt d,\qquad \big\|\big(|\mu_h^{(1)}|(\mathcal S),\dots,|\mu_h^{(d)}|(\mathcal S)\big)\big\|\le\sqrt d,
--   $$
--   where $|\mu|$ denotes the total variation measure of a signed measure $\mu$.
--
--   Under this assumption every action-value function is linear in $\phi$ (Proposition 2.3), which is what makes least-squares value iteration with $d$-dimensional features consistent.
--
--   **Formalization Note.** The paper normalizes the net masses, $\|\boldsymbol\mu_h(\mathcal S)\|\le\sqrt d$. That condition does not bound $\int V\,d\boldsymbol\mu_h$ for $0\le V\le H$, and under it Lemma B.1 is false (for $d=2$, $\mathcal S=\{1,2\}$, $\mu^{(1)}=\sqrt2(\tfrac12,\tfrac12)$, $\mu^{(2)}=M(\delta_1-\delta_2)$ and two features $(1/\sqrt2,t)$, $|t|\le 1/(2M)$, the unique weight has second coordinate $M(V(1)-V(2))$, unbounded in $M$). The total-variation form implies the printed one, makes Lemma B.1's proof valid, and is met with equality by the tabular Example 2.1. Measurability of $\phi(\cdot,a)$ is implicit in the paper (the features enter integrals through $V^\pi$).
-- source:
--   Jin, Yang, Wang, Jordan, arXiv:1907.05388v2, Assumption A, p. 5, equation (3); normalization strengthened to total variation (see Formalization Note)

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model

namespace LinearMDPRL.Linear

open MeasureTheory ProbabilityTheory

/-- Assumption A (linear MDP, p. 5), with the normalization of the signed measures stated through
their total variations. `M` is a linear MDP of horizon `H` with feature map
`φ : S × A → ℝ^d` if `‖φ(x, a)‖ ≤ 1`, each `φ(·, a)` is measurable, and for every step
`h ∈ [H]` there are `d` signed measures `µ_h = (µ_h^{(1)}, …, µ_h^{(d)})` on `S` and a vector
`θ_h ∈ ℝ^d` with

* `P_h(B | x, a) = ⟨φ(x, a), µ_h(B)⟩ = Σ_i φ_i(x, a) µ_h^{(i)}(B)` for every measurable `B`;
* `r_h(x, a) = ⟨φ(x, a), θ_h⟩`;
* `‖θ_h‖ ≤ √d` and `‖(|µ_h^{(1)}|(S), …, |µ_h^{(d)}|(S))‖ ≤ √d`, where `|µ|` is the total
  variation measure of `µ`. -/
def IsLinearMDP {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : EpisodicMDP S A)
    (H d : ℕ) (φ : S → A → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ x a, ‖φ x a‖ ≤ 1) ∧
  (∀ a, Measurable (fun x => φ x a)) ∧
  ∀ h ∈ Finset.Icc 1 H, ∃ (mu : Fin d → SignedMeasure S) (θ : EuclideanSpace ℝ (Fin d)),
    (∀ x a (B : Set S), MeasurableSet B →
        (M.P h (x, a) B).toReal = ∑ i, φ x a i * mu i B) ∧
    (∀ x a, M.r h x a = inner ℝ (φ x a) θ) ∧
    ‖θ‖ ≤ Real.sqrt d ∧
    Real.sqrt (∑ i, ((mu i).totalVariation Set.univ).toReal ^ 2) ≤ Real.sqrt d

end LinearMDPRL.Linear


