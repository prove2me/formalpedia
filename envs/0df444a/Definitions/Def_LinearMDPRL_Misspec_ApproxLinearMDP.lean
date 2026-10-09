-- Prove2me | Definitions.Def_LinearMDPRL_Misspec_ApproxLinearMDP
-- name    : LinearMDPRL_Misspec_ApproxLinearMDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:15.220867+00:00
-- url     : https://prove2.me/theorems/ef60ded3-1c49-40e2-9e6f-324718291e86
-- title:
--   Assumption B, p. 7 — ζ-approximate linear MDP, with the normalization on total variations of µ_h
-- statement:
--   This file states Assumption B ($\zeta$-approximate linear MDP, p. 7).
--
--   For signed measures $\mu^{(1)},\dots,\mu^{(d)}$ on $\mathcal S$, $\int f\,\mathrm d\mu^{(i)}$ is defined through the Jordan decomposition $\mu^{(i)}=\mu^{(i)}_+-\mu^{(i)}_-$, and $|\nu|(\mathcal S)$ denotes the total variation norm of a signed measure $\nu$. An episodic MDP is **$\zeta$-approximately linear** with feature map $\phi:\mathcal S\times\mathcal A\to\mathbb R^d$, where $0\le\zeta\le1$, if $\|\phi(x,a)\|\le1$ for all $(x,a)$, each $\phi(\cdot,a)$ is measurable, and for every $h\in[H]$ there exist signed measures $\mu_h=(\mu_h^{(1)},\dots,\mu_h^{(d)})$ and a vector $\theta_h\in\mathbb R^d$ with, for all $(x,a)$,
--   $$\big\|\mathbb P_h(\cdot\mid x,a)-\langle\phi(x,a),\mu_h(\cdot)\rangle\big\|_{\mathrm{TV}}\le\zeta,\qquad |r_h(x,a)-\langle\phi(x,a),\theta_h\rangle|\le\zeta,\qquad(4)$$
--   $$\|\theta_h\|\le\sqrt d,\qquad \Big(\sum_{i=1}^d|\mu^{(i)}_h|(\mathcal S)^2\Big)^{1/2}\le\sqrt d.$$
--
--   For a fixed representation $(\mu_h,\theta_h)_h$ and a policy $\pi$ the file also names the weights of Lemma C.1,
--   $$w^\pi_h=\theta_h+\int V^\pi_{h+1}(x')\,\mathrm d\mu_h(x').$$
--
--   At $\zeta=0$ this is a linear MDP (Assumption A). The assumption measures how far the MDP is from one, and Theorem 3.2's regret degrades linearly in $\zeta$.
--
--   **Formalization Note** $\|\cdot\|_{\mathrm{TV}}$ is the total variation norm $|\nu|(\mathcal S)$; this is the convention the proofs of Lemmas C.1 and C.5 use ($|\int V\,\mathrm d\nu|\le\|V\|_\infty|\nu|(\mathcal S)$, giving "$\zeta+H\zeta$"). The page normalizes $\|\mu_h(\mathcal S)\|\le\sqrt d$, which bounds only the net masses $\mu_h^{(i)}(\mathcal S)$; this file bounds the total variations instead. The printed form does not imply the bound $\|\int V\,\mathrm d\mu_h\|\le H\sqrt d$ used in Lemma C.2's proof, and Lemma C.2 is false under it (a two-state counterexample with $\mu^{(2)}=M(\delta_1-\delta_2)$, $M$ large, has $\mu^{(2)}(\mathcal S)=0$ but unbounded weights). The total-variation form implies the printed one and holds with equality for tabular MDPs. $0\le\zeta$ is implicit on the page (a distance bound); measurability of $\phi$ is implicit (it enters integrals through $V^k$).
-- source:
--   arXiv:1907.05388v2, Assumption B, (4), p. 7; Lemma C.1, p. 21 (w^π_h)

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model

open MeasureTheory ProbabilityTheory

namespace LinearMDPRL.Misspec

universe u v

variable {S : Type u} {A : Type v} [MeasurableSpace S] [MeasurableSpace A] {d : ℕ}

/-- `∫ v dµ` for a finite signed measure `µ`, through its Jordan decomposition `µ = µ⁺ − µ⁻`. -/
noncomputable def signedIntegral (mu : SignedMeasure S) (f : S → ℝ) : ℝ :=
  ∫ y, f y ∂mu.toJordanDecomposition.posPart - ∫ y, f y ∂mu.toJordanDecomposition.negPart

/-- Assumption B at one step `h`, for a given representation `(µ_h, θ_h)`:
`‖P_h(· | x, a) − ⟨φ(x, a), µ_h(·)⟩‖_TV ≤ ζ` (total variation norm `|ν|(S)` of the signed measure),
`|r_h(x, a) − ⟨φ(x, a), θ_h⟩| ≤ ζ`, `‖θ_h‖ ≤ √d`, and the normalization
`‖(|µ_h^{(1)}|(S), …, |µ_h^{(d)}|(S))‖ ≤ √d` on the total variations of the `µ_h^{(i)}`. -/
def IsApproxRep (M : LinearMDPRL.Linear.EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)) (ζ : ℝ) (h : ℕ)
    (mu : Fin d → SignedMeasure S) (θ : EuclideanSpace ℝ (Fin d)) : Prop :=
  haveI : IsMarkovKernel (M.P h) := M.isMarkov h
  (∀ x a, ((M.P h (x, a)).toSignedMeasure - ∑ i, (φ x a i) • mu i).totalVariation Set.univ
      ≤ ENNReal.ofReal ζ) ∧
  (∀ x a, |M.r h x a - inner ℝ (φ x a) θ| ≤ ζ) ∧
  ‖θ‖ ≤ Real.sqrt d ∧
  Real.sqrt (∑ i, ((mu i).totalVariation Set.univ).toReal ^ 2) ≤ Real.sqrt d

/-- Assumption B (ζ-approximate linear MDP), p. 7: `0 ≤ ζ ≤ 1`, `‖φ(x, a)‖ ≤ 1`, `φ(·, a)` measurable,
and for every `h ∈ [H]` a representation `(µ_h, θ_h)` satisfying `IsApproxRep`. -/
def IsApproxLinearMDP (M : LinearMDPRL.Linear.EpisodicMDP S A) (H d : ℕ) (φ : S → A → EuclideanSpace ℝ (Fin d))
    (ζ : ℝ) : Prop :=
  0 ≤ ζ ∧ ζ ≤ 1 ∧ (∀ x a, ‖φ x a‖ ≤ 1) ∧ (∀ a, Measurable (fun x => φ x a)) ∧
  ∀ h ∈ Finset.Icc 1 H, ∃ (mu : Fin d → SignedMeasure S) (θ : EuclideanSpace ℝ (Fin d)),
    IsApproxRep M φ ζ h mu θ

/-- The weights of Lemma C.1: `w^π_h = θ_h + ∫ LinearMDPRL.Linear.V^π_{h+1}(x′) dµ_h(x′)`, for a fixed representation
`(µ_h, θ_h)_h`. -/
noncomputable def repWeight (M : LinearMDPRL.Linear.EpisodicMDP S A) (H : ℕ) (π : LinearMDPRL.Linear.Policy S A)
    (mu : ℕ → Fin d → SignedMeasure S) (θ : ℕ → EuclideanSpace ℝ (Fin d)) (h : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  θ h + WithLp.toLp 2 (fun i => signedIntegral (mu h i) (LinearMDPRL.Linear.V M H π (h + 1)))

end LinearMDPRL.Misspec


