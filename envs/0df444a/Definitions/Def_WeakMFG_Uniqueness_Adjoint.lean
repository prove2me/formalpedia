-- Prove2me | Definitions.Def_WeakMFG_Uniqueness_Adjoint
-- name    : WeakMFG_Uniqueness_Adjoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:43.123378+00:00
-- url     : https://prove2.me/theorems/34121773-1511-434d-b35e-25fdc16e9faa
-- title:
--   The BSDE (7.1) for a pair $(\mu, q)$ and the set $\mathbb A(\mu, q)$ of Hamiltonian-maximizing controls (7.4)
-- statement:
--   For $\mu\in\mathcal P_\psi(\mathcal C)$ and a flow $q:[0,T]\to\mathcal P(A)$ (the measure flow $\nu_t=\delta_{q_t}$ of the paper), the pair $(Y,Z)$ with $Y$ real and $Z$ $\mathbb R^d$-valued, both square integrable and progressively measurable, solves the BSDE
--   $$Y_t = g(X,\mu) + \int_t^T H(s,X,\mu,q_s,Z_s)\,ds - \int_t^T Z_s\,dW_s,\qquad 0\le t\le T. \tag{7.1}$$
--   Given the adjoint process $Z$, the set
--   $$\mathbb A(\mu,q) = \{\alpha\in\mathbb A : \alpha_t\in A(t,X,\mu,q_t,Z_t)\ \ dt\times dP\text{-a.e.}\} \tag{7.4}$$
--   collects the admissible controls that maximize the Hamiltonian along the adjoint process.
--
--   By the comparison principle for BSDEs, every element of $\mathbb A(\mu,q)$ is an optimal control for the problem with $(\mu,q)$ frozen; these are the objects of the proofs of existence and uniqueness of the mean field game.
--
--   **Formalization Note.** The BSDE is the referenced `Peng1990.SMP.SolvesBSDE` with a one-point index set for the scalar state, so $Y_t(\omega)$ is a function on a one-point set and $Z$ has coordinates $Z^j_t(\omega)$; $Z_t$ as a vector of $\mathbb R^d$ is read off coordinatewise. "$dt\times dP$-a.e." is almost everywhere for the product of Lebesgue measure on $[0,T]$ and $P$.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §7, (7.1) p. 21 and (7.4) p. 22

import Mathlib
import Definitions.Def_WeakMFG_Uniqueness_Reward

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Uniqueness

variable {d : ℕ} {T : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω]
  {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
  {ψ : WeakMFG.Existence.Path d T → ℝ}

/-- The adjoint vector `Z_t(ω) ∈ ℝ^d` of a solution `(Y, Z)` of the scalar BSDE (7.1), read off
the `Peng1990.SMP.SolvesBSDE` encoding (state space `Unit → ℝ`, `Z_j : ℝ≥0 → Ω → Unit → ℝ`). -/
def zvec (Z : Fin d → ℝ≥0 → Ω → Unit → ℝ) (t : ℝ≥0) (ω : Ω) : Fin d → ℝ :=
  fun j => Z j t ω ()

/-- `(Y, Z)` solves the BSDE (7.1), p. 21, for the pair `(μ, q)` (the flow `ν_t = δ_{q_t}`):
`Y_t = g(X, μ) + ∫ₜᵀ H(s, X, μ, q_s, Z_s) ds − ∫ₜᵀ Z_s dW_s`, `0 ≤ t ≤ T`, with `Y` and `Z` in
`L²_𝔽` (`Peng1990.SMP.SolvesBSDE`, scalar state written as `Unit → ℝ`). -/
def SolvesBSDE71 (B : Base d Ω) (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (Xp : Ω → WeakMFG.Existence.Path d T) (μ : Ppsi ψ) (q : ℝ≥0 → PA A)
    (Y : ℝ≥0 → Ω → Unit → ℝ) (Z : Fin d → ℝ≥0 → Ω → Unit → ℝ) : Prop :=
  Peng1990.SMP.SolvesBSDE B.filt B.P T B.W (fun ω _ => g (Xp ω) μ)
    (fun s ω _ z _ => Ham A σ b f s (Xp ω) μ (q s) (fun j => z j ())) Y Z

/-- Membership in `𝔸(μ, ν)` of (7.4), p. 22, for `ν_t = δ_{q_t}` and the adjoint process `Z` of
(7.1): `α` is admissible and `α_t ∈ A(t, X, μ, q_t, Z_t)` for `dt × dP`-almost every
`(t, ω) ∈ [0, T] × Ω`. -/
def InAset (B : Base d Ω) (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ)
    (Xp : Ω → WeakMFG.Existence.Path d T) (μ : Ppsi ψ) (q : ℝ≥0 → PA A)
    (Z : Fin d → ℝ≥0 → Ω → Unit → ℝ) (α : ℝ≥0 → Ω → EA) : Prop :=
  B.IsAdmissible A α ∧
    ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod B.P),
      α p.1.toNNReal p.2 ∈ Amax A σ b f p.1.toNNReal (Xp p.2) μ (q p.1.toNNReal) (zvec Z p.1.toNNReal p.2)

end WeakMFG.Uniqueness


