-- Prove2me | Definitions.Def_MHSpectralGap_RWM_MHKernel
-- name    : MHSpectralGap_RWM_MHKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T22:13:27.953193+00:00
-- url     : https://prove2.me/theorems/71e10016-4e59-42ec-94c8-661b98f2f179
-- title:
--   (1.3), p. 3 — the Metropolis–Hastings transition kernel built from a proposal kernel Q and an acceptance probability α
-- statement:
--   Let $(X,\mathcal F)$ be a measurable space, $Q$ a Markov kernel on $X$ (the **proposal kernel**) and $\alpha : X\times X\to[0,1]$ a jointly measurable function (the **acceptance probability**). The **Metropolis–Hastings transition kernel** with proposal $Q$ and acceptance $\alpha$ is
--
--   $$
--   P(x,dz)=Q(x,dz)\,\alpha(x,z)+\delta_x(dz)\int_X\bigl(1-\alpha(x,u)\bigr)\,Q(x,du).
--   $$
--
--   From $x$ one draws a proposal $y\sim Q(x,\cdot)$ and moves to $y$ with probability $\alpha(x,y)$; otherwise one stays at $x$. The first term is the accepted part of the proposal, the second the total rejection mass placed at $x$. When $Q$ is Markov and $\alpha\le 1$, $P$ is again a Markov kernel.
--
--   This is the common kernel of both algorithms of the paper (pCN and RWM); Proposition 2.16 bounds the spectral gap of every such kernel.
--
--   **Formalization Note** The acceptance probability is typed $X\to X\to[0,\infty]$; every theorem using the kernel assumes $\alpha\le 1$ and joint measurability. Without measurability Mathlib's `Kernel.withDensity` returns the zero kernel, so the measurability hypothesis is essential and appears in every statement.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 3, display (1.3)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MHSpectralGap.RWM

/-- The Metropolis–Hastings transition kernel (1.3) of Hairer–Stuart–Vollmer (p. 3):
`P(x, dz) = Q(x, dz) α(x, z) + δ_x(dz) ∫ (1 − α(x, u)) Q(x, du)`,
for a proposal kernel `Q` and an acceptance probability `α : X → X → [0, ∞]`.
It is a Markov kernel whenever `Q` is Markov, `α` is jointly measurable and `α ≤ 1`
(otherwise `Kernel.withDensity` returns the zero kernel). -/
noncomputable def mhKernel {X : Type*} [MeasurableSpace X] (Q : ProbabilityTheory.Kernel X X)
    [ProbabilityTheory.IsSFiniteKernel Q] (α : X → X → ℝ≥0∞) : ProbabilityTheory.Kernel X X :=
  Q.withDensity (fun x y => α x y) +
    ProbabilityTheory.Kernel.withDensity ProbabilityTheory.Kernel.id
      (fun x _ => ∫⁻ u, (1 - α x u) ∂(Q x))

end MHSpectralGap.RWM


