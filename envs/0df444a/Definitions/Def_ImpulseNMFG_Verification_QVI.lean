-- Prove2me | Definitions.Def_ImpulseNMFG_Verification_QVI
-- name    : ImpulseNMFG_Verification_QVI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:39.434355+00:00
-- url     : https://prove2.me/theorems/9bccc29d-09ce-490a-aa76-b019d82f7dc1
-- title:
--   §2.2.1, pp. 8–10 — unique minimizers, intervention operators and N-player QVI
-- statement:
--   For candidate value functions $V_i$ and unique minimizing impulses $\xi_i(x)\in Z_i$, define the own and cross intervention operators
--   $$
--   \mathcal M_iV_i(x)=V_i(\Gamma^i(x,\xi_i(x)))+\phi_i(x,\xi_i(x)),\qquad
--   \mathcal H_{i,j}V_i(x)=V_i(\Gamma^j(x,\xi_j(x)))+\psi_{i,j}(x,\xi_j(x)).
--   $$
--   The strict waiting region is $D_i=\{x\in S:\mathcal M_iV_i(x)-V_i(x)>0\}$; the candidate action region is $A_i^*=\{x\in S:\mathcal M_iV_i(x)-V_i(x)=0\}$. For a fixed player $i$, the common waiting region $W_i$ is $S\cap\bigcap_{j\ne i}D_j$. The candidate profile is formed from the $A_i^*$ and $\xi_i$.
--
--   The QVI system imposes the boundary limit $V_i\to h_i$ from within $S$, nonnegativity of every own intervention gap, zero cross gap when another player intervenes, and
--   $$
--   \min\{\mathcal LV_i-\rho_iV_i+f_i,\ \mathcal M_iV_i-V_i\}=0
--   \quad\text{on }W_i\setminus\partial D_i.
--   $$
--   Here $\mathcal L$ is the diffusion generator built from the same $b$ and $\sigma$ as the stochastic equation. The regularity assumptions require $C^2$ smoothness away from $\partial D_i$, $C^1$ smoothness on $W_i$, continuity on its closure, polynomial growth, a Lipschitz boundary surface, and locally bounded first and second derivatives near that surface.
--
--   Finally, the boundary $\partial D_i$ is *negligible* for player $i$ at $x$ if, for every strategy $\varphi_i$ of player $i$ with $(\varphi^{*,-i},\varphi_i)\in\Phi_x$ and every admissible realization, almost surely the set of times $s\in[0,\tau_S)$ with $X_s\in\partial D_i$ has Lebesgue measure zero.
--
--   These definitions supply the hypotheses and the candidate profile of the verification theorem.
--
--   **Formalization Note** The QVI is evaluated off $\partial D_i$, where the second derivative exists. The within-$S$ limit is the paper's explanation of (2.13a). The explicit intersection with $S$ gives $W_i=S$ when $N=1$. The published generator and polynomial-growth and Lipschitz-surface predicates are reused; the maximizing two-player QVI is not reused. The negligibility of $\partial D_i$ is the occupation-time hypothesis of Øksendal's Theorem 10.4.1, which the paper cites on p. 10; it is not stated in the paper and is used as an added hypothesis of the verification theorem.
-- source:
--   Basei, Cao, Guo, Nonzero-sum stochastic games and mean-field games with impulse controls, arXiv:1901.08085v4, pp. 8–10, (2.10)–(2.13) and Theorem 2.12(ii)–(iii)

import Mathlib
import Definitions.Def_ImpulseGames_Verification_QVI
import Definitions.Def_ImpulseNMFG_Verification_Game
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ImpulseGames.Verification (State)

namespace ImpulseNMFG.Verification
noncomputable section
variable {N d M : ℕ} [NeZero N]

section QVI
variable (G : Game N d M) (V : Fin N → State d → ℝ)
    (ξ : (i : Fin N) → State d → G.Imp i)

/-- Basei, Cao, Guo, arXiv:1901.08085v4, p. 8, (2.10): ξ_i is the
unique minimizer of the impulse cost among Z_i. Continuity follows separately from Φ_x. -/
def IsUniqueMinimizer (i : Fin N) : Prop :=
  ∀ y ∈ G.S, ξ i y ∈ G.Z i ∧ ∀ z ∈ G.Z i, z ≠ ξ i y →
    V i (G.Γ i y (ξ i y)) + G.φ i y (ξ i y) <
      V i (G.Γ i y z) + G.φ i y z

/-- Own intervention operator (2.11). -/
def ownOp (i : Fin N) (y : State d) : ℝ :=
  V i (G.Γ i y (ξ i y)) + G.φ i y (ξ i y)

/-- Opponent intervention operator (2.11), meaningful when j ≠ i. -/
def crossOp (i j : Fin N) (y : State d) : ℝ :=
  V i (G.Γ j y (ξ j y)) + G.ψ i j y (ξ j y)

/-- Player i's strict waiting region, contained in S. -/
def waitRegion (i : Fin N) : Set (State d) :=
  {y | y ∈ G.S ∧ 0 < ownOp G V ξ i y - V i y}

/-- The candidate action region, restricted to S. -/
def starAction (i : Fin N) : Set (State d) :=
  {y | y ∈ G.S ∧ ownOp G V ξ i y - V i y = 0}

/-- Common waiting region for all players other than i. For N=1 this is S. -/
def commonWait (i : Fin N) : Set (State d) :=
  G.S ∩ ⋂ j : {j : Fin N // j ≠ i}, waitRegion G V ξ j.1

/-- Candidate equilibrium strategy profile built from V and ξ. -/
def starProfile : Profile G := ⟨starAction G V ξ, ξ⟩

/-- Basei, Cao, Guo, arXiv:1901.08085v4, p. 9, (2.13a)–(2.13d).
The boundary value is a limit within S. The generator is the published operator
of the same b and σ, and the fourth line is off ∂D_i where D²V_i exists. -/
def SolvesQVI (i : Fin N) : Prop :=
  (∀ y ∈ frontier G.S, Tendsto (V i) (𝓝[G.S] y) (𝓝 (G.h i y))) ∧
  (∀ j, ∀ y ∈ G.S, 0 ≤ ownOp G V ξ j y - V j y) ∧
  (∀ j, j ≠ i → ∀ y ∈ G.S,
    ownOp G V ξ j y - V j y = 0 → crossOp G V ξ i j y - V i y = 0) ∧
  (∀ y ∈ commonWait G V ξ i \ frontier (waitRegion G V ξ i),
    min (ImpulseGames.Verification.generator G.b G.σ (V i) y - G.ρ i * V i y + G.f i y)
      (ownOp G V ξ i y - V i y) = 0)

/-- Basei, Cao, Guo, arXiv:1901.08085v4, p. 10, Theorem 2.12(ii).
Continuity is on the closure of the common waiting region. -/
def Regular (i : Fin N) : Prop :=
  ContDiffOn ℝ 2 (V i) (commonWait G V ξ i \ frontier (waitRegion G V ξ i)) ∧
  ContDiffOn ℝ 1 (V i) (commonWait G V ξ i) ∧
  ContinuousOn (V i) (closure (commonWait G V ξ i)) ∧
  ImpulseGames.Verification.HasPolyGrowth (V i) G.S

/-- Basei, Cao, Guo, arXiv:1901.08085v4, p. 10, Theorem 2.12(iii).
The first two Frechet derivatives are locally bounded where they exist, off ∂D_i. -/
def BoundaryRegular (i : Fin N) : Prop :=
  ImpulseGames.Verification.IsLipschitzSurface (frontier (waitRegion G V ξ i)) ∧
  ∃ U : Set (State d), IsOpen U ∧ frontier (waitRegion G V ξ i) ⊆ U ∧
    ∀ K ⊆ U, IsCompact K → ∃ B : ℝ,
      ∀ y ∈ K ∩ (commonWait G V ξ i \ frontier (waitRegion G V ξ i)),
        ‖fderiv ℝ (V i) y‖ ≤ B ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (V i) z) y‖ ≤ B
end QVI

section Occupation
variable {Ω : Type*} [m : MeasurableSpace Ω]

/-- The time the controlled state spends on the boundary ∂D_i is Lebesgue-null, for player i
and every admissible realization of every unilateral deviation (φ^{*,-i}, φ_i) from the
candidate profile (the choice φ_i = φ*_i gives the candidate profile itself).
Formalization Note: this is the occupation-time hypothesis of Øksendal's Theorem 10.4.1, whose
proof and Appendix D the paper cites on p. 10 for the approximation (a)–(c); the passage from
(2.17) to (2.18) needs it, since (c) gives convergence of 𝓛V_{i,m} only off ∂D_i. It holds
automatically for a nondegenerate diffusion; without it the theorem fails for degenerate σ. -/
def BoundaryNegligible (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m)
    (W : ℝ≥0 → Ω → (Fin M → ℝ)) (G : Game N d M) (V : Fin N → State d → ℝ)
    (ξ : (i : Fin N) → State d → G.Imp i) (x : State d) (i : Fin N) : Prop :=
  ∀ (A : Set (State d)) (ξ' : State d → G.Imp i) (Y : ℕ → ℝ≥0 → Ω → State d),
    IsAdmissible P 𝔽 W G x ((starProfile G V ξ).update i A ξ') Y →
    ∀ᵐ ω ∂P, volume {s : ℝ |
      s ∈ ImpulseGames.Verification.before
        (exitTime G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω)) ∧
      ctrl G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) s.toNNReal ∈
        frontier (waitRegion G V ξ i)} = 0
end Occupation
end
end ImpulseNMFG.Verification


