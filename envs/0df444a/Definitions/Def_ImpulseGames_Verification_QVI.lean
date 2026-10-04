-- Prove2me | Definitions.Def_ImpulseGames_Verification_QVI
-- name    : ImpulseGames_Verification_QVI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:03:56.220879+00:00
-- url     : https://prove2.me/theorems/03d846c9-18d4-4aa0-9564-c0649a0e3981
-- title:
--   Intervention operators (3.1)–(3.2), generator $\mathcal A$, QVI system (3.3), and the hypotheses (ii)–(iii) of Theorem 3.3
-- statement:
--   Let $V_1,V_2$ be real functions on $\bar S$ (in Lean, on $\mathbb R^d$, only their values on $\bar S$ matter) and $\delta_i:S\to Z_i$, $i\in\{1,2\}$; $j$ denotes the opponent of $i$.
--
--   1. **Assumption (3.1).** $\delta_i$ is measurable on $S$ and, for every $x\in S$, $\delta_i(x)$ is the unique maximizer of $\delta\mapsto V_i(\Gamma^i(x,\delta))+\phi_i(x,\delta)$ over $Z_i$:
--   $$\{\delta_i(x)\}=\arg\max_{\delta\in Z_i}\{V_i(\Gamma^i(x,\delta))+\phi_i(x,\delta)\}.$$
--   2. **Intervention operators (3.2).** For $x\in S$,
--   $$\mathcal M_iV_i(x)=V_i(\Gamma^i(x,\delta_i(x)))+\phi_i(x,\delta_i(x)),\qquad \mathcal H_iV_i(x)=V_i(\Gamma^j(x,\delta_j(x)))+\psi_i(x,\delta_j(x)).$$
--   3. **Continuation regions.** $\mathcal D_i=\{x\in S:\mathcal M_iV_i(x)-V_i(x)<0\}$, and the candidate equilibrium strategies are $\varphi_i^*=(\mathcal D_i,\delta_i)$.
--   4. **Generator.** $\mathcal AV=b\cdot\nabla V+\tfrac12\operatorname{tr}(\sigma\sigma^{t}D^2V)$.
--   5. **QVI system (3.3).**
--   $$
--   \begin{aligned}
--   &V_i=h_i &&\text{in }\partial S,\\
--   &\mathcal M_jV_j-V_j\le0 &&\text{in }S,\\
--   &\mathcal H_iV_i-V_i=0 &&\text{in }\{\mathcal M_jV_j-V_j=0\},\\
--   &\max\{\mathcal AV_i-\rho_iV_i+f_i,\ \mathcal M_iV_i-V_i\}=0 &&\text{in }\{\mathcal M_jV_j-V_j<0\}=\mathcal D_j .
--   \end{aligned}
--   $$
--   6. **Regularity (ii).** $V_i\in C^2(\mathcal D_j\setminus\partial\mathcal D_i)\cap C^1(\mathcal D_j)\cap C(\bar S)$, and $|V_i(y)|\le c(1+|y|^p)$ on $\bar S$ for some $c$ and $p\in\mathbb N$.
--   7. **Regularity (iii).** $\partial\mathcal D_i$ is a Lipschitz surface (near each of its points it is, in suitable orthonormal coordinates, the graph of a Lipschitz function of $d-1$ variables), and on some open neighbourhood $N$ of $\partial\mathcal D_i$ the first and second derivatives of $V_i$ are bounded on every compact subset of $N$.
--
--   These are the hypotheses of the verification theorem (Theorem 3.3): a regular solution of the QVI system yields a Nash equilibrium.
--
--   **Formalization Note.** Derivatives are Fréchet derivatives; the trace is written $\sum_{p,q}(\sigma\sigma^t)_{pq}D^2V[e_p,e_q]$. The fourth line of (3.3) is required on $\mathcal D_j\setminus\partial\mathcal D_i$, where $V_i$ is twice differentiable by (ii); on $\partial\mathcal D_i$ the paper's $\mathcal AV_i$ is undefined and a Lean junk value would impose a condition the paper does not. The derivative bounds of (iii) are read on the points of the compact set in $\mathcal D_j\setminus\partial\mathcal D_i$, where both derivatives exist. A Lipschitz surface is encoded with a unit vector $\nu$ and a Lipschitz $g$ constant along $\nu$: locally the surface is $\{y:\langle y,\nu\rangle=g(y)\}$. `VerificationHypotheses` bundles (3.1), continuity of $\delta_i$ on $S$, (3.3) and (ii)–(iii) for both players. Continuity of $\delta_i$ is added: $\varphi_i^*$ must be a strategy, and Definition 2.1 asks $\xi_i$ to be continuous (Remark 3.6 also uses it to make $\mathcal D_i$ open).
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, Section 3.1: (3.1)–(3.3d) (pp. 7–8); Theorem 3.3 (ii)–(iii) (p. 9)

import Mathlib
import Definitions.Def_ImpulseGames_Verification_Game

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ImpulseGames.Verification

noncomputable section

variable {d k : ℕ}

section QVI

variable (G : Game d k) (V : Player → State d → ℝ) (δ : (i : Player) → State d → G.Imp i)

/-- Assumption (3.1) for player `i`: `δ_i` is measurable on `S` and, for each `y ∈ S`, `δ_i(y)` is the
unique maximizer over `Z_i` of `z ↦ V_i(Γ_i(y, z)) + ϕ_i(y, z)`. -/
def IsUniqueMaximizer (i : Player) : Prop :=
  Measurable (fun y : G.S => δ i y) ∧
  ∀ y ∈ G.S, δ i y ∈ G.Z i ∧ ∀ z ∈ G.Z i, z ≠ δ i y →
    V i (G.Γ i y z) + G.cost i y z < V i (G.Γ i y (δ i y)) + G.cost i y (δ i y)

/-- The intervention operator (3.2): `𝓜_i V_i(y) = V_i(Γ_i(y, δ_i(y))) + ϕ_i(y, δ_i(y))`. -/
def interventionOp (i : Player) (y : State d) : ℝ :=
  V i (G.Γ i y (δ i y)) + G.cost i y (δ i y)

/-- The operator (3.2): `𝓗_i V_i(y) = V_i(Γ_j(y, δ_j(y))) + ψ_i(y, δ_j(y))`, `j ≠ i`. -/
def opponentOp (i : Player) (y : State d) : ℝ :=
  V i (G.Γ i.other y (δ i.other y)) + G.gain i y (δ i.other y)

/-- `𝒟_i = {y ∈ S : 𝓜_i V_i(y) - V_i(y) < 0}`, the continuation region of player `i`. -/
def contRegion (i : Player) : Set (State d) :=
  {y | y ∈ G.S ∧ interventionOp G V δ i y - V i y < 0}

/-- The candidate equilibrium strategies `φ_i^* = (𝒟_i, δ_i)`. -/
def starProfile : Profile G := ⟨fun i => contRegion G V δ i, δ⟩

end QVI

/-- The generator `𝓐u = b · ∇u + ½ tr(σσᵗ D²u)`, written with Fréchet derivatives:
`𝓐u(y) = Du(y)[b(y)] + ½ ∑_{p,q} (σσᵗ)_{pq}(y) D²u(y)[e_p, e_q]`. -/
def generator (b : State d → State d) (σ : State d → Matrix (Fin d) (Fin k) ℝ)
    (u : State d → ℝ) (y : State d) : ℝ :=
  fderiv ℝ u y (b y) + (1 / 2) * ∑ p : Fin d, ∑ q : Fin d,
    (∑ r : Fin k, σ y p r * σ y q r) *
      fderiv ℝ (fun z => fderiv ℝ u z) y (EuclideanSpace.single p 1)
        (EuclideanSpace.single q 1)

section QVI2

variable (G : Game d k) (V : Player → State d → ℝ) (δ : (i : Player) → State d → G.Imp i)

/-- The quasi-variational inequalities (3.3a)–(3.3d) for player `i` (with `j = i.other`):
(3.3a) `V_i = h_i` on `∂S`; (3.3b) `𝓜_j V_j - V_j ≤ 0` on `S`;
(3.3c) `𝓗_i V_i - V_i = 0` on `{𝓜_j V_j - V_j = 0}`;
(3.3d) `max {𝓐V_i - ρ_i V_i + f_i, 𝓜_i V_i - V_i} = 0` on `𝒟_j = {𝓜_j V_j - V_j < 0}`,
required off `∂𝒟_i`, where `V_i` is twice differentiable. -/
def SolvesQVI (i : Player) : Prop :=
  (∀ y ∈ frontier G.S, V i y = G.h i y) ∧
  (∀ y ∈ G.S, interventionOp G V δ i.other y - V i.other y ≤ 0) ∧
  (∀ y ∈ G.S, interventionOp G V δ i.other y - V i.other y = 0 →
    opponentOp G V δ i y - V i y = 0) ∧
  (∀ y ∈ contRegion G V δ i.other \ frontier (contRegion G V δ i),
    max (generator G.b G.σ (V i) y - G.ρ i * V i y + G.f i y)
      (interventionOp G V δ i y - V i y) = 0)

/-- Polynomial growth on a set `A`: `|u(y)| ≤ c (1 + ‖y‖^p)` for some `c`, `p ∈ ℕ`. -/
def HasPolyGrowth (u : State d → ℝ) (A : Set (State d)) : Prop :=
  ∃ (c : ℝ) (p : ℕ), ∀ y ∈ A, |u y| ≤ c * (1 + ‖y‖ ^ p)

/-- Condition (ii) of Theorem 3.3 for player `i`:
`V_i ∈ C²(𝒟_j \ ∂𝒟_i) ∩ C¹(𝒟_j) ∩ C(S̄)` with polynomial growth on `S̄`. -/
def Regular (i : Player) : Prop :=
  ContDiffOn ℝ 2 (V i) (contRegion G V δ i.other \ frontier (contRegion G V δ i)) ∧
  ContDiffOn ℝ 1 (V i) (contRegion G V δ i.other) ∧
  ContinuousOn (V i) (closure G.S) ∧
  HasPolyGrowth (V i) (closure G.S)

end QVI2

/-- `B` is a Lipschitz surface: every point of `B` has a neighbourhood `U` in which `B` is the
graph of a Lipschitz function over a hyperplane, i.e. for a unit vector `ν` and a Lipschitz
`g` constant along `ν`, `B ∩ U = {y ∈ U : ⟨y, ν⟩ = g(y)}`. -/
def IsLipschitzSurface (B : Set (State d)) : Prop :=
  ∀ p ∈ B, ∃ U ∈ 𝓝 p, ∃ ν : State d, ‖ν‖ = 1 ∧ ∃ (g : State d → ℝ) (L : ℝ≥0),
    LipschitzWith L g ∧ (∀ (y : State d) (t : ℝ), g (y + t • ν) = g y) ∧
    B ∩ U = {y | y ∈ U ∧ inner ℝ y ν = g y}

section Hyp

variable (G : Game d k) (V : Player → State d → ℝ) (δ : (i : Player) → State d → G.Imp i)

/-- Condition (iii) of Theorem 3.3 for player `i`: `∂𝒟_i` is a Lipschitz surface, and on some
open neighbourhood `N` of `∂𝒟_i` the first and second derivatives of `V_i` are bounded on every
compact `K ⊆ N` (at the points of `K` in `𝒟_j \ ∂𝒟_i`, where they exist). -/
def BoundaryRegular (i : Player) : Prop :=
  IsLipschitzSurface (frontier (contRegion G V δ i)) ∧
  ∃ N : Set (State d), IsOpen N ∧ frontier (contRegion G V δ i) ⊆ N ∧
    ∀ K ⊆ N, IsCompact K → ∃ M : ℝ,
      ∀ y ∈ K ∩ (contRegion G V δ i.other \ frontier (contRegion G V δ i)),
        ‖fderiv ℝ (V i) y‖ ≤ M ∧ ‖fderiv ℝ (fun z => fderiv ℝ (V i) z) y‖ ≤ M

/-- The analytic hypotheses of Theorem 3.3 on `(V_1, V_2)` and `(δ_1, δ_2)`, for both players:
(3.1) with `δ_i` continuous on `S`, (i) the QVI system, (ii) and (iii). -/
def VerificationHypotheses : Prop :=
  ∀ i, IsUniqueMaximizer G V δ i ∧ ContinuousOn (δ i) G.S ∧ SolvesQVI G V δ i ∧
    Regular G V δ i ∧ BoundaryRegular G V δ i

end Hyp

end

end ImpulseGames.Verification


