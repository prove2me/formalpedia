-- Prove2me | Definitions.Def_RiskExpPG_Model
-- name    : RiskExpPG_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:25:23.028027+00:00
-- url     : https://prove2.me/theorems/ff9b4fc3-210a-4b04-99b1-f032c7b8add2
-- title:
--   Parameterized chain, Assumptions 1–5, and the statistics $H$, $G^{(M)}$, $F^{(M)}$, $g$, $g^{(M)}$, $f^{(M)}$, $\Lambda^{(M)}_\theta$
-- statement:
--   A **model** consists of transition matrices $P_\theta$ and one-step costs $C_\theta$ on a finite set $\mathcal X$ for $\theta\in\mathbb R^l$, a function $L_\theta(x,y)\in\mathbb R^l$, a risk factor $\alpha$, and a state $x^*$. Every $P_\theta$ is stochastic and $\alpha>0$.
--
--   **Assumptions.**
--
--   1. Assumption 1: each matrix in the closure of $\{P_\theta:\theta\in\mathbb R^l\}$ is irreducible and aperiodic.
--   2. Assumption 2: $\theta\mapsto P_\theta(x,y)$ and $\theta\mapsto C_\theta(x)$ are bounded, twice differentiable, and have bounded first and second derivatives.
--   3. Assumption 3: $L$ is bounded with $\nabla_\theta P_\theta=P_\theta L_\theta$, and there is a bounded $L^{(2)}$ with $\nabla^2_\theta P_\theta=P_\theta L^{(2)}_\theta$.
--   4. Assumption 4, for a sequence $\{N_i\}$: $N_i\uparrow\infty$ and $\sum_i\sup_\theta\big(\Lambda^{(N_{i+1})}_\theta-\Lambda^{(N_i)}_\theta\big)<\infty$.
--   5. Assumption 5, for positive step sizes: $\sum_m\gamma_m=\infty$, $\sum_m\gamma_m^2<\infty$, $\sup_m\gamma_m<1$.
--
--   **Statistics of a cycle** from $x^*$ to $x^*$. Put
--   $$H(\theta,\Lambda):=\exp\Big(\sum_{i=0}^{\tau_{x^*}-1}(\alpha C_\theta(\Phi_i)-\Lambda)\Big),$$
--   $$G^{(M)}(\theta,\Lambda):=H\,\mathbb 1\{H\le M\}+M\Big[\sum_{i=0}^{4}\frac1{i!}\big(\ln(M^{-1}H)\big)^i\Big]\mathbb 1\{H>M\},$$
--   $$F^{(M)}(\theta,\Lambda):=G^{(M)}\sum_{i=0}^{\tau_{x^*}-1}L_\theta(\Phi_i,\Phi_{i+1})+\nabla_\theta H\,\mathbb 1\{H\le M\}+M\frac{\nabla_\theta H}{H}\Big[\sum_{i=0}^{3}\frac1{i!}\big(\ln(M^{-1}H)\big)^i\Big]\mathbb 1\{H>M\}.$$
--   Here $\nabla_\theta H=H\sum_{i=0}^{\tau_{x^*}-1}\alpha\nabla_\theta C_\theta(\Phi_i)$. The sum of $L$ runs over the $\tau_{x^*}$ transitions, including the last one into $x^*$. The sum of costs runs over the $\tau_{x^*}$ states $\Phi_0,\dots,\Phi_{\tau_{x^*}-1}$.
--
--   **Expectations.** $g(\theta,\Lambda):=E^\theta_{\Phi_0=x^*}[H]$, $g^{(M)}(\theta,\Lambda):=E^\theta_{\Phi_0=x^*}[G^{(M)}]$ and $f^{(M)}(\theta,\Lambda):=E^\theta_{\Phi_0=x^*}[F^{(M)}]$.
--
--   **Costs.** $\Lambda_\theta$ is the risk-sensitive cost of $(P_\theta,C_\theta)$, and $\Lambda^{(M)}_\theta$ is the unique solution of $g^{(M)}(\theta,\Lambda)=1$. The relative value function is $h_\theta(x)=E^\theta_{\Phi_0=x}\big[\exp\big(\sum_{i=0}^{\tau_{x^*}-1}(\alpha C_\theta(\Phi_i)-\Lambda_\theta)\big)\big]$, and the twisted kernel is
--   $$\check P_\theta(x,y):=\frac{\exp(\alpha C_\theta(x))\,P_\theta(x,y)\,h_\theta(y)}{\exp(\Lambda_\theta)\,h_\theta(x)}.$$
--
--   These are the objects on which the algorithm and every result of the mission are stated.
--
--   **Formalization Note** $g$ and $g^{(M)}$ take values in $[0,\infty]$, because $g$ can be $+\infty$. Their real-valued versions are differentiated only where they are finite. $\Lambda^{(M)}_\theta$ is the total function $\inf\{\Lambda: g^{(M)}(\theta,\Lambda)\le1\}$, and Corollary 14 proves that for $M>1$ it is the unique solution. $G^{(M)}$ is the smooth truncation of §5.2, not the hard truncation of §3. The supremum in Assumption 4 is written through a summable majorant. "Irreducible and aperiodic" is `Matrix.IsPrimitive`, and $x^*$ is a free state because every state of such a chain is recurrent.
-- source:
--   Moharrami, Murthy, Roy & Srikant, A Policy Gradient Algorithm for the Risk-Sensitive Exponential Cost MDP, arXiv:2202.04157v2, §2, pp.3–4, Eq. (1)–(3), Assumptions 1, 2; Assumption 3, p.6; §5.2, pp.8–9; Assumption 4, p.10; Assumption 5, p.11; Lemma 14, p.40

import Mathlib
import Definitions.Def_RiskExpPG_Chain

open Filter Topology
open scoped ENNReal

namespace RiskExpPG

/-- The parameter space `ℝ^l`, with its Euclidean norm. -/
abbrev Param (l : ℕ) : Type := EuclideanSpace ℝ (Fin l)

/-- The data of the parameterized chain of §2 (p.3) and of the score function of Assumption 3 (p.6):
a transition matrix `P θ` and a one-step cost `C θ` for each `θ ∈ ℝ^l`, the function
`L θ x y` of Assumption 3(a), the risk factor `α`, and the recurrent state `x*`.

**Formalization Note** The state space `X` is a parameter of the structure, finite wherever the
model is used. `L` is data because the algorithm evaluates it along the observed trajectory. -/
structure Model (X : Type*) (l : ℕ) where
  /-- The transition matrix `P_θ`. -/
  P : Param l → Matrix X X ℝ
  /-- The one-step cost `C_θ`. -/
  C : Param l → X → ℝ
  /-- The function `L_θ(x, y)` with `∇_θ P_θ(x, y) = P_θ(x, y) L_θ(x, y)`. -/
  L : Param l → X → X → Param l
  /-- The risk factor `α`. -/
  α : ℝ
  /-- The common recurrent state `x*`. -/
  xstar : X

variable {X : Type*} {l : ℕ}

/-- Standing conventions of §2 (p.3): every `P θ` is a transition matrix, and the risk factor is
positive. -/
def Model.IsValid [Fintype X] (m : Model X l) : Prop :=
  (∀ θ, IsStochastic (m.P θ)) ∧ 0 < m.α

/-- **Assumption 1** (p.3): each `Q` in the closure of `{P_θ : θ ∈ ℝ^l}` in the space of matrices
is aperiodic and irreducible.

**Formalization Note** For a stochastic matrix on a finite type, `Matrix.IsPrimitive` (nonnegative
with a strictly positive power) is exactly irreducible and aperiodic. Every state of such a chain
is recurrent, so the "common recurrent state `x*`" is the field `xstar`, a free choice. -/
def Model.Assumption1 [Fintype X] [DecidableEq X] (m : Model X l) : Prop :=
  ∀ Q ∈ closure (Set.range m.P), Matrix.IsPrimitive Q

/-- `f` is bounded, twice differentiable, and has bounded first and second derivatives
(Assumption 2, p.3).

**Formalization Note** "Twice differentiable" is differentiability of `fderiv ℝ f`; continuity of
the second derivative is not asked for. "Bounded" is uniform in `θ ∈ ℝ^l`. -/
def BoundedTwiceDiff (f : Param l → ℝ) : Prop :=
  Differentiable ℝ f ∧ Differentiable ℝ (fderiv ℝ f) ∧
    ∃ B : ℝ, ∀ θ, |f θ| ≤ B ∧ ‖fderiv ℝ f θ‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ f) θ‖ ≤ B

/-- **Assumption 2** (p.3): for each `x, y`, the functions `θ ↦ P_θ(x, y)` and `θ ↦ C_θ(x)` are
bounded, twice differentiable, and have bounded first and second derivatives. -/
def Model.Assumption2 (m : Model X l) : Prop :=
  (∀ x y, BoundedTwiceDiff fun θ => m.P θ x y) ∧ ∀ x, BoundedTwiceDiff fun θ => m.C θ x

/-- **Assumption 3** (p.6): the function `L` is bounded with `∇_θ P_θ(x, y) = P_θ(x, y) L_θ(x, y)`,
and there is a bounded `L²` with `∇²_θ P_θ(x, y) = P_θ(x, y) L²_θ(x, y)`.

**Formalization Note** The second gradient is `fderiv ℝ (fderiv ℝ _)`, a bilinear form in the
direction variables. Bounded means uniformly in `θ`, `x`, `y`. The function `L²` is used nowhere
else, so it is existentially quantified here. -/
def Model.Assumption3 (m : Model X l) : Prop :=
  (∃ B : ℝ, ∀ θ x y, ‖m.L θ x y‖ ≤ B) ∧
    (∀ θ x y, gradient (fun θ' => m.P θ' x y) θ = m.P θ x y • m.L θ x y) ∧
    ∃ L2 : Param l → X → X → (Param l →L[ℝ] Param l →L[ℝ] ℝ),
      (∃ B : ℝ, ∀ θ x y, ‖L2 θ x y‖ ≤ B) ∧
        ∀ θ x y, fderiv ℝ (fderiv ℝ fun θ' => m.P θ' x y) θ = m.P θ x y • L2 θ x y

/-- The risk-sensitive cost `Λ_θ` of Eq. (1) (p.3), read at the initial state `x*`. Proposition 2
shows that the initial state does not matter. -/
noncomputable def Model.riskCost [Fintype X] (m : Model X l) (θ : Param l) : ℝ :=
  riskRate (m.P θ) (m.C θ) m.α m.xstar

/-- `H(θ, Λ) := exp(Σ_{i=0}^{τ_{x*}-1} (α C_θ(Φᵢ) - Λ))` (§5.2, p.8), as a function of the excursion
`l` from `x*`. -/
noncomputable def Model.H (m : Model X l) (θ : Param l) (Λ : ℝ) (e : List X) : ℝ :=
  Real.exp (excursionCost (m.C θ) m.α Λ m.xstar e)

/-- The smooth truncation at level `M` of a value `h`, as in `G^(M)` (§5.2, p.8): `h` if `h ≤ M`, and
`M Σ_{i=0}^{4} (1/i!) (ln(M⁻¹ h))^i` if `h > M`. -/
noncomputable def smoothTrunc (M h : ℝ) : ℝ :=
  if h ≤ M then h
  else M * ∑ i ∈ Finset.range 5, (1 / (i.factorial : ℝ)) * Real.log (M⁻¹ * h) ^ i

/-- `G^(M)(θ, Λ)` (§5.2, p.8), the smooth truncation of `H(θ, Λ)`, as a function of the excursion.
This is the smooth truncation of §5.2, not the hard truncation of §3. -/
noncomputable def Model.G (m : Model X l) (M : ℝ) (θ : Param l) (Λ : ℝ) (e : List X) : ℝ :=
  smoothTrunc M (m.H θ Λ e)

/-- `∇_θ H(θ, Λ) = H(θ, Λ) Σ_{i=0}^{τ_{x*}-1} α ∇_θ C_θ(Φᵢ)`, as a function of the excursion. -/
noncomputable def Model.gradH (m : Model X l) (θ : Param l) (Λ : ℝ) (e : List X) : Param l :=
  m.H θ Λ e • ((m.xstar :: e).map fun y => m.α • gradient (fun θ' => m.C θ' y) θ).sum

/-- `F^(M)(θ, Λ)` in the second display of its definition (pp.8–9):
`G^(M) Σ_{i=0}^{τ_{x*}-1} L_θ(Φᵢ, Φᵢ₊₁) + ∇_θ H 1{H ≤ M}
  + M (∇_θ H / H) [Σ_{i=0}^{3} (1/i!) (ln(M⁻¹ H))^i] 1{H > M}`.
The sum of `L` runs over the `τ` transitions of the cycle, including the last one into `x*`. Here
`Λ` is held fixed, so this is not the gradient of `Λ^(M)_θ`. -/
noncomputable def Model.F (m : Model X l) (M : ℝ) (θ : Param l) (Λ : ℝ) (e : List X) : Param l :=
  m.G M θ Λ e • sumPairs (m.L θ) m.xstar (e ++ [m.xstar]) +
    if m.H θ Λ e ≤ M then m.gradH θ Λ e
    else (M / m.H θ Λ e *
        ∑ i ∈ Finset.range 4, (1 / (i.factorial : ℝ)) * Real.log (M⁻¹ * m.H θ Λ e) ^ i) •
      m.gradH θ Λ e

/-- `g(θ, Λ) := E^θ_{Φ₀ = x*}[exp(Σ_{i=0}^{τ_{x*}-1} (α C_θ(Φᵢ) - Λ))]` (p.4), with values in
`(0, ∞]`. -/
noncomputable def Model.g (m : Model X l) (θ : Param l) (Λ : ℝ) : ℝ≥0∞ :=
  excursionExp (m.P θ) m.xstar m.xstar fun e => ENNReal.ofReal (m.H θ Λ e)

/-- `g^(M)(θ, Λ) := E^θ_{Φ₀ = x*}[G^(M)(θ, Λ)]` (§5.2, p.8), in `ℝ≥0∞`. -/
noncomputable def Model.gTrunc (m : Model X l) (M : ℝ) (θ : Param l) (Λ : ℝ) : ℝ≥0∞ :=
  excursionExp (m.P θ) m.xstar m.xstar fun e => ENNReal.ofReal (m.G M θ Λ e)

/-- `g` as a real-valued function on `ℝ^{l+1}`. It is differentiated only where `g < ∞`. -/
noncomputable def Model.gReal (m : Model X l) (r : Param l × ℝ) : ℝ :=
  (m.g r.1 r.2).toReal

/-- `g^(M)` as a real-valued function on `ℝ^{l+1}`. -/
noncomputable def Model.gTruncReal (m : Model X l) (M : ℝ) (r : Param l × ℝ) : ℝ :=
  (m.gTrunc M r.1 r.2).toReal

/-- `f^(M)(θ, Λ) := E^θ_{Φ₀ = x*}[F^(M)(θ, Λ)]` (§5.2, p.8). -/
noncomputable def Model.fTrunc (m : Model X l) (M : ℝ) (θ : Param l) (Λ : ℝ) : Param l :=
  excursionMean (m.P θ) m.xstar m.xstar (m.F M θ Λ)

/-- `Λ^(M)_θ`, "the unique solution of `g^(M)(θ, Λ) = 1`" (§5.2, p.8), as a total function.

**Formalization Note** The set `{Λ | g^(M)(θ, Λ) ≤ 1}` is a half-line starting at the solution, so
its infimum is the solution. Corollary 14 proves, as its first clause, that for `M > 1` the
equation has a unique solution and that this function is that solution. This is the smooth
truncation of §5.2, which is the one meant in Assumption 4 and Theorem 1. -/
noncomputable def Model.truncCost (m : Model X l) (M : ℝ) (θ : Param l) : ℝ :=
  sInf {Λ | m.gTrunc M θ Λ ≤ 1}

/-- The risk-sensitive relative value function `h_θ` of Eq. (2) (p.3), with the normalization given
by Eq. (3) (`h_θ(x*) = 1`): `h_θ(x) = E^θ_{Φ₀ = x}[exp(Σ_{i=0}^{τ_{x*}-1} (α C_θ(Φᵢ) - Λ_θ))]`. -/
noncomputable def Model.relValue [Fintype X] (m : Model X l) (θ : Param l) (x : X) : ℝ :=
  (cycleMgf (m.P θ) (m.C θ) m.α m.xstar (m.riskCost θ) x).toReal

/-- The twisted kernel `P̌_θ(x, y) := exp(α C_θ(x)) P_θ(x, y) h_θ(y) / (λ_θ h_θ(x))` of p.4, with
`λ_θ = exp(Λ_θ)`. -/
noncomputable def Model.twisted [Fintype X] (m : Model X l) (θ : Param l) : Matrix X X ℝ :=
  Matrix.of fun x y =>
    Real.exp (m.α * m.C θ x) * m.P θ x y * m.relValue θ y /
      (Real.exp (m.riskCost θ) * m.relValue θ x)

/-- `Σ_{i=0}^{τ_{x*}-1} (α ∇_θ C_θ(Φᵢ) + L_θ(Φᵢ, Φᵢ₊₁))`, the sum in Lemma 14 (p.40), as a function
of the excursion from `x*`. -/
noncomputable def Model.score (m : Model X l) (θ : Param l) (e : List X) : Param l :=
  sumPairs (fun a b => m.α • gradient (fun θ' => m.C θ' a) θ + m.L θ a b) m.xstar (e ++ [m.xstar])

/-- **Assumption 4** (p.10) for a sequence `N`: `N_i ↑ ∞`, each `N_i > 1` (§5.2 defines everything
for `M > 1`), and `Σ_i sup_θ (Λ^(N_{i+1})_θ - Λ^(N_i)_θ) < ∞`.

**Formalization Note** The sum of suprema is written through a summable majorant `d`, which avoids a
real `⨆` of a family not known to be bounded. Since the differences are nonnegative
(Corollary 14), this is equivalent to the printed condition. -/
def Model.Assumption4 (m : Model X l) (N : ℕ → ℝ) : Prop :=
  Monotone N ∧ Tendsto N atTop atTop ∧ (∀ i, 1 < N i) ∧
    ∃ d : ℕ → ℝ, Summable d ∧ ∀ i θ, m.truncCost (N (i + 1)) θ - m.truncCost (N i) θ ≤ d i

/-- **Assumption 5** (p.11): `Σ_m γ_m = ∞`, `Σ_m γ_m² < ∞` and `γ_max := sup_m γ_m < 1`, for a
sequence of positive step sizes.

**Formalization Note** Positivity is what "step-size sequence" means here: Theorem 1(ii) writes
`1/γ_m^β`. Given positivity, `¬ Summable γ` is `Σ_m γ_m = ∞`. -/
def Assumption5 (γ : ℕ → ℝ) : Prop :=
  (∀ k, 0 < γ k) ∧ ¬ Summable γ ∧ Summable (fun k => γ k ^ 2) ∧ ∃ c < 1, ∀ k, γ k ≤ c

end RiskExpPG


