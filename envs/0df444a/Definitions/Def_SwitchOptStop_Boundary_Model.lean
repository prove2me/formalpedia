-- Prove2me | Definitions.Def_SwitchOptStop_Boundary_Model
-- name    : SwitchOptStop_Boundary_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:49.489611+00:00
-- url     : https://prove2.me/theorems/3060e808-8360-4ffe-be14-6b7164215162
-- title:
--   §1–§2, pp. 1–4 — generator Q, coefficients a^i, b^{ij}, σ^i, λ, cost H, Assumptions 2.1–2.2, H̲, and the SDE (2.2) setting
-- statement:
--   The regime-switching linear diffusion of Ernst and Mei. Let $M=\{1,2\}$ be the regimes and $x=(x_1,x_2)\in[0,\infty)^2$. The data are a generator $Q=(q_{\iota\kappa})$ (off-diagonal entries $\ge0$, rows summing to $0$), coefficients $a^i(\iota)$, $b^{ij}(\iota)$, $\sigma^i(\iota)$, a discount rate $\lambda(\iota)$ and a running cost $H(\iota,x)$ on $[0,\infty)^2$.
--
--   **Assumption 2.1.** $\lambda(\iota)>0$, $a^i(\iota)\ge0$, $\sigma^i(\iota)\neq0$ for all $\iota,i$, and $b^{ij}(\iota)\ge0$ for $i\ne j$.
--
--   **Assumption 2.2.** Each $H(\iota,\cdot)$ is concave on $[0,\infty)^2$, locally Lipschitz up to the boundary, increasing in each variable, and $\lim_{z\to\infty}H(\iota,(z,0))=\lim_{z\to\infty}H(\iota,(0,z))=\infty$.
--
--   Set $\underline H=\min_\iota H(\iota,(0,0))$ and $H^N(\iota,x)=\min(H(\iota,x),N)$ (2.8).
--
--   **Setting.** On one probability space, $\alpha$ is a two-state Markov chain with generator $Q$, $W=(W^1,W^2)$ are independent Brownian motions independent of $\alpha$, $\mathbb F$ is the augmented filtration of $(\alpha,W)$, and for every $x\in[0,\infty)^2$ the process $X=X^x$ solves
--   $$
--   dX^i_t=\Big(a^i(\alpha_t)+\sum_{j=1}^2 b^{ij}(\alpha_t)X^j_t\Big)dt+\sigma^i(\alpha_t)X^i_t\,dW^i_t,\qquad X_0=x,\quad i=1,2, \tag{2.2}
--   $$
--   while for every $z\ge0$ the one-dimensional process $\tilde X^i$ solves $d\tilde X^i_t=(a^i(\alpha_t)+b^{ii}(\alpha_t)\tilde X^i_t)dt+\sigma^i(\alpha_t)\tilde X^i_t\,dW^i_t$, $\tilde X^i_0=z$. The stopping times of the problem are those of the natural filtration of $(\alpha,X^x)$ (resp. $(\alpha,\tilde X^{1})$), augmented with the null sets.
--
--   This is the model in which every result of the mission is stated.
--
--   **Formalization Note** Regimes and coordinates are `Fin 2`, 0-based: `x 0` is $x_1$, regime `0` is state 1. The SDEs are required in integral form, $P$-a.s. for all $t$, with continuous paths for every $\omega$; the stochastic integrals are the published relation `EthierKurtz.HasBrownianItoIntegral`. $P$ is assumed complete (the paper augments with all null sets), and both initial regimes have positive probability so that conditioning on $\alpha_0=\iota$ is defined. "Locally Lipschitz up to the boundary" is read as Lipschitz on every bounded part $[0,\infty)^2\cap\{x_i\le K\}$, which for the closed convex quadrant is equivalent. Existence of such a setting is the standard strong existence for SDEs with Lipschitz coefficients, cited on p. 3; it is not proved here.
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, pp. 1–5, (2.2), Assumptions 2.1–2.2, H̲ (p. 4), Assumption 2.3's SDE (p. 4), (2.8)

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_SwitchOptStop_Boundary_Basics

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- A point `x = (x₁, x₂)` of the plane; `x 0` is the paper's `x₁` and `x 1` is `x₂`. -/
abbrev Pt := Fin 2 → ℝ

/-- The closed quadrant `[0, ∞)²`. -/
def quadrant : Set Pt := {x | ∀ i, 0 ≤ x i}

/-- The open quadrant `(0, ∞)²`. -/
def openQuadrant : Set Pt := {x | ∀ i, 0 < x i}

/-- The data of the model (1.1)–(1.2), (2.1)–(2.2). Regimes and coordinates are both `Fin 2`, 0-based:
regime `0` is the paper's state 1, regime `1` its state 2.
* `q ι κ` is the generator entry `q_{ικ}` of the chain `α`;
* `a ι i` is `a^i(ι)`, `b ι i j` is `b^{ij}(ι)`, `σ ι i` is `σ^i(ι)` (coefficients of (2.2));
* `lam ι` is the discount rate `λ(ι)`;
* `H ι x` is the running cost `H(ι, x)`, which the paper defines (and which is read here) on
  `[0, ∞)²` only. -/
structure Model where
  q : Fin 2 → Fin 2 → ℝ
  a : Fin 2 → Fin 2 → ℝ
  b : Fin 2 → Fin 2 → Fin 2 → ℝ
  σ : Fin 2 → Fin 2 → ℝ
  lam : Fin 2 → ℝ
  H : Fin 2 → Pt → ℝ

/-- `Q` is the generator of a continuous-time Markov chain on `M`: off-diagonal entries are
nonnegative and every row sums to zero (p. 3). -/
def IsGenerator (m : Model) : Prop :=
  (∀ ι κ, ι ≠ κ → 0 ≤ m.q ι κ) ∧ ∀ ι, ∑ κ, m.q ι κ = 0

/-- Assumption 2.1 (p. 3): `λ(ι) > 0`, `a^i(ι) ≥ 0`, `σ^i(ι) ≠ 0` for all `ι, i`, and
`b^{ij}(ι) ≥ 0` for `i ≠ j`. -/
def Assumption21 (m : Model) : Prop :=
  (∀ ι, 0 < m.lam ι) ∧ (∀ ι i, 0 ≤ m.a ι i ∧ m.σ ι i ≠ 0) ∧ ∀ ι i j, i ≠ j → 0 ≤ m.b ι i j

/-- Assumption 2.2 (p. 4): for each regime `ι`, `H(ι, ·)` is concave on `[0, ∞)²`, locally Lipschitz
up to the boundary of `[0, ∞)²` (read: Lipschitz on every bounded part `[0, K]²` of the closed
quadrant), increasing in each variable (monotone for the coordinatewise order on `[0, ∞)²`), and
`H(ι, (z, 0)) → ∞`, `H(ι, (0, z)) → ∞` as `z → ∞`. -/
def Assumption22 (m : Model) : Prop :=
  ∀ ι,
    ConcaveOn ℝ quadrant (m.H ι) ∧
    (∀ K : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L (m.H ι) (quadrant ∩ {x | ∀ i, x i ≤ K})) ∧
    MonotoneOn (m.H ι) quadrant ∧
    Tendsto (fun z : ℝ => m.H ι ![z, 0]) atTop atTop ∧
    Tendsto (fun z : ℝ => m.H ι ![0, z]) atTop atTop

/-- `H̲ := min_ι H(ι, (0, 0))` (p. 4). -/
noncomputable def Hlow (m : Model) : ℝ := min (m.H 0 0) (m.H 1 0)

/-- The truncated cost `H^N(ι, x) = min(H(ι, x), N)` of (2.8). -/
noncomputable def HN (m : Model) (N : ℝ) (ι : Fin 2) (x : Pt) : ℝ := min (m.H ι x) N

/-- The random objects on one probability space `(Ω, P)`:
* `α t ω` is the regime chain `α_t`;
* `W i` is the Brownian motion `W^{i+1}`;
* `X x t ω` is the solution `X_t` of (2.2) started at `X_0 = x` (one flow `x ↦ X x`, read for
  `x ∈ [0, ∞)²`);
* `Xt i z t ω` is the one-dimensional process `X̃^{i+1}_t` of Assumption 2.3 started at `z ≥ 0`
  (`Xt 0 z` is the `X̃¹` of (2.7));
* `𝔽` is the filtration of `(α, W)` (the filtration of the SDEs);
* `𝔾 x` is the natural filtration of `(α, X x)`, augmented with the null sets: `T_{α,X}` of (2.1),
  (3.4) is the class of `𝔾 x`-stopping times;
* `𝔾₁ z` is the augmented natural filtration of `(α, Xt 0 z)`: the stopping times of (2.7). -/
structure Setting (Ω : Type) [mΩ : MeasurableSpace Ω] where
  P : Measure Ω
  α : ℝ≥0 → Ω → Fin 2
  W : Fin 2 → ℝ≥0 → Ω → ℝ
  X : Pt → ℝ≥0 → Ω → Pt
  Xt : Fin 2 → ℝ → ℝ≥0 → Ω → ℝ
  𝔽 : Filtration ℝ≥0 mΩ
  𝔾 : Pt → Filtration ℝ≥0 mΩ
  𝔾₁ : ℝ → Filtration ℝ≥0 mΩ

/-- The standing probabilistic setting of §§1–2 (pp. 1–4):
1. `P` is a complete probability measure, and both initial regimes have positive probability (so
   that `P_{ι,x}` is defined);
2. `α` is a two-state Markov chain with generator `Q` with respect to `𝔽`;
3. `W⁰, W¹` are `𝔽`-Brownian motions, independent of each other, and the pair is independent of
   the chain `α` (as path-valued random variables);
4. `𝔽`, `𝔾 x`, `𝔾₁ z` are the natural filtrations of `(α, W⁰, W¹)`, `(α, X x)` and `(α, Xt 0 z)`,
   each augmented with the `P`-null sets;
5. for every `x ∈ [0, ∞)²`, `X x` has continuous paths, is `𝔽`-adapted and solves (2.2) in integral
   form: there are continuous Itô integrals `J^i = ∫₀^· σ^i(α_u) X^i_u dW^i_u` (the platform relation
   `EthierKurtz.HasBrownianItoIntegral`) with, `P`-a.s. for all `t`,
   `X^i_t = x_i + ∫₀ᵗ (a^i(α_u) + Σ_j b^{ij}(α_u) X^j_u) du + J^i_t`;
6. for every `z ≥ 0` and `i`, `Xt i z` has continuous paths, is `𝔽`-adapted and solves
   `dX̃^i = (a^i(α) + b^{ii}(α) X̃^i) dt + σ^i(α) X̃^i dW^i`, `X̃^i_0 = z`, in the same sense. -/
def IsSetting (m : Model) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) : Prop :=
  IsProbabilityMeasure S.P ∧ S.P.IsComplete ∧
  (∀ ι : Fin 2, 0 < S.P {ω | S.α 0 ω = ι}) ∧
  IsTwoStateChain S.P S.𝔽 m.q S.α ∧
  (∀ i, IsFBrownian S.P S.𝔽 (S.W i)) ∧
  IndepFun (fun ω t => S.W 0 t ω) (fun ω t => S.W 1 t ω) S.P ∧
  IndepFun (fun ω (p : Fin 2 × ℝ≥0) => S.W p.1 p.2 ω) (fun ω t => S.α t ω) S.P ∧
  (∀ t : ℝ≥0, S.𝔽 t =
    (⨆ s ≤ t, (MeasurableSpace.comap (S.α s) inferInstance
      ⊔ MeasurableSpace.comap (S.W 0 s) inferInstance
      ⊔ MeasurableSpace.comap (S.W 1 s) inferInstance))
    ⊔ MeasurableSpace.generateFrom {A | MeasurableSet A ∧ S.P A = 0}) ∧
  (∀ (x : Pt) (t : ℝ≥0), S.𝔾 x t =
    (⨆ s ≤ t, (MeasurableSpace.comap (S.α s) inferInstance
      ⊔ MeasurableSpace.comap (S.X x s) inferInstance))
    ⊔ MeasurableSpace.generateFrom {A | MeasurableSet A ∧ S.P A = 0}) ∧
  (∀ (z : ℝ) (t : ℝ≥0), S.𝔾₁ z t =
    (⨆ s ≤ t, (MeasurableSpace.comap (S.α s) inferInstance
      ⊔ MeasurableSpace.comap (S.Xt 0 z s) inferInstance))
    ⊔ MeasurableSpace.generateFrom {A | MeasurableSet A ∧ S.P A = 0}) ∧
  (∀ x ∈ quadrant,
    (∀ ω, Continuous fun t => S.X x t ω) ∧
    (∀ t, Measurable[S.𝔽 t] (S.X x t)) ∧
    ∃ J : Fin 2 → ℝ≥0 → Ω → ℝ,
      (∀ i ω, Continuous fun t => J i t ω) ∧
      (∀ i, EthierKurtz.HasBrownianItoIntegral S.P (fun t => S.𝔽 t) (S.W i)
        (fun t ω => m.σ (S.α t ω) i * S.X x t ω i) (J i)) ∧
      ∀ᵐ ω ∂S.P, ∀ (t : ℝ≥0) (i : Fin 2),
        S.X x t ω i = x i
          + (∫ u in (0 : ℝ)..(t : ℝ),
              (m.a (S.α u.toNNReal ω) i
                + ∑ j, m.b (S.α u.toNNReal ω) i j * S.X x u.toNNReal ω j))
          + J i t ω) ∧
  (∀ (i : Fin 2) (z : ℝ), 0 ≤ z →
    (∀ ω, Continuous fun t => S.Xt i z t ω) ∧
    (∀ t, Measurable[S.𝔽 t] (S.Xt i z t)) ∧
    ∃ J : ℝ≥0 → Ω → ℝ,
      (∀ ω, Continuous fun t => J t ω) ∧
      EthierKurtz.HasBrownianItoIntegral S.P (fun t => S.𝔽 t) (S.W i)
        (fun t ω => m.σ (S.α t ω) i * S.Xt i z t ω) J ∧
      ∀ᵐ ω ∂S.P, ∀ t : ℝ≥0,
        S.Xt i z t ω = z
          + (∫ u in (0 : ℝ)..(t : ℝ),
              (m.a (S.α u.toNNReal ω) i + m.b (S.α u.toNNReal ω) i i * S.Xt i z u.toNNReal ω))
          + J t ω)

end SwitchOptStop.Boundary


