-- Prove2me | Definitions.Def_ProbMFG_Existence_Solution
-- name    : ProbMFG_Existence_Solution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:06.01333+00:00
-- url     : https://prove2.me/theorems/e369027a-c623-4e7c-a855-a06b32d06eb2
-- title:
--   Controlled diffusion, frozen-flow FBSDE and McKean–Vlasov solution
-- statement:
--   For a measurable probability flow $\mu_t$, a controlled state $U$ follows the affine drift under a progressively measurable square-integrable control $\beta$. Its cost is
--   $$J(\beta;\mu)=\mathbb E\left[g(U_T,\mu_T)+\int_0^T f(t,U_t,\mu_t,\beta_t)\,dt\right].$$
--   A frozen-flow solution $(X,Y,Z)$ solves the coupled forward and backward stochastic equations (2.13), with the control chosen as the Hamiltonian minimizer, and satisfies the square-integrability condition (2.14). A McKean–Vlasov solution solves the same system with $\mu_t=\mathcal L(X_t)$ at every time, as required in (3.1). The file also defines continuous path laws and their time marginals.
--
--   This distinction between a prescribed flow and the law of the forward process is central to the matching problem.
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$, the Brownian filtration is augmented, and the stochastic equations use Peng's componentwise Itô predicates; Euclidean states are converted to coordinate functions at that interface. Each $X_t$ is measurable so its law is a genuine probability measure. The solution class includes continuous trajectories and the finite moment in (2.14). The path-space sigma algebra is Borel.
-- source:
--   Carmona and Delarue, Probabilistic analysis of mean-field games, SIAM J. Control Optim. 51 (2013), p. 2711, (2.12)–(2.14), (3.1), §3.2; https://doi.org/10.1137/120883499

import Mathlib
import Definitions.Def_ProbMFG_Existence_Model
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMFG.Existence

noncomputable section

variable {d m k : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- A Euclidean-state process, its adjoint, and noise-indexed matrix process. -/
abbrev StateProcess (Ω : Type*) (d : ℕ) := ℝ≥0 → Ω → State d
abbrev NoiseProcess (Ω : Type*) (d m : ℕ) := Fin m → ℝ≥0 → Ω → Fin d → ℝ

/-- The cost in (2.12), evaluated for a controlled state and an admissible control. -/
def Model.cost (M : Model d m k) (P : Measure Ω) (μ : ℝ≥0 → Measure (State d))
    (U : StateProcess Ω d) (β : ℝ≥0 → Ω → Action k) : ℝ :=
  ∫ ω, (M.g (U M.T ω) (μ M.T) +
    ∫ t in Set.Icc (0 : ℝ) M.T,
      M.f t.toNNReal (U t.toNNReal ω) (μ t.toNNReal) (β t.toNNReal ω)) ∂P

/-- The controlled SDE in (2.12) and (2.16). -/
def Model.IsControlled (M : Model d m k) (P : Measure Ω)
    {W : ℝ≥0 → Ω → Fin m → ℝ}
    (hW : Peng1990.SMP.IsStdBrownian P W)
    (μ : ℝ≥0 → Measure (State d)) (x₀' : State d)
    (U : StateProcess Ω d) (β : ℝ≥0 → Ω → Action k) : Prop :=
  Peng1990.SMP.SolvesSDE (ReflectedBSDE.Existence.augmentedFiltration P hW)
    P M.T W x₀'.ofLp
    (fun t ω x => (M.b t (WithLp.toLp 2 x) (μ t) (β t ω)).ofLp)
    (fun j _ _ _ i => M.σ i j)
    (fun t ω => (U t ω).ofLp) ∧
  (∀ t ≤ M.T, Measurable (U t)) ∧
  ∀ᵐ ω ∂P, ContinuousOn (fun t => U t ω) (Set.Iic M.T)

/-- The solution class of (2.13), including the finite-moment condition (2.14).
The equation is written through Peng's componentwise Itô-process and BSDE predicates. -/
def Model.SolvesFrozen (M : Model d m k) (P : Measure Ω)
    {W : ℝ≥0 → Ω → Fin m → ℝ}
    (hW : Peng1990.SMP.IsStdBrownian P W)
    (μ : ℝ≥0 → Measure (State d))
    (X Y : StateProcess Ω d) (Z : NoiseProcess Ω d m) : Prop :=
  M.IsFlow μ ∧
  Peng1990.SMP.SolvesSDE (ReflectedBSDE.Existence.augmentedFiltration P hW)
    P M.T W M.x₀.ofLp
    (fun t ω x =>
      (M.b t (WithLp.toLp 2 x) (μ t)
        (M.alphaHat t (WithLp.toLp 2 x) (μ t) (Y t ω))).ofLp)
    (fun j _ _ _ i => M.σ i j)
    (fun t ω => (X t ω).ofLp) ∧
  Peng1990.SMP.SolvesBSDE (ReflectedBSDE.Existence.augmentedFiltration P hW)
    P M.T W (fun ω => (M.dgx (X M.T ω) (μ M.T)).ofLp)
    (fun t ω y _ =>
      (M.dxH t (X t ω) (μ t) (WithLp.toLp 2 y)
        (M.alphaHat t (X t ω) (μ t) (WithLp.toLp 2 y))).ofLp)
    (fun t ω => (Y t ω).ofLp) Z ∧
  (∀ t ≤ M.T, Measurable (X t)) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Iic M.T) ∧
    ContinuousOn (fun t => Y t ω) (Set.Iic M.T)) ∧
  (∫⁻ ω, (⨆ t ≤ M.T, (‖X t ω‖ₑ ^ 2 + ‖Y t ω‖ₑ ^ 2)) ∂P) +
    (∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) M.T,
      ∑ j : Fin m, ‖WithLp.toLp 2 (Z j t.toNNReal ω)‖ₑ ^ 2 ∂volume ∂P) < ⊤

/-- Continuous paths on the compact time interval [0,T]. -/
abbrev Model.Path (M : Model d m k) :=
  ContinuousMap {t : ℝ≥0 // t ≤ M.T} (State d)

instance Model.pathMeasurableSpace (M : Model d m k) : MeasurableSpace M.Path :=
  borel M.Path

/-- Time marginal of a law on continuous paths, extending the flow constantly
past T solely to make it a total function on nonnegative time. -/
def Model.marginalFlow (M : Model d m k) (ν : Measure M.Path) (t : ℝ≥0) :
    Measure (State d) :=
  ν.map (fun w => w ⟨min t M.T, min_le_right t M.T⟩)

/-- Equation (3.1): the frozen flow is the law of the *same* forward process X. -/
def Model.SolvesMKV (M : Model d m k) (P : Measure Ω)
    {W : ℝ≥0 → Ω → Fin m → ℝ}
    (hW : Peng1990.SMP.IsStdBrownian P W)
    (X Y : StateProcess Ω d) (Z : NoiseProcess Ω d m) : Prop :=
  M.SolvesFrozen P hW (fun t => P.map (X t)) X Y Z

end
end ProbMFG.Existence


