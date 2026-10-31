-- Prove2me | Definitions.Def_BroadieKaya_SV_HestonModel
-- name    : BroadieKaya_SV_HestonModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:08:15.032521+00:00
-- url     : https://prove2.me/theorems/05ac6487-fda1-4e69-994e-36b54022a1fc
-- title:
--   The correlated multiplicative Heston stock-price model
-- statement:
--   Let $W^{(1)},W^{(2)}$ be independent standard Brownian motions on a usual filtered probability space. The variance follows the separately defined square-root diffusion driven by $W^{(1)}$. The stock process satisfies
--   $$dS_q=rS_q\,dq+\sqrt{V_q}S_q\bigl(\rho\,dW_q^{(1)}+\sqrt{1-\rho^2}\,dW_q^{(2)}\bigr).$$
--   The parameters obey $r\in\mathbb R$, $-1\le\rho\le1$, and the positive square-root parameter convention. The two Brownian path maps are independent; joint increments are independent of the past filtration. The stock is adapted and almost surely continuous, and its integral equation uses two local Itô integrals of $\sqrt V S$.
--
--   This model is built on the general square-root SDE definition. The stock is not defined by its exponential solution. There is no assumed correct sampler, conditional normal law, transform formula, exponential moment bound, or stock-integrand global $L^2$ condition. Starting stock positivity is imposed by the stock-price theorems rather than baked into the SDE predicate.
-- source:
--   Broadie and Kaya, Exact Simulation of Stochastic Volatility and Other Affine Jump Diffusion Processes, Operations Research 54(2), 217–231 (2006), published version, https://doi.org/10.1287/opre.1050.0247; §2.1, (1)–(2), p. 218 (PDF 2)

import Definitions.Def_BroadieKaya_SV_SquareRootProcesses

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace BroadieKaya.SV


structure HestonParameters where
  cir : CIRParameters
  r : ℝ
  rho : ℝ

def HestonParameters.Valid (p : HestonParameters) : Prop :=
  p.cir.Valid ∧ -1 ≤ p.rho ∧ p.rho ≤ 1

/-- Equations (1)-(2), with a two-dimensional Brownian driver relative to F.
No terminal law, exponential solution, or sampler correctness is assumed. -/
def IsHeston {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (p : HestonParameters) (P : Measure Ω) (F : Filtration ℝ mΩ)
    (W₁ W₂ S V : ℝ → Ω → ℝ) (u t : ℝ) : Prop :=
  IsCIR p.cir P F W₁ V u t ∧
  EntropyMFG.Enhanced.BrownianOn P F W₂ t ∧
  IndepFun (fun ω => fun z : Icc 0 t => W₁ z ω)
    (fun ω => fun z : Icc 0 t => W₂ z ω) P ∧
  (∀ a ∈ Icc 0 t, ∀ b ∈ Icc a t,
    Indep (MeasurableSpace.comap
      (fun ω => (W₁ b ω - W₁ a ω, W₂ b ω - W₂ a ω)) inferInstance) (F a) P) ∧
  (∀ z ∈ Icc u t, Measurable[F z] (S z)) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun z => S z ω) (Icc u t)) ∧
  ∃ J₁ J₂ : ℝ → Ω → ℝ,
    EntropyMFG.Enhanced.HasItoIntegral P F W₁ u t
      (fun z ω => Real.sqrt (V z ω) * S z ω) J₁ ∧
    EntropyMFG.Enhanced.HasItoIntegral P F W₂ u t
      (fun z ω => Real.sqrt (V z ω) * S z ω) J₂ ∧
    ∀ᵐ ω ∂P, ∀ z ∈ Icc u t,
      S z ω = S u ω + (∫ q in Icc u z, p.r * S q ω) +
        p.rho * J₁ z ω + Real.sqrt (1-p.rho^2) * J₂ z ω

end BroadieKaya.SV


