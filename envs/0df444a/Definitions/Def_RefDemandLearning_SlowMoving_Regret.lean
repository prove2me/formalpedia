-- Prove2me | Definitions.Def_RefDemandLearning_SlowMoving_Regret
-- name    : RefDemandLearning_SlowMoving_Regret
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:24:13.990995+00:00
-- url     : https://prove2.me/theorems/3cf3417e-3667-40ef-83be-2460d6265e24
-- title:
--   Dynamic clairvoyant benchmark and expected regret
-- statement:
--   For the demand model and a continuous reference mechanism, define the dynamic clairvoyant benchmark at horizon $T$ by
--   $$\Pi^*(T,\rho,\theta)=\sup_{(p_1,\ldots,p_T)\in[\ell,u]^T}\sum_{t=1}^{T}R(p_t,\rho_t(p_1,\ldots,p_{t-1}),\theta).$$
--   For a fixed feasible price $p$, define $\Pi_{\mathrm{fixed}}(p;T,\rho,\theta)$ by evaluating this cumulative revenue on the constant path, and set $\Delta_{\mathrm{fixed}}=\Pi^*-\Pi_{\mathrm{fixed}}$. For the actual two-block policy run on iid shocks, define
--   $$\Delta_S(T,\rho,\theta)=\Pi^*(T,\rho,\theta)-\mathbb E\!\left[\sum_{t=1}^{T}R(p_t,r_t,\theta)\right].$$
--   This benchmark optimizes over all dynamic real price vectors, with full knowledge of $\rho,\theta$. It is not a fixed-price benchmark. The expected revenue uses expected demand, as in (2.8).
--
--   **Formalization Note.** The finite price box is nonempty and compact, and its continuous revenue image is bounded, so the real supremum is finite. Under the standing assumptions and admissible tuning, the generated prices lie in the interval. The finite-horizon random revenue is measurable and bounded, hence integrable under a probability measure. The Bochner integral therefore cannot return a spurious zero from nonintegrability. At $T=0$ both cumulative revenues and regret are zero, although the theorems retain $T\ge1$. The fixed-price definition is used only at a feasible price; clipping in reference inputs is then the identity.
--
--   The generated price path is interval-valued by construction and is passed directly to the reference mechanism.
-- source:
--   den Boer and Keskin, Dynamic Pricing with Demand Learning and Reference Effects, DOI https://doi.org/10.1287/mnsc.2021.4234, supplied April 19, 2021 artifact, Section 2, printed/PDF p. 9, (2.7)–(2.8); Section 3.1, printed/PDF p. 10

import Definitions.Def_RefDemandLearning_SlowMoving_Policy
import Definitions.Def_RefDemandLearning_SlowMoving_Noise

set_option autoImplicit false
open MeasureTheory

noncomputable section

namespace RefDemandLearning.SlowMoving

/-- Dynamic benchmark: supremum over the entire real price box of length T. -/
def benchmark (B : Bounds) (ρ : Mechanism B.prices) (θ : Parameters) (T : ℕ) : ℝ :=
  ⨆ p : Fin T → Price B.prices,
    ∑ j : Fin T, revenue θ (p j) (ρ.ref j.val (fun k => p ⟨k.val, lt_trans k.isLt j.isLt⟩))

def fixedRevenue (B : Bounds) (ρ : Mechanism B.prices) (θ : Parameters)
    (p : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Finset.range T, revenue θ p (reference ρ (fun _ => clipPrice B.prices p) n)

def fixedRegret (B : Bounds) (ρ : Mechanism B.prices) (θ : Parameters)
    (p : ℝ) (T : ℕ) : ℝ := benchmark B ρ θ T - fixedRevenue B ρ θ p T

def runRevenue (B : Bounds) (ρ : Mechanism B.prices) (θ : Parameters)
    (c₀ a₀ b₀ : ℝ) (e : ℕ → ℝ) (T : ℕ) : ℝ :=
  let p := pricePath B ρ θ c₀ a₀ b₀ e
  ∑ n ∈ Finset.range T, revenue θ (p n)
    (reference ρ p n)

def regret (B : Bounds) (ρ : Mechanism B.prices) (θ : Parameters)
    (c₀ a₀ b₀ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ε : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  benchmark B ρ θ T - ∫ ω, runRevenue B ρ θ c₀ a₀ b₀ (fun n => ε n ω) T ∂P

end RefDemandLearning.SlowMoving


