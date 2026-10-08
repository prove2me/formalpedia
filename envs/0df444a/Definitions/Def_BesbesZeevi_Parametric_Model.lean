-- Prove2me | Definitions.Def_BesbesZeevi_Parametric_Model
-- name    : BesbesZeevi_Parametric_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:42:59.356422+00:00
-- url     : https://prove2.me/theorems/7f24fcc6-ac30-4598-8425-3c55e9e306da
-- title:
--   Parametric demand family and deterministic relaxation
-- statement:
--   A market has positive horizon $T$, initial stock $x$, ordinary prices in $[\underline p,\overline p]$, and a demand-stopping price $p_\infty$. A regular demand curve has an inverse $\gamma$, concave rate revenue $r(\ell)=\ell\gamma(\ell)$, and the uniform bounds of Assumption 1. The parameter set $\Theta\subseteq\mathbb R^k$ is nonempty, compact, and convex; every curve $\lambda(\cdot;\theta)$ belongs to the same regular class. Assumption 2 supplies distinct test prices, a Lipschitz inverse $g$ for their rate vector, differentiability of square-root rates, and a parameter Lipschitz bound.
--
--   $$J^D(x,T\mid\theta)=\sup_{p(\cdot)}\left\{\int_0^T p(t)\lambda(p(t);\theta)\,dt:\int_0^T\lambda(p(t);\theta)\,dt\le x\right\}.$$
--
--   The supremum ranges over measurable admissible price paths, including $p_\infty$. **Formalization Note** The $k$-coordinate norm is the sup norm. The map $g$ returns a parameter in $\Theta$ and recovers every true parameter from its test-price rate vector; this is the bounded-domain interpretation of the printed Assumption 2(i)b. The scaled benchmark substitutes $n\lambda$ and $nx$.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 6 (PDF p. 8), §3 regular demand and prices; p. 8 (PDF p. 10), Eq. (5); p. 11 (PDF p. 13), Assumption 1; p. 15 (PDF p. 17), Assumption 2

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess

namespace BesbesZeevi.Parametric

open MeasureTheory

/-- Fixed market parameters and the common constants in Assumption 1. -/
structure Market where
  pLo : ℝ
  pHi : ℝ
  pOff : ℝ
  x : ℝ
  T : ℝ
  M : ℝ
  KLo : ℝ
  KHi : ℝ
  m : ℝ
  pLo_pos : 0 < pLo
  price_order : pLo < pHi
  pOff_pos : 0 < pOff
  x_pos : 0 < x
  T_pos : 0 < T
  M_pos : 0 < M
  KLo_pos : 0 < KLo
  K_order : KLo ≤ KHi
  m_pos : 0 < m

/-- Regular demand and Assumption 1, with the inverse explicitly supplied. Its
conditions only apply to the admissible price and rate intervals. -/
def IsRegularDemand (D : Market) (lam γ : ℝ → ℝ) : Prop :=
  lam D.pOff = 0 ∧
  (∀ p ∈ Set.Icc D.pLo D.pHi, 0 ≤ lam p ∧ lam p ≤ D.M) ∧
  (∀ p ∈ Set.Icc D.pLo D.pHi, ∀ q ∈ Set.Icc D.pLo D.pHi,
    p ≤ q → lam q ≤ lam p) ∧
  (∀ p ∈ Set.Icc D.pLo D.pHi, γ (lam p) = p) ∧
  (∀ l ∈ Set.Icc (lam D.pHi) (lam D.pLo),
    γ l ∈ Set.Icc D.pLo D.pHi ∧ lam (γ l) = l) ∧
  ConcaveOn ℝ (Set.Icc (lam D.pHi) (lam D.pLo)) (fun l => l * γ l) ∧
  (∀ p ∈ Set.Icc D.pLo D.pHi, ∀ q ∈ Set.Icc D.pLo D.pHi,
    |lam p - lam q| ≤ D.KHi * |p - q|) ∧
  (∀ l ∈ Set.Icc (lam D.pHi) (lam D.pLo),
    ∀ l' ∈ Set.Icc (lam D.pHi) (lam D.pLo),
      |γ l - γ l'| ≤ D.KLo⁻¹ * |l - l'|) ∧
  (∃ p ∈ Set.Icc D.pLo D.pHi, D.m ≤ p * lam p)

/-- The paper's parametric family, including Assumption 2. The inverse `g`
projects estimates into `Θ`; this makes Assumption 2(ii) applicable to the estimate. -/
structure Family (k : ℕ) (D : Market) where
  k_pos : 0 < k
  Θ : Set (Fin k → ℝ)
  theta_nonempty : Θ.Nonempty
  theta_convex : Convex ℝ Θ
  theta_compact : IsCompact Θ
  demand : ℝ → (Fin k → ℝ) → ℝ
  inverse : ℝ → (Fin k → ℝ) → ℝ
  regular : ∀ θ ∈ Θ, IsRegularDemand D (fun p => demand p θ) (fun l => inverse l θ)
  testPrice : Fin k → ℝ
  test_range : ∀ i, testPrice i ∈ Set.Icc D.pLo D.pHi
  test_distinct : Function.Injective testPrice
  l0 : ℝ
  l0_pos : 0 < l0
  test_positive : ∀ i θ, θ ∈ Θ → l0 < demand (testPrice i) θ
  g : (Fin k → ℝ) → (Fin k → ℝ)
  g_range : ∀ d, g d ∈ Θ
  g_left_inverse : ∀ θ, θ ∈ Θ → g (fun i => demand (testPrice i) θ) = θ
  g_measurable : Measurable g
  alpha : ℝ
  alpha_pos : 0 < alpha
  g_lipschitz : ∀ d e, ‖g d - g e‖ ≤ alpha * ‖d - e‖
  sqrt_differentiable : ∀ i, DifferentiableOn ℝ
    (fun θ => Real.sqrt (demand (testPrice i) θ)) Θ
  K2 : ℝ
  K2_pos : 0 < K2
  parameter_lipschitz : ∀ p ∈ Set.Icc D.pLo D.pHi,
    ∀ θ ∈ Θ, ∀ θ' ∈ Θ,
      |demand p θ - demand p θ'| ≤ K2 * ‖θ - θ'‖

/-- Admissible measurable paths for the deterministic relaxation (5). -/
def DetFeasible (D : Market) (lam : ℝ → ℝ) (stock : ℝ) (p : ℝ → ℝ) : Prop :=
  Measurable p ∧
  (∀ t ∈ Set.Icc (0 : ℝ) D.T,
    p t ∈ Set.Icc D.pLo D.pHi ∨ p t = D.pOff) ∧
  IntegrableOn (fun t => lam (p t)) (Set.Icc (0 : ℝ) D.T) ∧
  IntegrableOn (fun t => p t * lam (p t)) (Set.Icc (0 : ℝ) D.T) ∧
  (∫ t in Set.Icc (0 : ℝ) D.T, lam (p t)) ≤ stock

/-- Equation (5), as the supremum over feasible measurable price paths. -/
noncomputable def jDet (D : Market) (lam : ℝ → ℝ) (stock : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ p : ℝ → ℝ, DetFeasible D lam stock p ∧
    v = ∫ t in Set.Icc (0 : ℝ) D.T, p t * lam (p t)}

/-- The deterministic benchmark in the market with inventory `nx` and rate `nlam`. -/
noncomputable def jDetScaled {k : ℕ} (D : Market) (F : Family k D)
    (θ : Fin k → ℝ) (n : ℕ) : ℝ :=
  jDet D (fun p => (n : ℝ) * F.demand p θ) ((n : ℝ) * D.x)

end BesbesZeevi.Parametric


