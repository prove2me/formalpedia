-- Prove2me | Definitions.Def_PrivateRoutingSignaling_PTAS_Signaling
-- name    : PrivateRoutingSignaling_PTAS_Signaling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T14:51:58.431187+00:00
-- url     : https://prove2.me/theorems/f97059f2-63d8-4dee-bf40-0cf9f77b3707
-- title:
--   Joint Borel signaling measures, weighted obedience, and the exact optimum
-- statement:
--   Let $\Theta$ be a finite nonempty state set with prior $\lambda$, and let each state's arc latencies be nonnegative, nondecreasing, continuous, and $L$-Lipschitz on $[0,1]$. The model places no restriction on values outside that load interval. A scheme is a Borel probability measure $\varphi$ on $\Theta\times\Delta_P$ with exactly the given state marginal. Zero-prior states are allowed.
--
--   Path latency and total flow cost use the published unrestricted routing sums. Define
--
--   $$\operatorname{SC}(\varphi)=\int\sum_p s_p c_p^\theta(s)\,d\varphi,\qquad \operatorname{OPT}=\inf_{\varphi\text{ exactly IC}}\operatorname{SC}(\varphi).$$
--
--   The relaxed obedience condition is $\int s_p(c_q^\theta(s)+\varepsilon-c_p^\theta(s))\,d\varphi\ge0$ for every $p\ne q$. Bicriteria approximation requires this and $\operatorname{SC}(\varphi)\le\operatorname{OPT}+\varepsilon$. The exact benchmark ranges over all such Borel schemes, without a finite-support or rational restriction.
--
--   The infimum uses extended reals, retaining empty and unbounded cases rather than replacing them by zero. A separate well-posedness predicate collects conclusions: valid arc-load ranges, integrability of all cost and obedience terms for every scheme, and finite attained exact optimum. These are obligations of the goal, never assumptions about its input. No special arithmetic on infinite differences is used.
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #439 (October 2026), §§2.1–2.3, pp. 5–8 (PDF pp. 5–8), especially the attainment discussion on pp. 7–8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/439.pdf

import Mathlib
import Definitions.Def_PrivateRoutingSignaling_PTAS_Network

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory

namespace PrivateRoutingSignaling.PTAS

/-- Mathematical instance. The prior and flow distributions are not restricted to rational support. -/
structure Instance where
  network : RoutingNetwork
  states : ℕ
  prior : Fin states → ℝ
  latency : Fin states → Fin network.arcs → ℝ → ℝ

abbrev Outcome (I : Instance) := Fin I.states × Flow I.network
abbrev Scheme (I : Instance) := Measure (Outcome I)

/-- The source's standing assumptions, only on the valid arc-load interval [0,1]. -/
def Standing (I : Instance) (L : ℝ) : Prop :=
  NetworkValid I.network ∧ 0 < I.states ∧ FiniteLaw I.prior ∧ 0 ≤ L ∧
  ∀ θ i, (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ I.latency θ i x) ∧
    MonotoneOn (I.latency θ i) (Set.Icc 0 1) ∧
    ContinuousOn (I.latency θ i) (Set.Icc 0 1) ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |I.latency θ i x - I.latency θ i y| ≤ L * |x - y|

def pathCost (I : Instance) (θ : Fin I.states) (s : Path I.network → ℝ)
    (p : Path I.network) : ℝ :=
  SelfishRouting.Bicriteria.pathLatency (incidence I.network) (I.latency θ) s p

def flowCost (I : Instance) (θ : Fin I.states) (s : Path I.network → ℝ) : ℝ :=
  SelfishRouting.Bicriteria.cost (incidence I.network) (I.latency θ) s

/-- Joint Borel probability measure, including zero-probability states. -/
def IsScheme (I : Instance) (φ : Scheme I) : Prop :=
  φ Set.univ = 1 ∧ ∀ θ, φ {z | z.1 = θ} = ENNReal.ofReal (I.prior θ)

/-- Probability weighting is inside the relaxed obedience integrand. -/
def icTerm (I : Instance) (ε : ℝ) (p q : Path I.network) (z : Outcome I) : ℝ :=
  z.2.val p * (pathCost I z.1 z.2.val q + ε - pathCost I z.1 z.2.val p)

def Obedient (I : Instance) (ε : ℝ) (φ : Scheme I) : Prop :=
  ∀ p q, p ≠ q → 0 ≤ ∫ z, icTerm I ε p q z ∂φ

noncomputable def socialCost (I : Instance) (φ : Scheme I) : ℝ :=
  ∫ z, flowCost I z.1 z.2.val ∂φ

/-- Extended-real infimum retains an empty feasible set as +∞ and unboundedness as -∞.
On Standing instances the goal proves finite attainment, rather than assuming it. -/
noncomputable def optimum (I : Instance) : EReal :=
  sInf ((fun φ : Scheme I => (socialCost I φ : EReal)) ''
    {φ | IsScheme I φ ∧ Obedient I 0 φ})

def Bicriteria (I : Instance) (ε : ℝ) (φ : Scheme I) : Prop :=
  IsScheme I φ ∧ Obedient I ε φ ∧
    (socialCost I φ : EReal) ≤ optimum I + (ε : EReal)

/-- These are conclusions required of the goal, not input certificates. -/
def Wellposed (I : Instance) : Prop :=
  (∀ s : Flow I.network, ∀ i, arcLoad I.network s.val i ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ φ, IsScheme I φ → Integrable (fun z : Outcome I => flowCost I z.1 z.2.val) φ ∧
    ∀ (ε : ℝ) (p q : Path I.network), Integrable (icTerm I ε p q) φ) ∧
  ∃ φ, IsScheme I φ ∧ Obedient I 0 φ ∧ optimum I = (socialCost I φ : EReal)

end PrivateRoutingSignaling.PTAS


