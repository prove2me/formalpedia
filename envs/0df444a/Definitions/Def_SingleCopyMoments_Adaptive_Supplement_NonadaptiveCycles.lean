-- Prove2me | Definitions.Def_SingleCopyMoments_Adaptive_Supplement_NonadaptiveCycles
-- name    : SingleCopyMoments_Adaptive_Supplement_NonadaptiveCycles
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:39:24.837287+00:00
-- url     : https://prove2.me/theorems/e8e92e47-5442-41e5-a1d6-5cbe654ac734
-- title:
--   Fixed rank-one refinements and raw cycle squares
-- statement:
--   For the published physical latent prior and rank-one transcript refinement, a fixed refinement means that each refined projector depends only on the round and seed. The phases of its representing unit vector do not matter. If $P_i$ is its observed projector and $f_i=d\operatorname{Tr}(P_i\rho_\theta)$, the raw cycle is the published ordered sum
--   $$\widehat C_{\ell,T}=\sum_{i_1,\ldots,i_\ell\ \mathrm{distinct}}
--    \operatorname{Tr}\!\left(\frac{P_{i_1}-I/d}{f_{i_1}}\cdots
--    \frac{P_{i_\ell}-I/d}{f_{i_\ell}}\right).$$
--   The two real integrands are $|\widehat C_{\ell,T}|^2$ and
--   $\mathbf1_{G_\kappa}|\widehat C_{\ell,T}|^2$, with the published event
--   $G_\kappa=\{\|\sum_{i=1}^T P_i\|_{\mathrm{op}}<\kappa\}$. They use the original joint law of latent vectors, seed and outcomes, with no conditioning on the good event and no retention indicators inside the raw matrices.
--
--   This module names those functions and the fixed-refinement predicate only; independence, integrability and second-moment bounds remain theorem conclusions.
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), §§7.1–7.3, 7.5, printed pp.32–38, 48–49 (PDF pp.34–40, 50–51); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Records

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Topology Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace SingleCopyMoments.Adaptive.Supplement

/-- A fixed rank-one refinement of each nonadaptive POVM. Phases may vary, but
its projectors, like the measurement effects, depend only on round and seed. -/
def FixedRefinement {d : ℕ} {hd : 0 < d} {P : Protocol d} (R : Refinement hd P) : Prop :=
  ∀ i z h h' y,
    outer (R.vector i (z,h) y) = outer (R.vector i (z,h') y)

/-- The square of the raw (unretained) cycle, Eq. (7.51). -/
def rawCycleSquare {d : ℕ} {hd : 0 < d} {P : Protocol d} (R : Refinement hd P)
    (r : ℕ) (α θ : ℝ) (T ℓ : ℕ) (w : Latent d r × Record P) : ℝ :=
  ‖rawCycle α θ (projectors R T w.2) ℓ w.1‖ ^ 2

/-- Multiplication by the indicator, not conditioning the joint law on G. -/
def goodCycleSquare {d : ℕ} {hd : 0 < d} {P : Protocol d} (R : Refinement hd P)
    (r : ℕ) (α θ κ : ℝ) (T ℓ : ℕ) (w : Latent d r × Record P) : ℝ := by
  classical
  exact if w.2 ∈ goodRecords R T κ then rawCycleSquare R r α θ T ℓ w else 0

end SingleCopyMoments.Adaptive.Supplement


