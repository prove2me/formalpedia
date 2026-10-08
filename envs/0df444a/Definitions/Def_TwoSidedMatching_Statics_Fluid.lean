-- Prove2me | Definitions.Def_TwoSidedMatching_Statics_Fluid
-- name    : TwoSidedMatching_Statics_Fluid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T09:27:18.405642+00:00
-- url     : https://prove2.me/theorems/06186297-fb07-419c-bc3a-d5e8d6d5e6bd
-- title:
--   Main text pp. 15–16 — two-sided fluid market, quantiles, and program (D)
-- statement:
--   Fix independent buyer valuations and seller costs, with positive densities on bounded intervals, and a horizon $T$. The buyer and seller arrival rates are $\lambda^d$ and $\lambda^s$. Their distribution functions are extended to all real prices by clamping at the support endpoints. Write $\bar F^d(p)=1-F^d(p)$ and retain the source's virtual value $V^d$ and virtual cost $V^s$.
--
--   The inverse survival and distribution functions on $[0,1]$ are $\bar F^{d,-1}$ and $F^{s,-1}$. For a proposed matched volume $\mu$, define
--
--   $$V(\mu)=V^d\!\left(\bar F^{d,-1}\!\left(\frac{\mu}{\lambda^dT}\right)\right)-V^s\!\left(F^{s,-1}\!\left(\frac{\mu}{\lambda^sT}\right)\right),\qquad \mu^*=\sup\{\mu\in[0,\min(\lambda^dT,\lambda^sT)]:V(\mu)\ge0\}.$$
--
--   The associated fixed prices are $p^*=\bar F^{d,-1}(\mu^*/(\lambda^dT))$ and $w^*=F^{s,-1}(\mu^*/(\lambda^sT))$. The fluid value $\bar J^*$ is the supremum of the net revenue in program (D) over measurable, nonnegative, market-clearing price trajectories on $[0,T]$.
--
--   These definitions keep the optimization problem distinct from the fixed-price identity that Proposition 1 establishes.
--
--   **Formalization Note** The integrands of each feasible path are interval integrable, so a non-integrable path cannot acquire Lean's default integral value. Outside the quantile interval, the total inverse functions have auxiliary values that none of the stated results uses. The seller support is required to be nonnegative in the theorems because (D) restricts bid prices to $\mathbb R_+$.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), main text pp. 8–16, Assumptions 1–2 and program (D), Proposition 1 (1)–(2)

import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace TwoSidedMatching.Statics

/-! The deterministic two-sided market of Chen and Hu, main text pp. 15–16. -/

abbrev Environment := MechanismDesign.BilateralTrade.Environment

/-- The buyer CDF, clamped to the valuation support. -/
noncomputable def Fd (E : Environment) (p : ℝ) : ℝ :=
  E.cdfB (max E.loB (min p E.hiB))

/-- The buyer survival function on all real prices. -/
noncomputable def FdBar (E : Environment) (p : ℝ) : ℝ := 1 - Fd E p

/-- The seller CDF, clamped to the cost support. -/
noncomputable def Fs (E : Environment) (w : ℝ) : ℝ :=
  E.cdfS (max E.loS (min w E.hiS))

/-- The inverse of the buyer survival function on `[0,1]`, represented by its supported level set. -/
noncomputable def FdBarInv (E : Environment) (q : ℝ) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc E.loB E.hiB ∧ FdBar E p ≤ q}

/-- The inverse of the seller CDF on `[0,1]`, represented by its supported level set. -/
noncomputable def FsInv (E : Environment) (q : ℝ) : ℝ :=
  sInf {w : ℝ | w ∈ Set.Icc E.loS E.hiS ∧ q ≤ Fs E w}

/-- Virtual buyer value minus virtual seller cost at a proposed matched volume. -/
noncomputable def V (E : Environment) (lamD lamS T μ : ℝ) : ℝ :=
  E.psiB (FdBarInv E (μ / (lamD * T))) -
    E.psiS (FsInv E (μ / (lamS * T)))

/-- The largest nonnegative volume up to both side capacities with nonnegative virtual surplus. -/
noncomputable def muStar (E : Environment) (lamD lamS T : ℝ) : ℝ :=
  sSup {μ : ℝ | μ ∈ Set.Icc 0 (min (lamD * T) (lamS * T)) ∧ 0 ≤ V E lamD lamS T μ}

/-- Optimal fixed buyer price from the volume quantile. -/
noncomputable def pStar (E : Environment) (lamD lamS T : ℝ) : ℝ :=
  FdBarInv E (muStar E lamD lamS T / (lamD * T))

/-- Optimal fixed seller price from the volume quantile. -/
noncomputable def wStar (E : Environment) (lamD lamS T : ℝ) : ℝ :=
  FsInv E (muStar E lamD lamS T / (lamS * T))

/-- A measurable nonnegative price trajectory satisfying (D)'s pointwise balance,
with both revenues integrable on the horizon. -/
def IsFeasiblePath (E : Environment) (lamD lamS T : ℝ) (π : ℝ → ℝ × ℝ) : Prop :=
  Measurable π ∧
  (∀ t ∈ Set.Icc 0 T, 0 ≤ (π t).1 ∧ 0 ≤ (π t).2 ∧
    lamD * FdBar E (π t).1 = lamS * Fs E (π t).2) ∧
  IntervalIntegrable (fun t => lamD * (π t).1 * FdBar E (π t).1) volume 0 T ∧
  IntervalIntegrable (fun t => lamS * (π t).2 * Fs E (π t).2) volume 0 T

/-- The net profit of a feasible deterministic price trajectory in (D). -/
noncomputable def fluidObjective (E : Environment) (lamD lamS T : ℝ)
    (π : ℝ → ℝ × ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..T, lamD * (π t).1 * FdBar E (π t).1) -
    (∫ t in (0 : ℝ)..T, lamS * (π t).2 * Fs E (π t).2)

/-- The value of program (D), a supremum over all feasible paths, rather than the
fixed-price identity that Proposition 1 has to establish. -/
noncomputable def fluidValue (E : Environment) (lamD lamS T : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ π : ℝ → ℝ × ℝ,
    IsFeasiblePath E lamD lamS T π ∧ v = fluidObjective E lamD lamS T π}

/-- Fraction of arriving buyers served in the fluid optimum. -/
noncomputable def nuStarD (E : Environment) (lamD lamS T : ℝ) : ℝ :=
  muStar E lamD lamS T / (lamD * T)

/-- Fraction of arriving sellers served in the fluid optimum. -/
noncomputable def nuStarS (E : Environment) (lamD lamS T : ℝ) : ℝ :=
  muStar E lamD lamS T / (lamS * T)

end TwoSidedMatching.Statics


