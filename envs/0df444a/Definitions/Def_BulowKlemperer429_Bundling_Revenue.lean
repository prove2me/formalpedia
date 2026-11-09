-- Prove2me | Definitions.Def_BulowKlemperer429_Bundling_Revenue
-- name    : BulowKlemperer429_Bundling_Revenue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:17.823465+00:00
-- url     : https://prove2.me/theorems/10d16d95-aaf1-41d8-b627-34a72281656e
-- title:
--   Posted-price revenue, regular marginals, and bundle competition
-- statement:
--   Let $F$ be a law on $[0,\infty)$. Its posted-price revenue and upper-tail quantile are
--   $$r(F)=\sup_{t\ge0}t\Pr[X\ge t],\qquad v_F(q)=\sup\{t\ge0:\Pr[X\ge t]\ge q\}\quad(0<q<1).$$
--   Regularity means concavity of $R_F(q)=qv_F(q)$ on $(0,1)$, including distributions with atoms. For a finite family of independent item laws $\nu_j$, let $S=\sum_jV_j$. Define $\mathrm{SREV}=\sum_jr(\nu_j)$, $\mathrm{BREV}=r(\operatorname{law}(S))$, and $\mathrm{BSPA}_k$ as the expected second-highest of $k$ independent draws of $S$.
--
--   These are the simple-auction benchmarks of the mission. The second-highest is computed as $\max_{i\ne j}\min(y_i,y_j)$, with zero for fewer than two draws.
--
--   **Formalization Note** Values use $\mathbb R_{\ge0}$ and revenues use $\mathbb R_{\ge0}\cup\{\infty\}$. For a probability law and $0<q<1$, the set defining the real supremum is nonempty and bounded above; quantile values outside this interval are unused. The sum map defining the bundle law is continuous, so its measure pushforward has no nonmeasurability default.
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 7, §2, regularity and simple-auction benchmarks (also p. 6) (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling

/-- Section 2, pp. 6–7: posted-price revenue with the weak sale inequality. -/
noncomputable def postedRevenue (ν : Measure ℝ≥0) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, (t : ℝ≥0∞) * ν {x | t ≤ x}

/-- The upper-tail quantile is used only for 0 < q < 1. -/
noncomputable def tailQuantile (ν : Measure ℝ≥0) (q : ℝ) : ℝ :=
  sSup {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal q ≤ ν {x | t ≤ (x : ℝ)}}

noncomputable def revenueCurve (ν : Measure ℝ≥0) (q : ℝ) : ℝ :=
  q * tailQuantile ν q

/-- Concavity on the open quantile interval; no density or atomlessness assumption. -/
def IsRegular (ν : Measure ℝ≥0) : Prop :=
  ConcaveOn ℝ (Set.Ioo 0 1) (revenueCurve ν)

variable {ι : Type} [Fintype ι]

def totalValue (v : ι → ℝ≥0) : ℝ≥0 := ∑ j, v j

noncomputable def bundleLaw (ν : ι → Measure ℝ≥0) : Measure ℝ≥0 :=
  (Measure.pi ν).map totalValue

noncomputable def BREV (ν : ι → Measure ℝ≥0) : ℝ≥0∞ :=
  postedRevenue (bundleLaw ν)

noncomputable def SREV (ν : ι → Measure ℝ≥0) : ℝ≥0∞ :=
  ∑ j, postedRevenue (ν j)

/-- Second-highest scalar value, with value zero for fewer than two bidders. -/
noncomputable def secondHighest {k : ℕ} (y : Fin k → ℝ≥0) : ℝ≥0 := by
  classical
  exact Finset.univ.sup fun i => Finset.univ.sup fun j =>
    if i = j then 0 else min (y i) (y j)

/-- Reserve-free second-price revenue from k independent bundle values (k ≥ 2 in use). -/
noncomputable def BSPA (k : ℕ) (ν : ι → Measure ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ y, (secondHighest y : ℝ≥0∞) ∂Measure.pi (fun _ : Fin k => bundleLaw ν)

end BulowKlemperer429.Bundling


