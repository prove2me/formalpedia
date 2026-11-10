-- Prove2me | Definitions.Def_OnlineDiscUniv_IsAdmLimitLaw
-- name    : OnlineDiscUniv_IsAdmLimitLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:31.963982+00:00
-- url     : https://prove2.me/theorems/a0901575-5933-4011-ae55-a1239dcd2b2d
-- title:
--   Admissible limit laws on $\mathcal C^2$ at aspect ratio $\alpha$ ((5.2)–(5.3))
-- statement:
--   On $\mathcal C^2$ let $(A,B)$ be the canonical processes and $\mathbb G$ their canonical joint filtration, $\mathcal G_t=\sigma((A_s,B_s):s\le t)$. A law $m\in\mathcal P(\mathcal C^2)$ is **admissible at aspect ratio $\alpha$** if under $m$, $B$ is a Brownian motion in $\mathbb G$ and there is a $\mathbb G$-progressively measurable $a$ with
--   $$
--   A_t=\int_0^t a_s\,ds\ \ (0\le t\le1),\qquad\mathbb E_m a_t^2\le\frac{2}{\pi\alpha}=c_\alpha^2\ \ \text{for a.e. }t\in[0,1].
--   $$
--   Proposition 5.1 asserts that every limit of the laws of $\widehat\nu_N$ is supported on such laws.
--
--   **Formalization Note** The uncompleted canonical filtration is used; the processes are indexed by $[0,\infty)$ and frozen after time $1$. (5.2) is required almost surely under $m$, simultaneously for all $t\in[0,1]$.
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), Proposition 5.1, (5.2)–(5.3), p.24 (PDF p.25)

import Mathlib
import Definitions.Def_OnlineDiscUniv_empMeas
import Definitions.Def_OnlineDiscUniv_IsProgOn
import Definitions.Def_ABPOnline_IsBrownianWrt

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal
open ABPOnline (IsBrownianWrt)

namespace OnlineDiscUniv

/-- The point `min(t, 1)` of `[0,1]`, for `t ≥ 0`. -/
noncomputable def clampI (t : ℝ≥0) : unitInterval :=
  ⟨min (t : ℝ) 1, le_min t.2 zero_le_one, min_le_right _ _⟩

/-- The canonical processes `A_t`, `B_t` on the path space `C([0,1], ℝ²)` (Jo–Lee,
arXiv:2610.00103, artifact sha256 cb190f12…, Proposition 5.1, printed p.24, PDF p.25), indexed by
`t ≥ 0` and frozen after time `1`. -/
noncomputable def canA (t : ℝ≥0) (w : C(unitInterval, ℝ × ℝ)) : ℝ := (w (clampI t)).1

/-- See `canA`. -/
noncomputable def canB (t : ℝ≥0) (w : C(unitInterval, ℝ × ℝ)) : ℝ := (w (clampI t)).2

/-- The canonical joint filtration of `(A, B)` on `C([0,1], ℝ²)` (Jo–Lee, arXiv:2610.00103,
Proposition 5.1, p.24, PDF p.25): `G_t = σ((A_s, B_s) : s ≤ t)`.

**Formalization Note** The uncompleted natural filtration of the canonical pair is used (the
paper does not say "completed" here). -/
noncomputable def canFiltration : Filtration ℝ≥0 (pathMeasurableSpace) where
  seq t := ⨆ s ≤ t, MeasurableSpace.comap (fun w : C(unitInterval, ℝ × ℝ) => w (clampI s))
    inferInstance
  mono' _ _ hst := iSup₂_mono' fun s hs => ⟨s, hs.trans hst, le_rfl⟩
  le' _ := iSup₂_le fun s _ =>
    (continuous_eval_const (clampI s)).measurable.comap_le

/-- A law `m` on `C([0,1], ℝ²)` is **admissible at aspect ratio `α`** (Jo–Lee, arXiv:2610.00103,
Proposition 5.1, (5.2)–(5.3), p.24, PDF p.25): under `m`, `B` is a Brownian motion in the
canonical joint filtration, and there is a progressively measurable `a` with
`A_t = ∫_0^t a_s ds` for `0 ≤ t ≤ 1` (almost surely) and `E_m a_t² ≤ 2/(πα) = c_α²` for a.e.
`t ∈ [0,1]`.

**Formalization Note** "Brownian motion in the canonical joint filtration" is the published
`ABPOnline.IsBrownianWrt` (a standard Brownian motion on `[0,1]`, adapted, with all future
increments independent of the past). (5.2) is required `m`-almost surely, simultaneously for all
`t ∈ [0,1]`; the time integral is a Bochner integral, a.s. finite because `E_m a_t² ≤ c_α²`. -/
def IsAdmLimitLaw (α : ℝ) (m : ProbabilityMeasure C(unitInterval, ℝ × ℝ)) : Prop :=
  IsBrownianWrt canFiltration canB (m : Measure C(unitInterval, ℝ × ℝ)) ∧
  ∃ a : ℝ≥0 → C(unitInterval, ℝ × ℝ) → ℝ, IsProgOn canFiltration 1 a ∧
    (∀ᵐ w ∂(m : Measure C(unitInterval, ℝ × ℝ)), ∀ t : ℝ≥0, t ≤ 1 →
      canA t w = ∫ s in Set.Icc (0 : ℝ) t, a s.toNNReal w) ∧
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∫⁻ w, ‖a t.toNNReal w‖ₑ ^ 2 ∂(m : Measure C(unitInterval, ℝ × ℝ)) ≤
        ENNReal.ofReal (2 / (Real.pi * α))

end OnlineDiscUniv


