-- Prove2me | Definitions.Def_HaarQuotient
-- name    : HaarQuotient
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/d8467ee6-e627-56d8-b16a-0c1e394e2850
-- title:
--   A weight-based quotient measure on right coset spaces
-- statement:
--   Throughout, $G$ is a group carrying both a topology and a measurable structure, $H \le G$ is a subgroup, $\mu$ a measure on $G$ and $\mu_H$ a measure on $H$; the subgroup acts on $G$ by left multiplication, so that the orbit space `MulAction.orbitRel.Quotient H G` is the space $H\backslash G$ of right cosets $Hg$, equipped with the measurable structure pushed forward along the quotient map. Three objects are defined, all total and proof-free.
--
--   First, [`HaarQuotient.weight H μH`](../def/HaarQuotient.html#L12) is a function $G \to [0,\infty]$. It is defined by cases on whether $G$ is $\sigma$-compact and weakly locally compact: if not, it is identically $0$; if so, one takes the compact exhaustion $(E_n)_{n\ge 0}$ of $G$ furnished by `CompactExhaustion.choice G`, sets $M_n = \mu_H\bigl(\iota^{-1}(E_{n+1}E_{n+1}^{-1})\bigr)$ where $\iota : H \to G$ is the inclusion, and puts
--   $$w(g) \;=\; \sum_{n=0}^{\infty} 2^{-n}\,(1+M_n)^{-1}\,\mathbf 1_{\operatorname{int} E_{n+1}}(g),$$
--   the sum being a `tsum` in $[0,\infty]$ and the indicators those of the interiors of the exhausting compacta. The normalising factors $(1+M_n)^{-1}$ are the inverses computed in $[0,\infty]$, so they vanish when $M_n = \infty$.
--
--   Second, [`HaarQuotient.density H μH g`](../def/HaarQuotient.html#L25) is the quotient, in extended non-negative arithmetic, of $w(g)$ by the lower Lebesgue integral $\int_H w(xg)\,\mathrm d\mu_H(x)$; thus the density at $g$ compares the weight of $g$ with the total weight of its coset $Hg$.
--
--   Third, [`HaarQuotient.measure μ H μH`](../def/HaarQuotient.html#L28) is the pushforward along $G \to H\backslash G$ of the measure $\mu$ weighted by this density, i.e. of $\mu\!\restriction$-with-density [`HaarQuotient.density H μH`](../def/HaarQuotient.html#L25). No invariance, closedness or local compactness hypotheses enter the definitions; degenerate inputs (for instance $\mu_H = 0$, or a subgroup for which some $M_n$ is infinite) simply yield degenerate values.
--
--   **Relation to Mathlib.** The construction is assembled from Mathlib's `MeasureTheory.Measure.withDensity`, `MeasureTheory.Measure.map` and `CompactExhaustion.choice`; the weight, the density and the resulting measure on the coset space are the project's own definitions.
--
--   **Where it is used.** These definitions supply the measure on a right coset space $H\backslash G$ for which a quotient (Weil-type) integration formula can be established, and so belong to the measure-theoretic infrastructure on which integration over group quotients in the analytic part of the argument rests.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HaarQuotient.lean

import Mathlib.MeasureTheory.Measure.WithDensity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace HaarQuotient

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

def weight (H : Subgroup G) (μH : Measure H) : G → ℝ≥0∞ :=
  open Classical in
  if h : SigmaCompactSpace G ∧ WeaklyLocallyCompactSpace G then
    haveI := h.1
    haveI := h.2
    fun g => ∑' n : ℕ,
      (2⁻¹ : ℝ≥0∞) ^ n *
        (1 + μH (((↑) : H → G) ⁻¹'
          ((CompactExhaustion.choice G (n + 1) : Set G) *
            (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)))⁻¹ *
        (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g
  else 0

def density (H : Subgroup G) (μH : Measure H) (g : G) : ℝ≥0∞ :=
  weight H μH g / ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH

def measure (μ : Measure G) (H : Subgroup G) (μH : Measure H) :
    Measure (MulAction.orbitRel.Quotient H G) :=
  Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)
    (μ.withDensity (density H μH))

end HaarQuotient

end


