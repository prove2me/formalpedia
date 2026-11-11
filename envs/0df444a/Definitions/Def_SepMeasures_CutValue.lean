-- Prove2me | Definitions.Def_SepMeasures_CutValue
-- name    : SepMeasures_CutValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:10:29.846229+00:00
-- url     : https://prove2.me/theorems/8df5f3a9-3267-4622-9fce-4ec509317c4e
-- title:
--   §2.1–2.2, pp.11–12 — $L_{\mu,\nu}$, $C_{\mu,\nu}(H)$ and the cut ratio $\alpha(\mathcal F)$ (Definition 2.1)
-- statement:
--   Let $\|\cdot\|$ be a norm on $\mathbb R^d$ and $\mu,\nu$ probability measures with finite first moments (the **red** and the **blue** measure). With $X\sim\mu$ and $Y\sim\nu$ independent, the **expected total red–blue distance** and the **cut value** of an oriented hyperplane $H$ are
--   $$L_{\mu,\nu}=\int\!\!\int\|x-y\|\,d\mu(x)\,d\nu(y)=\mathbb E\|X-Y\|,\qquad C_{\mu,\nu}(H)=\int\!\!\int_{\mathrm{Sep}(H)}\|x-y\|\,d\mu(x)\,d\nu(y).$$
--   For a family $\mathcal F$ of such pairs containing a pair with $L_{\mu,\nu}>0$, its **cut ratio** (Definition 2.1) is
--   $$\alpha(\mathcal F)=\inf_{\substack{(\mu,\nu)\in\mathcal F\\ L_{\mu,\nu}>0}}\ \sup_{H\in\mathbb H^d}\ \frac{C_{\mu,\nu}(H)}{L_{\mu,\nu}}.$$
--   It is the fraction of the total red–blue distance that the best hyperplane is guaranteed to cut, in the worst case over the family.
--
--   **Formalization Note** $L$ and $C(H)$ are Bochner integrals of $N(x-y)$ against the product measure $\mu\otimes\nu$, which equal the paper's values for pairs with finite first moments. The cut ratio is a real infimum over the subtype of pairs of $\mathcal F$ with $0<L$ of a real supremum over oriented hyperplanes; for such a pair $0\le C(H)\le L$, so the supremum lies in $[0,1]$. If no pair of $\mathcal F$ had $L>0$ the Lean value would be $0$; every family to which the mission applies the cut ratio contains such a pair.
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), §2.1, p.11 (L_{µ,ν}, C_{µ,ν}(H)); Definition 2.1, p.12

import Mathlib
import Definitions.Def_SepMeasures_Hyp

open MeasureTheory

namespace SepMeasures

/-- The expected total red–blue distance
`L_{μ,ν} := ∫∫ ‖x − y‖ dμ(x) dν(y) = E‖X − Y‖` for independent `X ∼ μ`, `Y ∼ ν`
(Correa et al., manuscript sha256 96a86924…fa82f, §2.1, p.11).

**Formalization Note.** The norm is an arbitrary `N : Seminorm ℝ (E d)` (definiteness is a
hypothesis wherever the paper says "norm"). The double integral is the Bochner integral over the
product measure `μ.prod ν`. For pairs with finite first moments the integrand is integrable
(`N (x − y) ≤ N x + N y`), so the value is the paper's; for a non-integrable integrand Lean
returns `0`, which `cutRatio` excludes by requiring `0 < L`. -/
noncomputable def totalDist {d : ℕ} (N : Seminorm ℝ (E d)) (μ ν : Measure (E d)) : ℝ :=
  ∫ p, N (p.1 - p.2) ∂(μ.prod ν)

/-- The cut value of an oriented hyperplane `H`,
`C_{μ,ν}(H) := ∫∫_{Sep(H)} ‖x − y‖ dμ(x) dν(y)`, the part of `L_{μ,ν}` carried by pairs that `H`
strictly separates (Correa et al., manuscript sha256 96a86924…fa82f, §2.1, p.11).

**Formalization Note.** Bochner set integral over `Sep H` (open half-spaces, strict separation)
with respect to `μ.prod ν`; see `totalDist`. -/
noncomputable def cutVal {d : ℕ} (N : Seminorm ℝ (E d)) (μ ν : Measure (E d)) (H : Hyp d) : ℝ :=
  ∫ p in Sep H, N (p.1 - p.2) ∂(μ.prod ν)

/-- The cut ratio of a family `F` of pairs of measures (Definition 2.1, p.12):
`α(F) := inf_{(μ,ν) ∈ F, L_{μ,ν} > 0} sup_{H ∈ ℍ^d} C_{μ,ν}(H) / L_{μ,ν}`.

**Formalization Note.** Infimum and supremum are taken in `ℝ`. The infimum ranges over the
pairs of `F` with `0 < L`, so the division is never by zero. For such a pair the integrand of
`L` is integrable and non-negative, so `0 ≤ C(H) ≤ L` and the inner supremum is over a set
bounded by `1` (and is `≥ 0`): it is an honest supremum (for `d ≥ 1`, where `Hyp d` is
non-empty). The outer infimum is over values `≥ 0`, hence an honest infimum. If no pair of `F`
has `0 < L`, Lean's value is `0`; Definition 2.1 assumes `F` contains such a pair, and every
family this mission applies `cutRatio` to does. -/
noncomputable def cutRatio {d : ℕ} (N : Seminorm ℝ (E d))
    (F : Set (Measure (E d) × Measure (E d))) : ℝ :=
  ⨅ p : {p : Measure (E d) × Measure (E d) // p ∈ F ∧ 0 < totalDist N p.1 p.2},
    ⨆ H : Hyp d, cutVal N p.1.1 p.1.2 H / totalDist N p.1.1 p.1.2

end SepMeasures


