-- Prove2me | Definitions.Def_BilatMatch_sellerCost
-- name    : BilatMatch_sellerCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:09:58.027453+00:00
-- url     : https://prove2.me/theorems/2d5d2be9-2524-45ea-8311-2168a1ddcbda
-- title:
--   Seller classes, cutoff allocations $Z_S$ and seller-side cost $C_\alpha$
-- statement:
--   Two seller classes are used in §3.2. A seller is **finite** if her prior is finitely supported (report domain: the support, $\alpha$-virtual cost $\tau^\alpha_S$ of (2)). A seller is **regular with interval support** if her prior lives on $[\underline c,\bar c]$, has a density in the interior, positive almost everywhere there, and an atom only at $\underline c$; then
--   $$\tau^\alpha_S(c)=(1+\alpha)c+\alpha F_S(c)/f_S(c)\ (\underline c<c<\bar c),\qquad \tau^\alpha_S(\underline c)=(1+\alpha)\underline c.$$
--   The seller is **$\alpha$-weakly regular** if $\tau^\alpha_S$ is nondecreasing on her domain (for an interval seller on $[\underline c,\bar c)$, where the formula is given; $\tau^\alpha_S$ may tend to $+\infty$ at $\bar c$).
--
--   The **cutoff allocation** $Z_S(\mu,\cdot)$ trades with the lowest-cost seller types up to total mass $\mu$, randomizing at a cutoff atom: at an atom $c$, $Z_S(\mu,c)=\min\{1,\max\{0,(\mu-\Pr(C<c))/\Pr(C=c)\}\}$; at a non-atom $c$, $Z_S(\mu,c)=1\{F_S(c)<\mu\}$. The seller-side Lagrangian cost is $C_\alpha(\mu)=\mathbb E_{c\sim F_S}[\tau^\alpha_S(c)Z_S(\mu,c)]$.
--
--   **Formalization Note** For an interval seller $\tau^\alpha_S$ depends on the chosen density only on a null set; $\alpha$-weak regularity asks for some version to be nondecreasing.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), §3.2, pp.10–11 (pdf pp.12–13); proof of Lemma 3.3, pp.28–29 (pdf pp.30–31)

import Mathlib
import Definitions.Def_BilatMatch_virtualValue

open MeasureTheory

namespace BilatMatch

/-!
# Seller classes, cutoff allocations and the seller-side cost `C_α`

Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from Trade*,
arXiv:2609.30702 (held version, sha256 ff1490ad…), §3.2, pp.10–11 (pdf pp.12–13), and the proof of
Lemma 3.3, pp.28–29 (pdf pp.30–31).

**Formalization Note**
* A regular interval-support seller: support `[c̲, c̄]`, `c̲ < c̄`, a density `f` on the interior,
  positive almost everywhere there, and an atom only at `c̲` (possibly of mass zero). Its `α`-virtual
  cost is `(1+α)c + α F_S(c)/f_S(c)` in the interior (with `F_S(c) = Pr(X ≤ c)`, the atom included) and
  `(1+α)c̲` at `c̲` (p.10). It depends on the chosen version `f` only on a null set.
* `α`-weak regularity is monotonicity of `τα` on the reports of positive upper mass,
  `{c ∈ DS | 0 < F_S([c, ∞))}`: every atom of a finite prior, and `[c̲, c̄)` for an interval seller.
  The non-atomic top endpoint `c̄` is excluded because the formula is given only on `[c̲, c̄)` (p.10)
  and the seller is inactive at and above `c̄` (p.30–31); `τα` may tend to `+∞` at `c̄`.
* `IsSellerData α F DS τα`: `F` is finitely supported with report domain its atoms and `τα` the
  finite `α`-virtual cost of eq. (2), or `F` is regular with interval support `DS = [c̲, c̄]` and
  `τα` the interval formula. `α`-weak regularity: `τα` is nondecreasing on `DS` (p.10).
* The cutoff allocation (p.11 and p.28): at an atom `c`,
  `Z_S(µ, c) = min{1, max{0, (µ − Pr(X < c))/Pr(X = c)}}`; at a non-atom, `Z_S(µ, c) = 1{Pr(X ≤ c) < µ}`
  (the strict cutoff `1{c < c_µ}` of the interval case).
-/

/-- A regular prior with interval support `[lo, hi]` and interior density `f` (p.10). -/
def IsRegularIntervalLaw (F : Measure ℝ) (lo hi : ℝ) (f : ℝ → ℝ) : Prop :=
  lo < hi ∧ Measurable f ∧ IsProbabilityMeasure F ∧
    (∀ᵐ c ∂(volume.restrict (Set.Ioo lo hi)), 0 < f c) ∧
    F = F {lo} • Measure.dirac lo +
      (volume.restrict (Set.Ioo lo hi)).withDensity (fun c => ENNReal.ofReal (f c))

/-- The `α`-virtual cost of a regular interval-support seller (p.10): `(1+α)c̲` at (and below) `c̲`,
`(1+α)c + α F_S(c)/f_S(c)` above. -/
noncomputable def intervalAlphaCost (α : ℝ) (F : Measure ℝ) (lo : ℝ) (f : ℝ → ℝ) (c : ℝ) : ℝ :=
  if c ≤ lo then (1 + α) * c else (1 + α) * c + α * (F (Set.Iic c)).toReal / f c

/-- The seller classes of §3.2 with their report domain `DS` and `α`-virtual cost `τα`. -/
def IsSellerData (α : ℝ) (F : Measure ℝ) (DS : Set ℝ) (τα : ℝ → ℝ) : Prop :=
  (IsFiniteSupport F ∧ DS = atoms F ∧ τα = alphaVirtualCost α F) ∨
    ∃ lo hi f, IsRegularIntervalLaw F lo hi f ∧ DS = Set.Icc lo hi ∧
      τα = intervalAlphaCost α F lo f

/-- `α`-weak regularity (p.10): the seller's `α`-virtual cost is nondecreasing on the reports of its
domain that carry positive upper mass (all atoms of a finite prior; `[c̲, c̄)` for an interval
seller). -/
def IsAlphaWeaklyRegular (α : ℝ) (F : Measure ℝ) (DS : Set ℝ) (τα : ℝ → ℝ) : Prop :=
  IsSellerData α F DS τα ∧ MonotoneOn τα {c | c ∈ DS ∧ 0 < F (Set.Ici c)}

/-- A regular interval-support seller in the sense of §3.2: interval support with an interior
density and an `α`-virtual cost nondecreasing on `[c̲, c̄)` (the formula's range, p.10). -/
def IsRegularIntervalSeller (α : ℝ) (F : Measure ℝ) : Prop :=
  ∃ lo hi f, IsRegularIntervalLaw F lo hi f ∧ MonotoneOn (intervalAlphaCost α F lo f) (Set.Ico lo hi)

open Classical in
/-- The seller-cost cutoff allocation `Z_S(µ, c)` (p.11): trade with the lowest-cost seller types up
to total probability mass `µ`, randomizing at a cutoff atom. -/
noncomputable def cutoffAlloc (F : Measure ℝ) (m c : ℝ) : ℝ :=
  if 0 < F {c} then min 1 (max 0 ((m - (F (Set.Iio c)).toReal) / (F {c}).toReal))
  else if (F (Set.Iic c)).toReal < m then 1 else 0

/-- The seller-side Lagrangian cost `C_α(µ) = E_{c∼F_S}[τ^α_S(c) Z_S(µ, c)]` (p.11). -/
noncomputable def sellerCost (F : Measure ℝ) (τα : ℝ → ℝ) (m : ℝ) : ℝ :=
  ∫ c, τα c * cutoffAlloc F m c ∂F

end BilatMatch


