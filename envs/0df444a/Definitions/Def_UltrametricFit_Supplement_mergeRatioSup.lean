-- Prove2me | Definitions.Def_UltrametricFit_Supplement_mergeRatioSup
-- name    : UltrametricFit_Supplement_mergeRatioSup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:21:26.270326+00:00
-- url     : https://prove2.me/theorems/03d8cacd-d050-4c50-ad34-0c32376c123b
-- title:
--   The worst-case ratio $C(\delta)$ of Merge($\delta$) against the $\ell_1$ LP cost
-- statement:
--   For a threshold $\delta\in\mathbb R$, the quantity $C(\delta)$ measures how far the analysis of Merge($\delta$) against the LP can be pushed for the $\ell_1$ objective. It is the supremum
--
--   $$C(\delta)=\sup\ \frac{\|U-X\|_1}{\text{lp-cost}_1(x)},$$
--
--   taken over every $n$, every instance $X:\binom{[n]}{2}\to\mathbb R_{>0}$, every feasible point $x$ of the standard LP (not necessarily optimal) with $\text{lp-cost}_1(x)>0$, every run of Merge($\delta$) on $x$ (every merge order, i.e. the worst one) and every output ultrametric $U$ of that run. Here $\|U-X\|_1=\sum_{i<j}|U(i,j)-X(i,j)|$.
--
--   An upper bound $C(\delta)\le\Gamma$ is exactly what the proof of Theorem 3 establishes for $\delta=(3-\sqrt5)/4$; a lower bound on $C(\delta)$ is a barrier for that style of analysis (Theorem 16).
--
--   **Formalization Note** The value lies in the extended reals, so an unbounded family gives $+\infty$ (the case $\delta\ge 1/2$ of Lemma 18). The ratio is only formed where the LP cost is positive, so a zero denominator never contributes.
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), §5, p.16 (PDF p.17): definition of C(δ); Lemma 15, p.17 (cost_w(x) > 0)

import Mathlib
import Definitions.Def_UltrametricFit_IsInstance
import Definitions.Def_UltrametricFit_IsFeasible
import Definitions.Def_UltrametricFit_IsRun

namespace UltrametricFit.Supplement

open UltrametricFit

/-- **The worst-case ratio `C(δ)` of Merge(δ) against the LP**, Charikar, Gao, *Fitting Ultrametrics
under any ℓ_p Objective*, STOC 2027 submission (manuscript sha256 87af12a2…), §5, p.16: "Let C(δ) be
the supremum over all instances and feasible LP solutions x of the ℓ1 error of the solution produced
by the Merge(δ)) algorithm divided by lp-costp(x)", under the worst merge order.

The supremum runs over every `n`, every instance `X`, every feasible point `x` of the LP with
positive `ℓ1` LP cost, every run `(Cl, M)` of Merge(δ) on `x` (every merge order), and every output
`U` of that run, of the ratio `‖U − X‖₁ / lp-cost₁(x)`.

**Formalization Note.** The value is in `EReal`, so an unbounded family gives `⊤` and no real
`sSup` junk value arises. The ratio is taken only where `lp-cost₁(x) > 0` (the hypothesis
"If cost_w(x) > 0" of Lemma 15, p.17); a zero denominator never enters. `x` is any feasible
point, not an optimal one, as the page says. `δ` is any real number; `lpDist 1` and
`lpCost X 1` are the `ℓ1` error and `lp-cost₁` of the published base definitions. -/
noncomputable def mergeRatioSup (δ : ℝ) : EReal :=
  ⨆ (n : ℕ) (X : Fin n → Fin n → ℝ) (_ : IsInstance X) (x : ℕ → Fin n → Fin n → ℝ)
    (_ : IsFeasible X x) (_ : 0 < lpCost X 1 x) (Cl : ℕ → Finset (Finset (Fin n)))
    (M : ℕ → List (Finset (Fin n) × Finset (Fin n))) (_ : IsRun X x δ Cl M)
    (U : Fin n → Fin n → ℝ) (_ : IsOutput X Cl U),
      ((lpDist 1 U X / lpCost X 1 x : ℝ) : EReal)

end UltrametricFit.Supplement


