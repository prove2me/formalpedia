-- Prove2me | Definitions.Def_PrivOptTest_infoCost
-- name    : PrivOptTest_infoCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:54.974086+00:00
-- url     : https://prove2.me/theorems/561a931a-90bf-402e-a839-bee2749cabb7
-- title:
--   Replacement distance, encoding diameter and internal information cost (Lemma 2.2)
-- statement:
--   For $S,S'\in\mathcal X^n$, $d_{\mathrm{ham}}(S,S')$ is the number of positions in which they differ, and the **encoding diameter** of $E:\mathcal A\to\mathcal X^n$ is $\Delta=\max_{a,a'}d_{\mathrm{ham}}(E(a),E(a'))$.
--
--   For finite $\mathcal A,\mathcal B$, a distribution $\mu$ on $\mathcal A\times\mathcal B$ and transcript laws $P_{a,b}$, the **internal information cost in bits** is
--   $$I(A;T\mid B)+I(B;T\mid A)=\frac{1}{\ln 2}\sum_{a,b}\mu(a,b)\Big[D\big(P_{a,b}\,\big\|\,\textstyle\sum_{a'}\mu(a'\mid b)P_{a',b}\big)+D\big(P_{a,b}\,\big\|\,\textstyle\sum_{b'}\mu(b'\mid a)P_{a,b'}\big)\Big],$$
--   where $D$ is the Kullback–Leibler divergence and the mixtures are the conditional laws $P_{T\mid B=b}$, $P_{T\mid A=a}$.
--
--   **Formalization Note** Values are in $[0,\infty]$, so an infinite divergence gives $\infty$. The conditional weights $\mu(a'\mid b)=\mu(a',b)/\mu(\cdot,b)$ matter only where $\mu(a,b)>0$.
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), §2.1, p.13; Lemma 2.2, p.14

import Mathlib

open MeasureTheory

namespace PrivOptTest

/-- The replacement distance `d_ham(S, S′)` (§2.1, p.13 of arXiv:2611.03599, manuscript sha256
4ac94dcf…): the number of positions in which two sequences differ. -/
def dham {D : Type} [DecidableEq D] {n : ℕ} (S S' : Fin n → D) : ℕ :=
  (Finset.univ.filter fun i => S i ≠ S' i).card

/-- The encoding diameter `Δ_E = max_{a,a′} d_ham(E(a), E(a′))` of Lemma 2.2, p.14. -/
def encDiam {A D : Type} [Fintype A] [DecidableEq D] {n : ℕ} (E : A → Fin n → D) : ℕ :=
  Finset.univ.sup fun p : A × A => dham (E p.1) (E p.2)

/-- **The internal information cost in bits** `I(A;T|B) + I(B;T|A)` (Lemma 2.2, p.14), where
`(A, B) ∼ μ` on finite sets and `P a b` is the law of the transcript `T` on inputs `a`, `b`:

`(Σ_{a,b} μ(a,b) · [D(P_{a,b} ‖ Σ_{a′} μ(a′|b) P_{a′,b}) + D(P_{a,b} ‖ Σ_{b′} μ(b′|a) P_{a,b′})]) / ln 2`.

**Formalization Note.** With `A`, `B` finite, the conditional mutual informations are these averages
of Kullback–Leibler divergences between `P_{T|a,b}` and the conditional mixtures `P_{T|b}`, `P_{T|a}`.
The value is in `ℝ≥0∞`, so an infinite divergence is `⊤`. Conditional weights `μ(a′|b) = μ(a′,b)/μ(·,b)`
matter only where `μ(a,b) > 0`, and then the denominator is positive. -/
noncomputable def infoCost {A B T : Type} [Fintype A] [Fintype B] [MeasurableSpace T]
    (μ : PMF (A × B)) (P : A → B → Measure T) : ENNReal :=
  (∑ a, ∑ b, μ (a, b) *
    (InformationTheory.klDiv (P a b) (∑ a', (μ (a', b) / ∑ a'', μ (a'', b)) • P a' b) +
      InformationTheory.klDiv (P a b) (∑ b', (μ (a, b') / ∑ b'', μ (a, b'')) • P a b'))) /
    ENNReal.ofReal (Real.log 2)

end PrivOptTest


