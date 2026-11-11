-- Prove2me | Definitions.Def_PriceIgnorance_Pairwise_Ratios
-- name    : PriceIgnorance_Pairwise_Ratios
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:13:39.761403+00:00
-- url     : https://prove2.me/theorems/12b1b2fb-e052-4cd4-a29e-58dd1af701d3
-- title:
--   Correlation-blind and correlation-aware competitive ratios and the price of ignorance (Definition 2.2)
-- statement:
--   Fix an arrival model, marginals $D_1,\dots,D_n$ and $k$. For a joint law $D$ write $\mathbb E_D[\mathrm{val}(A,V)]$ for the expected value of algorithm $A$ and $\mathbb E_D[\max_i V_i]$ for the prophet's expected value.
--
--   1. The **correlation-blind** competitive ratio given the marginals (p. 5) is
--   $$\mathrm{blind}(D_1,\dots,D_n)=\sup_{A\in\mathrm{ALG}}\ \inf_{D\in kI}\ \frac{\mathbb E_D[\mathrm{val}(A,V)]}{\mathbb E_D[\max_i V_i]} .$$
--   2. The **correlation-aware** competitive ratio given the marginals is
--   $$\mathrm{aware}(D_1,\dots,D_n)=\inf_{D\in kI}\ \sup_{A\in\mathrm{ALG}}\ \frac{\mathbb E_D[\mathrm{val}(A,V)]}{\mathbb E_D[\max_i V_i]} .$$
--   3. The **price of ignorance** given the marginals is
--   $$\mathrm{poi}(D_1,\dots,D_n)=\sup_{B\in\mathrm{ALG}}\ \inf_{D\in kI}\ \frac{\mathbb E_D[\mathrm{val}(B,V)]}{\sup_{A\in\mathrm{ALG}}\mathbb E_D[\mathrm{val}(A,V)]} .$$
--   4. $\mathrm{blindCR}$, $\mathrm{awareCR}$ and $\mathrm{PoI}$ are the infima of these quantities over all $n$ and all non-degenerate marginals $D_1,\dots,D_n$. For $k=2$, $\mathrm{PoI}$ is the pairwise-independent price of ignorance of Definition 2.2, and $\mathrm{awareCR}$ is the optimal competitive ratio of pairwise-independent prophet inequalities (p. 1).
--
--   A correlation-blind algorithm is chosen knowing only the marginals, and must then do well against every joint law in $kI$. A correlation-aware algorithm is chosen after $D$ is known.
--
--   **Formalization Note** Definition 2.2 writes $\inf_{A}\mathbb E_D[\mathrm{val}(B,V)]/\mathbb E_D[\mathrm{val}(A,V)]$. Since the numerator is nonnegative and $\sup_A\mathbb E_D[\mathrm{val}(A,V)]\ge\max_i\mathbb E[V_i]>0$ (stop exactly at the best index), this equals the numerator divided by $\sup_A$, which is the form used. Suprema and infima are real `⨆`/`⨅`. For non-degenerate marginals they never hit a junk value: $kI$ contains the product law, every denominator is positive, and every ratio lies in $[0,1]$.
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 1 (competitive ratio); p. 3, Definition 2.2; p. 5, displays after Theorem 3.1 and footnote 3

import Mathlib
import Definitions.Def_PriceIgnorance_Pairwise_Instance
import Definitions.Def_PriceIgnorance_Pairwise_Algorithms

/-!
# Competitive ratios (correlation-blind and correlation-aware) and the price of ignorance

Abdallah, Wajc, *Price of Ignorance in Pairwise-Independent Prophet Inequalities*, STOC 2027
submission (manuscript sha256 c79626fd…), p. 1 (competitive ratio), p. 3 (Definition 2.2),
p. 5 (the two displays after Theorem 3.1), p. 5 footnote 3.

For an arrival model `M`, marginals `Dm` and `k`:

* `blindCRGiven M Dm k = sup_A inf_{D ∈ kI} E_D[val(A,V)] / E_D[max_i V_i]`,
* `awareCRGiven M Dm k = inf_{D ∈ kI} sup_A E_D[val(A,V)] / E_D[max_i V_i]`,
* `poiGiven M Dm k = sup_B inf_{D ∈ kI} E_D[val(B,V)] / sup_A E_D[val(A,V)]`;

`blindCR`, `awareCR` and `PoI` take the infimum over all `n` and all non-degenerate marginals (non-degeneracy forces `n ≥ 1`)
(`Instance`). Real `⨆`/`⨅` are used: for non-degenerate marginals `kI` contains the product law,
every ratio lies in `[0, 1]`, and the denominators are positive, so no junk value is reached.
-/

namespace PriceIgnorance.Pairwise

open MeasureTheory

/-- `E_D[val(A, V)]`. -/
noncomputable def expVal (M : ArrivalModel) {n : ℕ} (A : M.Alg n) (D : Measure (Fin n → ℝ)) :
    ℝ :=
  ∫ v, M.val A v ∂D

/-- `E_D[max_i V_i]`, the prophet's expected value. -/
noncomputable def expMax {n : ℕ} (D : Measure (Fin n → ℝ)) : ℝ :=
  ∫ v, (⨆ i, v i) ∂D

/-- The best correlation-aware online value `sup_{A ∈ ALG} E_D[val(A, V)]`. -/
noncomputable def onlineOpt (M : ArrivalModel) {n : ℕ} (D : Measure (Fin n → ℝ)) : ℝ :=
  ⨆ A : M.Alg n, expVal M A D

/-- Correlation-blind competitive ratio given marginals `D_1, …, D_n` (p. 5). -/
noncomputable def blindCRGiven (M : ArrivalModel) {n : ℕ} (Dm : Fin n → Measure ℝ) (k : ℕ) :
    ℝ :=
  ⨆ A : M.Alg n, ⨅ D : kI Dm k, expVal M A D.1 / expMax D.1

/-- Correlation-aware optimal competitive ratio given marginals `D_1, …, D_n` (p. 5). -/
noncomputable def awareCRGiven (M : ArrivalModel) {n : ℕ} (Dm : Fin n → Measure ℝ) (k : ℕ) :
    ℝ :=
  ⨅ D : kI Dm k, ⨆ A : M.Alg n, expVal M A D.1 / expMax D.1

/-- Price of ignorance given marginals (Definition 2.2 without the outer infimum):
`sup_B inf_{D ∈ kI} E_D[val(B, V)] / sup_A E_D[val(A, V)]`. -/
noncomputable def poiGiven (M : ArrivalModel) {n : ℕ} (Dm : Fin n → Measure ℝ) (k : ℕ) : ℝ :=
  ⨆ B : M.Alg n, ⨅ D : kI Dm k, expVal M B D.1 / onlineOpt M D.1

/-- An instance: a number `n` of values and non-degenerate marginals `D_1, …, D_n`. -/
def Instance : Type :=
  Σ n : ℕ, {Dm : Fin n → Measure ℝ // NonDegenerate Dm}

/-- The optimal competitive ratio of correlation-blind algorithms under `k`-wise independence:
`inf_{D_1..D_n} sup_A inf_{D ∈ kI} E_D[val(A,V)] / E_D[max_i V_i]` (p. 5). -/
noncomputable def blindCR (M : ArrivalModel) (k : ℕ) : ℝ :=
  ⨅ I : Instance, blindCRGiven M I.2.1 k

/-- The optimal competitive ratio of correlation-aware algorithms under `k`-wise independence:
`inf_{D_1..D_n} inf_{D ∈ kI} sup_A E_D[val(A,V)] / E_D[max_i V_i]` (p. 1, p. 5). -/
noncomputable def awareCR (M : ArrivalModel) (k : ℕ) : ℝ :=
  ⨅ I : Instance, awareCRGiven M I.2.1 k

/-- The price of ignorance under `k`-wise independence (Definition 2.2 for `k = 2`):
`inf_{D_1..D_n} sup_B inf_{D ∈ kI} inf_A E_D[val(B,V)] / E_D[val(A,V)]`, written with
`inf_A x / E_D[val(A,V)] = x / sup_A E_D[val(A,V)]`. -/
noncomputable def PoI (M : ArrivalModel) (k : ℕ) : ℝ :=
  ⨅ I : Instance, poiGiven M I.2.1 k

end PriceIgnorance.Pairwise


