-- Prove2me | Definitions.Def_OptAbstention_TLA_Empirical
-- name    : OptAbstention_TLA_Empirical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:07:04.463203+00:00
-- url     : https://prove2.me/theorems/caa64bfb-69ab-4f94-a040-f9a3dde57977
-- title:
--   Finite samples as lists, empirical total variation, $(S_{\mathrm{cln}},\theta)$-corruptions, and the benchmarks $\lambda$ and $\mathrm{opt}_{\mathrm{train}}$
-- statement:
--   A finite multiset of size $n$ is a list $S=(S_1,\dots,S_n)$; distinct occurrences are distinct elements, and order is irrelevant wherever only the multiset matters. $U(S)$ is the uniform distribution on the occurrences, and for lists $S,S'$
--   $$d_{\mathrm{TV}}(U(S),U(S'))=\tfrac12\sum_{v}\Big|\tfrac{m_S(v)}{|S|}-\tfrac{m_{S'}(v)}{|S'|}\Big|,$$
--   where $m_S(v)$ is the multiplicity of the value $v$ in $S$. $S$ is an **$(S_{\mathrm{cln}},\theta)$-corruption** if it is obtained from $S_{\mathrm{cln}}$ by removing a submultiset of at most $\lfloor\theta|S_{\mathrm{cln}}|\rfloor$ points and adding the same number of arbitrary points.
--
--   A **labeled distribution** $\bar D$ is a probability measure on $X\times\{\pm1\}$ (labels as booleans, `true` $=+1$). For $f\in\mathcal C$, the training error is $\Pr_{(x,y)\sim\bar D}[f(x)\ne y]$, and for a labeled test list $\bar S_{\mathrm{test}}=((x_i,y_i))_{i\le n}$ the test error is $\frac1n\#\{i: f(x_i)\ne y_i\}$. The **joint error** and the **optimal training error** are
--   $$\lambda(\bar D_{\mathrm{train}},U(\bar S_{\mathrm{test}});\mathcal C)=\inf_{f\in\mathcal C}\Big(\Pr_{\bar D_{\mathrm{train}}}[f(x)\ne y]+\Pr_{U(\bar S_{\mathrm{test}})}[f(x)\ne y]\Big),\qquad \mathrm{opt}_{\mathrm{train}}=\inf_{f\in\mathcal C}\Pr_{\bar D_{\mathrm{train}}}[f(x)\ne y].$$
--
--   **Formalization Note.** Both infima are taken in $[0,\infty]$, so they are $+\infty$ (not $0$) for an empty class.
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 2, footnote 2; p. 3, (2.1) and the display below it; pp. 12–13, §5 Probability; p. 15, Definition 6.6

import Mathlib
import Definitions.Def_OptAbstention_TLA_Sandwiching

/-!
# Finite samples, empirical total variation, corruptions, and the error benchmarks λ and opt_train

Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, *Achieving the Optimal Abstention Rate
for Learning with Distribution Shift*, STOC 2027 submission (manuscript sha256 0fb30af1…):
footnote 2 (p. 2), (2.1) and the display below it (p. 3), §5 "Probability" (pp. 12–13),
Definition 6.6 (p. 15).

Conventions.
* A finite multiset of size `n` is a list `S : Fin n → Ω`; distinct occurrences are distinct
  elements (footnote 2), and a function on the multiset is a function on `Fin n`.
* `toMS S` is the underlying multiset (order forgotten). `U(S)` is the uniform distribution on the
  occurrences; `empTV S S'` is the total variation distance between `U(S)` and `U(S')`, i.e.
  `½ ∑_v |m_S(v)/|S| − m_{S'}(v)/|S'||` over the values `v` (order-free).
* A labeled distribution `D̄` is a probability measure on `X × Bool` (`true` = `+1`); its error
  `Pr_{(x,y)∼D̄}[f(x) ≠ y]` is a value in `ℝ≥0∞`. The infima `λ` and `opt_train` are taken in
  `ℝ≥0∞`, so they are `⊤` for an empty class.
-/

open MeasureTheory

namespace OptAbstention.TLA

/-- The multiset of the occurrences of a list. -/
def toMS {Ω : Type*} {n : ℕ} (S : Fin n → Ω) : Multiset Ω :=
  Finset.univ.val.map S

open Classical in
/-- `d_TV(U(S), U(S'))`: the total variation distance between the uniform distributions on the
occurrences of two finite multisets, `½ ∑_v |m_S(v)/|S| − m_{S'}(v)/|S'||`. -/
noncomputable def empTV {Ω : Type*} {n m : ℕ} (S : Fin n → Ω) (S' : Fin m → Ω) : ℝ :=
  (1 / 2 : ℝ) * ∑ v ∈ (toMS S + toMS S').toFinset,
    |((toMS S).count v : ℝ) / n - ((toMS S').count v : ℝ) / m|

open Classical in
/-- Definition 6.6: `S` is an `(S_cln, θ)`-corruption: it is obtained from `S_cln` by removing at
most `⌊θ |S_cln|⌋` points (the submultiset `A`) and replacing them with the same number of
arbitrary points (the multiset `B`). -/
def IsCorruption {Ω : Type*} {n m : ℕ} (Scln : Fin n → Ω) (S : Fin m → Ω) (θ : ℝ) : Prop :=
  ∃ A B : Multiset Ω, A ≤ toMS Scln ∧ Multiset.card A ≤ ⌊θ * n⌋₊ ∧
    Multiset.card B = Multiset.card A ∧ toMS S = toMS Scln - A + B

/-- The fraction of indices `i` with property `P i`, i.e. `Pr_{i∼U([n])}[P i]`. -/
noncomputable def frac {n : ℕ} (P : Fin n → Prop) [DecidablePred P] : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / n

/-- `Pr_{(x,y)∼D̄}[f(x) ≠ y]`, the error of `f` under a labeled distribution. -/
noncomputable def trainErr {Ω : Type*} [MeasurableSpace Ω] (Dbar : Measure (Ω × Bool))
    (f : Ω → ℝ) : ENNReal :=
  Dbar {p | f p.1 ≠ signOf p.2}

open Classical in
/-- `Pr_{(x,y)∼U(S̄_test)}[f(x) ≠ y]` for the labeled test list `(xs i, ys i)`. -/
noncomputable def testErr {Ω : Type*} {n : ℕ} (xs : Fin n → Ω) (ys : Fin n → Bool)
    (f : Ω → ℝ) : ℝ :=
  frac fun i => f (xs i) ≠ signOf (ys i)

/-- (2.1) with `D̄_test = U(S̄_test)`: the joint error
`λ(D̄_train, U(S̄_test); C) = inf_{f∈C} (Pr_{D̄_train}[f(x) ≠ y] + Pr_{U(S̄_test)}[f(x) ≠ y])`. -/
noncomputable def jointErr {Ω : Type*} [MeasurableSpace Ω] (Dbar : Measure (Ω × Bool))
    (C : Set (Ω → ℝ)) {n : ℕ} (xs : Fin n → Ω) (ys : Fin n → Bool) : ENNReal :=
  ⨅ f ∈ C, (trainErr Dbar f + ENNReal.ofReal (testErr xs ys f))

/-- `opt_train = inf_{f∈C} Pr_{(x,y)∼D̄_train}[f(x) ≠ y]` (p. 3). -/
noncomputable def optTrain {Ω : Type*} [MeasurableSpace Ω] (Dbar : Measure (Ω × Bool))
    (C : Set (Ω → ℝ)) : ENNReal :=
  ⨅ f ∈ C, trainErr Dbar f

end OptAbstention.TLA


