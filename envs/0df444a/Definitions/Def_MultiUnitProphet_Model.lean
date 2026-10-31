-- Prove2me | Definitions.Def_MultiUnitProphet_Model
-- name    : MultiUnitProphet_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:20.860991+00:00
-- url     : https://prove2.me/theorems/7ff908a4-52f1-4bd1-895d-ce6e34757b27
-- title:
--   Multi-unit prophet model: instance, $X_p$, sale rule, $\mathrm{Welfare}$, $\mathrm{Opt}$, $\delta_k(X_p)$, $\mu_k(X_p)$
-- statement:
--   An **instance** of the multi-unit prophet inequality problem is a list of $n$ probability distributions $F_1,\dots,F_n$ on the nonnegative reals, $F_t$ being the law of the value $v_t$ of the $t$-th arriving buyer; the values are independent. A supply of $k$ identical units is available.
--
--   A **static price** $p\in\mathbb R$ is posted to every buyer. Buyers arrive in the order $1,\dots,n$; buyer $t$ buys a unit iff $v_t\ge p$ and a unit is still available, i.e. fewer than $k$ earlier buyers bought. Let
--
--   $$X_p := |\{t : v_t \ge p\}|$$
--
--   be the number of buyers whose value is at least the price. The module defines:
--
--   1. $\mathrm{Welfare}(p,k,\mathcal F)$, the expected total value of the buyers who buy;
--   2. $\mathrm{Opt}(k,\mathcal F)=\mathbb E\big[\max_{S\subseteq[n],|S|\le k}\sum_{t\in S}v_t\big]$, the expected sum of the $k$ highest values;
--   3. $\mathrm{Utility}(p,k,\mathcal F)$, the expected total utility $v_t-p$ of the buyers who buy, and $U(p)=\sum_t\mathbb E[\max(0,v_t-p)]$;
--   4. $\delta_k(X_p) := \mathbb P[X_p\le k-1]$ (3.1), the probability that the units do not sell out;
--   5. $\mu_k(X_p) := \frac1k\,\mathbb E[\min\{X_p,k\}]$ (3.2), the expected fraction of units sold.
--
--   These are the objects of Lemma 1 and Theorem 1: the paper's pricing scheme posts a price with $\delta_k(X_p)=\mu_k(X_p)$.
--
--   **Formalization Note** Buyers are `Fin n` in arrival order; an instance is `F : Fin n → Measure ℝ` with every `F t` a probability measure and `F t (Set.Iio 0) = 0` (`IsInstance`), and values are drawn from `Measure.pi F`. A buyer buys iff `p ≤ v t` and `#{s < t | p ≤ v s} < k`. Welfare, Opt, Utility and $U(p)$ are lower Lebesgue integrals in $[0,\infty]$, so no finite-mean assumption is needed. $\delta_k$ is written $\mathbb P[X_p<k]$ (equal to $\mathbb P[X_p\le k-1]$ for $k\ge1$). Atoms are allowed in an instance; the atomless assumption is a separate hypothesis where needed.
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, §2, pp.6–7; §3, p.7, (3.1)–(3.2); §4, p.9

import Mathlib

namespace MultiUnitProphet

open MeasureTheory
open scoped ENNReal

/-- **Instance of the multi-unit prophet inequality problem.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, §2, p.6: "a set of n distributions supported on non-negative real numbers
F = {F_t : t ∈ [n]}", with F_t "the t-th arriving distribution" (footnote 3).

**Formalization Note.** Buyers are `Fin n`, indexed in **arrival order**; the order is arbitrary
because every theorem quantifies over every `F`. Each `F t` is a probability measure on `ℝ` with
`F t (Set.Iio 0) = 0` (support in `[0, ∞)`). Values are independent: they are drawn from
`Measure.pi F`. Atoms are allowed here; the atomless assumption of §2, p.7 is a separate
hypothesis (`∀ t, NullSingletonClass (F t)`) wherever a statement needs it. -/
def IsInstance {n : ℕ} (F : Fin n → Measure ℝ) : Prop :=
  ∀ t, IsProbabilityMeasure (F t) ∧ F t (Set.Iio 0) = 0

/-- **`X_p`, the number of buyers with value at least the price** (§3, p.7):
`X_p := |{t : v_t ≥ p}|`, evaluated at a realization `v` of the values. -/
noncomputable def Xp {n : ℕ} (p : ℝ) (v : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter (fun t => p ≤ v t)).card

/-- **The static-price sale rule** (§2, p.6): buyer `t` buys a unit at price `p` iff her value is
at least `p` and a unit is still available when she arrives, i.e. fewer than `k` **earlier**
buyers `s < t` bought.

**Formalization Note.** "Above the price" is read as `v_t ≥ p`, matching `X_p := |{t : v_t ≥ p}|`
(p.7). The earlier buyers who bought are exactly the earlier buyers with `v_s ≥ p` as long as that
count is below `k` (once `k` units are sold nobody else buys), so the availability test is
`#{s < t | p ≤ v s} < k`. Buyer `t` is not counted in her own test. -/
def buys {n : ℕ} (k : ℕ) (p : ℝ) (v : Fin n → ℝ) (t : Fin n) : Prop :=
  p ≤ v t ∧ (Finset.univ.filter (fun s => s < t ∧ p ≤ v s)).card < k

open Classical in
/-- **`Welfare(p, k, F)`** (§2, p.7): the expected total value of the buyers who purchase a unit
when the static price `p` is posted to the buyers arriving in the order `0, 1, …, n − 1` with
supply `k`.

**Formalization Note.** A lower Lebesgue integral in `ℝ≥0∞` (no integrability hypothesis is
needed; it is `+∞` if the expected welfare is infinite). -/
noncomputable def welfare {n : ℕ} (k : ℕ) (F : Fin n → Measure ℝ) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ v, ∑ t, (if buys k p v t then ENNReal.ofReal (v t) else 0) ∂(Measure.pi F)

/-- **`Opt(k, F)`** (§2, p.7): "the expected sum of the k highest realized values drawn from the
set of distributions F", written as on p.9, `E[max_{S ⊆ [n]; |S| ≤ k} Σ_{t ∈ S} v_t]`.

**Formalization Note.** A lower Lebesgue integral in `ℝ≥0∞`; the maximum over `|S| ≤ k` is a
`Finset.sup`. Values are nonnegative almost surely, so this is the sum of the `k` largest
values (all values when `n ≤ k`). -/
noncomputable def opt {n : ℕ} (k : ℕ) (F : Fin n → Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ v, ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ k)).sup
      (fun S => ∑ t ∈ S, ENNReal.ofReal (v t)) ∂(Measure.pi F)

open Classical in
/-- **`Utility(p, k, F)`** (§4, p.9): the expected total utility `v_t − p` of the buyers who
purchase a unit at the static price `p`.

**Formalization Note.** A lower Lebesgue integral in `ℝ≥0∞`; a buyer who buys has `v_t ≥ p`, so
`ENNReal.ofReal (v t - p)` is exactly `v_t − p` there. -/
noncomputable def utility {n : ℕ} (k : ℕ) (F : Fin n → Measure ℝ) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ v, ∑ t, (if buys k p v t then ENNReal.ofReal (v t - p) else 0) ∂(Measure.pi F)

/-- **`U(p) = Σ_t E[max(0, v_t − p)]`** (§1.2, p.3 and §4, p.9): the total excess value of the
buyers above the price, which (p.9) is `Σ_{t ∈ [n]} P[t ∈ Z_p] E[v_t − p | t ∈ Z_p]`.

**Formalization Note.** `ENNReal.ofReal x = max(0, x)`, so each summand is `E[max(0, v_t − p)]`,
which equals `P[t ∈ Z_p] · E[v_t − p | t ∈ Z_p]` without dividing by a possibly zero
probability. -/
noncomputable def surplus {n : ℕ} (F : Fin n → Measure ℝ) (p : ℝ) : ℝ≥0∞ :=
  ∑ t, ∫⁻ v, ENNReal.ofReal (v t - p) ∂(Measure.pi F)

/-- **`δ_k(X_p) := P[X_p ≤ k − 1]`** (3.1), p.7: the probability that the seller does not run out
of units at price `p`.

**Formalization Note.** Written as `P[X_p < k]`, which is `P[X_p ≤ k − 1]` for `k ≥ 1` and avoids
natural-number subtraction (at `k = 0` it is `0`). The measure `Measure.pi F` is a probability
measure for every instance (`IsInstance F`). -/
noncomputable def delta {n : ℕ} (k : ℕ) (F : Fin n → Measure ℝ) (p : ℝ) : ℝ :=
  (Measure.pi F).real {v | Xp p v < k}

/-- **`µ_k(X_p) := (1/k) E[min{X_p, k}]`** (3.2), p.7: the expected fraction of the `k` units sold
at price `p`.

**Formalization Note.** A Bochner integral of a function with values in `{0, …, k}`; it is
bounded and measurable, so it is integrable under every probability measure. -/
noncomputable def mu {n : ℕ} (k : ℕ) (F : Fin n → Measure ℝ) (p : ℝ) : ℝ :=
  (1 / (k : ℝ)) * ∫ v, ((min (Xp p v) k : ℕ) : ℝ) ∂(Measure.pi F)

end MultiUnitProphet


