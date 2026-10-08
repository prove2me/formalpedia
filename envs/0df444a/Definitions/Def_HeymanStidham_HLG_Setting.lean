-- Prove2me | Definitions.Def_HeymanStidham_HLG_Setting
-- name    : HeymanStidham_HLG_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:11:28.505982+00:00
-- url     : https://prove2.me/theorems/c5947bd3-4ce3-46ee-9ef9-309f69d4d715
-- title:
--   §1, pp. 984–986 — gₙ, h, N(t), λ, G, H, ASSUMPTION (i)–(ii), fₙ⁺, fₙ⁻, U(T), V(T)
-- statement:
--   This file sets up the sample-path framework of Heyman and Stidham (1980), §1. Everything refers to one fixed sample path; the paper's $\omega$ is suppressed.
--
--   Customers are numbered in order of arrival. Customer $n$ arrives at epoch $t_n$, with $0 \le t_1 \le t_2 \le \cdots$ (ties are allowed), and carries a real-valued function $f_n$ on $[0,\infty)$. The paper's objects are:
--
--   1. the **customer total** $g_n = \int_0^\infty f_n(t)\,dt$;
--   2. the **rate** $h(t) = \sum_{n=1}^\infty f_n(t)$, summed over all customers;
--   3. the **arrival count** $N(T)$, the number of $n$ with $t_n \le T$;
--   4. "$\lambda$ exists": $\lim_{T\to\infty} N(T)/T = \lambda$;
--   5. the **customer average** $G$: $\lim_{N\to\infty} \frac1N\sum_{n=1}^N a_n = G$ for a sequence $(a_n)$ (used with $a_n = g_n, g_n^+, g_n^-$);
--   6. the **time average** $H$: $\varphi$ is integrable on every $[0,T]$ and $\lim_{T\to\infty} \frac1T\int_0^T \varphi(t)\,dt = H$ (used with $\varphi = h, h^+, h^-$);
--   7. **ASSUMPTION (i)**: for each $n$ there is $s_n \in [0,\infty)$ with $f_n(t) = 0$ whenever $t \ge 0$ and $t \notin [t_n, t_n + s_n]$;
--   8. **ASSUMPTION (ii)**: $s_n/n \to 0$;
--   9. the parts $f_n^+(t) = \max[0, f_n(t)]$ and $f_n^-(t) = \max[0, -f_n(t)]$;
--   10. the partial totals $U(T) = \sum_{n:\, t_n \le T} a_n$ and $V(T) = \sum_{n:\, t_n + s_n \le T} a_n$ (used with $a_n = g_n$).
--
--   Then $g_n^\pm$ and $h^\pm$ are the customer total and rate of $f^\pm$.
--
--   These are the objects of the relation $H = \lambda G$ between a time average and a customer average, which contains Little's law $L = \lambda W$ as the case where $f_n$ is the indicator of customer $n$'s stay in the system.
--
--   **Formalization Note** Customers are 0-based in Lean: index $n$ is the paper's customer $n+1$, so $s_n/n \to 0$ reads $s_n/(n+1) \to 0$. Only values $f_n(t)$ with $t \ge 0$ enter: $g_n$ integrates over $[0,\infty)$, (i) constrains only $t \ge 0$, and time averages integrate over $[0,T]$. $N(T)$ is the cardinality of $\{n : t_n \le T\}$ (Lean's `ncard`, which is $0$ for an infinite set; an infinite set at some $T$ forces $N \equiv 0$ beyond $T$, so any statement assuming $\lambda > 0$ excludes it). $h$, $U$ and $V$ are infinite sums (`tsum`), which equal the finite sums of the page whenever only finitely many terms are nonzero; the theorems using them guarantee this. The integrability requirement inside the time average prevents a non-integrable $h$ from having "time average" $0$.
-- source:
--   Heyman and Stidham, The relation between customer and time averages in queues, Oper. Res. 28 (1980), pp. 984–986, §1 (definitions of gₙ, h, G, H, tₙ, N(t), λ; p. 984), the ASSUMPTION (p. 985), U, V (proof of Theorem 1, p. 985), fₙ⁺, fₙ⁻, gₙ±, h±, G±, H± (p. 986). DOI 10.1287/opre.28.4.983

import Mathlib

namespace HeymanStidham.HLG

open Filter Topology MeasureTheory

/-! Heyman and Stidham (1980), §1, pp. 984–986, and the ASSUMPTION of p. 985.

The paper works on one sample path `ω`, which is dropped here. Customers are numbered
`1, 2, …` on the page; in Lean index `n : ℕ` is the paper's customer `n + 1`.
`t n` is the arrival epoch, `f n : ℝ → ℝ` the function attached to the customer (only its
values on `[0, ∞)` matter), and `s n` the bound of the ASSUMPTION. -/

/-- `gₙ = ∫₀^∞ fₙ(t) dt`, the total of customer `n`'s function (p. 984). -/
noncomputable def custTotal (f : ℕ → ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ τ in Set.Ici (0 : ℝ), f n τ

/-- `h(t) = Σ_{n ≥ 1} fₙ(t)`, summed over all customers (p. 984). -/
noncomputable def rate (f : ℕ → ℝ → ℝ) (τ : ℝ) : ℝ :=
  ∑' n, f n τ

/-- `N(T)`, the number of arrivals by time `T`: the number of `n` with `tₙ ≤ T`
(`= max {n : tₙ ≤ T}` for nondecreasing `t`, p. 984). -/
noncomputable def arrivalCount (t : ℕ → ℝ) (T : ℝ) : ℕ :=
  {n : ℕ | t n ≤ T}.ncard

/-- `λ = lim_{T → ∞} N(T)/T` exists and equals `lam` (p. 984). -/
def IsArrivalRate (t : ℕ → ℝ) (lam : ℝ) : Prop :=
  Tendsto (fun T : ℝ => (arrivalCount t T : ℝ) / T) atTop (𝓝 lam)

/-- The customer average `lim_{N → ∞} Σ_{n=1}^N aₙ / N` exists and equals `G` (p. 984). -/
def IsCustomerAverage (a : ℕ → ℝ) (G : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, a n) / (N : ℝ)) atTop (𝓝 G)

/-- The time average `lim_{T → ∞} ∫₀^T φ(t) dt / T` exists and equals `H` (p. 984);
`φ` is required to be integrable on every `[0, T]`, `T ≥ 0`, so that the integral is a
genuine one. -/
def IsTimeAverage (φ : ℝ → ℝ) (H : ℝ) : Prop :=
  (∀ T : ℝ, 0 ≤ T → IntervalIntegrable φ volume 0 T) ∧
    Tendsto (fun T : ℝ => (∫ τ in (0 : ℝ)..T, φ τ) / T) atTop (𝓝 H)

/-- ASSUMPTION (i) (p. 985): `0 ≤ sₙ < ∞`, and for `t ≥ 0`,
`t ∉ [tₙ, tₙ + sₙ] ⇒ fₙ(t) = 0`. -/
def CondI (t : ℕ → ℝ) (f : ℕ → ℝ → ℝ) (s : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ s n) ∧ ∀ n τ, 0 ≤ τ → τ ∉ Set.Icc (t n) (t n + s n) → f n τ = 0

/-- ASSUMPTION (ii) (p. 985): `sₙ / n → 0` (customer `n + 1` in Lean indexing). -/
def CondII (s : ℕ → ℝ) : Prop :=
  Tendsto (fun n : ℕ => s n / ((n : ℝ) + 1)) atTop (𝓝 0)

/-- `fₙ⁺(t) = max[0, fₙ(t)]` (p. 986). -/
def posPartFn (f : ℕ → ℝ → ℝ) (n : ℕ) (τ : ℝ) : ℝ :=
  max 0 (f n τ)

/-- `fₙ⁻(t) = max[0, −fₙ(t)]` (p. 986). -/
def negPartFn (f : ℕ → ℝ → ℝ) (n : ℕ) (τ : ℝ) : ℝ :=
  max 0 (-f n τ)

/-- `U(T) = Σ_{n ∈ N₁(T)} aₙ` with `N₁(T) = {n : tₙ ≤ T}` (p. 985); used with `aₙ = gₙ`. -/
noncomputable def arrivedTotal (t : ℕ → ℝ) (a : ℕ → ℝ) (T : ℝ) : ℝ :=
  ∑' n, Set.indicator {n : ℕ | t n ≤ T} a n

/-- `V(T) = Σ_{n ∈ N₂(T)} aₙ` with `N₂(T) = {n : tₙ + sₙ ≤ T}` (p. 985); used with `aₙ = gₙ`. -/
noncomputable def finishedTotal (t s : ℕ → ℝ) (a : ℕ → ℝ) (T : ℝ) : ℝ :=
  ∑' n, Set.indicator {n : ℕ | t n + s n ≤ T} a n

end HeymanStidham.HLG


