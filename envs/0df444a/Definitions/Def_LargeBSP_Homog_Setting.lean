-- Prove2me | Definitions.Def_LargeBSP_Homog_Setting
-- name    : LargeBSP_Homog_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:07.509734+00:00
-- url     : https://prove2.me/theorems/13e88da3-19f9-4ce1-b349-c2c282beaa36
-- title:
--   §3–§4.2, pp. 7–12 — top-n valuation V_N(n), cost c_N(n) (1), BSP menus, choice ζ, profit (2), optimum (3), PPD, V̄_N, c̄_N (11)–(12), V̄, t⋆
-- statement:
--   The bundle-size pricing (BSP) model of Abdallah, Asadpour and Reed.
--
--   A firm sells $N \ge 1$ products to one customer whose valuations are $X_1, \dots, X_N \ge 0$, additive over bundles. The firm's marginal costs are $c_1, \dots, c_N \ge 0$.
--
--   1. **Order statistics and bundle value.** Let $X_{(1)} \le \dots \le X_{(N)}$ be the order statistics and $\tau$ the permutation with $X_{\tau(n)} = X_{(n)}$, ties broken so that the customer prefers the item with the lowest index. The value of a bundle of size $n$ is $V_N(n) = \sum_{k=0}^{n-1} X_{(N-k)}$ (the $n$ largest valuations), with $V_N(0) = 0$, and its cost is
--   $$c_N(n) = \sum_{k=0}^{n-1} c_{\tau(N-k)} \qquad (1).$$
--
--   2. **Menus and choice.** A BSP menu is $p = (p(1), \dots, p(N)) \in (\mathbb R_+ \cup \{\infty\})^N$; $p(n) = +\infty$ means size $n$ is not offered. The customer buys a size $\zeta(X,p) \in \arg\max_{n = 0, \dots, N} (V_N(n) - p(n))$, where $n = 0$ (no purchase, $p_0 = 0$) is always available.
--
--   3. **Profit and the BSP problem.** The realized profit is
--   $$\pi(p) = \sum_{n=1}^N (p(n) - c_N(n))\,\mathbf 1\{\zeta(X,p) = n\} \qquad (2),$$
--   and $\mathbb E[\pi(p^\star)] = \sup_{p} \mathbb E[\pi(p)]$ over all BSP menus is the value of [BSP] (3). The perfect-price-discrimination benchmark is $\mathrm{PPD} = \sum_{n=1}^N \mathbb E[(X_n - c_n)^+]$.
--
--   4. **Normalized curves (11)–(12).** $\bar V_N(t) = \frac1N V_N(\lfloor Nt \rfloor)$ and $\bar c_N(t) = \frac1N c_N(\lfloor Nt \rfloor)$ for $t \in [0,1]$.
--
--   5. **Limits of Theorem 2.** For the valuation distribution $F_X$, $\bar V(t) = \int_0^t F_X^{-1}(1-s)\,ds$ and $t^\star = \sup\{ s \in (0,1) : F_X^{-1}(1-s) \ge c\}$.
--
--   6. **The single-size menu of Theorem 1.** $p(n) = q$ if $n = m$ and $+\infty$ otherwise.
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** Items are 0-indexed (`i < N` is the page's item $i+1$) and a valuation profile is one sequence $x : \mathbb N \to \mathbb R$ whose first $N$ terms are the $N$-product vector. `rank x N i` counts the items ranked ahead of $i$ (higher value, or equal value and lower index), and `topSet x N n` is the set of the $n$ top-ranked items, so $V_N$ and $c_N$ are sums over it. A menu is `ℕ → WithTop ℝ` with `⊤` for $+\infty$; `IsBSPMenu` says every finite price is $\ge 0$; entry $0$ is ignored. The customer's choice is the **smallest** surplus-maximizing offered size (the page leaves ties between sizes unspecified; with this rule an indifferent customer does not buy, which is why $\mathbb E[\pi(p^\star)]$ is a supremum that need not be attained). $\mathbb E[\pi(p^\star)]$ is a real supremum over menus; it is bounded above by $\mathbb E\sum_n X_n$, so it is not a junk value under integrable valuations. $F_X$ is `cdf ν` for a probability measure `ν` on $\mathbb R$. $t^\star$'s set is taken over $(0,1)$, where $F_X^{-1}(1-s)$ is defined; its supremum is $0$ when the set is empty, which is the correct value (no profitable size).
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), §3, pp. 7–8, (1)–(3); p. 10 (PPD); §4.1, p. 11, (11)–(12), Theorem 1 (p_N); §4.2, p. 12, Theorem 2 (V̄, t⋆)

import Mathlib
import Definitions.Def_LargeBSP_Homog_Quantile

open MeasureTheory ProbabilityTheory

namespace LargeBSP.Homog

/-- The number of items `j < N` that the customer ranks ahead of item `i`: a strictly higher
valuation, or an equal valuation and a lower index (the page's tie-break, p. 7: "the customer prefers
the item with the lowest index amongst all such items"). Item `i < N` has rank `r` iff it is
`τ(N − r)` in the page's notation. -/
noncomputable def rank (x : ℕ → ℝ) (N i : ℕ) : ℕ :=
  ((Finset.range N).filter (fun j => x i < x j ∨ (x j = x i ∧ j < i))).card

/-- The items `τ(N), τ(N−1), …, τ(N−n+1)` placed in a bundle of size `n` (the `n` items of largest
valuation, ties broken towards the lowest index). Empty for `n = 0`; all of `{0, …, N−1}` for `n ≥ N`. -/
noncomputable def topSet (x : ℕ → ℝ) (N n : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun i => rank x N i < n)

/-- `V_N(n) = Σ_{k=0}^{n−1} X_(N−k)`, the valuation of a bundle of size `n` (p. 7); `V_N(0) = 0`. -/
noncomputable def V (x : ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑ i ∈ topSet x N n, x i

/-- `c_N(n) = Σ_{k=0}^{n−1} c_{τ(N−k)}`, the cost of a bundle of size `n`, display (1), p. 7. -/
noncomputable def cost (c x : ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑ i ∈ topSet x N n, c i

/-- `V̄_N(t) = (1/N) V_N(⌊Nt⌋)`, display (11), p. 11. -/
noncomputable def Vbar (x : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  V x N ⌊(N : ℝ) * t⌋₊ / N

/-- `c̄_N(t) = (1/N) c_N(⌊Nt⌋)`, display (12), p. 11. -/
noncomputable def cbar (c x : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  cost c x N ⌊(N : ℝ) * t⌋₊ / N

/-- A bundle-size price menu: `p n` is the price of a bundle of size `n`, and `p n = ⊤` (the page's
`+∞`) means size `n` is not offered. The entry `p 0` is ignored (the page's `p₀ = 0`). -/
abbrev Menu := ℕ → WithTop ℝ

/-- A BSP menu, `p ∈ (ℝ₊ ∪ ∞)^{N+1}` (display (3), p. 8): every finite price is nonnegative. -/
def IsBSPMenu (p : Menu) : Prop :=
  ∀ n (r : ℝ), p n = (r : WithTop ℝ) → 0 ≤ r

/-- The sizes the customer can choose: `0` (no purchase) and every `1 ≤ n ≤ N` with a finite price. -/
noncomputable def offered (N : ℕ) (p : Menu) : Finset ℕ :=
  insert 0 ((Finset.Icc 1 N).filter (fun n => p n ≠ ⊤))

/-- The price paid for size `n`: `0` for `n = 0`, the finite price otherwise (only read on offered
sizes, where `p n` is finite). -/
noncomputable def price (p : Menu) (n : ℕ) : ℝ :=
  if n = 0 then 0 else WithTop.untopD 0 (p n)

/-- The customer's surplus `V_N(n) − p(n)` from size `n`. -/
noncomputable def surplus (x : ℕ → ℝ) (N : ℕ) (p : Menu) (n : ℕ) : ℝ :=
  V x N n - price p n

/-- The size bought, `ζ(X, p) ∈ argmax_{n = 0,…,N} (V_N(n) − p(n))` (p. 7): the **smallest** offered
size maximizing the surplus (a tie-break the page leaves unstated). The set is nonempty (a finite
nonempty set of sizes has a maximizer), so `sInf` is its least element. -/
noncomputable def choice (x : ℕ → ℝ) (N : ℕ) (p : Menu) : ℕ :=
  sInf {n : ℕ | n ∈ offered N p ∧ ∀ k ∈ offered N p, surplus x N p k ≤ surplus x N p n}

/-- The firm's realized profit `π(p) = Σ_{n=1}^N (p(n) − c_N(n)) 1{ζ(X,p) = n}`, display (2), p. 8. -/
noncomputable def profit (c x : ℕ → ℝ) (N : ℕ) (p : Menu) : ℝ :=
  if choice x N p = 0 then 0 else price p (choice x N p) - cost c x N (choice x N p)

/-- The expected profit `E[π(p)]` when the customer's valuations are `X 0 ω, …, X (N−1) ω`. -/
noncomputable def expProfit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (c : ℕ → ℝ) (N : ℕ) (p : Menu) : ℝ :=
  ∫ ω, profit c (fun n => X n ω) N p ∂P

/-- `E[π(p⋆)]`, the value of the BSP problem (3), p. 8: the supremum of `E[π(p)]` over all menus with
prices in `ℝ₊ ∪ {∞}`. (The page notes the set `𝒫⋆` of optimal menus may be empty; the value is the
supremum.) -/
noncomputable def optProfit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ⨆ p : {p : Menu // IsBSPMenu p}, expProfit P X c N p.1

/-- Perfect price discrimination profit `PPD = Σ_{n=1}^N E[(X_n − c_n)^+]`, p. 10. -/
noncomputable def PPD {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ∫ ω, max (X n ω - c n) 0 ∂P

/-- The limit `V̄(t) = ∫_0^t F_X⁻¹(1 − s) ds` of Theorem 2, p. 12, with `F_X = cdf ν`. -/
noncomputable def Vlim (ν : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, quantile (cdf ν) (1 - s)

/-- `t⋆ = sup {s : F_X⁻¹(1 − s) ≥ c}` of Theorem 2, p. 12, the supremum taken over `s ∈ (0,1)`
(where `F_X⁻¹(1 − s)` is defined). It is `sSup ∅ = 0` when no `s` qualifies. -/
noncomputable def tstar (ν : Measure ℝ) (c : ℝ) : ℝ :=
  sSup {s : ℝ | s ∈ Set.Ioo 0 1 ∧ c ≤ quantile (cdf ν) (1 - s)}

/-- The single-size menu of Theorem 1, p. 11: size `m` at price `q`, every other size `+∞`. -/
noncomputable def singleSizeMenu (m : ℕ) (q : ℝ) : Menu :=
  fun n => if n = m then (q : WithTop ℝ) else ⊤

end LargeBSP.Homog


