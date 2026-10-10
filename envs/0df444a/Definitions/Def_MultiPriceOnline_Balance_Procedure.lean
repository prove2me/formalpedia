-- Prove2me | Definitions.Def_MultiPriceOnline_Balance_Procedure
-- name    : MultiPriceOnline_Balance_Procedure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:54.74165+00:00
-- url     : https://prove2.me/theorems/36d06676-401e-4907-abc2-b1366d9c8746
-- title:
--   (14)–(15), (17)–(18), Definition 3, (20) and (45), pp. 18–21, 43–44 — randomized procedures initializing one item's value function
-- statement:
--   This module defines the randomized procedures with which Multi-price Balance initializes the value function of one item, the conditions (17)–(18) of Theorem 4, and the two procedures the paper uses.
--
--   Fix an item with inventory $k$ and prices $r^{(1)}<\dots<r^{(m)}$ ($r^{(0)}=0$).
--
--   1. **Configurations** (14). Segment borders $\tilde L^{(0)},\dots,\tilde L^{(m)}\in\{0,\tfrac1k,\dots,1\}$ with $0=\tilde L^{(0)}\le\dots\le \tilde L^{(m)}=1$.
--   2. **Value functions** (15). Values $\tilde\Phi(0),\tilde\Phi(\tfrac1k),\dots,\tilde\Phi(1)$ with $0=\tilde\Phi(0)\le\tilde\Phi(\tfrac1k)\le\dots\le\tilde\Phi(1)$.
--   3. **Randomized procedure** (p. 21). A probability distribution $\rho$ over configurations, and for each configuration a value function. Configurations of positive probability must satisfy (14) and their value functions (15).
--   4. **Condition (17)** with constant $c$. For every configuration of positive probability, every $j\in[m]$ and every $N\in\{0,\dots,\tilde L^{(j)}k-1\}$,
--   $$
--   k\Big(\tilde\Phi\big(\tfrac{N+1}{k}\big)-\tilde\Phi\big(\tfrac Nk\big)\Big)+\tilde\Phi\big(\tilde L^{(j)}\big)-\tilde\Phi\big(\tfrac Nk\big)\le\frac{r^{(j)}}{c}.
--   $$
--   5. **Condition (18).** $\mathbb E[\tilde\Phi(\tilde L^{(j)})]\ge r^{(j)}$ for $j\in[m]$, the expectation over $\rho$.
--   6. **Definition 3.** Given booking limits $\alpha$ with borders $L^{(j)}$, draw $W$ uniformly from $[0,1]$. Set $\tilde L^{(j)}=(\lfloor L^{(j)}k\rfloor+1)/k$ if $W<L^{(j)}k-\lfloor L^{(j)}k\rfloor$ and $\tilde L^{(j)}=\lfloor L^{(j)}k\rfloor/k$ otherwise. For $q\in\{0,\tfrac1k,\dots,1\}$, let $\tilde\ell(q)$ be the $j\in[m]$ with $\tilde L^{(j-1)}\le q<\tilde L^{(j)}$, and $\tilde\ell(1)=m$. The value function is (20):
--   $$
--   \tilde\Phi(q)=\sum_{j=1}^{\tilde\ell(q)-1}\big(r^{(j)}-r^{(j-1)}\big)\frac{e^{\tilde L^{(j)}-\tilde L^{(j-1)}}-1}{e^{\alpha^{(j)}}-1}+\big(r^{(\tilde\ell(q))}-r^{(\tilde\ell(q)-1)}\big)\frac{e^{q-\tilde L^{(\tilde\ell(q)-1)}}-1}{e^{\alpha^{(\tilde\ell(q))}}-1}.
--   $$
--   The probability of a configuration is the Lebesgue measure of the seeds $W\in[0,1]$ that produce it.
--   7. **The procedure (45) for $k=1$.** Configuration $d\in[m]$ has $\tilde L^{(0)}=\dots=\tilde L^{(d-1)}=0$ and $\tilde L^{(d)}=\dots=\tilde L^{(m)}=1$. It is drawn with probability $\rho_d=\sigma^{(d)}$, and its value function is $f_d(0)=0$, $f_d(1)=r^{(d)}/\sigma^{(1)}$.
--
--   By Theorem 4, procedures satisfying (17)–(18) with constant $c$ make Multi-price Balance $c$-competitive. Theorem 5 and (45) supply such procedures, and together they give the bounds of Theorem 1.
--
--   **Formalization Note** Everything is in unit indices: a configuration is a map $c:\{0,\dots,m\}\to\{0,\dots,k\}$ with $c(j)=k\tilde L^{(j)}$, and a value function is $\varphi:\mathbb N\to\mathbb R$ with $\varphi(N)=\tilde\Phi(N/k)$, read only at $N=0,\dots,k$. In (17) the range $N\in\{0,\dots,\tilde L^{(j)}k-1\}$ is written $N<c(j)$, which is empty when $\tilde L^{(j)}=0$. In Definition 3, $\tilde\ell(N/k)$ is computed as $1+\#\{j\in[1,m-1]:c(j)\le N\}$. For a monotone configuration this is the unique $j$ with $c(j-1)\le N<c(j)$ (the half-open segments partition $\{0,\dots,k-1\}$, even when some are empty), and it is $m$ at $N=k$. Step 2 uses the natural-number floor and caps the result at $k$ so that it lies in $\{0,\dots,k\}$. For booking limits ($0\le L^{(j)}\le1$, $L^{(m)}=1$) the floor is the integer floor and the cap never binds. Configurations outside the support of (45) get probability $0$ and value function $0$.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 18, (14)–(15); p. 19, (17)–(18); p. 21, randomized procedures, Definition 3, (20); pp. 43–44, App. B.2, (44), (45)

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet

namespace MultiPriceOnline.Balance

/-! Randomized procedures for initializing one item's segment borders and value function
(Ma–Simchi-Levi, arXiv:1905.04770v1, §3, pp. 18–21, and App. B.2, pp. 43–44), for an item with
inventory `k` and `m` prices. Everything is in *unit indices*: a border `L̃⁽ʲ⁾ ∈ {0, 1/k, …, 1}` is
stored as the natural number `k L̃⁽ʲ⁾ ∈ {0, …, k}`, and a value function `Φ̃` on `{0, 1/k, …, 1}` is
stored as `φ : ℕ → ℝ` with `φ N = Φ̃(N/k)`, read only at `N = 0, …, k`. -/

/-- A configuration of segment borders: `c j = k L̃⁽ʲ⁾` for `j = 0, …, m`. -/
abbrev Config (k m : ℕ) := Fin (m + 1) → Fin (k + 1)

/-- The border `k L̃⁽ʲ⁾` of configuration `c`, read at a natural number `j ≤ m`
(the value `k` for `j > m` is never used). -/
def cv {k m : ℕ} (c : Config k m) (j : ℕ) : ℕ :=
  if h : j < m + 1 then ((c ⟨j, h⟩ : Fin (k + 1)) : ℕ) else k

/-- Condition (14) (p. 18): `0 = L̃⁽⁰⁾ ≤ … ≤ L̃⁽ᵐ⁾ = 1`, the borders lying in `{0, 1/k, …, 1}`. -/
def IsConfig {k m : ℕ} (c : Config k m) : Prop :=
  ((c 0 : Fin (k + 1)) : ℕ) = 0 ∧ ((c (Fin.last m) : Fin (k + 1)) : ℕ) = k ∧ Monotone c

/-- Condition (15) (p. 18): `0 = Φ̃(0) ≤ Φ̃(1/k) ≤ … ≤ Φ̃(1)`, with `φ N = Φ̃(N/k)`. -/
def IsValueFn (k : ℕ) (φ : ℕ → ℝ) : Prop :=
  φ 0 = 0 ∧ ∀ N, N < k → φ N ≤ φ (N + 1)

/-- A randomized procedure (p. 21; the variables `ρ_d`, `f_d` of (44), p. 43): a probability
weight `ρ c` on each configuration `c`, and for each configuration a value function `Φ c`. -/
structure Procedure (k m : ℕ) where
  /-- probability of drawing configuration `c` -/
  ρ : Config k m → ℝ
  /-- the value function used with configuration `c` (`Φ c N = Φ̃(N/k)`) -/
  Φ : Config k m → ℕ → ℝ

/-- `P` is a randomized procedure in the sense of p. 21: `ρ` is a probability distribution on
configurations, and every configuration drawn with positive probability satisfies (14) and its
value function satisfies (15). -/
def IsProcedure {k m : ℕ} (P : Procedure k m) : Prop :=
  (∀ c, 0 ≤ P.ρ c) ∧ (∑ c, P.ρ c) = 1 ∧
    ∀ c, P.ρ c ≠ 0 → IsConfig c ∧ IsValueFn k (P.Φ c)

/-- Condition (17) of Theorem 4 (p. 19) with constant `c`, for every potential initialization
(every configuration `c₀` of positive probability), every `j ∈ [m]` and every
`N ∈ {0, …, L̃⁽ʲ⁾k − 1}`:
`k (Φ̃((N+1)/k) − Φ̃(N/k)) + Φ̃(L̃⁽ʲ⁾) − Φ̃(N/k) ≤ r⁽ʲ⁾ / c`. -/
def Cond17 {k m : ℕ} (r : ℕ → ℝ) (P : Procedure k m) (c : ℝ) : Prop :=
  ∀ c₀, P.ρ c₀ ≠ 0 → ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ N : ℕ, N < cv c₀ j →
    (k : ℝ) * (P.Φ c₀ (N + 1) - P.Φ c₀ N) + P.Φ c₀ (cv c₀ j) - P.Φ c₀ N ≤ r j / c

/-- Condition (18) of Theorem 4 (p. 19): `𝔼[Φ̃(L̃⁽ʲ⁾)] ≥ r⁽ʲ⁾` for `j ∈ [m]`, the expectation being
over the procedure's distribution of configurations. -/
def Cond18 {k m : ℕ} (r : ℕ → ℝ) (P : Procedure k m) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ m → r j ≤ ∑ c₀, P.ρ c₀ * P.Φ c₀ (cv c₀ j)

/-- Step 2 of Definition 3 (p. 21) for seed `W`: `L̃⁽ʲ⁾ = (⌊L⁽ʲ⁾k⌋ + 1)/k` if
`W < L⁽ʲ⁾k − ⌊L⁽ʲ⁾k⌋`, and `L̃⁽ʲ⁾ = ⌊L⁽ʲ⁾k⌋/k` otherwise; in unit indices `k L̃⁽ʲ⁾`.
The value is capped at `k` to have type `Fin (k+1)`; for booking limits (`0 ≤ L⁽ʲ⁾ ≤ 1`) the cap
never binds. -/
noncomputable def def3Config (k m : ℕ) (α : ℕ → ℝ) (W : ℝ) : Config k m := fun j =>
  ⟨min k (⌊Lsum α j * k⌋₊ + if W < Lsum α j * k - ⌊Lsum α j * k⌋₊ then 1 else 0),
    Nat.lt_succ_of_le (min_le_left _ _)⟩

/-- Step 3 of Definition 3 (p. 21): `ℓ̃(q)` for `q = N/k`, the `j ∈ [m]` with
`L̃⁽ʲ⁻¹⁾ ≤ q < L̃⁽ʲ⁾` (and `m` at `q = 1`), computed as `1 + #{j ∈ [1, m−1] : k L̃⁽ʲ⁾ ≤ N}`. -/
def ellTilde {k m : ℕ} (c : Config k m) (N : ℕ) : ℕ :=
  1 + ((Finset.Icc 1 (m - 1)).filter (fun j => cv c j ≤ N)).card

/-- The value function (20) of Definition 3 (p. 21) for configuration `c`, at `q = N/k`:
`Φ̃(q) = ∑_{j=1}^{ℓ̃(q)−1} (r⁽ʲ⁾ − r⁽ʲ⁻¹⁾) (exp(L̃⁽ʲ⁾ − L̃⁽ʲ⁻¹⁾) − 1)/(exp(α⁽ʲ⁾) − 1)
  + (r^{(ℓ̃(q))} − r^{(ℓ̃(q)−1)}) (exp(q − L̃^{(ℓ̃(q)−1)}) − 1)/(exp(α^{(ℓ̃(q))}) − 1)`,
with `r⁽⁰⁾ = 0`. -/
noncomputable def def3Phi (k m : ℕ) (r α : ℕ → ℝ) (c : Config k m) (N : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 (ellTilde c N - 1),
      (pr r j - pr r (j - 1)) *
        (Real.exp ((cv c j : ℝ) / k - (cv c (j - 1) : ℝ) / k) - 1) / (Real.exp (α j) - 1)) +
    (pr r (ellTilde c N) - pr r (ellTilde c N - 1)) *
      (Real.exp ((N : ℝ) / k - (cv c (ellTilde c N - 1) : ℝ) / k) - 1) /
        (Real.exp (α (ellTilde c N)) - 1)

/-- The randomized procedure of Definition 3 (p. 21): the seed `W` is uniform on `[0, 1]`, so
configuration `c` has probability `vol{W ∈ [0, 1] : Step 2 yields c}`, and its value function is
(20). -/
noncomputable def def3Proc (k m : ℕ) (r α : ℕ → ℝ) : Procedure k m where
  ρ c := (MeasureTheory.volume (Set.Icc (0 : ℝ) 1 ∩ {W | def3Config k m α W = c})).toReal
  Φ := def3Phi k m r α

/-- For `k = 1`, configuration `d` of App. B.2 (p. 43): `L̃⁽⁰⁾ = … = L̃⁽ᵈ⁻¹⁾ = 0` and
`L̃⁽ᵈ⁾ = … = L̃⁽ᵐ⁾ = 1`. -/
def cfg45 (m d : ℕ) : Config 1 m := fun j => if (j : ℕ) < d then 0 else 1

/-- The `k = 1` procedure (45) (App. B.2, p. 44): configuration `d ∈ [m]` is drawn with probability
`ρ_d = σ⁽ᵈ⁾`, and its value function is `f_d(0) = 0`, `f_d(1) = r⁽ᵈ⁾/σ⁽¹⁾`. Configurations other than
`cfg45 m d`, `d ∈ [m]`, get probability `0` (and the value function `0`). -/
noncomputable def proc45 (m : ℕ) (r σ : ℕ → ℝ) : Procedure 1 m where
  ρ c := ∑ d ∈ Finset.Icc 1 m, if c = cfg45 m d then σ d else 0
  Φ c N := if N = 0 then 0 else ∑ d ∈ Finset.Icc 1 m, if c = cfg45 m d then r d / σ 1 else 0

end MultiPriceOnline.Balance


