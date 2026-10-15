-- Prove2me | Definitions.Def_InterdepSOS_RSVCG_Setting
-- name    : InterdepSOS_RSVCG_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:52.170803+00:00
-- url     : https://prove2.me/theorems/a2eb8727-ad76-4434-88f5-d12f62948ca8
-- title:
--   §2.2–§2.3 — multidimensional combinatorial signals, bundle valuations, SOS and separable SOS (Definitions 2.10–2.13, 2.16), combinatorial ex-post IC/IR
-- statement:
--   This file sets up the combinatorial auction with interdependent valuations and multidimensional signals of Eden, Feldman, Fiat, Goldner and Karlin (§2.2–§2.3).
--
--   There are $n$ agents $[n]$ and $m$ items $[m]$; a **bundle** is a subset $T \subseteq [m]$.
--
--   1. **Signals.** Each agent $i$ holds one private signal $s_{iT} \in \mathbb{R}_+ = [0,\infty)$ for every bundle $T$. For a bundle $T$, $s_T = (s_{1T}, \dots, s_{nT}) \in \mathbb{R}_+^n$ collects all agents' signals for $T$.
--   2. **Valuations.** Agent $i$'s value for $T$ is $v_{iT}(s_T)$, a function of $s_T$ only (Definition 2.10). The standing hypotheses are: $v_{iT} \ge 0$; $v_{i\emptyset} \equiv 0$; and for every nonempty $T$, $v_{iT}$ is weakly increasing in every coordinate and strictly increasing in the agent's own coordinate $s_{iT}$.
--   3. **Feasible allocations.** An allocation $(T_1, \dots, T_n)$ gives bundle $T_i$ to agent $i$; it is a feasible allocation to a set of agents $N$ when the bundles are pairwise disjoint and $T_i = \emptyset$ for $i \notin N$ (Definition 2.11). The (true) social welfare of $(T_i)$ at $s$ is $\sum_i v_{iT_i}(s_{T_i})$.
--   4. **SOS** (Definition 2.13 with $d = 1$). A function $w : \mathbb{R}_+^n \to \mathbb{R}$ is $d$-SOS if for every coordinate $j$, all $x, \delta \ge 0$ and all profiles $s, s'$ with $s'_l \le s_l$ for every $l \ne j$,
--   $$w(s_{-j}, x+\delta) - w(s_{-j}, x) \le d\,\bigl(w(s'_{-j}, x+\delta) - w(s'_{-j}, x)\bigr),$$
--   and SOS if this holds with $d = 1$.
--   5. **Separable SOS** (Definition 2.16). The valuations are separable SOS with decomposition $(g, h)$ if for every agent $i$ and nonempty bundle $T$,
--   $$v_{iT}(s_T) = g_{-iT}(s_{-iT}) + h_{iT}(s_{iT}),$$
--   where $g_{-iT}$ (a function of the other agents' bundle-$T$ signals) and $h_{iT}$ are weakly increasing and $g_{-iT}$ is SOS.
--   6. **Utility and incentives** (Definitions 2.3–2.5, 2.12). For a deterministic mechanism $(x, p)$ mapping reported profiles to allocations and payments, the utility of agent $i$ with true profile $s$ who reports $s'_i$ while the others report truthfully is $v_{iT'}(s_{T'}) - p_i(s'_i, s_{-i})$, where $T'$ is the bundle allocated to $i$ at $(s'_i, s_{-i})$. The mechanism is **ex-post IC** if truthful reporting maximises this utility for every $i$ and every $s$, and **ex-post IR** if the truthful utility is nonnegative.
--   7. **Random partition.** The expectation over a uniformly random partition $(A, B)$ of the agents is $\mathbb{E}_B[f(B)] = 2^{-n} \sum_{B \subseteq [n]} f(B)$, with $A = [n] \setminus B$.
--
--   These are the objects of Theorem 5.1 and of the RS-VCG mechanism built on them.
--
--   **Formalization Note** Signals are `NNReal` (the paper's $\mathbb{R}_+$, read as $[0,\infty)$ because the paper sets signals to $0$). Because a strictly increasing value is impossible for a bundle worth $0$, the empty bundle has value $0$ and the two monotonicity clauses, as well as the separable decomposition, are required for nonempty bundles only. The function $g_{-iT}$ is written on the whole vector $s_T$ with the hypothesis that it ignores coordinate $i$. A report of agent $i$ is a whole vector of bundle signals, and the value in the utility is taken at the true profile.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), pp. 10–12, Definitions 2.3–2.5, 2.10–2.13, 2.15, 2.16

import Mathlib

namespace InterdepSOS.RSVCG

/-- A bundle of items: a subset of `[m] = Fin m`. -/
abbrev Bundle (m : ℕ) := Finset (Fin m)

/-- A profile of signals for one bundle (`s_T = (s_{1T}, …, s_{nT}) ∈ ℝ₊ⁿ`). -/
abbrev Signal (n : ℕ) := Fin n → NNReal

/-- A full multi-dimensional signal profile: `s j T` is agent `j`'s signal `s_{jT}` for bundle `T`
(Definition 2.10). -/
abbrev Profile (n m : ℕ) := Fin n → Bundle m → NNReal

/-- Bundle valuations: `v i T z` is `v_{iT}(z)` for a bundle-`T` signal vector `z`. -/
abbrev Valuation (n m : ℕ) := Fin n → Bundle m → Signal n → ℝ

/-- A combinatorial allocation: agent `i` receives the bundle `T i`. -/
abbrev Alloc (n m : ℕ) := Fin n → Bundle m

/-- The bundle-`T` signal vector `s_T = (s_{1T}, …, s_{nT})`. -/
def sigT {n m : ℕ} (s : Profile n m) (T : Bundle m) : Signal n :=
  fun j => s j T

/-- Keep the coordinates in `S`, set the others to `0`. -/
def keepOn {n : ℕ} (S : Finset (Fin n)) (z : Signal n) : Signal n :=
  fun j => if j ∈ S then z j else 0

/-- Standing hypotheses on bundle valuations (Definition 2.10, read with slips 2 and 7):
values are nonnegative, the empty bundle is worth `0`, and for every nonempty bundle the value is
weakly increasing in every signal and strictly increasing in the agent's own signal. -/
def IsCombValuation {n m : ℕ} (v : Valuation n m) : Prop :=
  (∀ i T z, 0 ≤ v i T z) ∧
  (∀ i z, v i ∅ z = 0) ∧
  (∀ i (T : Bundle m), T.Nonempty → Monotone (v i T)) ∧
  (∀ i (T : Bundle m), T.Nonempty → ∀ (z : Signal n) (x y : NNReal), x < y →
    v i T (Function.update z i x) < v i T (Function.update z i y))

/-- `d`-SOS (Definition 2.13, inequality (1)): raising coordinate `j` from `x` to `x + δ` gains at a
profile `s` at most `d` times what it gains at any profile `s'` that is coordinatewise below `s` off `j`. -/
def IsDSOS {n : ℕ} (d : ℝ) (w : Signal n → ℝ) : Prop :=
  ∀ j (x δ : NNReal) (s s' : Signal n),
    (∀ l, l ≠ j → s' l ≤ s l) →
    w (Function.update s j (x + δ)) - w (Function.update s j x) ≤
      d * (w (Function.update s' j (x + δ)) - w (Function.update s' j x))

/-- SOS: `d`-SOS with `d = 1`. -/
def IsSOS {n : ℕ} (w : Signal n → ℝ) : Prop := IsDSOS 1 w

/-- Separable SOS valuations (Definition 2.16): for every agent `i` and nonempty bundle `T`,
`v_{iT}(s_T) = g_{−iT}(s_{−iT}) + h_{iT}(s_{iT})` with `g_{−iT}`, `h_{iT}` weakly increasing and
`g_{−iT}` SOS. The function `g i T` is written on the whole vector `s_T` and ignores coordinate `i`. -/
def IsSeparableSOS {n m : ℕ} (v : Valuation n m) (g : Valuation n m)
    (h : Fin n → Bundle m → NNReal → ℝ) : Prop :=
  ∀ i (T : Bundle m), T.Nonempty →
    (∀ z, v i T z = g i T z + h i T (z i)) ∧
    (∀ z y, g i T (Function.update z i y) = g i T z) ∧
    Monotone (g i T) ∧ Monotone (h i T) ∧ IsSOS (g i T)

/-- `T` is a feasible allocation to the agents of `N`: bundles of different agents are disjoint and
agents outside `N` receive nothing (Definition 2.11). -/
def IsAllocOn {n m : ℕ} (N : Finset (Fin n)) (T : Alloc n m) : Prop :=
  (Pairwise fun i j => Disjoint (T i) (T j)) ∧ ∀ i, i ∉ N → T i = ∅

/-- True social welfare `Σ_i v_{i T_i}(s_{T_i})` of the allocation `T` at the profile `s`. -/
def welfare {n m : ℕ} (v : Valuation n m) (s : Profile n m) (T : Alloc n m) : ℝ :=
  ∑ i, v i (T i) (sigT s (T i))

/-- Utility (Definition 2.12) of agent `i` with true profile `s` who reports `y` (a signal per
bundle) while the others report truthfully: the value at the true signals of the bundle allocated at
the reported profile, minus the payment at the reported profile. -/
def utility {n m : ℕ} (v : Valuation n m) (x : Profile n m → Alloc n m)
    (p : Profile n m → Fin n → ℝ) (i : Fin n) (s : Profile n m) (y : Bundle m → NNReal) : ℝ :=
  v i (x (Function.update s i y) i) (sigT s (x (Function.update s i y) i)) -
    p (Function.update s i y) i

/-- Deterministic ex-post incentive compatibility (Definition 2.4, combinatorial version). -/
def IsExPostIC {n m : ℕ} (v : Valuation n m) (x : Profile n m → Alloc n m)
    (p : Profile n m → Fin n → ℝ) : Prop :=
  ∀ i s y, utility v x p i s y ≤ utility v x p i s (s i)

/-- Deterministic ex-post individual rationality (Definition 2.5, combinatorial version). -/
def IsExPostIR {n m : ℕ} (v : Valuation n m) (x : Profile n m → Alloc n m)
    (p : Profile n m → Fin n → ℝ) : Prop :=
  ∀ i s, 0 ≤ utility v x p i s (s i)

/-- Expectation over the uniformly random partition `(A, B) = (Bᶜ, B)` of the agents. -/
noncomputable def avgB {n : ℕ} (f : Finset (Fin n) → ℝ) : ℝ :=
  (2 ^ n : ℝ)⁻¹ * ∑ B : Finset (Fin n), f B

end InterdepSOS.RSVCG


