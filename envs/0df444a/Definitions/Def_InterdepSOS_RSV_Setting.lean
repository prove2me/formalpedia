-- Prove2me | Definitions.Def_InterdepSOS_RSV_Setting
-- name    : InterdepSOS_RSV_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:55.43586+00:00
-- url     : https://prove2.me/theorems/c8122308-89f1-4d9f-b1a8-5fd534b4ed82
-- title:
--   §2.1, §2.3, §4 — single-parameter interdependent valuations, d-SOS (Definition 2.13), ex-post IC/IR (Definitions 2.3–2.6), downward-closed systems, the RS-V mechanism
-- statement:
--   This file fixes the single-parameter model of §2.1 and §2.3 of Eden, Feldman, Fiat, Goldner and Karlin and the Random Sampling Vickrey (RS-V) mechanism of §4.
--
--   There are $n$ agents $[n]$. Agent $i$ holds a private signal $s_i\in\mathbb R_+=[0,\infty)$; a profile is $\mathbf s=(s_1,\dots,s_n)$, and $(\mathbf s_{-i},x_i)$ replaces agent $i$'s signal by $x$. For a set $S$ of agents, $(\mathbf s_S,\mathbf 0_{[n]\setminus S})$ keeps the coordinates in $S$ and sets the others to $0$.
--
--   1. **Valuations** (Definition 2.1). Agent $i$'s value for being served is $v_i(\mathbf s)\ge0$, weakly increasing in every signal and strictly increasing in $s_i$.
--   2. **$d$-SOS** (Definition 2.13). A function $w$ of the profile is $d$-SOS if for every coordinate $j$, all $x,\delta\ge0$, and profiles $\mathbf s,\mathbf s'$ with $s'_l\le s_l$ for every $l\ne j$,
--   $$w(\mathbf s_{-j},x+\delta)-w(\mathbf s_{-j},x)\;\le\;d\cdot\bigl(w(\mathbf s'_{-j},x+\delta)-w(\mathbf s'_{-j},x)\bigr).$$
--   It is SOS if this holds with $d=1$.
--   3. **Feasibility.** A set system $\mathcal I\subseteq 2^{[n]}$ is downward closed if every subset of a member is a member.
--   4. **Incentives** (Definitions 2.2–2.6). A deterministic mechanism is an allocation rule $x$ (the set of agents served) and a payment rule $p$, both functions of the reported profile. The utility of agent $i$ with true profile $\mathbf s$ who reports $y$ while the others report truthfully is
--   $$u_i(y,\mathbf s_{-i}\mid s_i)=\mathbf 1[i\in x(\mathbf s_{-i},y)]\,v_i(\mathbf s)-p_i(\mathbf s_{-i},y).$$
--   The mechanism is ex-post IC if $u_i(y,\mathbf s_{-i}\mid s_i)\le u_i(s_i,\mathbf s_{-i}\mid s_i)$ for all $i$, $\mathbf s$ and $y$, and ex-post IR if $u_i(s_i,\mathbf s_{-i}\mid s_i)\ge0$. The allocation rule is monotone if raising one's own signal never loses service.
--   5. **RS-V** (§4, p. 14). For a partition $(A,B)$ of the agents, each $i\in B$ gets the proxy weight
--   $$w_i=v_i(\mathbf s_A,s_i,\mathbf 0_{B\setminus\{i\}}),$$
--   and the mechanism serves a set $S\in\mathcal I$ with $S\subseteq B$ maximizing $\sum_{i\in S}w_i$. A **selector** is any function of $B$ and the reported profile that returns such a maximizer.
--   6. **Random partition.** The uniform average over the partition $(A,B)$ is $\mathbb E_B[f(B)]=2^{-n}\sum_{B\subseteq[n]}f(B)$.
--
--   These objects are shared by every statement of the RS-V mission; the random-partition average is reused by the k-HL and k-SS missions.
--
--   **Formalization Note** Signals are nonnegative reals (`NNReal`); values and their differences are real. Monotonicity is with respect to the coordinate-wise order on profiles. The parameter $d$ of $d$-SOS is an arbitrary real here; the statements that need $d\ge0$ assume it. The partition is encoded by $B$, with $A=[n]\setminus B$. A downward-closed system may be empty here; for a nonempty one $\emptyset\in\mathcal I$ and a maximizing selector exists, while for $\mathcal I=\emptyset$ no selector exists.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), pp. 9–14, Definitions 2.1–2.8, 2.13, §4

import Mathlib

namespace InterdepSOS.RSV

/-- A profile of single-dimensional signals: agent `i` holds `s i ∈ ℝ_+ = [0, ∞)`
(Definition 2.1). -/
abbrev Signal (n : ℕ) := Fin n → NNReal

/-- `v i s` is agent `i`'s value for receiving service at the signal profile `s`. -/
abbrev Valuation (n : ℕ) := Fin n → Signal n → ℝ

/-- A deterministic allocation rule: the set of agents served at the reported profile. -/
abbrev Allocation (n : ℕ) := Signal n → Finset (Fin n)

/-- A deterministic payment rule: `p s i` is agent `i`'s payment at the reported profile `s`. -/
abbrev Payment (n : ℕ) := Signal n → Fin n → ℝ

/-- Keep the coordinates in `S` and set the others to `0`. -/
def keepOn {n : ℕ} (S : Finset (Fin n)) (s : Signal n) : Signal n :=
  fun j => if j ∈ S then s j else 0

/-- Standing hypotheses of Definition 2.1: values are nonnegative, weakly increasing in every
signal, and strictly increasing in the agent's own signal. -/
def IsValuation {n : ℕ} (v : Valuation n) : Prop :=
  (∀ i s, 0 ≤ v i s) ∧
  (∀ i, Monotone (v i)) ∧
  (∀ i s x y, x < y →
    v i (Function.update s i x) < v i (Function.update s i y))

/-- `d`-SOS (Definition 2.13, inequality (1)): raising coordinate `j` from `x` to `x + δ`
increases `w` at the profile `s` by at most `d` times the increase at a profile `s'` whose other
coordinates are coordinate-wise smaller. -/
def IsDSOS {n : ℕ} (d : ℝ) (w : Signal n → ℝ) : Prop :=
  ∀ j (x δ : NNReal) (s s' : Signal n),
    (∀ l, l ≠ j → s' l ≤ s l) →
    w (Function.update s j (x + δ)) - w (Function.update s j x) ≤
      d * (w (Function.update s' j (x + δ)) - w (Function.update s' j x))

/-- SOS: `d`-SOS with `d = 1` (Definition 2.13). -/
def IsSOS {n : ℕ} (w : Signal n → ℝ) : Prop := IsDSOS 1 w

/-- A downward-closed set system `I ⊆ 2^[n]`. -/
def IsDownwardClosed {n : ℕ} (I : Set (Finset (Fin n))) : Prop :=
  ∀ S ∈ I, ∀ T ⊆ S, T ∈ I

/-- Utility of agent `i` with true profile `s` who reports `y` while the others report
truthfully (Definition 2.3): value at the true profile if served at the reported profile, minus
the payment at the reported profile. -/
def utility {n : ℕ} (v : Valuation n) (x : Allocation n) (p : Payment n)
    (i : Fin n) (s : Signal n) (y : NNReal) : ℝ :=
  (if i ∈ x (Function.update s i y) then v i s else 0) -
    p (Function.update s i y) i

/-- Ex-post incentive compatibility (Definition 2.4). -/
def IsExPostIC {n : ℕ} (v : Valuation n) (x : Allocation n) (p : Payment n) : Prop :=
  ∀ i s y, utility v x p i s y ≤ utility v x p i s (s i)

/-- Ex-post individual rationality (Definition 2.5). -/
def IsExPostIR {n : ℕ} (v : Valuation n) (x : Allocation n) (p : Payment n) : Prop :=
  ∀ i s, 0 ≤ utility v x p i s (s i)

/-- A monotone allocation rule (Definition 2.6): raising one's own signal never loses service. -/
def IsMonotoneAlloc {n : ℕ} (x : Allocation n) : Prop :=
  ∀ i s a b, a ≤ b → i ∈ x (Function.update s i a) →
    i ∈ x (Function.update s i b)

/-- RS-V's proxy weight `w_i = v_i(s_A, s_i, 0_{B∖{i}})` with `A = Bᶜ` (§4, p. 14). -/
def rsvWeight {n : ℕ} (v : Valuation n) (B : Finset (Fin n))
    (s : Signal n) (i : Fin n) : ℝ :=
  v i (keepOn (insert i (Bᶜ)) s)

/-- `sel B s` is a set of `I` contained in `B` that maximizes the total proxy weight
`∑_{i ∈ S} w_i` over the sets `S ∈ I` with `S ⊆ B` (RS-V's allocation, §4, p. 14). -/
def IsRSVSelector {n : ℕ} (I : Set (Finset (Fin n))) (v : Valuation n)
    (sel : Finset (Fin n) → Allocation n) : Prop :=
  ∀ B s, sel B s ∈ I ∧ sel B s ⊆ B ∧
    ∀ S ∈ I, S ⊆ B →
      (∑ i ∈ S, rsvWeight v B s i) ≤
        (∑ i ∈ sel B s, rsvWeight v B s i)

/-- The uniform average over the random partition `(A, B) = (Bᶜ, B)`:
`2^{-n} ∑_{B ⊆ [n]} f B`. -/
noncomputable def avgB {n : ℕ} (f : Finset (Fin n) → ℝ) : ℝ :=
  (2 ^ n : ℝ)⁻¹ * ∑ B : Finset (Fin n), f B

end InterdepSOS.RSV


