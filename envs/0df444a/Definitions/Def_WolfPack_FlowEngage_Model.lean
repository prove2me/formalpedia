-- Prove2me | Definitions.Def_WolfPack_FlowEngage_Model
-- name    : WolfPack_FlowEngage_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:11.080927+00:00
-- url     : https://prove2.me/theorems/5736de0d-0b72-4bf1-ac7e-36c45b5aabfa
-- title:
--   §2, Definitions 1 and 5, pp. 9–18 — engagement games with and without competition for flow, Kη, ĉ, maximal success equilibrium
-- statement:
--   This file sets up the wolf-pack engagement model of Brav, Dasgupta and Mathews (§2) and the three engagement games compared in §3–§4.
--
--   **Parameters.** A firm has a unit continuum of shares. There are $N$ skilled and $M$ unskilled activist funds, each holding one block of size $b$ and cash $c$. A block is a fraction $\phi$ of the fund's own (proprietary) capital and $1-\phi$ of delegated capital, on which the fund earns an assets-under-management fee $w$. The firm is worth $P_h$ if engagement succeeds and $P_l = 0$ otherwise; skilled funds reinvest at gross return $R_S$. The engagement difficulty $\eta$ lives in the support $(b, U]$. The **standing assumptions** are
--   $$0<b<1,\quad c>0,\quad U>1,\quad R_S>1,\quad 0<\phi<1,\quad 0<w<1,\quad P_h>0,\quad M\ge 1,\quad (M+N)\,b\le 1 .$$
--   The last three are not displayed in the paper but are part of its model: $P_l=0$ normalizes the low value, there are unskilled funds, and the activist blocks are part of the firm's unit of shares.
--
--   **Derived quantities.** $\alpha = Nb$ is the skilled ownership. $K_\eta$ is the smallest natural number $x$ with $xb \ge \eta$. Definition 5 sets
--   $$\hat c(x) = w\Big((1-\phi)\,b P_h + \frac1x\,(M+N-x)\,b(1-\phi)P_h\Big),$$
--   the fee value of an engaging fund's delegated capital when exactly $x$ funds engage.
--
--   **Games.** Only the $N$ skilled funds act; each chooses to engage (E) or not (NE). If $k$ funds engage, engagement succeeds iff $kb \ge \eta$, and then $P_2 = P_h$, else $P_2 = 0$. A fund's payoff is
--   $$\big(s\,bP_2 + w f_2 + c\,\mathbf 1_{NE}\big)R_S ,$$
--   where $s$ is its proprietary fraction ($s=\phi$ in the two delegated games, $s=1$ in the proprietary blocks game) and $f_2$ is the $t=2$ value of the delegated capital it holds:
--   1. *with competition for flow*: if $k\ge1$ funds engage, all delegated capital of the $M+N-k$ non-engagers is reallocated evenly to the engagers, so an engager holds $(1-\phi)bP_2 + \frac1k(M+N-k)b(1-\phi)P_2$ and a non-engager $0$; if nobody engages, each fund keeps $(1-\phi)bP_2$;
--   2. *without competition for flow*: each fund keeps $(1-\phi)bP_2$;
--   3. *proprietary blocks*: there is no delegated capital.
--
--   For each $\eta$ this defines a finite game among the $N$ skilled funds (the $\eta$-subgame); its pure and mixed Nash equilibria are those of the published finite-game vocabulary. The **success probability** of a mixed profile is the probability that at least $\eta/b$ funds engage. A **maximal success equilibrium** (Definition 1) assigns to each $\eta\in(b,U]$ a Nash equilibrium of the $\eta$-subgame whose success probability is at least that of every Nash equilibrium of the same subgame.
--
--   These objects are the common language of Lemma 2 and Propositions 2, 3, 4 and 7.
--
--   **Formalization Note.** Actions are `Bool`, with `true` = engage; players are `Fin N`. $K_\eta$ is `sInf` over the natural numbers, $\hat c$ casts $M$, $N$ and $x$ to reals before subtracting. The reallocation rule of item 1 is the off-equilibrium belief fixed in the proof of Lemma 2 (p. A3: engagers get posterior 1, non-engagers less than 1), which agrees with Bayes' rule on the path because only skilled funds engage and $M\ge1$; it is built into the payoff, not a parameter. The proprietary game keeps $N$, $M$, $b$, $c$, $P_h$, $R_S$ and sets $\phi=1$ (p. 15 and footnote 14).
-- source:
--   Brav, Dasgupta & Mathews, Wolf Pack Activism, accepted manuscript (May 2021, LSE eprint 112118 / SSRN 2529230), pp. 9–18 (PDF 10–19): §2 Ownership, Skill, Skin in the game, Competition for flow, Fund fees, payoff and Kη (pp. 9–12); Definition 1 (p. 14); proprietary benchmark φ = 1 (p. 15); Definition 5 (p. 18); off-equilibrium beliefs, proof of Lemma 2, p. A3 (PDF 38)

import Mathlib
import Definitions.Def_agt_games

namespace WolfPack.FlowEngage

/-- The primitives of the wolf-pack engagement model (Brav–Dasgupta–Mathews, §2,
pp. 9–12): `N` skilled funds, `M` unskilled funds, block size `b`, proprietary
fraction `phi` (φ, "skin in the game"), AUM fee `w`, cash / engagement cost `c`,
firm value on success `Ph` (the value on failure, `Pl`, is normalized to `0`),
gross reinvestment return `RS` of skilled funds, and the upper end `U` of the
support `(b, U]` of the engagement difficulty `η`. -/
structure Params where
  N : ℕ
  M : ℕ
  b : ℝ
  phi : ℝ
  w : ℝ
  c : ℝ
  Ph : ℝ
  RS : ℝ
  U : ℝ

/-- The standing assumptions of §2 (pp. 9–11): `b ∈ (0,1)`, `c > 0`, `U > 1`,
`RS > 1`, `φ ∈ (0,1)`, `w ∈ (0,1)`; written out from the model: `Ph > 0`
(`Pl = 0` normalizes the *low* value), `M ≥ 1` (there are unskilled funds), and
`(M + N)·b ≤ 1` (the `M + N` activist blocks are part of the firm's unit
continuum of shares). -/
structure Params.Standing (p : Params) : Prop where
  b_pos : 0 < p.b
  b_lt_one : p.b < 1
  c_pos : 0 < p.c
  one_lt_U : 1 < p.U
  one_lt_RS : 1 < p.RS
  phi_pos : 0 < p.phi
  phi_lt_one : p.phi < 1
  w_pos : 0 < p.w
  w_lt_one : p.w < 1
  Ph_pos : 0 < p.Ph
  one_le_M : 1 ≤ p.M
  blocks_le_one : ((p.M : ℝ) + p.N) * p.b ≤ 1

/-- `α = N b`, the total share ownership of skilled funds (p. 10). -/
def alpha (p : Params) : ℝ := (p.N : ℝ) * p.b

/-- `Kη`, the smallest natural number `x` with `x b ≥ η` (p. 12). -/
noncomputable def Keta (p : Params) (eta : ℝ) : ℕ :=
  sInf {x : ℕ | eta ≤ (x : ℝ) * p.b}

/-- Definition 5 (p. 18): `ĉ(x) = w((1 − φ) b Ph + (1/x)(M + N − x) b (1 − φ) Ph)`,
the fee value of an engaging fund's delegated capital when exactly `x` funds
engage (all quantities in `ℝ`). -/
noncomputable def chat (p : Params) (x : ℕ) : ℝ :=
  p.w * ((1 - p.phi) * p.b * p.Ph +
    (1 / (x : ℝ)) * ((p.M : ℝ) + p.N - (x : ℝ)) * p.b * (1 - p.phi) * p.Ph)

/-- The three games of the paper: the delegated game with competition for flow
(§3.3), the delegated game without competition for flow (§3.2), and the
proprietary blocks game (§3.1). -/
inductive GameKind
  | flow
  | noFlow
  | proprietary

/-- The proprietary fraction of a block: `φ` in the two delegated games, and
`1` in the proprietary blocks game ("φ = 1 so that funds manage only their own
money", p. 15). -/
def skin (p : Params) : GameKind → ℝ
  | .proprietary => 1
  | .flow => p.phi
  | .noFlow => p.phi

/-- The firm's value at `t = 2` when `k` blocks engage at difficulty `η`:
`Ph` if the engaging measure `k b` is at least `η`, else `Pl = 0` (p. 10). -/
noncomputable def P2 (p : Params) (eta : ℝ) (k : ℕ) : ℝ :=
  if eta ≤ (k : ℝ) * p.b then p.Ph else 0

/-- The `t = 2` value `f₂ⁱ` of the delegated capital held by a skilled fund that
plays `a` (`true` = engage, `false` = not engage) when `k` funds in total engage
(the fund itself included when `a = true`).

* With competition for flow (p. 11; beliefs of the proof of Lemma 2, p. A3):
  when some fund engages, engagers are believed skilled and all delegated
  capital of the `M + N − k` non-engagers moves evenly to the `k` engagers; an
  engager holds its own `(1 − φ) b P2` plus `1/k` of theirs, a non-engager holds
  `0`. When nobody engages, all posteriors coincide and each fund keeps its own.
* Without competition for flow, and in the proprietary game, there is no
  reallocation: each fund holds `(1 − skin) b P2` (`0` when `skin = 1`). -/
noncomputable def delegValue (p : Params) (eta : ℝ) : GameKind → Bool → ℕ → ℝ
  | .flow, true, k =>
      (1 - p.phi) * p.b * P2 p eta k +
        (1 / (k : ℝ)) * ((p.M : ℝ) + p.N - (k : ℝ)) * p.b * (1 - p.phi) * P2 p eta k
  | .flow, false, k => if k = 0 then (1 - p.phi) * p.b * P2 p eta k else 0
  | g, _, k => (1 - skin p g) * p.b * P2 p eta k

/-- A skilled fund's final payoff (p. 12), `(skin·b·P2 + w f₂ⁱ + c·I_NE)·R_S`, where
`a = true` means the fund engages (and spends its cash `c`) and `k` is the total
number of engaging funds. -/
noncomputable def payoff (p : Params) (eta : ℝ) (g : GameKind) (a : Bool) (k : ℕ) : ℝ :=
  (skin p g * p.b * P2 p eta k + p.w * delegValue p eta g a k + (if a then 0 else p.c)) * p.RS

/-- The number of funds that engage (`true`) in a pure profile. -/
def numEngaged {n : ℕ} (s : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun j => s j = true)).card

/-- The `η`-subgame of game `g` among the `N` skilled funds: players `Fin N`,
actions `Bool` (`true` = engage), payoff of fund `i` under the pure profile `s`. -/
noncomputable def subgamePayoff (p : Params) (eta : ℝ) (g : GameKind) :
    Fin p.N → (Fin p.N → Bool) → ℝ :=
  fun i s => payoff p eta g (s i) (numEngaged s)

/-- The probability that engagement succeeds at difficulty `η` when the skilled
funds play the mixed profile `σ` (`σ i true` = probability that fund `i` engages). -/
noncomputable def successProb (p : Params) (eta : ℝ) (σ : Fin p.N → Bool → ℝ) : ℝ :=
  ∑ s : Fin p.N → Bool,
    AGT.profileProb σ s * (if eta ≤ (numEngaged s : ℝ) * p.b then 1 else 0)

/-- A pure profile viewed as a degenerate mixed profile. -/
def pureLottery {n : ℕ} (s : Fin n → Bool) : Fin n → Bool → ℝ :=
  fun i a => if a = s i then 1 else 0

/-- Definition 1 (p. 14): a maximal success equilibrium of game `g` is a family
of profiles `σ η`, one for each difficulty `η` in the support `(b, U]`, such that
`σ η` is a (mixed) Nash equilibrium of the `η`-subgame and no Nash equilibrium of
that subgame has a larger probability of successful engagement. -/
def IsMaxSuccessEq (p : Params) (g : GameKind) (σ : ℝ → Fin p.N → Bool → ℝ) : Prop :=
  ∀ eta ∈ Set.Ioc p.b p.U,
    AGT.IsMixedNash (subgamePayoff p eta g) (σ eta) ∧
      ∀ τ : Fin p.N → Bool → ℝ, AGT.IsMixedNash (subgamePayoff p eta g) τ →
        successProb p eta τ ≤ successProb p eta (σ eta)

end WolfPack.FlowEngage


