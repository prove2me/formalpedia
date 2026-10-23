-- Prove2me | Definitions.Def_RandomGames_BRD_Game
-- name    : RandomGames_BRD_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:14.922979+00:00
-- url     : https://prove2.me/theorems/c6ad51f1-50d7-49e0-af02-3efc8d05b05d
-- title:
--   §2–§3, pp. 6–10 — the random game Ξ_N, α and β (2.4), PNE (Definition 2.1), D(s) (3.2), accessibility (Definition 3.2), L→^{β,0}_N (3.4), traps (Definition 3.5), the BRD chain BR^(N) (3.3)
-- statement:
--   **The random binary game.** For $N$ players $[N]=\{1,\dots,N\}$, each with strategy set $S_i=\{0,1\}$, a strategy profile is a vector $\boldsymbol s=(s_1,\dots,s_N)\in S=\{0,1\}^N$; the profile $(0,\dots,0)$ is denoted $\mathbf 0$. A game with payoff functions $g_i : S\to\mathbb R$ has a **pure Nash equilibrium** (PNE, Definition 2.1) at $\boldsymbol s^*$ if
--   $$g_i(\boldsymbol s^*) \ge g_i(s_i,\boldsymbol s^*_{-i})\qquad\text{for all } i\in[N],\ s_i\in S_i .$$
--
--   In the **random game** $\Xi_N$ the payoffs $g_i(\boldsymbol s)=Z^{\boldsymbol s}_i$, $i\in[N]$, $\boldsymbol s\in S$, are i.i.d. real random variables with a common law $\mu$, which may have atoms. With $Z_1,Z_2$ i.i.d. of law $\mu$,
--   $$\alpha := \mathsf P(Z_1=Z_2),\qquad \beta := \mathsf P(Z_1<Z_2) = \tfrac{1-\alpha}{2}. \tag{2.4}$$
--   $\mathsf{card}(\mathsf{PNE}(\Xi_N))$ is the number of PNE.
--
--   **Oriented hypercube.** Write $\boldsymbol s\sim_i\boldsymbol t$ if $\boldsymbol s,\boldsymbol t$ differ exactly in coordinate $i$. The oriented edge $[\boldsymbol s,\boldsymbol t]^{\to}$ is present iff $Z^{\boldsymbol s}_i<Z^{\boldsymbol t}_i$ (player $i$ strictly prefers $\boldsymbol t$); this is the random partially oriented hypercube $\vec{\mathscr H}^\beta_N$. The set of **strictly profitable deviations** from $\boldsymbol s$ is
--   $$\mathscr D(\boldsymbol s) := \{\boldsymbol t : \exists i,\ \boldsymbol s\sim_i\boldsymbol t,\ g_i(\boldsymbol t)>g_i(\boldsymbol s)\}. \tag{3.2}$$
--   A profile $\boldsymbol t$ is **accessible** from $\boldsymbol s$ if there is a finite oriented path from $\boldsymbol s$ to $\boldsymbol t$ (Definition 3.2); $\vec{\mathscr L}^{\beta,\mathbf 0}_N$ is $\mathbf 0$ together with all profiles accessible from $\mathbf 0$ (3.4). A **trap** (Definition 3.5) is a vertex set $T$ with at least two vertices that is strongly connected (every vertex of $T$ is accessible from every other) and closed (no vertex outside $T$ is accessible from a vertex of $T$).
--
--   **Best-response dynamics** (3.3). $\mathsf{BR}^{(N)}$ starts at $\mathbf 0$; at each step it moves to a uniformly random element of $\mathscr D$ of the current profile, independently of the past. It **converges to a PNE** if $\mathscr D(\mathsf{BR}^{(N)}_k)=\varnothing$ for all large $k$. Given the payoffs, $p_{\mathrm{nc}}(Z)$ denotes the conditional probability that $\mathsf{BR}^{(N)}$ does not converge to a PNE, and $\mathsf P(\mathsf{BR}^{(N)}\text{ does not converge to a PNE}) = \mathsf E[p_{\mathrm{nc}}(Z)]$.
--
--   These objects are the setting of every statement of the mission.
--
--   **Formalization Note** Players are `Fin N` (0-based), profiles `Fin N → Bool` with `false` for strategy $0$, and `Z i s` is $Z^{\boldsymbol s}_i$. The law of the payoff family is the product measure `gameMeasure μ N` on `Fin N → Profile N → ℝ`; each $N$ has its own space, which is all the summability statements need. `IsPNE` is the published general pure-Nash predicate `CarbonDoubleCount.Planner.IsPureNash` (payoffs maximised, unilateral deviations by `Function.update`) with two strategies per player and every strategy feasible, by definition. The page leaves the chain undefined when $\mathscr D=\varnothing$; here it stays put there, so PNE are absorbing and "does not converge" has conditional probability $1-\sup_k \mathsf P(\mathsf{BR}^{(N)}_k\in\mathsf{PNE})$ (`notConvProb`, an extended nonnegative real built from the `PMF` iterates `brdLaw`). Expectations of it are lower Lebesgue integrals `∫⁻`, never Bochner integrals.
-- source:
--   Amiet, Collevecchio, Scarsini & Zhong, Pure Nash Equilibria and Best-Response Dynamics in Random Games, arXiv:1905.10758v4, pp. 6–10, (2.1)–(2.4), Definitions 2.1, 3.1, 3.2, 3.5, (3.2)–(3.4)

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_PureGame

namespace RandomGames.BRD

open MeasureTheory

/-- §2, p. 6: a strategy profile of the binary game `Ξ_N`; player `i ∈ Fin N` (the paper's
`[N]`, 0-based) plays `false` (strategy `0`) or `true` (strategy `1`). -/
abbrev Profile (N : ℕ) := Fin N → Bool

/-- p. 8: the profile `0 = (0, …, 0)`. -/
def zeroProfile (N : ℕ) : Profile N := fun _ => false

/-- (3.1), p. 7: `flip s i` is the unique profile `t` with `s ∼_i t`. -/
def flip {N : ℕ} (s : Profile N) (i : Fin N) : Profile N := Function.update s i (!s i)

/-- (2.4), p. 6: `α = P(Z₁ = Z₂)` for i.i.d. `Z₁, Z₂ ∼ μ`. -/
noncomputable def alpha (μ : Measure ℝ) : ℝ := ((μ.prod μ) {p : ℝ × ℝ | p.1 = p.2}).toReal

/-- (2.4), p. 6: `β = P(Z₁ < Z₂)` for i.i.d. `Z₁, Z₂ ∼ μ`. -/
noncomputable def beta (μ : Measure ℝ) : ℝ := ((μ.prod μ) {p : ℝ × ℝ | p.1 < p.2}).toReal

/-- §2, p. 6: the law of the payoff family `(Z^s_i)_{i ∈ [N], s ∈ S}` of `Ξ_N`, i.i.d. with law
`μ`. `Z i s` is `Z^s_i = g_i(s)`. -/
noncomputable def gameMeasure (μ : Measure ℝ) (N : ℕ) : Measure (Fin N → Profile N → ℝ) :=
  Measure.pi (fun _ : Fin N => Measure.pi (fun _ : Profile N => μ))

/-- Definition 2.1, p. 6, for `Ξ_N`: `s` is a PNE of the game with payoffs `g_i = Z i`, i.e.
`Z i (s_i', s_{-i}) ≤ Z i s` for every player `i` and every strategy `s_i' ∈ {0, 1}`. This is the
published general pure-Nash predicate with every strategy feasible. -/
def IsPNE {N : ℕ} (Z : Fin N → Profile N → ℝ) (s : Profile N) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (strategy := fun _ : Fin N => Bool) (fun _ => Set.univ) Z s

open Classical in
/-- p. 6: `card(PNE(Ξ_N))`. -/
noncomputable def pneCount {N : ℕ} (Z : Fin N → Profile N → ℝ) : ℕ :=
  (Finset.univ.filter (fun s => IsPNE Z s)).card

/-- p. 8: the oriented edge `[s, t]→` lies in `E→_N`: `s ∼_i t` and `Z^s_i < Z^t_i`. -/
def arrow {N : ℕ} (Z : Fin N → Profile N → ℝ) (s t : Profile N) : Prop :=
  ∃ i, t = flip s i ∧ Z i s < Z i t

open Classical in
/-- (3.2), p. 8: the set `D(s)` of strictly profitable deviations from `s`. -/
noncomputable def devSet {N : ℕ} (Z : Fin N → Profile N → ℝ) (s : Profile N) :
    Finset (Profile N) :=
  Finset.univ.filter (fun t => arrow Z s t)

/-- Definition 3.2, p. 8: `t` is accessible from `s` (a finite oriented path, possibly of
length `0`). -/
def Accessible {N : ℕ} (Z : Fin N → Profile N → ℝ) (s t : Profile N) : Prop :=
  Relation.ReflTransGen (arrow Z) s t

/-- (3.4), p. 9: `L→^{β,0}_N`, the profile `0` together with every profile accessible from `0`. -/
def reach0 {N : ℕ} (Z : Fin N → Profile N → ℝ) : Set (Profile N) :=
  {t | Accessible Z (zeroProfile N) t}

/-- Definition 3.5, p. 10: the vertex set `T` of a trap: at least two vertices, strongly
connected, and no vertex outside `T` is accessible from a vertex of `T`. -/
def IsTrap {N : ℕ} (Z : Fin N → Profile N → ℝ) (T : Finset (Profile N)) : Prop :=
  2 ≤ T.card ∧ (∀ s ∈ T, ∀ t ∈ T, Accessible Z s t) ∧ (∀ s ∈ T, ∀ t ∉ T, ¬ Accessible Z s t)

/-- (3.3), p. 8: one step of best-response dynamics: a uniformly random element of `D(s)`; at a
profile with `D(s) = ∅` (a PNE) the chain stays put. -/
noncomputable def brdStep {N : ℕ} (Z : Fin N → Profile N → ℝ) (s : Profile N) : PMF (Profile N) :=
  if h : (devSet Z s).Nonempty then PMF.uniformOfFinset (devSet Z s) h else PMF.pure s

/-- (3.3), p. 8: the law of `Brd_k(Ξ_N, 0) = BR^(N)_k` given the payoffs. -/
noncomputable def brdLaw {N : ℕ} (Z : Fin N → Profile N → ℝ) : ℕ → PMF (Profile N)
  | 0 => PMF.pure (zeroProfile N)
  | k + 1 => (brdLaw Z k).bind (brdStep Z)

/-- p. 8: the conditional probability, given the payoffs, that `BR^(N)` does not converge to a
PNE, i.e. that `D(BR^(N)_k) ≠ ∅` for infinitely many `k`. Since PNE are absorbing, this is
`1 − sup_k P(BR^(N)_k ∈ PNE)`. -/
noncomputable def notConvProb {N : ℕ} (Z : Fin N → Profile N → ℝ) : ENNReal :=
  1 - ⨆ k, (brdLaw Z k).toOuterMeasure {s | IsPNE Z s}

end RandomGames.BRD


