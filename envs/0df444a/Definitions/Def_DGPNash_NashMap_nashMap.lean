-- Prove2me | Definitions.Def_DGPNash_NashMap_nashMap
-- name    : DGPNash_NashMap_nashMap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:36:56.526692+00:00
-- url     : https://prove2.me/theorems/47d32a45-95ef-4b4f-9c4d-8a31e66cc92d
-- title:
--   Nash's map and its finite-game payoff quantities
-- statement:
--   This bundle fixes the payoff quantities of a finite game in normal form that Daskalakis, Goldberg and Papadimitriou use in §2.1 and §3.2, together with Nash's map.
--
--   A game has players $p\in[r]$; player $p$ has a finite set $S_p$ of pure strategies, and for every pure strategy profile $s\in S=\prod_q S_q$ a payoff $u^p_s\in\mathbb R$. A profile $x=\{x^p_j\}$ assigns a weight $x^p_j$ to each strategy $j\in S_p$ of each player; it is a **mixed profile** when every $x^p$ is a probability distribution on $S_p$. For a profile $s\in S_{-p}$ of the players other than $p$, write $x_s=\prod_{q\ne p}x^q_{s_q}$, and $u^p_{js}$ for the payoff to $p$ when $p$ plays $j$ and the others play $s$.
--
--   1. **Payoff of a pure strategy** (p. 205). The expected utility of player $p$ playing $j\in S_p$ while the others use $x$ is
--   $$U^p_j(x)=\sum_{s\in S_{-p}}u^p_{js}\,x_s .$$
--   The expected utility of $p$ when everybody uses $x$ is $U^p(x)=\sum_{s\in S}u^p_s\,x_s$, the expected payoff of the published bundle `agt_games`.
--
--   2. **Largest payoff entries.** $U_{\max}$ is the largest entry of all payoff tables, $\max_{p,\,s}u^p_s$ (p. 205), and for a fixed player $p$ and strategy $j\in S_p$, $\max_{s\in S_{-p}}u^p_{js}$ is the largest payoff $p$ can get from $j$ (Lemma 3.5, p. 205).
--
--   3. **Gain** (p. 205). For $p\in[r]$ and $j\in[n]$,
--   $$B^p_j(x)=\max\bigl(0,\;U^p_j(x)-U^p(x)\bigr).$$
--
--   4. **Nash's map** (p. 205). For a game in which every player has the strategy set $[n]$, $f(x)=y$ with
--   $$y^p_j=\frac{x^p_j+B^p_j(x)}{1+\sum_{k\in[n]}B^p_k(x)}\qquad(p\in[r],\ j\in[n]).$$
--
--   5. **$\varepsilon$-approximate Nash equilibrium** (p. 199; Eq. (27), p. 243). A profile $x$ is an $\varepsilon$-approximate Nash equilibrium if it is a mixed profile and, for every player $p$ and every mixed strategy $y$ of $p$, the expected utility of $p$ when $p$ switches to $y$ and the others keep $x$ is at most $U^p(x)+\varepsilon$: no player can gain more than $\varepsilon$ by a unilateral deviation.
--
--   These are the objects of Lemmas 3.4–3.8 (membership of Nash in PPAD) and of the payoff estimates of §4.6–4.7; Nash's map has the Nash equilibria as its fixed points.
--
--   **Formalization Note** The paper's $[r]$ and $[n]$ are the zero-based `Fin r` and `Fin n`. $U^p_j$ and $\max_{s_{-p}}u^p_{js}$ are defined for an arbitrary finite strategy family `S : ι → Type`; $U_{\max}$, the gain, Nash's map and the approximate equilibrium for the uniform family `Fin r → Fin n`. $U^p_j(x)$ is `AGT.expectedPayoff` of the profile in which only player $p$'s weights are replaced by the point mass at $j$. The two maxima are real suprema of finite sets: they equal the maximum when the set is nonempty, and are $0$ when it is empty ($r=0$ or $n=0$ for $U_{\max}$, an empty strategy set for the other), a case the theorems exclude by their hypotheses. The definitions do not assume nonnegative payoffs; the paper's standing assumption $u^p_s\ge0$ is a hypothesis of each theorem. Nash's map is given by the same formula on all real profiles; since every gain is nonnegative, its denominator is at least $1$. The approximate-equilibrium condition imposes no sign on $\varepsilon$.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), pp. 199, 205, 243; §2.1, Nash's map in §3.2, Eq. (27); https://doi.org/10.1137/070699652

import Definitions.Def_agt_games
import Mathlib

namespace DGPNash.NashMap

open Finset

/-- The payoff to player `p` when they play `j` and the other players use `x` (p. 205). -/
def purePayoff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (p : ι) (j : S p) : ℝ :=
  AGT.expectedPayoff u (Function.update x p (fun k => if k = j then 1 else 0)) p

/-- The alternative approximate Nash condition of p. 199 and Eq. (27), p. 243. -/
def IsApproxNash {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ)
    (x : Fin r → Fin n → ℝ) (ε : ℝ) : Prop :=
  AGT.IsMixedProfile x ∧
    ∀ p (y : Fin n → ℝ), AGT.IsLottery y →
      AGT.expectedPayoff u (Function.update x p y) p ≤ AGT.expectedPayoff u x p + ε

/-- The largest entry of all payoff tables, `U_max` (p. 205). -/
noncomputable def maxPayoff {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ) : ℝ :=
  sSup (Set.range (fun ps : Fin r × (Fin r → Fin n) => u ps.1 ps.2))

/-- The largest payoff for player `p`'s pure strategy `j`, across opponents' profiles (Lemma 3.5). -/
noncomputable def maxPurePayoff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (p : ι) (j : S p) : ℝ :=
  sSup (Set.range (fun s : ∀ i, S i => u p (Function.update s p j)))

/-- The excess payoff `B⁽ᵖ⁾ⱼ(x)` of p. 205. -/
def gain {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ)
    (x : Fin r → Fin n → ℝ) (p : Fin r) (j : Fin n) : ℝ :=
  max 0 (purePayoff u x p j - AGT.expectedPayoff u x p)

/-- Nash's map `f` from p. 205, extended by the same formula to all real profiles. -/
noncomputable def nashMap {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ)
    (x : Fin r → Fin n → ℝ) (p : Fin r) (j : Fin n) : ℝ :=
  (x p j + gain u x p j) / (1 + ∑ k : Fin n, gain u x p k)

end DGPNash.NashMap


