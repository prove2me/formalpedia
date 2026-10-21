-- Prove2me | Definitions.Def_GenPayoffSG_Solvable_OneShot
-- name    : GenPayoffSG_Solvable_OneShot
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:45.94671+00:00
-- url     : https://prove2.me/theorems/457ea9b8-0277-4d27-89b7-3bfd6f780a33
-- title:
--   §3, p. 8 — the one-shot game G_O(D, h): E[D_i | h, a], E[D_i | h, x], minmax value v̄_{O,i}(D_i, h), its equilibria, and Martin functions (Theorem 3.1 (1)–(3))
-- statement:
--   This file defines the auxiliary one-shot games of §3 and the properties of a Martin function.
--
--   Let $D=(D_i)_{i\in I}$ assign a real number $D_i(h)$ to every history $h$. At each history $h$ it induces the **one-shot game** $G_O(D,h)$: the action set of player $i$ is $A_i$, and under the action profile $a$ player $i$ receives the expectation of $D_i$ at the next history,
--   $$\mathbf E[D_i\mid h,a]=\sum_{s\in S}p(s\mid s_h,a)\,D_i(h,a,s).$$
--   For a mixed action profile $x\in\prod_{i\in I}\Delta(A_i)$,
--   $$\mathbf E[D_i\mid h,x]=\sum_{a\in A}\mathbf E[D_i\mid h,a]\prod_{j\in I}x_j(a_j),$$
--   and player $i$'s minmax value in $G_O(D,h)$ is
--   $$\overline v_{O,i}(D_i,h)=\min_{x_{-i}\in\prod_{j\ne i}\Delta(A_j)}\ \max_{x_i\in\Delta(A_i)}\ \mathbf E[D_i\mid h,x_i,x_{-i}],$$
--   which depends on $D_i$ only. A mixed profile $x$ is an **equilibrium of $G_O(D,h)$** if it is a mixed Nash equilibrium of this finite game.
--
--   For $\varepsilon>0$ and a player $i$, a function $D_i:H\to\mathbb R$ is a **Martin function** for $\varepsilon$ and $i$ (Theorem 3.1, minmax version) if it is bounded on $H$ and
--   1. $\overline v_i(h)-\varepsilon\le D_i(h)\le\overline v_i(h)$ for every $h\in H$;
--   2. $D_i(h)\le\overline v_{O,i}(D_i,h)$ for every $h\in H$;
--   3. for every $h'\in H$ and every strategy profile $\sigma$: if $\overline v_{O,i}(D_i,h)\le\mathbf E[D_i\mid h,\sigma(h)]$ for every $h\in H$ with $h'\preceq h$, then $\overline v_{O,i}(D_i,h)\le\mathbf E_{h,\sigma}[f_i]$ for every $h\in H$ with $h'\preceq h$.
--
--   Theorem 3.1 asserts that Martin functions exist; Theorem 4.4 and the proof of Theorem 4.9 use their properties.
--
--   **Formalization Note** $D_i$ is a real function on all finite sequences (`HistFun`); only its values on feasible histories enter. The sum over $S$ is a `tsum`: terms with $p(s\mid s_h,a)=0$ vanish, and the remaining extensions of a feasible $h$ are feasible, so boundedness of $D_i$ on $H$ (the first clause of `IsMartinFunction`) makes the sum absolutely convergent. The paper's $\min$/$\max$ are written as real `⨅`/`⨆` over mixed actions (`PMF`s); since $\mathbf E[D_i\mid h,\cdot]$ is bounded and continuous on a compact set, they coincide with the attained min and max. The equilibrium of $G_O(D,h)$ is the platform's `AGT.IsMixedNash` (definition `agt_games`) for the payoffs $a\mapsto\mathbf E[D_j\mid h,a]$ and the weights $x_j(a_j)$. Lean index $n$ is paper stage $n+1$.
-- source:
--   Flesch & Solan, Stochastic Games with General Payoff Functions, arXiv:2208.12096v1, p. 8, The auxiliary one-shot games (E[D_i | h, a], E[D_i | h, x], v̄_{O,i}); pp. 8–9, Theorem 3.1 properties 1–3 (minmax version)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_GenPayoffSG_Solvable_Game

namespace GenPayoffSG.Solvable

open MeasureTheory ProbabilityTheory Finset

variable {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

/-- A real function on histories, `Dᵢ : H → ℝ` (one player's component of `D`). -/
abbrev HistFun (I S : Type) (A : I → Type) := (n : ℕ) → Hist I S A n → ℝ

/-- `E[Dᵢ | h, a] = ∑_{s ∈ S} p(s | s_h, a) · Dᵢ(h, a, s)`, the payoff of the one-shot game
`G_O(D, h)` under the pure action profile `a`. -/
noncomputable def oneShotPayoffPure (G : Game I S A) (D : HistFun I S A)
    {n : ℕ} (h : Hist I S A n) (a : ∀ i, A i) : ℝ :=
  ∑' s : S, (G.p (lastState h) a s).toReal * D (n + 1) (extend h a s)

/-- `E[Dᵢ | h, x] = ∑_{a ∈ A} E[Dᵢ | h, a] · ∏_{j ∈ I} x_j(a_j)` for a mixed action profile
`x`. -/
noncomputable def oneShotPayoff (G : Game I S A) (D : HistFun I S A)
    {n : ℕ} (h : Hist I S A n) (x : ∀ j, PMF (A j)) : ℝ :=
  ∑ a : ∀ j, A j, oneShotPayoffPure G D h a * ∏ j, (x j (a j)).toReal

/-- `v̄_{O,i}(Dᵢ, h) = min_{x₋ᵢ} max_{xᵢ} E[Dᵢ | h, xᵢ, x₋ᵢ]`, player `i`'s minmax value in the
one-shot game `G_O(D, h)` (p. 8). The opponents' part of `x` is `x₋ᵢ`; its `i`-th component is
overwritten by `y = xᵢ`. -/
noncomputable def oneShotMinmax (G : Game I S A) (i : I) (D : HistFun I S A)
    {n : ℕ} (h : Hist I S A n) : ℝ :=
  ⨅ x : (∀ j, PMF (A j)), ⨆ y : PMF (A i), oneShotPayoff G D h (Function.update x i y)

/-- `x` is an equilibrium (mixed Nash equilibrium) of the one-shot game `G_O(D, h)`, in which
player `j`'s payoff under the pure profile `a` is `E[D_j | h, a]`. -/
def IsOneShotEquilibrium (G : Game I S A) (D : I → HistFun I S A)
    {n : ℕ} (h : Hist I S A n) (x : ∀ j, PMF (A j)) : Prop :=
  AGT.IsMixedNash (fun j a => oneShotPayoffPure G (D j) h a) (fun j b => (x j b).toReal)

/-- **Theorem 3.1, properties (1)–(3)** (minmax version): `D` is a bounded Martin function for
the parameter `ε` and player `i`. All quantifiers over histories range over the paper's `H`,
the feasible histories. -/
def IsMartinFunction (G : Game I S A) (ε : ℝ) (i : I) (D : HistFun I S A) : Prop :=
  -- `Dᵢ^ε` is bounded on `H`
  (∃ C : ℝ, ∀ n (h : Hist I S A n), Feasible G h → |D n h| ≤ C) ∧
  -- property 1
  (∀ n (h : Hist I S A n), Feasible G h →
    minmax G i n h - ε ≤ D n h ∧ D n h ≤ minmax G i n h) ∧
  -- property 2
  (∀ n (h : Hist I S A n), Feasible G h → D n h ≤ oneShotMinmax G i D h) ∧
  -- property 3
  (∀ m (h' : Hist I S A m), Feasible G h' → ∀ σ : Profile G,
    (∀ n (h : Hist I S A n), Feasible G h → Extends h' h →
      oneShotMinmax G i D h ≤ oneShotPayoff G D h (fun j => σ j n h)) →
    ∀ n (h : Hist I S A n), Feasible G h → Extends h' h →
      oneShotMinmax G i D h ≤ payoff G σ n h i)

end GenPayoffSG.Solvable


