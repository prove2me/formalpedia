-- Prove2me | Definitions.Def_DGPNash_Gadget_BasicGadgets
-- name    : DGPNash_Gadget_BasicGadgets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:28:40.458218+00:00
-- url     : https://prove2.me/theorems/85c70b2f-7ec1-4ae3-b786-472e3cc731ee
-- title:
--   The gadgets $\mathcal G_{\times\alpha}$ (Prop. 4.2), the arithmetic gadget of Prop. 4.3, $\mathcal G_\alpha$ (Prop. 4.5) and the comparator $\mathcal G_<$ (Lemma 5.3)
-- statement:
--   Four small binary graphical games (every player has strategies $\{0, 1\}$). $[A]$ is $1$ if $A$ holds and $0$ otherwise.
--
--   1. **$\mathcal G_{\times\alpha}$** (Proposition 4.2, p. 215), for a nonnegative real $\alpha$: players $v_1$ (input), $w$, $v_2$ (output). Payoff to $v_2$: $[w = 1]$ if $v_2$ plays $0$, $[w = 0]$ if it plays $1$. Payoff to $w$: $\alpha [v_1 = 1]$ if $w$ plays $0$, $[v_2 = 1]$ if it plays $1$.
--   2. **The arithmetic gadget of Proposition 4.3** (pp. 215–216), for nonnegative reals $\alpha, \beta, \gamma$: players $v_1, v_2$ (inputs), $w$, $v_3$ (output). Payoff to $v_3$: $[w = 1]$ if $v_3$ plays $0$, $[w = 0]$ if it plays $1$. Payoff to $w$ when it plays $1$: $[v_3 = 1]$; when it plays $0$: $0, \beta, \alpha, \alpha + \beta + \gamma$ for $(v_1, v_2) = (0,0), (0,1), (1,0), (1,1)$.
--   3. **$\mathcal G_\alpha$** (Proposition 4.5, p. 218), for a nonnegative real $\alpha$: players $w$ and $v_1$ (output). Payoff to $v_1$: $[w = 1]$ if $v_1$ plays $0$, $[w = 0]$ if it plays $1$. Payoff to $w$: $\alpha$ if $w$ plays $0$, $[v_1 = 1]$ if it plays $1$.
--   4. **The comparator $\mathcal G_<$** (proof of Lemma 5.3, p. 245): players $a, b$ (inputs) and $d$ (output). $d$ receives $1$ if it plays $0$ and $a$ plays $1$, $1$ if it plays $1$ and $b$ plays $1$, and $0$ otherwise.
--
--   The payoffs of the input players ($v_1$ in 1, $v_1, v_2$ in 2, $a, b$ in 4) are unconstrained in the paper and are $0$ here. These games are the elementary building blocks the paper uses to simulate arithmetic circuits by graphical games.
--
--   **Formalization Note** Each game has its own inductive player type (`MulRole`, `ArithRole`, `ConstRole`, `CompRole`) and strategy type `Fin 2` for every player. With zero payoffs, the $\epsilon$-well-supported condition at an input player holds for every profile, so an $\epsilon$-Nash equilibrium of the standalone game leaves the inputs' mixed strategies arbitrary, which is the paper's meaning when the gadget is a part of a larger game whose input payoffs are arbitrary.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 215, Proposition 4.2; pp. 215–216, Proposition 4.3; p. 218, Proposition 4.5; p. 245, proof of Lemma 5.3

import Mathlib
import Definitions.Def_DGPNash_Gadget_AddMulGame

namespace DGPNash.Gadget

/-- Players of the game `G_{×α}` of Proposition 4.2 (p. 215, Fig. 3): input `v₁`, output `v₂`,
intermediate `w`. -/
inductive MulRole
  | v1 | v2 | w
  deriving DecidableEq

instance MulRole.instFintype : Fintype MulRole :=
  Fintype.ofList [.v1, .v2, .w] (by intro x; cases x <;> simp)

/-- Payoffs of Proposition 4.2 (p. 215), every player having strategies `{0, 1}` (`Fin 2`). The
input `v₁` receives payoff `0` (its payoff is unconstrained in the paper). -/
noncomputable def mulPayoff (α : ℝ) : MulRole → (MulRole → Fin 2) → ℝ
  | .v1, _ => 0
  | .v2, s => if s .v2 = 0 then ind (s .w = 1) else ind (s .w = 0)
  | .w, s => if s .w = 0 then α * ind (s .v1 = 1) else ind (s .v2 = 1)

/-- Players of the game of Proposition 4.3 (pp. 215–216, Fig. 5): inputs `v₁, v₂`, output `v₃`,
intermediate `w`. -/
inductive ArithRole
  | v1 | v2 | v3 | w
  deriving DecidableEq

instance ArithRole.instFintype : Fintype ArithRole :=
  Fintype.ofList [.v1, .v2, .v3, .w] (by intro x; cases x <;> simp)

/-- Payoffs of Proposition 4.3 (pp. 215–216), every player having strategies `{0, 1}`. When `w`
plays `0` its payoff is `0, β, α, α + β + γ` for `(v₁, v₂) = (0,0), (0,1), (1,0), (1,1)`. The
inputs `v₁, v₂` receive payoff `0` (their payoffs are unconstrained in the paper). -/
noncomputable def arithPayoff (α β γ : ℝ) : ArithRole → (ArithRole → Fin 2) → ℝ
  | .v1, _ => 0
  | .v2, _ => 0
  | .v3, s => if s .v3 = 0 then ind (s .w = 1) else ind (s .w = 0)
  | .w, s =>
      if s .w = 0 then
        (if s .v1 = 0 then (if s .v2 = 0 then 0 else β)
         else (if s .v2 = 0 then α else α + β + γ))
      else ind (s .v3 = 1)

/-- Players of the game `G_α` of Proposition 4.5 (p. 218, Fig. 4): `w` and the output `v₁`. -/
inductive ConstRole
  | w | v1
  deriving DecidableEq

instance ConstRole.instFintype : Fintype ConstRole :=
  Fintype.ofList [.w, .v1] (by intro x; cases x <;> simp)

/-- Payoffs of Proposition 4.5 (p. 218), both players having strategies `{0, 1}`. -/
noncomputable def constPayoff (α : ℝ) : ConstRole → (ConstRole → Fin 2) → ℝ
  | .v1, s => if s .v1 = 0 then ind (s .w = 1) else ind (s .w = 0)
  | .w, s => if s .w = 0 then α else ind (s .v1 = 1)

/-- Players of the comparator game `G_<` of Lemma 5.3 (p. 245): inputs `a, b` and output `d`. -/
inductive CompRole
  | a | b | d
  deriving DecidableEq

instance CompRole.instFintype : Fintype CompRole :=
  Fintype.ofList [.a, .b, .d] (by intro x; cases x <;> simp)

/-- Payoffs of the comparator game in the proof of Lemma 5.3 (p. 245), every player having
strategies `{0, 1}`: `d` receives `1` if it plays `0` and `a` plays `1`, `1` if it plays `1` and
`b` plays `1`, and `0` otherwise. The inputs `a, b` receive payoff `0`. -/
noncomputable def compPayoff : CompRole → (CompRole → Fin 2) → ℝ
  | .a, _ => 0
  | .b, _ => 0
  | .d, s => if s .d = 0 then ind (s .a = 1) else ind (s .b = 1)

end DGPNash.Gadget


