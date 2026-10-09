-- Prove2me | Definitions.Def_CostSharingPNE_Char_Setting
-- name    : CostSharingPNE_Char_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:23:01.594345+00:00
-- url     : https://prove2.me/theorems/b7a0aa42-f893-4ed1-a2a5-9df1beb9c148
-- title:
--   §2 and §4 — welfare sharing games, pure Nash equilibria, the class 𝒢(N, f^𝕎, 𝕎), budget-balance and the distributed welfare (10)
-- statement:
--   Let $N=\{1,\dots,n\}$ be a set of players and $R=\{r_1,\dots,r_m\}$ a set of resources. A **local welfare function** is a map $W:2^N\to\mathbb R$, and a **distribution rule** is a map $f:N\times 2^N\to\mathbb R$; the number $f(i,S)$ is the share of player $i$ when it shares a resource with the coalition $S$. Only the values with $i\in S$ carry meaning (the paper sets $f(i,S):=0$ for $i\notin S$).
--
--   A **welfare sharing game** assigns to each resource $r$ a local welfare function $W_r$, to each welfare function $W$ one distribution rule $f^W$ (so resources with the same welfare function use the same rule), and to each player $i$ a nonempty action set $\mathcal A_i\subseteq 2^R$. In an allocation $a=(a_1,\dots,a_n)$ the players on resource $r$ are $\{a\}_r=\{i\in N: r\in a_i\}$, and player $i$ receives
--   $$
--   U_i(a)=\sum_{r\in a_i} f^{W_r}\bigl(i,\{a\}_r\bigr).
--   $$
--   A **pure Nash equilibrium** is an allocation $a^*$ with $a^*_i\in\mathcal A_i$ for all $i$ and $U_i(a^*)\ge U_i(a_i,a^*_{-i})$ for every player $i$ and every $a_i\in\mathcal A_i$.
--
--   For a set $\mathbb W$ of local welfare functions, the class $\mathcal G(N,f^{\mathbb W},\mathbb W)$ consists of all such games with every $W_r\in\mathbb W$, any number $m>1$ of resources and arbitrary nonempty action sets. The rules $f^{\mathbb W}$ **guarantee equilibrium existence** if every game of the class has a pure Nash equilibrium.
--
--   A rule $g$ is **budget-balanced** for $W$ if $\sum_{i\in S} g(i,S)=W(S)$ for every $S\subseteq N$. The welfare **actually distributed** by $g$ is
--   $$
--   W'(S)=\sum_{i\in S} g(i,S)\qquad (S\subseteq N),
--   $$
--   the map $g_{SV}$ of (10).
--
--   These are the objects of the characterization theorems: equilibrium existence is a property of the family of rules, quantified over every game of the class.
--
--   **Formalization Note** Players are `Fin n`, resources `Fin m`, actions `Finset (Fin m)` (the empty action is allowed, as $\mathcal A_i\subseteq 2^R$). The family of rules is a function `f : Welfare n → Rule n`, which encodes the paper's assumption $W_r=W_{r'}\Rightarrow f^r=f^{r'}$. `GuaranteesPNE 𝕎 f` quantifies over every `m > 1`, every assignment `Fin m → 𝕎` (repetitions allowed) and every family of nonempty action sets. Nonemptiness of the action sets is implicit on the page (a game needs a profile) and is required here: without it no game could have an equilibrium.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, §2 (pp. 3–4), §4 (p. 9), (10) (p. 9)

import Mathlib

namespace CostSharingPNE.Char

/-- A local welfare function `W : 2^N → ℝ` on coalitions of the players `N = Fin n`
(Gopalakrishnan–Marden–Wierman, arXiv:1402.3610v1, §2, p. 4). -/
abbrev Welfare (n : ℕ) := Finset (Fin n) → ℝ

/-- A distribution rule `f : N × 2^N → ℝ`; `f i S` is the share of player `i` when sharing with
the coalition `S` (§2, p. 4). Only the values with `i ∈ S` are meaningful; the paper sets
`f(i, S) := 0` for `i ∉ S`. -/
abbrev Rule (n : ℕ) := Fin n → Finset (Fin n) → ℝ

/-- `{a}_r = {i ∈ N : r ∈ a_i}`, the players allocated to resource `r` in the allocation `a`
(§2, p. 4). Resources are `Fin m`, an action is a set of resources. -/
def players {n m : ℕ} (a : Fin n → Finset (Fin m)) (r : Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun j => r ∈ a j)

/-- The utility `U_i(a) = ∑_{r ∈ a_i} f^{W_r}(i, {a}_r)` of player `i` in the welfare sharing
game with local welfare functions `W : Fin m → Welfare n` and the family of distribution rules
`f`, one rule `f W` per welfare function (so `W_r = W_{r'}` forces `f^r = f^{r'}`) (§2, p. 4). -/
def utility {n m : ℕ} (W : Fin m → Welfare n) (f : Welfare n → Rule n)
    (a : Fin n → Finset (Fin m)) (i : Fin n) : ℝ :=
  ∑ r ∈ a i, f (W r) i (players a r)

/-- A pure Nash equilibrium (§2, p. 4): a profile `a` with `a i ∈ A i` for every player, at which
no player can raise its utility by a unilateral change to another action of its action set. -/
def IsPureNash {n m : ℕ} (W : Fin m → Welfare n) (f : Welfare n → Rule n)
    (A : Fin n → Finset (Finset (Fin m))) (a : Fin n → Finset (Fin m)) : Prop :=
  (∀ i, a i ∈ A i) ∧
    ∀ i, ∀ b ∈ A i, utility W f (Function.update a i b) i ≤ utility W f a i

/-- "All games in `𝒢(N, f^𝕎, 𝕎)` possess a pure Nash equilibrium" (§4, p. 9): for every number of
resources `m > 1`, every assignment `r ↦ W_r ∈ 𝕎` of local welfare functions to resources
(repetitions allowed) and every family of nonempty action sets `A_i ⊆ 2^R`, the game has a pure
Nash equilibrium. For a single welfare function this is `GuaranteesPNE {W} f`. -/
def GuaranteesPNE {n : ℕ} (𝕎 : Set (Welfare n)) (f : Welfare n → Rule n) : Prop :=
  ∀ m : ℕ, 1 < m → ∀ W : Fin m → Welfare n, (∀ r, W r ∈ 𝕎) →
    ∀ A : Fin n → Finset (Finset (Fin m)), (∀ i, (A i).Nonempty) →
      ∃ a, IsPureNash W f A a

/-- `g` is budget-balanced for `W`: `∑_{i ∈ S} g(i, S) = W(S)` for every `S ⊆ N` (§2, p. 4). -/
def IsBudgetBalanced {n : ℕ} (g : Rule n) (W : Welfare n) : Prop :=
  ∀ S : Finset (Fin n), ∑ i ∈ S, g i S = W S

/-- The welfare actually distributed by `g`, `W'(S) = ∑_{i ∈ S} g(i, S)` ((10), p. 9). -/
def distributed {n : ℕ} (g : Rule n) : Welfare n :=
  fun S => ∑ i ∈ S, g i S

end CostSharingPNE.Char


