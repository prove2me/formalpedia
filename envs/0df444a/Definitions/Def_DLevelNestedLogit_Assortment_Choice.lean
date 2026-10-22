-- Prove2me | Definitions.Def_DLevelNestedLogit_Assortment_Choice
-- name    : DLevelNestedLogit_Assortment_Choice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T04:46:51.781016+00:00
-- url     : https://prove2.me/theorems/72ec6f10-73f4-4dcb-8008-55985c83bbaa
-- title:
--   Preference weights V_j (1), expected revenues R_j (2), the assortment problem (3), the scalars t*_j and the local problem (4)
-- statement:
--   The quantities of the $d$-level nested logit model on a product tree (see the tree definition), with nest parameters $\eta_j$, attractiveness parameters $v_0,\dots,v_n$ and revenues $r_1,\dots,r_n$.
--
--   An **assortment** is a set $S\subseteq\{1,\dots,n\}$; the no-purchase option is always offered. **Preference weights** (1): at a product leaf $j\ne 0$, $V_j=v_j$ if $j\in S$ and $V_j=0$ otherwise; at leaf $0$, $V_0=v_0$; at a nonleaf node
--   $$V_j(S_j)=\Big(\sum_{k\in\mathrm{Children}(j)}V_k(S_k)\Big)^{\eta_j}.$$
--   The standing range of the parameters is $\eta_{\mathrm{root}}=0$ (so $V_{\mathrm{root}}=1$) and $\eta_j\in(0,1]$ at every other nonleaf node. **Expected revenues** (2): at a product leaf $j\ne0$, $R_j=r_j$ if $j\in S$ and $0$ otherwise; $R_0=0$; at a nonleaf node
--   $$R_j(S_j)=\frac{\sum_{k\in\mathrm{Children}(j)}V_k(S_k)\,R_k(S_k)}{\sum_{k\in\mathrm{Children}(j)}V_k(S_k)}.$$
--   The **assortment problem** (3) is $Z^*=\max_{S\subseteq\{1,\dots,n\}}R_{\mathrm{root}}(S_{\mathrm{root}})$; $S^*$ is optimal if $R_{\mathrm{root}}(S)\le R_{\mathrm{root}}(S^*)$ for every assortment $S$. From an assortment $S^*$ the **scalars** $t^*_j$ are computed top-down,
--   $$t^*_j=\max\{t^*_{\mathrm{Parent}(j)},\ \eta_j t^*_{\mathrm{Parent}(j)}+(1-\eta_j)R_j(S^*_j)\},\qquad t^*_{\mathrm{Parent}(\mathrm{root})}=0.$$
--   The **local problem** (4) at node $j$ with threshold $u$ is $\max_{S_j\subseteq N_j}V_j(S_j)\,(R_j(S_j)-u)$, and a set $\hat S_j$ is an optimal solution of it if $\hat S_j\subseteq N_j$, $0\notin\hat S_j$, and no set $S_j\subseteq N_j$ with $0\notin S_j$ has a larger objective.
--
--   **Formalization Note.** Assortments are `Finset (Fin (n + 1))` not containing `0` (`IsAssortment`). `V η v S j` and `R η v r S j` take the whole assortment `S`; they only look at the leaves below `j`, so they equal $V_j(S\cap N_j)$ and $R_j(S\cap N_j)$. The no-purchase leaf contributes $v_0$ regardless of $S$ (the convention $S_0=\{0\}$), and its membership in a set is never used. Powers are `Real.rpow`, so $x^{0}=1$ (giving $V_{\mathrm{root}}=1$ when $\eta_{\mathrm{root}}=0$) and $0^{\eta}=0$ for $\eta>0$. Division is Lean's (`x / 0 = 0`), which fixes the value $R_j(\emptyset)=0$ at a nonleaf node whose subtree offers no product (a $0/0$ in (2)); when $S^*_j=\emptyset$ this gives $t^*_j=\max\{t^*_{\mathrm{Parent}(j)},\eta_jt^*_{\mathrm{Parent}(j)}\}=t^*_{\mathrm{Parent}(j)}$, as $t^*\ge0$. `tstar` is computed from an arbitrary finset `Sstar`; the theorems apply it to an optimal one. `tparent j` is $t^*_{\mathrm{Parent}(j)}$, and `0` at the root. `StandingEta η` records the parameter range; positivity of $v$ is a hypothesis of the theorems.
-- source:
--   Li, Rusmevichientong, Topaloglu, The d-Level Nested Logit Model: Assortment and Price Optimization Problems, Oper. Res. 63(2), 2015, pp. 328–329, §3 (1), (2), (3) and §4 (definition of t*_j, (4))

import Mathlib
import Definitions.Def_DLevelNestedLogit_Assortment_Tree

namespace DLevelNestedLogit.Assortment

/-- An assortment is a set of products `S ⊆ {1, …, n}`, i.e. a finset of `Fin (n + 1)` not
containing the no-purchase option `0`. -/
def IsAssortment {n : ℕ} (S : Finset (Fin (n + 1))) : Prop := (0 : Fin (n + 1)) ∉ S

namespace ProductTree

variable {n : ℕ} (T : ProductTree n)

/-- The standing range of the nest parameters (p. 328): `η_root = 0`, and `η_j ∈ (0, 1]` at
every other nonleaf node. (Leaves carry no parameter; the values of `η` there are unused.) -/
def StandingEta (η : T.Node → ℝ) : Prop :=
  η T.root = 0 ∧ ∀ j, j ≠ T.root → ¬ T.IsLeaf j → 0 < η j ∧ η j ≤ 1

/-- The preference weight `V_j(S_j)` of node `j` when the assortment `S` is offered
(p. 328, (1)). At a leaf `leaf i` with `i ≠ 0` it is `v_i` if `i ∈ S` and `0` otherwise; at the
no-purchase leaf it is always `v_0` (the convention `S_0 = {0}`); at a nonleaf node it is
`(∑_{k ∈ Children(j)} V_k(S_k))^{η_j}` (a real power, `Real.rpow`). Since the leaf values only
look at `S ∩ N_j`, this is `V_j(S_j)` with `S_j = S ∩ N_j`. -/
noncomputable def V (η : T.Node → ℝ) (v : Fin (n + 1) → ℝ) (S : Finset (Fin (n + 1)))
    (j : T.Node) : ℝ :=
  if h : T.IsLeaf j then
    (if T.leafIndex j h = 0 then v 0 else if T.leafIndex j h ∈ S then v (T.leafIndex j h) else 0)
  else (∑ k ∈ (T.children j).attach, V η v S k.1) ^ η j
termination_by T.d - T.depth j
decreasing_by exact T.depth_lt_of_mem_children k.2

/-- The expected revenue `R_j(S_j)` from a customer at node `j` when the assortment `S` is
offered (pp. 328–329, (2)). At a leaf `leaf i` with `i ≠ 0` it is `r_i` if `i ∈ S` and `0`
otherwise; at the no-purchase leaf it is `0`; at a nonleaf node it is
`∑_k V_k(S_k) R_k(S_k) / ∑_k V_k(S_k)` over `k ∈ Children(j)`. Lean's `x / 0 = 0` makes
`R_j(∅) = 0` at a nonleaf node whose subtree offers nothing (a `0/0` on the page). -/
noncomputable def R (η : T.Node → ℝ) (v r : Fin (n + 1) → ℝ) (S : Finset (Fin (n + 1)))
    (j : T.Node) : ℝ :=
  if h : T.IsLeaf j then
    (if T.leafIndex j h ≠ 0 ∧ T.leafIndex j h ∈ S then r (T.leafIndex j h) else 0)
  else (∑ k ∈ (T.children j).attach, T.V η v S k.1 * R η v r S k.1) /
      (∑ k ∈ (T.children j).attach, T.V η v S k.1)
termination_by T.d - T.depth j
decreasing_by exact T.depth_lt_of_mem_children k.2

/-- An assortment `Sstar` is an optimal solution to the assortment problem (3),
`Z* = max_{S ⊆ {1,…,n}} R_root(S_root)` (p. 329). -/
def IsOptimalAssortment (η : T.Node → ℝ) (v r : Fin (n + 1) → ℝ)
    (Sstar : Finset (Fin (n + 1))) : Prop :=
  IsAssortment Sstar ∧ ∀ S, IsAssortment S → T.R η v r S T.root ≤ T.R η v r Sstar T.root

/-- The scalars `t*_j` computed from an assortment `Sstar` (p. 329):
`t*_j = max{t*_Parent(j), η_j t*_Parent(j) + (1 − η_j) R_j(S*_j)}`, with the convention
`t*_Parent(root) = 0`. Computed top-down by recursion on the depth. -/
noncomputable def tstar (η : T.Node → ℝ) (v r : Fin (n + 1) → ℝ) (Sstar : Finset (Fin (n + 1)))
    (j : T.Node) : ℝ :=
  if h : j = T.root then max 0 (η j * 0 + (1 - η j) * T.R η v r Sstar j)
  else max (tstar η v r Sstar (T.parent j))
    (η j * tstar η v r Sstar (T.parent j) + (1 - η j) * T.R η v r Sstar j)
termination_by T.depth j
decreasing_by exact T.depth_parent_lt h

/-- `t*_Parent(j)`, with the convention `t*_Parent(root) = 0` (p. 329). -/
noncomputable def tparent (η : T.Node → ℝ) (v r : Fin (n + 1) → ℝ)
    (Sstar : Finset (Fin (n + 1))) (j : T.Node) : ℝ :=
  if j = T.root then 0 else T.tstar η v r Sstar (T.parent j)

/-- The objective of the local problem (4) at node `j` with threshold `u`:
`V_j(S_j) (R_j(S_j) − u)`. -/
noncomputable def localObj (η : T.Node → ℝ) (v r : Fin (n + 1) → ℝ) (j : T.Node) (u : ℝ)
    (S : Finset (Fin (n + 1))) : ℝ :=
  T.V η v S j * (T.R η v r S j - u)

/-- `Sj` is an optimal solution to the local problem at node `j`,
`max_{S_j ⊆ N_j} V_j(S_j)(R_j(S_j) − u)` (p. 329, (4), with `u = t*_Parent(j)`): `Sj` is a set of
products `1, …, n` inside `N_j`, and no such set has a larger objective. (The no-purchase
option is never a member of the set; it is always offered, see `V`.) -/
def IsLocalOptimal (η : T.Node → ℝ) (v r : Fin (n + 1) → ℝ) (j : T.Node) (u : ℝ)
    (Sj : Finset (Fin (n + 1))) : Prop :=
  Sj ⊆ T.N j ∧ IsAssortment Sj ∧
    ∀ S, S ⊆ T.N j → IsAssortment S → T.localObj η v r j u S ≤ T.localObj η v r j u Sj

end ProductTree

end DLevelNestedLogit.Assortment


