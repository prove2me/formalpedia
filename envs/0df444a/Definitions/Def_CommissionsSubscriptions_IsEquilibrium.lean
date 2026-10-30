-- Prove2me | Definitions.Def_CommissionsSubscriptions_IsEquilibrium
-- name    : CommissionsSubscriptions_IsEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:25:47.892992+00:00
-- url     : https://prove2.me/theorems/24b3d907-8799-4f41-bb96-59371be68a34
-- title:
--   Competitive equilibrium $(p,x,q^s,q^b)\in X(\gamma,\mu)$ (Definition 1)
-- statement:
--   Given fees $(\gamma,\mu)$, a **competitive equilibrium** is a tuple of prices $p\in\mathbb R^{|S|}_+$, supplies $q^s$, demands $q^b$ and a flow $x$ on the edges such that
--
--   1. (2a) $q^s_i=s_i\,F_{s_i}\bigl((1-\gamma^s_i)p_i-\mu^s_i\bigr)$ for every seller type $i$;
--   2. (2b) $q^b_j=b_j\Bigl[1-F_{b_j}\Bigl(\min_{i':(i',j)\in E}\{(1+\gamma^b_j)p_{i'}+c_{i'}\}+\mu^b_j\Bigr)\Bigr]$ for every buyer type $j$;
--   3. (2c) $q^s_i=\sum_{j':(i,j')\in E}x_{ij'}$ and $q^b_j=\sum_{i':(i',j)\in E}x_{i'j}$;
--   4. (2d) $x_{ij}\ge0$ on $E$, and $x_{ij}=0$ whenever $i$ does not attain the minimum in (2b).
--
--   Sellers and buyers with nonnegative surplus participate, the market clears, and buyers trade only with the sellers that are cheapest for them. The set of such tuples is $X(\gamma,\mu)$.
--
--   **Formalization Note** The flow is a function on $S\times B$ of which only the entries on $E$ are read. "$i\notin\arg\min$" is written as "the effective price of $i$ differs from the minimum".
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), Definition 1, (2a)–(2d), p. 9

import Mathlib
import Definitions.Def_CommissionsSubscriptions_Market
import Definitions.Def_CommissionsSubscriptions_Fees
import Definitions.Def_CommissionsSubscriptions_minCost

namespace CommissionsSubscriptions

/-- **Competitive equilibrium `(p, x, q^s, q^b) ∈ X(γ, µ)` (Definition 1).**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), Definition 1, (2a)–(2d), p. 9.

Under the fees `f = (γ, µ)`, the tuple consists of prices `p ∈ ℝ^{|S|}_+`, supplies `qs`, demands
`qb` and a flow `x` on the edges, satisfying
* (2a) `q^s_i = s_i F_{s_i}((1 − γ^s_i) p_i − µ^s_i)` for every `i ∈ S`;
* (2b) `q^b_j = b_j [1 − F_{b_j}(min_{i′:(i′,j)∈E} {(1 + γ^b_j) p_{i′} + c_{i′}} + µ^b_j)]`;
* (2c) `q^s_i = Σ_{j′:(i,j′)∈E} x_{ij′}` and `q^b_j = Σ_{i′:(i′,j)∈E} x_{i′j}`;
* (2d) `x_{ij} ≥ 0` on `E`, and `x_{ij} = 0` unless `i` attains the minimum in (2b).

**Formalization Note (Readings 6, 7).** The flow is a function `x : S → B → ℝ` of which only the
entries on `E` are read (the paper's `x ∈ ℝ^{|E|}`). "`i ∉ argmin`" is written as "the effective
price of `i` differs from `minCost`", which is the same since `minCost` is the minimum over the
neighbours of `j`. -/
def IsEquilibrium {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) :
    Prop :=
  (∀ i, 0 ≤ p i) ∧
    (∀ i, qs i = M.s i * M.Fs i ((1 - f.gs i) * p i - f.ms i)) ∧
    (∀ j, qb j = M.b j * (1 - M.Fb j (minCost M f p j + f.mb j))) ∧
    (∀ i, qs i = ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ M.E), x i j) ∧
    (∀ j, qb j = ∑ i ∈ Finset.univ.filter (fun i => (i, j) ∈ M.E), x i j) ∧
    (∀ e ∈ M.E, 0 ≤ x e.1 e.2) ∧
    (∀ e ∈ M.E, (1 + f.gb e.2) * p e.1 + M.c e.1 ≠ minCost M f p e.2 → x e.1 e.2 = 0)

end CommissionsSubscriptions


