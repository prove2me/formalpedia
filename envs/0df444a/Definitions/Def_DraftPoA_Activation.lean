-- Prove2me | Definitions.Def_DraftPoA_Activation
-- name    : DraftPoA_Activation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:20.170199+00:00
-- url     : https://prove2.me/theorems/fdfa9e2a-158e-4cca-a9c7-f7cde96003a2
-- title:
--   Competitors' prices $\pi^i_j(b)$, the single-price profit $\Phi_i(p;b)$ and the activation deviation
-- statement:
--   For a pure profile $b$, a bidder $i$ and an item $j$, let $\pi^i_j(b)=p_j(b)$ if $j\notin B_i(b)$ and $\pi^i_j(b)=0$ if $j\in B_i(b)$: the price a competitor paid for $j$. For a set $O$ and a price $p$, the **single-price profit** is
--
--   $$\Phi_i(p;b)=\max\{\,v_i(U)-p|U|\;:\;U\subseteq O,\ \pi^i_j(b)<p\text{ for all }j\in U\,\}.$$
--
--   The **activation deviation** $d(b_i,v_i,p)$: at every node let $(\beta,X)$ be $b_i$'s action, $H$ bidder $i$'s holdings and $I$ the remaining items, and let the demand set $D$ maximize $v_i(H\cup X')-p|X'|$ over $X'\subseteq I$, chosen to be $\emptyset$ whenever $\emptyset$ attains the maximum and by a fixed rule among nonempty maximizers otherwise.
--
--   1. If $d$ has activated (at an earlier node $i$ won the round while $\beta<p$ and $D\neq\emptyset$ held there), bid $0$ with one remaining item.
--   2. Otherwise, if $\beta\ge p$ or $D=\emptyset$, play $(\beta,X)$.
--   3. Otherwise play $(p,D)$.
--
--   The deviation reads only $b_i$, $v_i$, $p$ and the public node, which is what lets the upper bound extend to mixed, correlated and Bayes–Nash equilibria.
--
--   **Formalization Note** The deviation is given as an action rule on nodes; Lemma 3.1 asserts that a legal pure strategy with this action map exists. The fixed rule among nonempty maximizers is a choice function. The "single remaining item" after activation is the first remaining item in index order.
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), §3 "Prices paid by competitors" and §3.1 "The activation deviation", p.6 (PDF 7); App. A.1, p.15 (PDF 16)

import Mathlib
import Definitions.Def_DraftPoA_Auction

namespace DraftPoA

/-!
# Competitors' prices, the single-price profit and the activation deviation

H. T. Truong, N. Thach, H. Chan, M. Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027
submission (manuscript sha256 270ffdaa…), §3 "Prices paid by competitors" and §3.1 "The activation
deviation", p.6 (PDF 7); App. A.1 "The strategy", p.15 (PDF 16).

**Formalization Note.**
* `compPrice prio b i j` is `π^i_j(b)`: the price of item `j` on the path of `b` if bidder `i`
  did not get it, and `0` if she did.
* `singlePriceProfit v O π p` is `max { v(U) − p|U| : U ⊆ O, π_j < p for all j ∈ U }`; the
  empty set is always eligible, so the maximum exists and is `≥ v(∅)`. It is `Φ_i(p; b)` for
  `v = v_i`, `O = O_i`, `π = π^i(b)` (p.6), and `Φ(p)` of Lemma 3.2 for `O = S` (p.7).
* The activation deviation is given as a rule on actions, `activationAct i bi vi p`, built from
  bidder `i`'s strategy (its action map `bi`), her valuation `vi` and the price `p` only. At a node
  `ν` with `b_i`'s action `(β, X)`, holdings `H` and remaining items `I`:
  - the demand set `D` maximizes `v(H ∪ X′) − p|X′|` over `X′ ⊆ I`; it is `∅` whenever `∅`
    attains the maximum, and otherwise a fixed (choice-function) maximizer;
  - `d` has *activated* at `ν` if at some earlier node `ν′` of `ν` bidder `i` won the round while
    `β < p` and `D ≠ ∅` held at `ν′` (App. A.1);
  - after activation: bid `0` for the first remaining item; otherwise, if `β ≥ p` or `D = ∅`,
    play `(β, X)`; else play `(p, D)`.
-/

variable {n m : ℕ}

/-- `π^i_j(b)`: the price a competitor paid for item `j` on the path of `b`, or `0` if bidder `i`
obtained `j` herself (p.6). -/
noncomputable def compPrice [NeZero n] {δ Mbar : ℝ} (prio : Equiv.Perm (Fin n))
    (b : Fin n → Strategy n m δ Mbar) (i : Fin n) (j : Fin m) : ℝ :=
  if j ∈ holdings (play prio b) i then 0 else price (play prio b) j

open Classical in
/-- The single-price profit `max { v(U) − p|U| : U ⊆ O, π_j < p for all j ∈ U }` (p.6, p.7). -/
noncomputable def singlePriceProfit (v : Finset (Fin m) → ℝ) (O : Finset (Fin m))
    (π : Fin m → ℝ) (p : ℝ) : ℝ :=
  (O.powerset.filter fun U => ∀ j ∈ U, π j < p).sup'
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset O, by simp⟩⟩
    (fun U => v U - p * (U.card : ℝ))

/-- The objective of the demand set at holdings `H` and price `p`: `v(H ∪ X′) − p|X′|`. -/
def demandValue (v : Finset (Fin m) → ℝ) (H : Finset (Fin m)) (p : ℝ) (X' : Finset (Fin m)) : ℝ :=
  v (H ∪ X') - p * (X'.card : ℝ)

/-- The largest value of `v(H ∪ X′) − p|X′|` over `X′ ⊆ I`. -/
noncomputable def demandMax (v : Finset (Fin m) → ℝ) (H I : Finset (Fin m)) (p : ℝ) : ℝ :=
  I.powerset.sup' ⟨∅, Finset.empty_mem_powerset I⟩ (demandValue v H p)

open Classical in
/-- The demand set at price `p` (p.6; App. A.1): `∅` whenever buying nothing attains the maximum,
otherwise a fixed maximizer among the subsets of the remaining items `I`. -/
noncomputable def demandSet (v : Finset (Fin m) → ℝ) (H I : Finset (Fin m)) (p : ℝ) :
    Finset (Fin m) :=
  if demandValue v H p ∅ = demandMax v H I p then ∅
  else Classical.choose (Finset.exists_mem_eq_sup' ⟨∅, Finset.empty_mem_powerset I⟩
    (demandValue v H p))

/-- The demand set of bidder `i` at node `ν`. -/
noncomputable def demandAt (i : Fin n) (vi : Finset (Fin m) → ℝ) (p : ℝ) (ν : Node n m) :
    Finset (Fin m) :=
  demandSet vi (holdings ν i) (remaining ν) p

/-- The activation deviation has activated at `ν`: at some earlier node `ν′ = ν.take k` bidder `i`
won the round (the `k`-th triple names her) while `β < p` and `D ≠ ∅` held at `ν′` (App. A.1). -/
def activated (i : Fin n) (bi : Node n m → ℝ × Finset (Fin m)) (vi : Finset (Fin m) → ℝ)
    (p : ℝ) (ν : Node n m) : Prop :=
  ∃ k, ∃ hk : k < ν.length, (ν[k]).1 = i ∧ (bi (ν.take k)).1 < p ∧
    demandAt i vi p (ν.take k) ≠ ∅

open Classical in
/-- The action of the activation deviation `d(b_i, v_i, p)` at node `ν` (p.6; App. A.1). -/
noncomputable def activationAct (i : Fin n) (bi : Node n m → ℝ × Finset (Fin m))
    (vi : Finset (Fin m) → ℝ) (p : ℝ) (ν : Node n m) : ℝ × Finset (Fin m) :=
  if activated i bi vi p ν then
    (0, if h : (remaining ν).Nonempty then {(remaining ν).min' h} else ∅)
  else if p ≤ (bi ν).1 ∨ demandAt i vi p ν = ∅ then bi ν
  else (p, demandAt i vi p ν)

end DraftPoA


