-- Prove2me | Definitions.Def_GSRandomOrder_Supplement_frozenRouting
-- name    : GSRandomOrder_Supplement_frozenRouting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:07:42.033846+00:00
-- url     : https://prove2.me/theorems/f23a0449-5ca3-45fe-b064-0de89b3183a1
-- title:
--   Frozen routing (Section 4.2): bidder $i$'s bundle at time $s$
-- statement:
--   Fix $\lambda\in(0,1)$, a total order $\prec$ on the item labels and a tie-breaking order on the bidders, and let $\bar v_i$ be the envelope of $v_i$. **Frozen routing** works as follows.
--
--   1. *Coins and times.* Every item $g$ has heads independently with probability $\lambda$; $L$ is the set of items with heads. The items without heads arrive at independent times $t_g$ uniform on $[0,1]$.
--   2. *Training and pools.* Start with empty training bundles $B_1,\dots,B_m$ and empty pools $R_1,\dots,R_m$ and process all labels in the order $\prec$. At label $g$ let
--   $$
--   i(g)=\arg\max_i\ \bar v_i(g\mid B_i),
--   $$
--   with ties broken by the order on bidders, and add $g$ to $B_{i(g)}$ if $g$ has heads and to $R_{i(g)}$ if it has tails.
--   3. *Selection.* Every bidder $i$ runs the survival algorithm of Section 3.1 for the restriction of $v_i$ to its pool $R_i$; an arriving item $g\notin L$ is passed with its time $t_g$ to the copy of bidder $i(g)$ and given to $i(g)$ if that copy accepts it. Items with heads are discarded.
--
--   The object defined is $A_i(s)$, the bundle of bidder $i$ at real time $s$, as a function of the coins and times.
--
--   **Formalization Note** The sample space has one uniform heads variable $h_g$ (heads iff $h_g<\lambda$), one uniform arrival time $r_g$ and one uniform acceptance coin $c_g$ per item, all independent. The paper draws $K\sim\mathrm{Bin}(n,\lambda)$, discards the first $K$ arrivals and attaches sorted uniforms to the others; this produces the same joint law of $L$ and $(t_g)_{g\notin L}$. The label order is a bijection `π` ($\pi_k$ is the $k$-th label) and the bidder order a bijection `ρ`; both are arbitrary. Selection is the published `runSurvival` for $v_i$ on the item set $R_i$, which queries $v_i$ only on subsets of arrived items of $R_i$. One coin per item serves all copies, since the pools are disjoint.
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §4.2, pp.12–13 ("Coins and times", "Training and pools", "Selection"), eq. (10)

import Mathlib
import Definitions.Def_GSRandomOrder_runSurvival
import Definitions.Def_GSRandomOrder_Supplement_envelope

set_option autoImplicit false

namespace GSRandomOrder.Supplement

/-- The sample space of frozen routing: one heads coin `h_g ∈ [0, 1]` per item, together with the
sample space `Ω n` of the survival algorithm (one arrival variable `r_g` and one acceptance coin
`c_g` per item). Under `volume` all coordinates are independent and uniform on `[0, 1]`. -/
abbrev FRΩ (n : ℕ) := (Fin n → unitInterval) × Ω n

/-- The heads set `L = {g : h_g < λ}`: each item has heads independently with probability `λ`
(for `λ ∈ [0, 1]`). -/
noncomputable def headsSet {n : ℕ} (lam : ℝ) (h : Fin n → unitInterval) : Finset (Fin n) :=
  Finset.univ.filter fun g => (h g : ℝ) < lam

open Classical in
/-- The route `i(g) = argmax_i v̄_i(g | B_i)` of label `g` (§4.2, p.13, eq. (10)), ties broken by
the order on bidders: `ρ k` is the `k`-th bidder in that order, and the route is the first bidder
in it whose marginal is maximal. It is `none` only when there are no bidders (`m = 0`). -/
noncomputable def route {n m : ℕ} (v : Fin m → Finset (Fin n) → WithBot ℝ) (ρ : Fin m ≃ Fin m)
    (B : Fin m → Finset (Fin n)) (g : Fin n) : Option (Fin m) :=
  ((List.finRange m).map ρ).find? fun i =>
    decide (∀ j, envelopeMarginal (v j) g (B j) ≤ envelopeMarginal (v i) g (B i))

/-- One step of the training pass (§4.2, p.13, "Training and pools"): the state is the pair
(training bundles `B`, pools `R`); label `g` is routed to `i(g)` and added to `B_{i(g)}` if it has
heads (`g ∈ L`) and to `R_{i(g)}` if it has tails. -/
noncomputable def trainStep {n m : ℕ} (v : Fin m → Finset (Fin n) → WithBot ℝ)
    (ρ : Fin m ≃ Fin m) (L : Finset (Fin n))
    (st : (Fin m → Finset (Fin n)) × (Fin m → Finset (Fin n))) (g : Fin n) :
    (Fin m → Finset (Fin n)) × (Fin m → Finset (Fin n)) :=
  match route v ρ st.1 g with
  | none => st
  | some i =>
    if g ∈ L then (Function.update st.1 i (insert g (st.1 i)), st.2)
    else (st.1, Function.update st.2 i (insert g (st.2 i)))

/-- The training pass over all labels in the order `≺`, where `π k` is the `k`-th label in that
order, starting from empty bundles and pools. Its output is (final training bundles, pools). -/
noncomputable def trainPass {n m : ℕ} (v : Fin m → Finset (Fin n) → WithBot ℝ)
    (π : Fin n ≃ Fin n) (ρ : Fin m ≃ Fin m) (L : Finset (Fin n)) :
    (Fin m → Finset (Fin n)) × (Fin m → Finset (Fin n)) :=
  ((List.finRange n).map π).foldl (trainStep v ρ L) (fun _ => ∅, fun _ => ∅)

/-- **Frozen routing** (R. Paes Leme, M. Pál, N. Patel, *Gross Substitutes Welfare in Random
Order*, STOC 2027 submission, manuscript sha256 69787f50…, §4.2, pp.12–13), with parameter `λ`,
label order `≺` (`π k` is the `k`-th label) and bidder tie-breaking order (`ρ k` is the `k`-th
bidder): `frozenRouting v π ρ λ x s i` is bidder `i`'s bundle `A_i` at real time `s` on the sample
point `x = (h, (r, c))`.
1. *Coins.* Item `g` has heads iff `h_g < λ`; `L` is the heads set.
2. *Training and pools.* Process all labels in the order `≺` with empty training bundles `B_i`
   and pools `R_i`; route label `g` to `i(g) = argmax_i v̄_i(g | B_i)` (ties by the bidder order)
   and add it to `B_{i(g)}` if it has heads, to `R_{i(g)}` if it has tails.
3. *Selection.* Bidder `i` runs the survival algorithm of §3.1 (`GSRandomOrder.runSurvival`) for
   `v_i` on the items of its pool `R_i`, which arrive at the times `r_g` (uniform on `[0, 1]`); an
   item is given to `i(g)` iff that copy accepts it. Heads items are discarded.

**Formalization Note.** The paper draws `K ∼ Bin(n, λ)`, lets the first `K` arrivals be `L`, and
attaches sorted uniforms to the other arrivals; this gives the same joint law of
`(L, (t_g)_{g ∉ L})` as independent heads coins and independent uniform times, which is the model
used here (the times of heads items are never read). One acceptance coin per item suffices for the
"independent copies" of the survival algorithm, since the pools are disjoint. The survival
algorithm run on `Q = R_i` queries `v_i` only on sets of arrived items of `R_i`, i.e. it is the
algorithm for the restriction of `v_i` to `R_i`. The orders `≺` and the bidder order are
arbitrary bijections, not the orders of `Fin n` and `Fin m`. -/
noncomputable def frozenRouting {n m : ℕ} (v : Fin m → Finset (Fin n) → WithBot ℝ)
    (π : Fin n ≃ Fin n) (ρ : Fin m ≃ Fin m) (lam : ℝ) (x : FRΩ n) (s : ℝ) (i : Fin m) :
    Finset (Fin n) :=
  (runSurvival (v i) ((trainPass v π ρ (headsSet lam x.1)).2 i) 1 x.2 s).2

end GSRandomOrder.Supplement


