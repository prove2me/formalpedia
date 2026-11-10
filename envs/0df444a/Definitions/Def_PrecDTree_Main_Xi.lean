-- Prove2me | Definitions.Def_PrecDTree_Main_Xi
-- name    : PrecDTree_Main_Xi
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:51:47.760923+00:00
-- url     : https://prove2.me/theorems/b5b1ae91-69ac-44ea-a4d8-61ed8bf4c3ee
-- title:
--   The covering instance ξ(T), U_ξ, and the path D_C of one call of Algorithm 1 (§3)
-- statement:
--   For the hypothesis set $H$ of the current call and each test $t$,
--   $$\xi(t)=\{h\in H \mid h\in X \text{ for some } X\in t \text{ with } |X|\le \tfrac34\,|H|\},$$
--   the blocks $X$ being those of $t$ restricted to $H$. $\xi(T)$ is the indexed family $(\xi(t))_{t\in T}$ with the order of the tests, and $U_\xi=\bigcup_t\xi(t)$. One call of **Algorithm 1** (Identify) on $H$, $|H|\ge 2$, obtains a cover $\mathcal C$ for the f-PCSC instance $(U_\xi,\xi(T),\preceq_\xi,f=1/4)$ from a subroutine FindCover, orders it topologically, $\langle\xi(t_1),\dots,\xi(t_{|\mathcal C|})\rangle$, and performs $t_1,t_2,\dots$ in order, recursing on the remaining set $H'$ as soon as $|H'|\le\frac{5\beta-1}{5\beta}|H|$. $D_{\mathcal C}$ is the path of this call obtained by following replies that do not reach this threshold; it ends with the first test for which every reply reaches it. $\mathrm{cost}_W(D_{\mathcal C})$ is its number of test nodes.
--
--   **Formalization Note.** `xi T Hs t` uses the integer form $4|X|\le 3|H|$; `Uxi T Hs = coverUniverse (xi T Hs)`. `IsTopoOrder le C L` says the list `L` enumerates `C` without repetition as a precedence-closed sequence. `callPathCost T Hs β Hs L` is $\mathrm{cost}_W(D_{\mathcal C})$: the head test of `L` is performed; if a reply block of the hypotheses still on the path has more than $\frac{5\beta-1}{5\beta}|H|$ elements (at most one can, the threshold exceeding $1/2$ for $\beta\ge1$) the path continues into it, otherwise this test ends the path. Only the part of Algorithm 1 the milestones use, one call's path, is defined.
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 6 (ξ, U_ξ) and p. 7 (Algorithm 1, D_C)

import Mathlib
import Definitions.Def_PrecDTree_Main_DecisionTree
import Definitions.Def_PrecDTree_Main_PCSC

set_option autoImplicit false

/-!
# The covering instance ξ and the path D_C of one call of Algorithm 1 (§3, pp. 6–7)

Szyfelbein, Dereniowski, *Precedence-Constrained Decision Trees and Coverings*, arXiv:2602.21312
(STOC 2027 submission version), p. 6 (ξ, U_ξ), p. 7 (Algorithm 1 and D_C).

* `xi T Hs t = ξ(t) = {h ∈ H | h ∈ X for some X ∈ t with |X| ≤ 3/4 · |H|}`, where `H = Hs` is the
  hypothesis set of the current call and the blocks `X` are those of the restricted test `t(H)`.
  `ξ(T)` is the indexed family `xi T Hs : Fin m → Finset H`, with the order `⪯` of the tests
  (`⪯_ξ`). Its universe `U_ξ = ⋃_t ξ(t)` is `coverUniverse (xi T Hs)`.
* One call of Algorithm 1 on `H = Hs` obtains a cover `C` from FindCover on
  `(U_ξ, ξ(T), ⪯_ξ, f = 1/4)`, orders it topologically as a list `L`, and performs the tests of
  `L` in order. `D_C` is the path obtained by following replies that do not reach the recursion
  threshold `|H'| ≤ (5β−1)/(5β) · |H|`; it ends with the first test for which every reply reaches
  the threshold. `callPathCost T Hs β Hs L = cost_W(D_C)`, its number of test nodes.
-/

namespace PrecDTree.Main

variable {m : ℕ} {H : Type} [DecidableEq H]

/-- `ξ(t)`: the hypotheses of `Hs` lying in a reply block of `t(Hs)` of size at most
`3/4 · |Hs|` (written `4 · |X| ≤ 3 · |Hs|`). -/
def xi (T : Fin m → H → ℕ) (Hs : Finset H) (t : Fin m) : Finset H :=
  Hs.filter (fun h => 4 * (block T Hs t (T t h)).card ≤ 3 * Hs.card)

/-- `U_ξ = ⋃_{t ∈ T} ξ(t)`. -/
def Uxi (T : Fin m → H → ℕ) (Hs : Finset H) : Finset H := coverUniverse (xi T Hs)

open Classical in
/-- Number of test nodes of the path `D_C` of the current call on `Hs` (threshold parameter `β`),
when the tests still to be performed are `L` and the hypotheses still on the path are `Hc`: the
test `t` at the head of `L` is performed; if some reply block of `t` on `Hc` has more than
`(5β−1)/(5β) · |Hs|` hypotheses (at most one has, as the threshold exceeds `1/2`), the path follows
it, otherwise `t` is the last node of the path. -/
noncomputable def callPathCost (T : Fin m → H → ℕ) (Hs : Finset H) (β : ℝ) :
    Finset H → List (Fin m) → ℕ
  | _, [] => 0
  | Hc, t :: L =>
      if h : ∃ v : ℕ, (5 * β - 1) / (5 * β) * (Hs.card : ℝ) < ((block T Hc t v).card : ℝ) then
        1 + callPathCost T Hs β (block T Hc t h.choose) L
      else 1

/-- `L` lists the cover `C` in a topological order of `⪯`: without repetition, exactly the
elements of `C`, and precedence-closed as a sequence. -/
def IsTopoOrder (le : Fin m → Fin m → Prop) (C : Finset (Fin m)) (L : List (Fin m)) : Prop :=
  L.Nodup ∧ L.toFinset = C ∧ PrecClosedSeq le L

end PrecDTree.Main


