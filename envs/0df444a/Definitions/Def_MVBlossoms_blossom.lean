-- Prove2me | Definitions.Def_MVBlossoms_blossom
-- name    : MVBlossoms_blossom
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:44:28.552819+00:00
-- url     : https://prove2.me/theorems/0a57feaf-aa3b-4f6e-b3b4-8056f5877f45
-- title:
--   The blossom $B_{b,t}$
-- statement:
--   The **blossom of tenacity $t$ and base $b$** is defined by recursion on $t$:
--
--   $$
--   B_{b,t}=\begin{cases}\emptyset & t<t_m,\\ T_{b,t}\ \cup \displaystyle\bigcup_{w\in T_{b,t}\cup\{b\}} B_{w,t-2} & t\ge t_m.\end{cases}
--   $$
--
--   At $t=t_m$ this is $B_{b,t_m}=T_{b,t_m}$ (Definition 22), and for $t>t_m$ it is Definition 31: the vertices of tenacity $t$ with base $b$, together with the blossoms of tenacity $t-2$ whose bases are $b$ or such vertices. If $T_{b,t}=\emptyset$ then $B_{b,t}=B_{b,t-2}$.
--
--   **Formalization Note** Definition 31 restricts the union to basal $w$; a non-basal $w$ has $B_{w,t-2}=\emptyset$, so the restriction is dropped. "The blossoms of tenacity $t$" are the sets $B_{b,t}$ for $b$ basal at stage $t$ with $\mathrm{tenacity}(b)>t$ (`IsBlossomBase`).
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definitions 22 and 31, pp.2031, 2037

import Mathlib
import Definitions.Def_MVBlossoms_tm
import Definitions.Def_MVBlossoms_Tset

namespace MVBlossoms

/-- **The blossom `B_{b,t}`.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 22 (p.2031): "the blossom of tenacity
tm and base b is the set B_{b,tm} = {v ∈ Um | base(v) = b}", and Definition 31 (p.2037):
"B_{b,t} = T_{b,t} ∪ ( ⋃_{v ∈ (T_{b,t} ∪ {b}), v is basal} B_{v,t−2} )."

`blossom M b s` is the recursion
`B(b, s) = ∅` if `s < t_m`, and otherwise `B(b, s) = T_{b,s} ∪ ⋃_{w ∈ T_{b,s} ∪ {b}} B(w, s − 2)`
(with `B(w, s − 2) = ∅` when `s < 2`).

**Formalization Note.** One recursion serves Definitions 22 and 31: at `s = t_m` the union is
empty, giving `T_{b,t_m}` (Definition 22). The qualifier "v is basal" is dropped: for a non-basal
`w` every `T_{w,s'}` with `s' ≤ s − 2` is empty, so `B(w, s − 2) = ∅` and the union is
unchanged. It also gives `B_{b,t} = B_{b,t−2}` when `T_{b,t} = ∅`, as the paper notes. The
function is defined for every `b` and `s`; "the blossom of tenacity t with base b" is
`blossom M b t` for `b` with `IsBlossomBase M b t`. -/
noncomputable def blossom {V : Type} [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph) :
    V → ℕ → Set V
  | b, 0 => if ((0 : ℕ) : ℕ∞) < tm M then ∅ else Tset M b 0
  | b, 1 => if ((1 : ℕ) : ℕ∞) < tm M then ∅ else Tset M b 1
  | b, s + 2 => if ((s + 2 : ℕ) : ℕ∞) < tm M then ∅ else
      Tset M b (s + 2) ∪ ⋃ w ∈ Tset M b (s + 2) ∪ {b}, blossom M w s

end MVBlossoms


