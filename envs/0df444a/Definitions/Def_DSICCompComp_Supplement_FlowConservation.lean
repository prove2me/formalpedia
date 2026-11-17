-- Prove2me | Definitions.Def_DSICCompComp_Supplement_FlowConservation
-- name    : DSICCompComp_Supplement_FlowConservation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:28:15.425032+00:00
-- url     : https://prove2.me/theorems/1b8b1a8f-bbd5-41b4-a7d4-77296a218885
-- title:
--   Flow conservation of a dual solution $\lambda$ (Definition C.1)
-- statement:
--   A dual solution assigns a multiplier $\lambda^{v_{-i}}_i(v_i, v'_i)$ to each DSIC constraint: bidder $i$, profile $v_{-i}$ of the others, value $v_i \in \mathrm{supp}(D_i)$ and report $v'_i \in \mathrm{supp}(D_i) \cup \{\varnothing\}$. It satisfies **flow conservation** if for all bidders $i$, profiles $v_{-i}$ and values $v_i \in \mathrm{supp}(D_i)$,
--
--   $$
--   \sum_{v'_i \in \mathrm{supp}(D_i) \cup \{\varnothing\}} \lambda^{v_{-i}}_i(v_i, v'_i) \;=\; f(v) + \sum_{v'_i \in \mathrm{supp}(D_i)} \lambda^{v_{-i}}_i(v'_i, v_i).
--   $$
--
--   Equivalently, for each $i$ and $v_{-i}$, the network with a source $s$, a sink $\varnothing$ and one node per $v_i \in \mathrm{supp}(D_i)$, with flow $f(v_i, v_{-i})$ on the edge $s \to v_i$ and flow $\lambda^{v_{-i}}_i(v_i, v'_i)$ on the edge $v_i \to v'_i$, conserves flow at every node other than $s$ and $\varnothing$.
--
--   **Formalization Note** A dual solution is a function `lam i v w` of a bidder $i$, a full profile $v \in \mathrm{supp}(D)$ (which carries both $v_{-i}$ and $v_i$) and a report $w \in \mathrm{supp}(D_i) \cup \{\varnothing\}$, with `lam i v w` $= \lambda^{v_{-i}}_i(v_i, w)$. Thus $\lambda^{v_{-i}}_i(v'_i, v_i)$ is `lam i (Function.update v i v'_i) (some (v i))`.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Definition C.1, pp.35–36 (pdf pp.36–37)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_jointPMF

namespace DSICCompComp

namespace Supplement

/-- Flow conservation of a dual solution `λ` (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Definition C.1, pp.35–36 (pdf pp.36–37)): for all bidders `i`, profiles `v_{-i}` of the other bidders
and values `v_i ∈ supp(D_i)`,
`∑_{v'_i ∈ supp(D_i) ∪ {∅}} λ^{v_{-i}}_i(v_i, v'_i) = f(v) + ∑_{v'_i ∈ supp(D_i)} λ^{v_{-i}}_i(v'_i, v_i)`.

**Formalization Note** A dual solution is `lam : (i : Fin n) → ((k : Fin n) → S k) → Option (S i) → ℝ`
with `lam i v w = λ^{v_{-i}}_i(v_i, w)`: one multiplier for each bidder `i`, profile `v ∈ supp(D)`
(which carries both `v_{-i}` and `v_i`) and report `w ∈ supp(D_i) ∪ {∅}` (`none` = `∅`). So
`λ^{v_{-i}}_i(v'_i, v_i) = lam i (Function.update v i v'_i) (some (v i))`. -/
def FlowConservation {n m : ℕ} (E : FiniteSetting n m)
    (lam : (i : Fin n) → ((k : Fin n) → E.S k) → Option (E.S i) → ℝ) : Prop :=
  ∀ (i : Fin n) (v : (k : Fin n) → E.S k),
    ∑ w : Option (E.S i), lam i v w =
      jointPMF E v + ∑ u : E.S i, lam i (Function.update v i u) (some (v i))

end Supplement

end DSICCompComp


