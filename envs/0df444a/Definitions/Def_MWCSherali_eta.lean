-- Prove2me | Definitions.Def_MWCSherali_eta
-- name    : MWCSherali_eta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:51.425226+00:00
-- url     : https://prove2.me/theorems/1108de97-8bee-4033-b9f8-2a82b3cea775
-- title:
--   The tube-to-centre measure $\eta_{ab}$
-- statement:
--   With the tube coordinates $t_{ab}(w,u,v)=we_a+(1-w-u-v)e_b+ue_i+ve_j$, $\{i,j\}=[4]\setminus\{a,b\}$, $i<j$,
--
--   $$\int\varphi\,d\eta_{ab}=C\int_{1-\alpha-\beta}^{\alpha}\int_0^\beta\varphi\big(t_{ab}(w,u,\beta-u)\big)\,du\,dw,\tag{13}$$
--
--   the flow passing from the tube $T_{ab}$ into the central region through the face $t_i+t_j=\beta$.
--
--   **Formalization Note** Swapping $i$ and $j$ replaces $u$ by $\beta-u$ and gives the same measure.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), (12)–(13), p.35

import Mathlib
import Definitions.Def_MWCSherali_otherPair

namespace MWCSherali

open MeasureTheory

/-- **The tube-to-centre measure `η_{ab}`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), (12)–(13), p.35: with
`t_{ab}(w, u, v) = w e_a + (1 − w − u − v) e_b + u e_i + v e_j`,
"`∫ φ dη_{ab} = C ∫_{1−α−β}^{α} ∫_0^β φ(t_{ab}(w, u, β − u)) du dw`".

`eta α β C a b` is `C` times the image of Lebesgue measure on `[1 − α − β, α] × [0, β]` under
`(w, u) ↦ t_{ab}(w, u, β − u) = w e_a + (1 − w − β) e_b + u e_i + (β − u) e_j`.

**Formalization Note.** `(i, j) = otherPair a b` (increasing order); swapping `i` and `j`
replaces `u` by `β − u` and gives the same measure. -/
noncomputable def eta (α β C : ℝ) (a b : Fin 4) : Measure (Fin 4 → ℝ) :=
  ENNReal.ofReal C • Measure.map
    (fun p : ℝ × ℝ => p.1 • Pi.single a 1 + (1 - p.1 - β) • Pi.single b 1 +
      p.2 • Pi.single (otherPair a b).1 1 + (β - p.2) • Pi.single (otherPair a b).2 1)
    (volume.restrict (Set.Icc (1 - α - β) α ×ˢ Set.Icc 0 β))

end MWCSherali


