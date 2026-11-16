-- Prove2me | Definitions.Def_MaxCompForest_Supplement_cube
-- name    : MaxCompForest_Supplement_cube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:14:05.755006+00:00
-- url     : https://prove2.me/theorems/bfc9b0c5-21dc-432f-80d2-a10bab48a209
-- title:
--   Unit-conductance $h$-cube $Q_h$
-- statement:
--   The **unit-conductance $h$-cube** $Q_h$ has vertex set $\{-1,1\}^h$, an edge between two points that differ in exactly one coordinate, and every conductance equal to $1$. It has $n=2^h$ vertices, is $h$-regular ($D=hI$), and is the extremal example of the logarithmic penalty of independent averaging (Theorem K.2) and of the cube estimate (Lemma 2.9).
--
--   **Formalization Note** Vertices are `Fin h → Bool`; the edge labelled $(x,i)$ with $x_i=\mathrm{false}$ joins $x$ to $x$ with coordinate $i$ set to true, so every edge has exactly one label.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 2.9, p.12 (PDF p.14); Theorem K.2, p.62 (PDF p.64)

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
open EffResSparsify.ResistanceSketch
set_option autoImplicit false

namespace MaxCompForest.Supplement

/-- **The unit-conductance `h`-cube** `Q_h`: vertices `{−1, 1}^h` (here `Fin h → Bool`), an edge between two points
that differ in exactly one coordinate, every conductance `1`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Lemma 2.9 p.12, Theorem K.2 p.62.

**Formalization Note.** The edge labelled `(x, i)` with `x i = false` joins `x` to `x` with coordinate `i` set to
`true`, so each of the `h 2^{h−1}` edges carries exactly one label. -/
def cube (h : ℕ) : WGraph (Fin h → Bool) {p : (Fin h → Bool) × Fin h // p.1 p.2 = false} where
  head p := p.1.1
  tail p := Function.update p.1.1 p.1.2 true
  w _ := 1
  head_ne_tail p := by
    intro hp
    have h1 := congrFun hp p.1.2
    simp [p.2] at h1
  w_pos _ := one_pos

end MaxCompForest.Supplement


