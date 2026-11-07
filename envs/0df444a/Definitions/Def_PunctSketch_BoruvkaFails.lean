-- Prove2me | Definitions.Def_PunctSketch_BoruvkaFails
-- name    : PunctSketch_BoruvkaFails
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:45:57.645726+00:00
-- url     : https://prove2.me/theorems/4a42448b-323a-4034-bdfc-ccb8e16025cd
-- title:
--   The failure modes of the Borůvka process, and $R$
-- statement:
--   The process fails on a coin string when (i) at the end two vertices are connected in $G\setminus F$ but not in $T\setminus F$, or (ii) some query at a blob $C$ returned a pair outside $\partial_{-F}C$.
--
--   The number of rounds is $R=10(a+1)g$ with $g=\lceil\log_{4/3}n\rceil$; the printed value is $a=0$.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.1, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_PunctSketch_boruvkaState
import Definitions.Def_PunctSketch_puncturedBoundary

namespace PunctSketch

/-- **The two failure modes of the Borůvka process.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.1, p.17: "(i) It could fail to merge
regions as much as possible and thus end with a vertex partition that is a strict refinement of the
true connected-components partition of G ⧵ F. (ii) It could hallucinate an edge of G ⧵ F at some
point."

Mode (ii) is read at the sampler: some query at a blob `C` returned a pair outside `∂_{−F} C`, the
event bounded by Definition 2.1. -/
def BoruvkaFails {n R : ℕ} {Ω : Type*} (G : SimpleGraph (Fin n))
    (BS : Finset (Fin n) → Ω → Option (Sym2 (Fin n))) (F : Finset (Fin n)) (ω : Fin R → Ω) : Prop :=
  (∃ x y, ConnAvoid G F x y ∧ ¬ ConnAvoid (forestGraph (boruvkaState BS F ω R)) F x y) ∨
    ∃ (r : Fin R) (x : Fin n) (e : Sym2 (Fin n)), x ∉ F ∧
      BS (blob F (boruvkaState BS F ω r) x) (ω r) = some e ∧
      e ∉ puncturedBoundary G F (blob F (boruvkaState BS F ω r) x)

/-- **The number of rounds.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), proof of Lemma 5.2, p.17: `g = ⌈log_{4/3} n⌉`, `R = 10 g`. The
parameter `a` scales it to `R = 10 (a + 1) g`; `a = 0` is the printed value. -/
noncomputable def boruvkaRounds (a n : ℕ) : ℕ := 10 * (a + 1) * ⌈Real.logb (4 / 3) (n : ℝ)⌉₊

end PunctSketch


