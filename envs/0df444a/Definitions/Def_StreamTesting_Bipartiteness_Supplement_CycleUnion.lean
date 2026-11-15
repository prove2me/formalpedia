-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_CycleUnion
-- name    : StreamTesting_Bipartiteness_Supplement_CycleUnion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:55:45.802582+00:00
-- url     : https://prove2.me/theorems/4fb9932e-48f5-462a-943c-89eef65ae5df
-- title:
--   Disjoint union of six-cycles
-- statement:
--   For $m\in\mathbb N$, take $m$ disjoint ordinary simple cycles of length six, on labels $(a,b)\in[m]\times[6]$:
--
--   $$ (a,b)\sim(a',b')\quad\Longleftrightarrow\quad a=a'\ \text{and }b,b'\text{ are adjacent around }C_6.$$
--
--   There are no edges between different copies. The cycle graph is Mathlib's ordinary cycle, and graph isomorphisms will cover every labeling of this union.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; §3.2–3.3 and Theorem 11, printed/PDF pp.15–16.

import Mathlib

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

def sixCycleUnion (m : ℕ) : SimpleGraph (Fin m × Fin 6) where
  Adj u v := u.1 = v.1 ∧ (SimpleGraph.cycleGraph 6).Adj u.2 v.2
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro u h; exact (SimpleGraph.cycleGraph 6).loopless.irrefl u.2 h.2⟩

end StreamTesting.Bipartiteness.Supplement


