-- Prove2me | Definitions.Def_LowDiameterNashWilliams_Main_Supplement_Tail
-- name    : LowDiameterNashWilliams_Main_Supplement_Tail
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:34:01.833357+00:00
-- url     : https://prove2.me/theorems/8604cd7f-5ef3-4f71-bbc3-c76509822eb2
-- title:
--   Exact tail blocks and attachment at a prescribed root
-- statement:
--   For $k$ tree indices, length $\ell$, and $d$ dummy vertices, the tail has terminals $0,\ldots,\ell$, two vertices $a_{j,i},b_{j,i}$ for every block and index, and the $d$ dummies only in the first block. In block $j$ its nonterminals form a clique, and its terminal edges are exactly $\alpha_ja_{j,i}$ and $\beta_jb_{j,i}$. Consecutive terminals are identified. Thus the tail order is
--   $$|V(H)|=\ell+1+2k\ell+d.$$
--   The first and last terminals are $s=0$ and $t=\ell$. The extension of a finite rooted graph $(F,r)$ identifies only $s$ with $r$ and includes precisely the old edges and tail edges. Every remaining label is distinct, and no additional edge crosses between the two graphs. Its order is $|V(F)|+(2k+1)\ell+d$.
--
--   These are finite constructions of the graphs preceding Claims 5.1–5.2, independent of tree existence or diameter conclusions. Arbitrary dummy counts are retained before the final padding choice in the proof of Theorem 5.
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Section 7.1, Theorem 5 construction before Claims 5.1–5.2, pp. 27–28 (PDF pp. 28–29)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_GraphEncoding

set_option autoImplicit false
open scoped ENNReal NNReal
open Classical

namespace LowDiameterNashWilliams.Main.Supplement

/-- Tail vertices: ell+1 terminals, 2k vertices per block, then dummies in the first block only. -/
def tailOrder (k ell d : ℕ) : ℕ := ell + 1 + 2 * k * ell + d

def tailA (k ell j i : ℕ) : ℕ := ell + 1 + 2 * k * j + 2 * i
def tailB (k ell j i : ℕ) : ℕ := tailA k ell j i + 1

def inBlock (k ell d j v : ℕ) : Prop :=
  (ell + 1 + 2 * k * j ≤ v ∧ v < ell + 1 + 2 * k * (j + 1)) ∨
  (j = 0 ∧ ell + 1 + 2 * k * ell ≤ v ∧ v < tailOrder k ell d)

/-- Clique interiors and exactly alpha-a_i / beta-b_i terminal edges. Symmetrized by graphFromRel. -/
def tailRel (k ell d u v : ℕ) : Prop :=
  (∃ j : Fin ell, inBlock k ell d j.val u ∧ inBlock k ell d j.val v) ∨
  (∃ j : Fin ell, ∃ i : Fin k, u = j.val ∧ v = tailA k ell j.val i.val) ∨
  (∃ j : Fin ell, ∃ i : Fin k, u = j.val + 1 ∧ v = tailB k ell j.val i.val)

noncomputable def tailGraph (k ell d : ℕ) : GraphInput :=
  graphFromRel (tailOrder k ell d) (tailRel k ell d)

def tailStart (k ell d : ℕ) : Fin (tailGraph k ell d).n :=
  ⟨0, by change 0 < tailOrder k ell d; unfold tailOrder; omega⟩

def tailEnd (k ell d : ℕ) : Fin (tailGraph k ell d).n :=
  ⟨ell, by change ell < tailOrder k ell d; unfold tailOrder; omega⟩

def gluedVertex (N r v : ℕ) : ℕ := if v = 0 then r else N + (v - 1)

/-- F and the tail meet at precisely r=s. All other labels and all cross edges are explicit. -/
noncomputable def tailExtension (F : GraphInput) (r : Fin F.n) (k ell d : ℕ) : GraphInput :=
  graphFromRel (F.n + ell + 2 * k * ell + d) fun x y =>
    (∃ e : Fin F.m, x = (F.uv e).1.val ∧ y = (F.uv e).2.val) ∨
    (∃ u v : Fin (tailOrder k ell d), tailRel k ell d u.val v.val ∧
      x = gluedVertex F.n r.val u.val ∧ y = gluedVertex F.n r.val v.val)

end LowDiameterNashWilliams.Main.Supplement


