-- Prove2me | Definitions.Def_OptInapprox_Bal2Sat_Supplement_QCut
-- name    : OptInapprox_Bal2Sat_Supplement_QCut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:54:35.246971+00:00
-- url     : https://prove2.me/theorems/45444f8d-5381-40f5-82e1-ad354b4aeb9b
-- title:
--   Definition 13 — encodable MAX-q-CUT inputs and gap hardness
-- statement:
--   A MAX-$q$-CUT input has vertices $\{0,\ldots,n-1\}$ and a finite list of ordered vertex pairs; a pair listed $m$ times has weight $m$, so the list represents a natural-number weight function $W:V\times V\to\mathbb R^+$. For a partition $c:V\to[q]$ into $q$ parts, the cut fraction is the listed weight between different parts divided by the total listed weight, and
--
--   $$\operatorname{optFrac}_q(G)=\max_{c:V\to[q]}\frac{\#\{e\in G:\ c(e_1)\ne c(e_2)\}}{|G|}.$$
--
--   Inputs are encoded in unary over the published two-symbol alphabet. Gap hardness uses the published polynomial-time many-one reductions from every NP language; both promises require at least one listed pair.
--
--   **Formalization Note** Pairs $(v,v)$ are allowed, as in Definition 13, and are never cut. Natural weights by repetition form an encodable subclass of the nonnegative real weights of Definition 13.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 26, Definition 13

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC

namespace OptInapprox.Bal2Sat.Supplement

/-- A MAX-q-CUT input (Definition 13, p. 26): vertices `Fin n` and a list of ordered vertex
pairs; a pair listed `m` times has weight `m` (natural-number weights of `W : V × V → ℝ⁺`).
Pairs `(v, v)` are allowed, as `W` is defined on all of `V × V`; they are never cut. -/
structure QCutInput where
  n : ℕ
  edges : List (Fin n × Fin n)

namespace QCutInput

/-- The fraction of the listed weight between different parts of the partition `c` of the
vertices into the `q` sets `c⁻¹(0), …, c⁻¹(q-1)`. -/
noncomputable def cutFrac {q : ℕ} (G : QCutInput) (c : Fin G.n → Fin q) : ℝ :=
  ((G.edges.countP fun e => decide (c e.1 ≠ c e.2) : ℕ) : ℝ) / (G.edges.length : ℝ)

/-- The optimum fraction: maximum of `cutFrac` over the finitely many partitions. -/
noncomputable def optFrac (q : ℕ) [NeZero q] (G : QCutInput) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun c : Fin G.n → Fin q => G.cutFrac c)

/-- Encoding over the published two-symbol alphabet: `n` and both endpoints of each listed pair
in unary. -/
def enc (G : QCutInput) : List OptInapprox.MaxCut.MCSym :=
  OptInapprox.MaxCut.MCSym.unary G.n ++
    G.edges.flatMap fun e => OptInapprox.MaxCut.MCSym.unary (e.1 : ℕ) ++
      OptInapprox.MaxCut.MCSym.unary (e.2 : ℕ)

end QCutInput

/-- NP-hardness of distinguishing MAX-q-CUT inputs with optimum fraction at least `c` from those
with optimum fraction at most `s` (published gap convention); both promises require an edge. -/
def QCutGapHard (q : ℕ) [NeZero q] (c s : ℝ) : Prop :=
  OptInapprox.MaxCut.GapNPHard QCutInput.enc
    (fun G : QCutInput => G.edges ≠ [] ∧ c ≤ G.optFrac q)
    (fun G : QCutInput => G.edges ≠ [] ∧ G.optFrac q ≤ s)

end OptInapprox.Bal2Sat.Supplement


