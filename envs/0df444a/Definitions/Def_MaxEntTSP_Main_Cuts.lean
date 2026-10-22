-- Prove2me | Definitions.Def_MaxEntTSP_Main_Cuts
-- name    : MaxEntTSP_Main_Cuts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:11.868855+00:00
-- url     : https://prove2.me/theorems/5f309a73-8189-46c9-9193-f876ede10540
-- title:
--   Rooted cuts, tour support, and payment constant
-- statement:
--   For a set of vertices $S$, the cut weight is $w(\delta(S))=\sum_{a\in S}\sum_{b\notin S}w_{ab}$: each undirected crossing edge is counted once. The edge-set version $\delta(S)_T$ counts the crossing edges of a tree $T$.
--
--   An $\eta$-near minimum cut is a nonempty $S$ with $u_0,v_0\notin S$ and $w(\delta(S))\le2+\eta$. For an optimal tour with incidence vector $\chi_{E^*}$, set $z=(x+\chi_{E^*})/2$. The payment constant is $\varepsilon_P=3.12\cdot10^{-16}$.
--
--   These shared definitions fix the cut and edge-count conventions used by Theorem 3.1.
-- source:
--   Karlin, Klein & Oveis Gharan, A (Slightly) Improved Approximation Algorithm for Metric TSP, arXiv:2007.01409v6, p. 5 (PDF 7), §2.1; p. 18 (PDF 20), Theorem 3.1

import Mathlib
import Definitions.Def_MaxEntTSP_Main_Model
import Definitions.Def_MetricTSP_tour_vector

namespace MaxEntTSP.Main

open MetricTSP Finset

/-- The paper's once-counted weight of a cut. -/
def cutW {m : ℕ} (w : Fin m → Fin m → ℝ) (S : Finset (Fin m)) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ Sᶜ, w a b

def edgeCrosses {m : ℕ} (S : Finset (Fin m)) (e : Sym2 (Fin m)) : Prop :=
  ∃ a b, e = s(a, b) ∧ ((a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S))

def edgeInside {m : ℕ} (S : Finset (Fin m)) (e : Sym2 (Fin m)) : Prop :=
  ∃ a b, e = s(a, b) ∧ a ∈ S ∧ b ∈ S

noncomputable def cutEdges {m : ℕ} (F : Finset (Sym2 (Fin m))) (S : Finset (Fin m)) :
    Finset (Sym2 (Fin m)) := by
  classical
  exact F.filter (edgeCrosses S)

noncomputable def edgeMass {m : ℕ} (w : Fin m → Fin m → ℝ) (F : Finset (Sym2 (Fin m))) : ℝ :=
  ∑ e ∈ F, pairCost w e

noncomputable def internalEdges {m : ℕ} (F : Finset (Sym2 (Fin m)))
    (S : Finset (Fin m)) : Finset (Sym2 (Fin m)) := by
  classical
  exact F.filter (edgeInside S)

noncomputable def crossCount {m : ℕ} (T : Finset (Sym2 (Fin m))) (S : Finset (Fin m)) : ℕ :=
  (cutEdges T S).card

noncomputable def randomCutSum {m : ℕ} (r : Finset (Sym2 (Fin m)) → Sym2 (Fin m) → ℝ)
    (T F : Finset (Sym2 (Fin m))) (S : Finset (Fin m)) : ℝ :=
  ∑ e ∈ cutEdges F S, r T e

/-- The paper excludes the empty cut and places both endpoints of `e₀` outside it. -/
def IsNearMinCut {m : ℕ} (w : Fin m → Fin m → ℝ) (a b : Fin m)
    (η : ℝ) (S : Finset (Fin m)) : Prop :=
  S.Nonempty ∧ a ∉ S ∧ b ∉ S ∧ cutW w S ≤ 2 + η

/-- The characteristic vector of the tour's edge set. -/
noncomputable def tourSupport {m : ℕ} (π : Equiv.Perm (Fin m)) :
    Finset (Sym2 (Fin m)) :=
  univ.filter (fun e => 0 < pairCost (tourVec π) e)

noncomputable def zVector {m : ℕ} (x : Fin m → Fin m → ℝ) (π : Equiv.Perm (Fin m)) :
    Fin m → Fin m → ℝ :=
  fun a b => (x a b + tourVec π a b) / 2

/-- The absolute payment constant stated in Theorem 3.1. -/
noncomputable def epsP : ℝ := 312 / 10 ^ 18

end MaxEntTSP.Main


