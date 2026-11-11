-- Prove2me | Definitions.Def_HarmonicRanking_Main_Instance
-- name    : HarmonicRanking_Main_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:25.406853+00:00
-- url     : https://prove2.me/theorems/de752c35-a417-4380-a2e4-ce7407f38010
-- title:
--   Finite instances, continuous ranks, and score-balanced gains
-- statement:
--   Let $L$ and $R$ be arbitrary finite vertex types, whose disjoint sum is the vertex set. An instance $G=(L,R,w,E)$ supplies nonnegative real potential weights $w_{uv}$ and a fixed realized edge set $E\subseteq L\times R$. A matching uses each endpoint at most once; this condition reuses the published generic multigraph matching definition. Its total weight and the optimum are
--
--   $$
--   w(M)=\sum_{e\in M}w_e,\qquad \operatorname{OPT}(G)=\max_{M\subseteq E\text{ matching}}w(M).
--   $$
--
--   The empty matching is included. A sampled rank belongs to $[0,1)$ with Lebesgue probability; all vertices on both sides receive independent ranks, including the empty product when there are no vertices. A score is positive, nonincreasing, and right-continuous on $[0,1)$. It induces $g_h(x,y)=h(y)/(h(x)+h(y))$ on sampled ranks, with $g_h(t,1)=0$, $g_h(1,t)=1$ for $t<1$, and $g_h(1,1)=1/2$. These shared definitions keep the scan, credits, and continuous analysis on the same model.
--
--   **Formalization Note** Real extensions of a score outside $[0,1)$ do not affect any sampled value. The optimum is a finite maximum in the nonnegative reals, with bottom value 0; it is never an unbounded real supremum.
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), pp. 5, 8, 13, §2.1, Eq. (4), Eq. (8)

import Definitions.Def_CombOpt_MatroidPolytope_Graph_IsMatching

open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace HarmonicRanking.Main

/-- Sampled ranks exclude 1, including for the step score. -/
abbrev Rank := Set.Ico (0 : ℝ) 1

/-- Lebesgue probability on the half-open unit interval. -/
def rankLaw : Measure Rank := Measure.comap Subtype.val volume

abbrev Ranks (L R : Type*) := (L ⊕ R) → Rank

/-- The finite independent product law, including the empty product. -/
def ranksLaw (L R : Type*) [Fintype L] [Fintype R] : Measure (Ranks L R) :=
  Measure.pi (fun _ => rankLaw)

/-- Potential weights are known, while the realized set is fixed and hidden. -/
structure Instance (L R : Type*) where
  weight : L × R → NNReal
  realized : Finset (L × R)

/-- Potential pairs have endpoints in the disjoint sum of the two vertex types. -/
def pairGraph (L R : Type*) : CombOpt.MatroidPolytope.Graph (L ⊕ R) (L × R) where
  ends := fun e => Sym2.mk (Sum.inl e.1) (Sum.inr e.2)

/-- Reuse the published generic graph matching predicate. -/
def IsMatching {L R : Type*} (M : Finset (L × R)) : Prop :=
  (pairGraph L R).IsMatching M

def matchingWeight {L R : Type*} (G : Instance L R) (M : Finset (L × R)) : ℝ :=
  ∑ e ∈ M, (G.weight e : ℝ)

/-- Finite maximum, with bottom 0. The empty matching is always feasible. -/
def OPT {L R : Type*} [Fintype L] [Fintype R] (G : Instance L R) : ℝ := by
  classical
  exact (((G.realized.powerset.filter IsMatching).sup
    (fun M => ∑ e ∈ M, G.weight e) : NNReal) : ℝ)

/-- Values outside [0,1) are irrelevant to this predicate. -/
def IsScore (h : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Ico (0 : ℝ) 1, 0 < h x) ∧
  AntitoneOn h (Set.Ico 0 1) ∧
  ∀ x ∈ Set.Ico (0 : ℝ) 1, ContinuousWithinAt h (Set.Ico x 1) x

/-- Analytical extension, equation (8); these boundary inputs are never sampled. -/
def gain (h : ℝ → ℝ) (x y : ℝ) : ℝ :=
  if x = 1 then (if y = 1 then 1 / 2 else 1)
  else if y = 1 then 0 else h y / (h x + h y)

end HarmonicRanking.Main


