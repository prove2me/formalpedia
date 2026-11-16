-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_Supplement_Hardness
-- name    : ConstrainedCorrelationRepulsion_Main_Supplement_Hardness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:03:35.042285+00:00
-- url     : https://prove2.me/theorems/0d0de8cd-2f68-4fab-a1eb-5f3c73cc44f9
-- title:
--   Explicit approximation gaps and polynomial NP reductions
-- statement:
--   A gap input comprises a complete signed instance $I$ on $n$ vertices and two natural thresholds $a,b$. Its bit encoding contains a self-delimiting unary $n$, the three full adjacency matrices, then self-delimiting unary $a,b$. For a fixed $q>1$, both sides of the promise require feasibility, $M=\varnothing$, $H=E^-$ and
--
--   $$0<a<b,\qquad qa<b.$$
--
--   A yes-instance has $\operatorname{OPT}(I)\le a$; a no-instance has $b\le\operatorname{OPT}(I)$. These promises are disjoint. Hardness at requested factor $r$ means that some fixed $q>\max\{1,r\}$ has this gap task NP-hard in the published sense: every NP language over every finite nonempty alphabet has a polynomial-time encoding map taking its members to yes-instances and its nonmembers to no-instances. The polynomial time predicate uses the published Cook Turing machines, not an uninterpreted hardness proposition.
--
--   The explicit harder-gap convention allows the source's full range of positive accuracies, including requested factors at or below one, by monotonicity. The thresholds are encoded data, not free real oracles. Restricting hardness witnesses to cluster deletion is the subclass explicitly used in the source and implies hardness of the general constrained task.
--
--   Differences from the source:
--   - encoding: NP-hardness of approximation → polynomial reductions to explicit, strictly separated feasible minimization gaps; reason: this is the monotone approximation-task interpretation, with polynomial-size unary integer thresholds and a fixed intermediate harder factor.
-- source:
--   Yixin Cao, Ying Xu, STOC 2027 submission #869 (October 2026), Theorem 1.2 and §7, printed pp.1, 37 (PDF pp.2, 38)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Supplement_Graphs
import Definitions.Def_OptInapprox_MaxCut_UGC

namespace ConstrainedCorrelationRepulsion.Main.Supplement

open Classical

/-- Explicit minimization-gap input. No computational or hardness claim is an input field. -/
structure GapInput where
  n : ℕ
  input : Instance n
  low : ℕ
  high : ℕ

/-- Self-delimiting unary integers; a polynomial encoding for graph-sized thresholds. -/
def unary (k : ℕ) : List Bool := List.replicate k true ++ [false]

/-- Full matrices, not an abstract graph oracle, in the Cook reduction's output. -/
noncomputable def encodeInstance {n : ℕ} (I : Instance n) : List Bool :=
  unary n ++ (List.finRange n).flatMap fun u => (List.finRange n).flatMap fun v =>
    [decide (I.positive.Adj u v), decide (I.mustLink.Adj u v),
      decide (I.cannotLink.Adj u v)]

noncomputable def encodeGap (X : GapInput) : List Bool :=
  encodeInstance X.input ++ unary X.low ++ unary X.high

/-- Feasible cluster-deletion inputs with positive separated thresholds.
The same well-formedness test is used on both sides of the promise. -/
def GapWellFormed (q : ℝ) (X : GapInput) : Prop :=
  X.input.mustLink = ⊥ ∧ X.input.cannotLink = X.input.positiveᶜ ∧
  FeasibleInput X.input ∧ 0 < X.low ∧ X.low < X.high ∧
  q * (X.low : ℝ) < (X.high : ℝ)

def GapYes (q : ℝ) (X : GapInput) : Prop :=
  GapWellFormed q X ∧ OPT X.input ≤ X.low

def GapNo (q : ℝ) (X : GapInput) : Prop :=
  GapWellFormed q X ∧ X.high ≤ OPT X.input

/-- Monotone approximation-task convention: a strictly harder separated gap proves hardness
at the requested ratio, including ratios at or below one. The actual reductions are quantified
by the published GapNPHard predicate, over every NP language and every finite alphabet. -/
def ApproximationNPHard (ratio : ℝ) : Prop :=
  ∃ q : ℝ, max 1 ratio < q ∧
    OptInapprox.MaxCut.GapNPHard encodeGap (GapYes q) (GapNo q)

end ConstrainedCorrelationRepulsion.Main.Supplement


