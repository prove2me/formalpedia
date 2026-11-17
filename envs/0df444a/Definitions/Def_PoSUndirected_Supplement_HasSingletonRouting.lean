-- Prove2me | Definitions.Def_PoSUndirected_Supplement_HasSingletonRouting
-- name    : PoSUndirected_Supplement_HasSingletonRouting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:32:18.664517+00:00
-- url     : https://prove2.me/theorems/49955f93-8798-434e-b66a-76e5be6639ad
-- title:
--   Repeated-demand classes, abstract singleton routing and the nonbridge native-load cap
-- statement:
--   Players are partitioned by equality of their unordered terminal pairs. A singleton class has one player. Every class of size at least two contributes one labelled abstract edge to $D_{\mathrm{rep}}$; the least player label is used only as a canonical representative.
--
--   `HasSingletonRouting` says that every singleton terminal pair has a path in $D_{\mathrm{rep}}$ and those abstract paths are pairwise edge-disjoint. It imposes no disjointness on the corresponding physical host paths. `HasCappedOptimumForest` says that one socially optimal forest profile has native load at most eight on each of its edges that is not a bridge of the full physical host; host bridges are deliberately left uncapped.
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), §5.1 and Theorem 5.3, p.12 (PDF p.14); Appendix E, pp.63–64 (PDF pp.65–66)

import Mathlib
import Definitions.Def_PoSUndirected_Supplement_IsSocialOptimum

open CongestionPoA.AsymSum

set_option autoImplicit false

namespace PoSUndirected.Supplement

variable {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-!
# Repeated-demand classes and the hypotheses of Theorem 5.3

Tsoufis, preprint sha256 c095d811…, §5.1, p.12 (PDF p.14).  Representatives are chosen by
the fixed label order only to make the quotient by equal unordered terminal pairs into a finite
edge type; the routing property is invariant under this choice.
-/

/-- Two independently labelled players belong to the same repeated-demand class exactly when their
unordered terminal pairs agree. -/
def SameDemand (s t : ι → V) (i j : ι) : Prop :=
  s(s i, t i) = s(s j, t j)

/-- A player is a singleton class. -/
def IsSingletonDemand (s t : ι → V) (i : ι) : Prop :=
  ∀ j : ι, SameDemand s t i j → j = i

/-- The least-labelled member of a maximal demand class of size at least two. -/
def IsRepeatedRepresentative (s t : ι → V) (i : ι) : Prop :=
  (∀ j : ι, SameDemand s t i j → i ≤ j) ∧ ∃ j : ι, j ≠ i ∧ SameDemand s t i j

abbrev RepeatedRepresentative (s t : ι → V) := {i : ι // IsRepeatedRepresentative s t i}

/-- Endpoint pair of the abstract edge of `D_rep` represented by `a`. -/
def repeatedEnds (s t : ι → V) (a : RepeatedRepresentative s t) : Sym2 V :=
  s(s a.1, t a.1)

/-- The singleton terminal pairs can be joined by pairwise edge-disjoint paths in `D_rep`.
The disjointness is among abstract repeated-class edges, not physical host edges. -/
def HasSingletonRouting (s t : ι → V) : Prop :=
  ∃ route : (i : {j : ι // IsSingletonDemand s t j}) →
      Finset (RepeatedRepresentative s t),
    (∀ i, IsSimplePathEdges (repeatedEnds s t) (s i.1) (t i.1) (route i)) ∧
    ∀ i j, i ≠ j → Disjoint (route i) (route j)

/-- One stated optimum forest has native load at most eight on precisely those forest edges that are
not bridges of the full physical host.  Bridge loads are deliberately unrestricted. -/
def HasCappedOptimumForest (ends : E → Sym2 V) (c : E → ℝ) (s t : ι → V) : Prop :=
  ∃ (F : Finset E) (O : ι → Finset E),
    IsForestProfile ends s t F O ∧
    IsSocialOptimum (ndGame ends c s t) c O ∧
    ∀ e ∈ F, ¬ IsHostBridge ends e → load O e ≤ 8

end PoSUndirected.Supplement


