-- Prove2me | Definitions.Def_N25_CanonicalChartPresentations
-- name    : N25_CanonicalChartPresentations
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:06.281394+00:00
-- url     : https://prove2.me/theorems/fb6a2783-9650-4a0b-8c91-c456293d80b4
-- title:
--   Jacobian presentations indexed by non-pivot column pairs
-- statement:
--   For a chart pivot $i$, the file defines the increasing pairs $j<k$ among the other three coordinates and the ordered column map $(j,k,i)$. It packages the four-variable relations $(Q,C,x_i-1)$ as a pre-submersive presentation whose Jacobian element is the selected minor in columns $j,k$. This lets the span of explicit minors certify local standard smoothness of every chart.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CuspPresentations
/-! Presentations selecting two non-pivot columns and the pivot column. -/
noncomputable section
namespace N25

/-- Increasing pairs among the three columns other than the chart pivot. -/
abbrev CanonicalChartColumnPair25 (pivot : Fin 4) :=
  {jk : Fin 4 × Fin 4 // jk.1 ≠ pivot ∧ jk.2 ≠ pivot ∧ jk.1 < jk.2}

/-- The two chosen columns followed by the pivot column. -/
def canonicalChartPairColumns25 (pivot : Fin 4) (pair : CanonicalChartColumnPair25 pivot) :
    Fin 3 → Fin 4 :=
  ![pair.val.1, pair.val.2, pivot]

theorem canonicalChartPairColumns25_injective (pivot : Fin 4) (pair : CanonicalChartColumnPair25 pivot) :
    Function.Injective (canonicalChartPairColumns25 pivot pair) := by
  rcases pair with ⟨⟨j, k⟩, hj, hk, hjk⟩
  dsimp only at hj hk hjk
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    simp_all [canonicalChartPairColumns25, ne_of_lt hjk, ne_of_gt hjk, Ne.symm hj, Ne.symm hk]

private theorem chartRelationIdeal_eq (K : Type*) [CommRing K] (pivot : Fin 4) :
    Ideal.span (Set.range (canonicalChartRelations25 K pivot)) = canonicalChartIdeal25 K pivot := by
  unfold canonicalChartIdeal25
  congr 1
  ext f
  simp [canonicalChartRelations25]
  tauto

/-- The actual four-variable, three-relation presentation with columns
j,k,pivot, whose Jacobian is the chosen two-column minor. -/
def canonicalChartPairPresentation25 (K : Type*) [CommRing K]
    (pivot : Fin 4) (pair : CanonicalChartColumnPair25 pivot) :
    Algebra.PreSubmersivePresentation K (CanonicalChartRing25 K pivot) (Fin 4) (Fin 3) :=
  (Algebra.PreSubmersivePresentation.naive (v := canonicalChartRelations25 K pivot)
    (canonicalChartPairColumns25 pivot pair) (canonicalChartPairColumns25_injective pivot pair)).ofAlgEquiv
      (Ideal.quotientEquivAlgOfEq K (chartRelationIdeal_eq K pivot))

end N25


