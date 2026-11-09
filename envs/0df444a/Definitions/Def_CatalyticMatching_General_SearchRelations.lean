-- Prove2me | Definitions.Def_CatalyticMatching_General_SearchRelations
-- name    : CatalyticMatching_General_SearchRelations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:46.294092+00:00
-- url     : https://prove2.me/theorems/7a41c514-7ae1-4432-8670-36051f92c91e
-- title:
--   Explicit domains and output relations for the five catalytic tasks
-- statement:
--   The graph domain consists of every binary encoding of a finite simple graph; the perfect-graph domain adds exactly existence of a perfect matching. The rank-test domain consists of the graph followed by an arbitrary rational Tutte evaluation. These domains are defined independently of output correctness.
--
--   $$R_{\max}(\operatorname{enc}G,\operatorname{enc}M)\iff M\text{ is a matching and }|M|=\nu(G).$$
--
--   The other relations output respectively the exact binary integer $\nu(G)$, a whole rational evaluation attaining generic rank, a perfect matching, or the truth bit of the conjunction of generic rank and full deficiency equality. Relations specify mathematical answers, with no cost certificates. The computational theorems must produce machines realizing them under all resource and restoration requirements.
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Definitions 2.1–2.3 p.10; Lemma 3.4 p.12; Theorem 3.8 p.13; Corollary 3.8.2 p.16; Lemma 3.11 p.20; Theorem 3.12 p.22

import Definitions.Def_CatalyticMatching_General_Tutte
import Definitions.Def_CatalyticMatching_General_CatalyticSpace

namespace CatalyticMatching.General

/-- Explicit input domain, independent of existence of the desired output. -/
def graphDomain (x : Bits) : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)), x = graphBits G

def perfectGraphDomain (x : Bits) : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)), x = graphBits G ∧
    ∃ M : Finset G.edgeSet, MulmuleyVV.Matching.IsPerfectMatchingEdges G M

noncomputable def rankTestDomain (x : Bits) : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (a : G.edgeSet → ℚ),
    x = graphBits G ++ matrixBits (tutteEval G a)

/-- Actual maximum-matching construction, no promise of perfectness. -/
def maximumMatchingRelation (x y : Bits) : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (M : Finset G.edgeSet),
    x = graphBits G ∧ y = matchingBits M ∧ IsMatching M ∧ M.card = matchingNumber G

/-- Single-valued output, hence independent of the catalyst. -/
def matchingSizeRelation (x y : Bits) : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    x = graphBits G ∧ y = natBits (matchingNumber G)

/-- Domain is exactly the graphs admitting a perfect matching. -/
def perfectMatchingRelation (x y : Bits) : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (M : Finset G.edgeSet),
    x = graphBits G ∧ y = matchingBits M ∧ MulmuleyVV.Matching.IsPerfectMatchingEdges G M

/-- One consistent rational assignment is output; not a rank oracle. -/
def maximumRankRelation (x y : Bits) : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (a : G.edgeSet → ℚ),
    x = graphBits G ∧ y = matrixBits (tutteEval G a) ∧
      (tutteEval G a).rank = (genericTutte G).rank

/-- Graph plus the entire rational evaluation; total input length charges its entries. -/
noncomputable def rankTestRelation (x y : Bits) : Prop := by
  classical
  exact ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (a : G.edgeSet → ℚ),
    x = graphBits G ++ matrixBits (tutteEval G a) ∧
      y = [decide ((genericTutte G).rank = (tutteEval G a).rank ∧
        deficiency (genericTutte G) = deficiency (tutteEval G a))]

end CatalyticMatching.General


