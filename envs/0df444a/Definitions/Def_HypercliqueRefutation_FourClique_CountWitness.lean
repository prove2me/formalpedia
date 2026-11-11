-- Prove2me | Definitions.Def_HypercliqueRefutation_FourClique_CountWitness
-- name    : HypercliqueRefutation_FourClique_CountWitness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:21.882741+00:00
-- url     : https://prove2.me/theorems/670809ec-cfa8-4e64-8297-edfd812c1535
-- title:
--   Four-hyperclique input, exact count and witness output
-- statement:
--   Let G be a 3-uniform hypergraph on the labels 0 through n−1. Its four-cliques are exactly its four-element vertex subsets whose every three-element subset is an edge. Write
--
--   $$N(G)=\#\{U\subseteq[n]: |U|=4,\ \forall T\subseteq U,\ |T|=3\Rightarrow T\in E(G)\}.$$
--
--   The input is the n³-cell symmetric Boolean indicator of ordered triples; repeated labels give zero. The published machine prepends n. The output consists of an exact count N(G), a 0/1 tag, and four labels. Tag 1 requires N(G)>0, four distinct in-range labels and their clique property. Tag 0 requires N(G)=0 and zeros in the four unused label cells. Acceptance agrees with positivity of N(G). No answer or precomputed auxiliary data is included in the input. This gives zero/none on all instances with fewer than four vertices.
--
--   This specification defines the actual counting-and-finding problem for the runtime theorem. It supplies no program and assumes no runtime guarantee. Zeroing unused witness cells is a canonical output encoding.
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, The 3-Uniform Hyperclique Hypothesis is False, STOC 2027 submission #1431 (October 2026), held source.pdf SHA-256 fda90f18867fd07883366a1bc49a8afa652b8712f71402e11ccd45e6633b127a; Sections 1 and 2.1, pp.1,3, and Theorem 2.8, p.6; explicit count/witness reading of Section 2.1.

import Mathlib
import Definitions.Def_HypercliqueFalse_IsHyperclique
import Definitions.Def_HypercliqueFalse_edgeIndicator
import Definitions.Def_TrulySubcubicAPSP_WordRAM

set_option autoImplicit false

namespace HypercliqueRefutation.FourClique

/- Chan--Itakura--Ma--Yu, STOC 2027 submission #1431 (October 2026),
   Sections 1 and 2.1, pp.1,3; Theorem 2.8, p.6.
   This is an output specification, with no algorithm or running-time assumption. -/

def fourCliques {n : ℕ} (G : HypercliqueFalse.Hypergraph n 3) :
    Finset (Finset (Fin n)) := by
  letI : DecidablePred (HypercliqueFalse.IsHyperclique G 4) := fun s => by
    unfold HypercliqueFalse.IsHyperclique
    infer_instance
  exact Finset.univ.filter (HypercliqueFalse.IsHyperclique G 4)

def cliqueCount {n : ℕ} (G : HypercliqueFalse.Hypergraph n 3) : ℕ :=
  (fourCliques G).card

def denseInput {n : ℕ} (G : HypercliqueFalse.Hypergraph n 3) : List ℤ :=
  (List.ofFn fun a : Fin n =>
    (List.ofFn fun b : Fin n =>
      List.ofFn fun c : Fin n => HypercliqueFalse.edgeIndicator G ![a, b, c]).flatten).flatten

/-- Six observed cells: exact count, a 0/1 witness tag, then four vertex labels.
    In the absence case the four unused label cells are required to be zero. -/
def CountWitnessOutput {n : ℕ} (G : HypercliqueFalse.Hypergraph n 3)
    (out : ℕ → ℤ) : Prop :=
  out 0 = (cliqueCount G : ℤ) ∧
    ((cliqueCount G = 0 ∧ out 1 = 0 ∧ ∀ j : Fin 4, out (2 + j.val) = 0) ∨
     (0 < cliqueCount G ∧ out 1 = 1 ∧
       ∃ v : Fin 4 → Fin n, Function.Injective v ∧
         (∀ j : Fin 4, out (2 + j.val) = (v j).val) ∧
         HypercliqueFalse.IsHyperclique G 4 (Finset.univ.image v)))

/-- The published machine places n in cell 0, then precisely n^3 Boolean entries.
    No certificate or precomputed coefficient is supplied in the input. -/
def countWitnessProblem : TrulySubcubicAPSP.Problem where
  Instance n := HypercliqueFalse.Hypergraph n 3
  input := denseInput
  yes G := 0 < cliqueCount G
  output := CountWitnessOutput

end HypercliqueRefutation.FourClique


