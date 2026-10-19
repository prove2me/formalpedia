-- Prove2me | Definitions.Def_QAlgorithms_Defs_ExpanderCodeGraphs
-- name    : QAlgorithms_Defs_ExpanderCodeGraphs
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:25:32.564128+00:00
-- url     : https://prove2.me/theorems/77a26604-aff5-44db-aa54-880934f4a782
-- title:
--   ExpanderCodeGraphs
-- statement:
--   ExpanderCodeGraphs
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ExpanderCodeGraphs.lean

import Definitions.Def_QAlgorithms_Defs_HypergraphProducts
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.ExpanderCodes

/-- Simple positively biregular labelled graph; 1504.00822 p.4.
Positive sizes/degrees are the proof's nondegenerate domain. -/
structure BipartiteData (nA nB : ℕ) where
  right_pos : 0 < nB
  parts_le : nB ≤ nA
  degreeA : ℕ
  degreeB : ℕ
  degreeA_pos : 0 < degreeA
  degreeB_pos : 0 < degreeB
  adjacent : Fin nA → Fin nB → Bool
  regularA : ∀ a, (Finset.univ.filter fun b => adjacent a b).card = degreeA
  regularB : ∀ b, (Finset.univ.filter fun a => adjacent a b).card = degreeB

/-- Two-sided small-set vertex expansion; 1504.00822 p.4. -/
def LeftRightExpanding {nA nB : ℕ} (G : BipartiteData nA nB)
    (gammaA deltaA gammaB deltaB : ℝ) : Prop :=
  0 < gammaA ∧ 0 < deltaA ∧ 0 < gammaB ∧ 0 < deltaB ∧
  (∀ S : Finset (Fin nA), (S.card : ℝ) ≤ gammaA*nA →
    (1-deltaA)*G.degreeA*S.card ≤
      ((Finset.univ.filter fun b => ∃ a ∈ S, G.adjacent a b = true).card : ℝ)) ∧
  ∀ S : Finset (Fin nB), (S.card : ℝ) ≤ gammaB*nB →
    (1-deltaB)*G.degreeB*S.card ≤
      ((Finset.univ.filter fun a => ∃ b ∈ S, G.adjacent a b = true).card : ℝ)

/-- Graph-computed binary parity matrix; 1504.00822 p.4. -/
def parityMatrix {nA nB : ℕ} (G : BipartiteData nA nB) :
    Matrix (Fin nB) (Fin nA) (ZMod 2) :=
  Matrix.of fun b a => if G.adjacent a b then 1 else 0

/-- Source-specific X/Z adapter; 1504.00822 p.5 (1)–(2). -/
def checks {nA nB : ℕ} (G : BipartiteData nA nB) :=
  (HypergraphProduct.variableCheck (parityMatrix G) (parityMatrix G),
    HypergraphProduct.checkVariable (parityMatrix G) (parityMatrix G))

/-- Constructed pair (ker H_X, ker H_Z); 1504.00822 pp.2,5. -/
def cssPair {nA nB : ℕ} (G : BipartiteData nA nB) :=
  (FieldCodes.parityCheckCode (checks G).1, FieldCodes.parityCheckCode (checks G).2)

example {nA nB : ℕ} (G : BipartiteData nA nB) (a : Fin nA) (b : Fin nB)
    (h : G.adjacent a b = true) : parityMatrix G b a = 1 := by
  simp [parityMatrix, h]

end QAlgorithms.ExpanderCodes


