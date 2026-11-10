-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:21:54.685142+00:00
-- url     : https://prove2.me/theorems/a08ea4cc-ee99-4e4c-801e-affe7612c501
-- title:
--   Physical Locality
-- statement:
--   Definitions and structural lemmas for Physical Locality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_faceQ_surjective

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RandomPhysicalLocality
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open BDL26TannerLocalRegularity
open BDL26QuantitativeBounds BDL26DecodingGraph BDL26CSSHamiltonian
open Semantics Semantics.Davies
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def qubitHits (P : TannerSquarePresentation) (J : Vertex P → E) (ball : Set E) : Finset P.Q :=
  Finset.univ.filter (fun q => J (.q q) ∈ ball)
def qubitCorner (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (q : P.Q) :
    P.Face × Two := Classical.choose (faceQ_surjective P A q)
def checkCenter (S : OddScale) (n : Nat) (J : Vertex (state S n).presentation → E) :
    Sum (ZLabel S n) (XLabel S n) → E
  | .inl z => J (.z z)
  | .inr x => J (.x x)
def PhysicalGeometry (S : OddScale) (n : Nat) (J : Vertex (state S n).presentation → E)
    (t : ℝ) : Prop :=
  (∀ c, ((qubitHits (state S n).presentation J (Metric.closedBall c 1)).card : ℝ) ≤ 2*t) ∧
  (∀ j : Sum (ZLabel S n) (XLabel S n),
    (∀ r ∈ checkSupport S n j, dist (J (.q r)) (checkCenter S n J j) ≤ 1) ∧
    (∀ r ∈ checkSupport S n j, ∀ s ∈ checkSupport S n j, dist (J (.q r)) (J (.q s)) ≤ 2) ∧
    (checkSupport S n j).card ≤ 7) ∧
  (∀ q : Physical S n,
    (∀ r ∈ region S n q, dist (J (.q r)) (J (.q q)) ≤ 2) ∧
    (∀ r ∈ region S n q, ∀ s ∈ region S n q, dist (J (.q r)) (J (.q s)) ≤ 4) ∧
    (region S n q).card ≤ 50)
end QEC.Coding.BDL26RandomPhysicalLocality


