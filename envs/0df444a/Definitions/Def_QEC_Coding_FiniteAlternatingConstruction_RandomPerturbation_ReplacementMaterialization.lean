-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T03:01:28.20095+00:00
-- url     : https://prove2.me/theorems/7629936c-1a56-426e-8d72-40fba2955c11
-- title:
--   Replacement Materialization
-- statement:
--   Definitions and structural lemmas for Replacement Materialization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Theorems.Thm_QEC_Semantics_CompletelyPositive_add
import Theorems.Thm_QEC_Semantics_JumpProtected_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26ReplacementMaterialization
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
def pointRowQuery {A : Type*} [DecidableEq A] (v : A) : List (A × Space) → Space × ℕ
  | [] => (0,0)
  | (a,x)::R => if a = v then (x,2) else
      let q := pointRowQuery v R
      (q.1,q.2+2)
def labelReadCost {A : Type*} [DecidableEq A] (v : A) : List A → ℕ
  | [] => 0
  | a::R => if a = v then 2 else labelReadCost v R+2
inductive PointCode (A : Type*) where
  | read (v : A)
  | add (a b : PointCode A)
  | scale (r : RealExpr) (a : PointCode A)
  | choose (test : RealTest) (a b : PointCode A)
  | tag (a : PointCode A)
namespace PointCode
variable {A B : Type*}
def eval (J : A → Space) : PointCode A → Space
  | .read v => J v
  | .add a b => a.eval J + b.eval J
  | .scale r a => r.eval (fun _ => 0) 0 0 • a.eval J
  | .choose t a b => if t.eval (fun _ => 0) 0 0 then a.eval J else b.eval J
  | .tag a => a.eval J
def run [DecidableEq A] (R : List (A × Space)) : PointCode A → Space × ℕ
  | .read v => let q := pointRowQuery v R; (q.1,q.2+1)
  | .add a b => let x := a.run R; let y := b.run R; (x.1+y.1,x.2+y.2+4)
  | .scale r a => let x := r.run (fun _ => 0) 0 0; let y := a.run R
                  (x.1 • y.1,x.2+y.2+4)
  | .choose t a b => let q := t.run (fun _ => 0) 0 0
                     let out := if q.1 then a.run R else b.run R
                     (out.1,q.2+out.2+1)
  | .tag a => let out := a.run R; (out.1,out.2+1)
def reads : PointCode A → ℕ
  | .read _ => 1
  | .add a b => a.reads+b.reads
  | .scale _ a => a.reads
  | .choose _ a b => max a.reads b.reads
  | .tag a => a.reads
def work : PointCode A → ℕ
  | .read _ => 1
  | .add a b => a.work+b.work+4
  | .scale r a => 2*r.cost+a.work+4
  | .choose t a b => 2*t.cost+max a.work b.work+1
  | .tag a => a.work+1
def rename (f : A → B) : PointCode A → PointCode B
  | .read v => .read (f v)
  | .add a b => .add (a.rename f) (b.rename f)
  | .scale r a => .scale r (a.rename f)
  | .choose t a b => .choose t (a.rename f) (b.rename f)
  | .tag a => .tag (a.rename f)
def costOnLabels [DecidableEq A] (L : List A) : PointCode A → ℕ
  | .read v => labelReadCost v L+1
  | .add a b => a.costOnLabels L+b.costOnLabels L+4
  | .scale r a => (r.run (fun _ => 0) 0 0).2+a.costOnLabels L+4
  | .choose t a b => let q := t.run (fun _ => 0) 0 0
                     q.2+(if q.1 then a.costOnLabels L else b.costOnLabels L)+1
  | .tag a => a.costOnLabels L+1
end PointCode
def ratioExpr (a b : ℕ) : RealExpr := .div (.constant a) (.constant b)
def contractionExpr (S : OddScale) : RealExpr :=
  .div (.mul (.constant 2) (.constant S.half)) (.constant S.ell)
def stepExpr (S : OddScale) (i : ℕ) : RealExpr :=
  .div (.mul (.constant 2) (.add (.constant i) (.constant 1))) (.constant S.ell)
def centerExpr (S : OddScale) (i : ℕ) : RealExpr :=
  .div (.add (.mul (.constant 2) (.constant i)) (.constant 1)) (.constant S.ell)
def blendCode {A : Type*} (t : RealExpr) (a b : PointCode A) : PointCode A :=
  .add (.scale (.sub (.constant 1) t) a) (.scale t b)
def faceCode (P : TannerSquarePresentation) (f : P.Face) (u v : RealExpr) :
    PointCode (Vertex P) :=
  let x := PointCode.read (.x (P.faceX f))
  let q0 := PointCode.read (.q (P.faceQ f 0))
  let q1 := PointCode.read (.q (P.faceQ f 1))
  let z := PointCode.read (.z (P.faceZ f))
  .tag (.choose (.le v u)
    (.add (.add (.scale (.sub (.constant 1) u) x) (.scale (.sub u v) q0)) (.scale v z))
    (.add (.add (.scale (.sub (.constant 1) v) x) (.scale (.sub v u) q1)) (.scale u z)))
def starCode (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (v : XStarVertex P x) : PointCode (Vertex P) :=
  .tag (blendCode (contractionExpr S) (.read (.x x)) (.read v.1))
def subdivisionCode (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    SubdivisionVertex P x S → PointCode (Vertex P)
  | .inl v => .tag (starCode P S x v)
  | .inr (.inl (e,i)) => .tag (blendCode
      (.div (.add (.constant i.val) (.constant 1)) (.constant S.half))
      (starCode P S x (xStarEdgeStart P x e)) (starCode P S x (xStarEdgeEnd P x e)))
  | .inr (.inr (f,i,j)) => .tag (faceCode P f.1 (stepExpr S i.val) (stepExpr S j.val))
def qSubdivisionCode (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    QSubdivisionVertex P q S → PointCode (Vertex P)
  | .inl (.inl _) => .tag (.read (.q q))
  | .inl (.inr e) => .tag (blendCode (contractionExpr S) (.read (.q q)) (.read (.z e.1)))
  | .inr (e,i) => .tag (blendCode (stepExpr S i.val) (.read (.q q)) (.read (.z e.1)))
def rxZeroCode (P : TannerSquarePresentation) (S : OddScale) (v : RX0 P S) : PointCode (Vertex P) :=
  .tag (subdivisionCode P S v.1 v.2.2)
def rxOneCode (P : TannerSquarePresentation) (S : OddScale) : RX1 P S → PointCode (Vertex P)
  | .inl ⟨x,e⟩ => .tag (.scale (ratioExpr 1 2) (.add
      (subdivisionCode P S x (tannerDoubleCylinderEdgeStart P x S e).2)
      (subdivisionCode P S x (tannerDoubleCylinderEdgeEnd P x S e).2)))
  | .inr ⟨q,_,v⟩ => .tag (qSubdivisionCode P S q v)
def rxTwoCode (P : TannerSquarePresentation) (S : OddScale) : RX2 P S → PointCode (Vertex P)
  | .inl (.inl ⟨_, .inl (_,f,i,j)⟩) => .tag (faceCode P f.1 (centerExpr S i.val) (centerExpr S j.val))
  | .inl (.inl ⟨x, .inr e⟩) => .tag (.scale (ratioExpr 1 2) (.add
      (subdivisionCode P S x (subdivisionEdgeStart P x S e.1))
      (subdivisionCode P S x (subdivisionEdgeEnd P x S e.1))))
  | .inl (.inr ⟨q,e⟩) => .tag (.scale (ratioExpr 1 2) (.add
      (qSubdivisionCode P S q (qDoubleCylinderEdgeStart P q S e).2)
      (qSubdivisionCode P S q (qDoubleCylinderEdgeEnd P q S e).2)))
  | .inr (z,_) => .tag (.read (.z z))
def rxCode (P : TannerSquarePresentation) (S : OddScale) :
    Vertex (rxReplacementPresentation P S) → PointCode (Vertex P)
  | .x x => .tag (rxZeroCode P S x)
  | .q q => .tag (rxOneCode P S q)
  | .z z => .tag (rxTwoCode P S z)
def rzCode (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale) :
    Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S) → PointCode (Vertex P)
  | .x x => .tag ((rxTwoCode (transposePresentation P) S x).rename (transposeVertexEquiv P))
  | .q q => .tag ((rxOneCode (transposePresentation P) S q).rename (transposeVertexEquiv P))
  | .z z => .tag ((rxZeroCode (transposePresentation P) S z).rename (transposeVertexEquiv P))
def successorCode {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (v : Vertex (StagePresentation p (n+1))) : PointCode (Vertex (StagePresentation p n)) :=
  if h : n % 2 = 0 then
    rxCode _ (perturbationOddScale p) (nextRXVertex _ n (state (perturbationOddScale p) n) h v)
  else rzCode _ (state (perturbationOddScale p) n).admissible.toTannerSquareAdmissible
    (perturbationOddScale p) (nextRZVertex _ n (state (perturbationOddScale p) n) h v)
def emittedRows {L : ℝ} (p : GeometricParameters L) (n : ℕ) (J : StageMaps p n)
    (T : StageTables p n) : List (Vertex (StagePresentation p n) × Space) :=
  (outputStateRowsQuery (StagePresentation p n) J p.lambda
    (actualPrefixQuery (StagePresentation p n) J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)
      (eventUniverseQuery (StagePresentation p n) J (by positivity : (0 : ℝ) ≤ anchorRadius p.m)).1 T
      (haltTime (eventSupport (StagePresentation p n) J (anchorRadius p.m))
        (eventBad (StagePresentation p n) J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T)).1).1
def materializeRows {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (R : List (Vertex (StagePresentation p n) × Space)) :
    List (Vertex (StagePresentation p (n+1)) × Space) × ℕ :=
  mapQuery (fun v => let q := (successorCode p n v).run R
                     ((v,q.1),q.2+1)) (vertexInputList (StagePresentation p (n+1)))
def materializationLabelCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) : ℕ :=
  (mapQuery (fun v => ((v,(0 : Space)),
    (successorCode p n v).costOnLabels (vertexInputList (StagePresentation p n))+1))
      (vertexInputList (StagePresentation p (n+1)))).2
def materializationCost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (w : StageMaps p n × StageTables p n) : ℕ := (materializeRows p n (emittedRows p n w.1 w.2)).2
def paidSuccessorQuery {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    List (Vertex (StagePresentation p (n+1)) × Space) × ℝ≥0∞ :=
  let events := eventUniverseQuery (StagePresentation p n) J
    (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
  let prior := actualPrefixQuery (StagePresentation p n) J (anchorRadius p.m) p.lambda
    ((6*p.m+2)*p.lambda) events.1 T
    (haltTime (eventSupport (StagePresentation p n) J (anchorRadius p.m))
      (eventBad (StagePresentation p n) J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T)
  let scan := actualScanQuery (StagePresentation p n) J (anchorRadius p.m) p.lambda
    ((6*p.m+2)*p.lambda) events.1 prior.1
  let oldRows := outputStateRowsQuery (StagePresentation p n) J p.lambda prior.1
  let newRows := materializeRows p n oldRows.1
  (newRows.1, if Halts (eventSupport (StagePresentation p n) J (anchorRadius p.m))
      (eventBad (StagePresentation p n) J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T
    then ((events.2+prior.2+scan.2+oldRows.2+newRows.2 : ℕ) : ℝ≥0∞) else ∞)
def stageMaterializationCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : ℕ := materializationCost p i.val (stagePair p N i z)
def totalMaterializationCost {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : ℕ := ∑ i : Fin N, stageMaterializationCost p N i z
def extendedStageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : ℝ≥0∞ :=
  (paidSuccessorQuery p i.val (stageInput p N i z) (tableAt p N i z)).2
def extendedTotalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : ℝ≥0∞ := ∑ i : Fin N, extendedStageCost p N i z
end QEC.Coding.BDL26ReplacementMaterialization


