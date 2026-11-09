-- Prove2me | Definitions.Def_CaiZhuInfo_Matrix_Protocol
-- name    : CaiZhuInfo_Matrix_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:11.69444+00:00
-- url     : https://prove2.me/theorems/7eb3a2fe-3e33-4b4d-91e8-71e5eb2b925a
-- title:
--   Finite interactive protocols and information-complexity infima
-- statement:
--   A protocol is a finite binary communication tree with a specified speaker at each internal node. Alice's messages depend on her input, the public tape, her retained private tape and the previous messages; Bob's messages depend on his corresponding information. Each tape is an arbitrary probability space, and execution uses the product of the input law and the three tape laws. Thus all tapes are independent of the inputs and of one another. There is no common bound on the depths of all protocols.
--   The transcript consists of the public tape and all messages. Bob's final output also uses his input and private tape. Transcript-determined output means a measurable function of the transcript alone, up to null tape outcomes for each fixed input. The execution law, transcript law, posteriors and errors are computed from this execution. The information cost is
--   $$\mathrm{IC}_\mu(\Pi)=I(X;\Pi\mid Y)+I(Y;\Pi\mid X).$$
--   For a public tape $R$ and finite complete-message-history label $H$, the cost is computed equivalently as $I(H;X\mid Y,R)+I(H;Y\mid X,R)$. Independence of $R$ from the inputs, the chain rule and symmetry of conditional mutual information give the displayed source cost. Terminal labels encode the full message list bijectively. This expression remains finite for infinite discrete input alphabets, as required by Lemma E.1.
--
--   The four complexities are real infima of these costs over all eligible protocols, separately for average or pointwise error and Bob-only or transcript-determined output. Exact transmission gives a feasible finite protocol for every nonnegative error allowance on finite nonempty alphabets, and nonnegativity bounds the costs below. Binary coding of finite messages preserves the full transcript information. The structure carries only operational and measurability conditions, without correctness, posterior factorization or information bounds.
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), §1, (1), error/output conventions, §6.1 and Appendix E.1, printed pp.1–2,19,33–34 / PDF pp.2–3,20,34–35; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_conditionalInformation

open MeasureTheory
open scoped ENNReal

namespace CaiZhuInfo.Matrix

/-! Operational finite binary communication trees, Cai–Zhu §1 and §6.1,
printed pp.1–2,19 / PDF pp.2–3,20. Binary coding of finite messages preserves
histories and information; there is no common depth bound across protocols.
Tapes are arbitrary probability spaces, permitting arbitrary real mixture weights.
A private tape is retained for all rounds, so private-memory strategies are included. -/
noncomputable section

instance historyMeasurableSpace : MeasurableSpace (List Bool) := ⊤

structure RandomSource where
  Carrier : Type
  measurable : MeasurableSpace Carrier
  law : @Measure Carrier measurable
  probability : @IsProbabilityMeasure Carrier measurable law

attribute [instance] RandomSource.measurable RandomSource.probability

inductive CommunicationTree where
  | leaf
  | alice (zero one : CommunicationTree)
  | bob (zero one : CommunicationTree)

/-- A finite label for each terminal history, without any restriction on inputs. -/
def CommunicationTree.Outcome : CommunicationTree → Type
  | .leaf => Unit
  | .alice zero one => zero.Outcome ⊕ one.Outcome
  | .bob zero one => zero.Outcome ⊕ one.Outcome

instance CommunicationTree.outcomeFintype (tree : CommunicationTree) : Fintype tree.Outcome := by
  induction tree with
  | leaf => exact inferInstanceAs (Fintype Unit)
  | alice zero one ih0 ih1 =>
    letI := ih0
    letI := ih1
    exact inferInstanceAs (Fintype (zero.Outcome ⊕ one.Outcome))
  | bob zero one ih0 ih1 =>
    letI := ih0
    letI := ih1
    exact inferInstanceAs (Fintype (zero.Outcome ⊕ one.Outcome))

/-- Execute the same tree, recording a finite terminal-history label. -/
def CommunicationTree.executeOutcome : (tree : CommunicationTree) →
    (List Bool → Bool) → (List Bool → Bool) → List Bool → tree.Outcome
  | .leaf, _, _, _ => ()
  | .alice zero one, a, b, h =>
      if a h then Sum.inr (one.executeOutcome a b (h ++ [true]))
      else Sum.inl (zero.executeOutcome a b (h ++ [false]))
  | .bob zero one, a, b, h =>
      if b h then Sum.inr (one.executeOutcome a b (h ++ [true]))
      else Sum.inl (zero.executeOutcome a b (h ++ [false]))

/-- Recover the complete message list from its terminal-history label. -/
def CommunicationTree.outcomeMessages : (tree : CommunicationTree) → tree.Outcome → List Bool
  | .leaf, _ => []
  | .alice zero _, .inl o => false :: zero.outcomeMessages o
  | .alice _ one, .inr o => true :: one.outcomeMessages o
  | .bob zero _, .inl o => false :: zero.outcomeMessages o
  | .bob _ one, .inr o => true :: one.outcomeMessages o

/-- The history contains every message, in chronological order. -/
def CommunicationTree.execute : CommunicationTree →
    (List Bool → Bool) → (List Bool → Bool) → List Bool → List Bool
  | .leaf, _, _, h => h
  | .alice zero one, a, b, h =>
      if a h then one.execute a b (h ++ [true]) else zero.execute a b (h ++ [false])
  | .bob zero one, a, b, h =>
      if b h then one.execute a b (h ++ [true]) else zero.execute a b (h ++ [false])

/-- Only locality and measurability are fields; no correctness, factorization or
information inequality is assumed. The tree fixes the speaker at each history. -/
structure Protocol (X Y Z : Type) where
  shared : RandomSource
  privateA : RandomSource
  privateB : RandomSource
  tree : CommunicationTree
  sendA : X → shared.Carrier → privateA.Carrier → List Bool → Bool
  sendB : Y → shared.Carrier → privateB.Carrier → List Bool → Bool
  out : Y → shared.Carrier → privateB.Carrier → List Bool → Z
  sendA_measurable : ∀ x h, Measurable (fun u : shared.Carrier × privateA.Carrier => sendA x u.1 u.2 h)
  sendB_measurable : ∀ y h, Measurable (fun u : shared.Carrier × privateB.Carrier => sendB y u.1 u.2 h)
  out_measurable : ∀ y h, @Measurable (shared.Carrier × privateB.Carrier) Z
    inferInstance ⊤ (fun u => out y u.1 u.2 h)

namespace Protocol
variable {X Y Z : Type} (P : Protocol X Y Z)

abbrev Coins := P.shared.Carrier × (P.privateA.Carrier × P.privateB.Carrier)
abbrev Sample := (X × Y) × P.Coins
abbrev Transcript := P.shared.Carrier × List Bool

def coinsLaw : Measure P.Coins :=
  P.shared.law.prod (P.privateA.law.prod P.privateB.law)

def history (x : X) (y : Y) (c : P.Coins) : List Bool :=
  P.tree.execute (P.sendA x c.1 c.2.1) (P.sendB y c.1 c.2.2) []

def transcript (x : X) (y : Y) (c : P.Coins) : P.Transcript :=
  (c.1, P.history x y c)

def output (x : X) (y : Y) (c : P.Coins) : Z :=
  P.out y c.1 c.2.2 (P.history x y c)

variable [MeasurableSpace X] [MeasurableSpace Y]

def executionLaw (μ : PMF (X × Y)) : Measure P.Sample :=
  μ.toMeasure.prod P.coinsLaw

def transcriptVar (ω : P.Sample) : P.Transcript := P.transcript ω.1.1 ω.1.2 ω.2

def outputVar (ω : P.Sample) : Z := P.output ω.1.1 ω.1.2 ω.2

def transcriptLaw (μ : PMF (X × Y)) : Measure P.Transcript :=
  (P.executionLaw μ).map P.transcriptVar

def outcomeVar (ω : P.Sample) : P.tree.Outcome :=
  P.tree.executeOutcome (P.sendA ω.1.1 ω.2.1 ω.2.2.1)
    (P.sendB ω.1.2 ω.2.1 ω.2.2.2) []

/-- For the public tape R and finite terminal history H, independence of R from
inputs and symmetry of conditional mutual information give
I(X;R,H | Y) = I(H;X | Y,R), and likewise for Bob. The finite first slot
keeps both terms finite even for infinite discrete input alphabets. -/
def informationCost (μ : PMF (X × Y)) : ℝ :=
  conditionalInformation (P.executionLaw μ) P.outcomeVar (fun ω => ω.1.1)
    (fun ω => (ω.1.2, ω.2.1)) +
  conditionalInformation (P.executionLaw μ) P.outcomeVar (fun ω => ω.1.2)
    (fun ω => (ω.1.1, ω.2.1))

def averageError (μ : PMF (X × Y)) (f : X → Y → Z) : ℝ :=
  ((P.executionLaw μ) {ω | P.outputVar ω ≠ f ω.1.1 ω.1.2}).toReal

def pointwiseError (f : X → Y → Z) (x : X) (y : Y) : ℝ :=
  (P.coinsLaw {c | P.output x y c ≠ f x y}).toReal

/-- The output is a measurable function of the public transcript alone.
Null tape outcomes are immaterial, for every fixed input. -/
def TranscriptDetermined : Prop :=
  ∃ g : P.Transcript → Z, @Measurable _ Z inferInstance ⊤ g ∧
    ∀ x y, (fun c => P.output x y c) =ᵐ[P.coinsLaw] (fun c => g (P.transcript x y c))

/-- Changing only the final decoder preserves all interaction and tape laws. -/
def replaceDecoder (z : Y → P.Transcript → Z)
    (hz : ∀ y, @Measurable _ Z inferInstance ⊤ (z y)) : Protocol X Y Z :=
  { P with
    out := fun y r _ h => z y (r, h)
    out_measurable := fun y _h => (hz y).comp (measurable_fst.prodMk measurable_const) }

/-- Actual posterior point masses, as conditional expectations on the execution space. -/
def posteriorX (μ : PMF (X × Y)) (x : X) : P.Sample → ℝ :=
  conditionalMass (P.executionLaw μ) (fun ω => ω.1.1) (observedSigma P.transcriptVar) x

def posteriorY (μ : PMF (X × Y)) (y : Y) : P.Sample → ℝ :=
  conditionalMass (P.executionLaw μ) (fun ω => ω.1.2) (observedSigma P.transcriptVar) y

def posteriorXY (μ : PMF (X × Y)) (x : X) (y : Y) : P.Sample → ℝ :=
  conditionalMass (P.executionLaw μ) (fun ω => ω.1) (observedSigma P.transcriptVar) (x,y)

/-- Atomic conditional law, used only when the denominator is positive and
its transcript singleton is measurable. -/
def atomicPosterior (μ : PMF (X × Y)) (π : P.Transcript) (x : X) (y : Y) : ℝ :=
  ((P.executionLaw μ) {ω | ω.1 = (x,y) ∧ P.transcriptVar ω = π}).toReal /
    ((P.transcriptLaw μ) {π}).toReal

end Protocol

/-- Infima over every finite interactive protocol, with the actual execution cost.
For finite nonempty alphabets and ε ≥ 0, exact transmission makes the sets nonempty;
conditional information is nonnegative, so these real infima are bounded below.
Outside the intended error domain a real sInf has Lean's default convention. -/
def informationComplexity {X Y Z : Type} [Fintype X] [Fintype Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : PMF (X × Y)) (f : X → Y → Z) (ε : ℝ)
    (pointwise transcriptOutput : Bool) : ℝ :=
  sInf {c : ℝ | ∃ P : Protocol X Y Z,
    c = P.informationCost μ ∧
    (if pointwise then ∀ x y, P.pointwiseError f x y ≤ ε else P.averageError μ f ≤ ε) ∧
    (if transcriptOutput then P.TranscriptDetermined else True)}

end
end CaiZhuInfo.Matrix


