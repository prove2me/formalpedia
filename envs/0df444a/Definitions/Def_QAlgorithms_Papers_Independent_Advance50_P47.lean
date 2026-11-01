-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P47
-- name    : QAlgorithms_Papers_Independent_Advance50_P47
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T04:31:32.431639+00:00
-- url     : https://prove2.me/theorems/cd6aab3b-f7b5-474d-8dde-fc036cca7ec9
-- title:
--   prove2quantum library: Papers.Independent.Advance50.P47
-- statement:
--   Shared definitions of the prove2quantum Lean library (`QAlgorithms.Papers.Independent.Advance50.P47`), reused by its paper formalizations.
--
--   - `Box`: PDF p.4, Section 3.1: conditional probabilities, with independently typed Alice and Bob measurement choices and outcomes.
--   - `IsCorrelation`: PDF p.4, Section 3.1: normalization is required at every input pair.
--   - `IsNoSignaling`: PDF p.5, (11),(12): both scalar no-signaling equalities. Validity as a conditional probability law is separate, through IsCorrelation.
--   - `HasLocalModel`: PDF p.4, (9): a discrete shared hidden variable independent of the inputs. PMF permits an arbitrary discrete alphabet with countable support; the local response laws are normalized even on hidden-variable events of zero mass.
--   - `correlationMixture`: PDF p.13, Proposition 10: the mixture is computed from its two boxes. This raw formula is used on 0 <= lambda <= 1 and valid correlations. The accepted Information100.P47.mixture instead mixes finite complex-matrix POVM families, so it cannot be applied to these real-valued conditional laws.
--   - `TwoLocalBoxes`: PDF pp.5–6, (15)–(17): exactly the two independent local boxes printed in the source. Neither local response accesses the remote party's data. The two shared-variable laws are fixed independently of all measurement choices.
--   - `inputBox`: PDF p.6, (16): the input local box, including the averaging over Lambda2.
--   - `outputBox`: PDF p.6, (17): the output local box has its own input-independent law.
--   - `losrTransform`: PDF p.5, (15), and pp.9,12, (34),(54): the source's computed LOSR output.
--   - `prBox`: PDF p.5, (14): the binary PR-box conditional law. true labels 1.
--   - `NSOperatorExtension`: PDF p.7, (19),(20),(22): Eve's positive subnormalized trace-class blocks. The space H is arbitrary; no Fintype instance or dimension bound is imposed. The constraints hold for every input, independently of any chosen input law. Zero-trace blocks are permitted; no conditional state is divided by p(a,b|x,y).
--   - `Assemblage`: PDF p.3, (1),(2): an assemblage of positive subnormalized Bob operators, with a common normalized total state. The total is constructed by summation, and normalization is stated at every input. Zero blocks are allowed.
--   - `Assemblage.HasLHS`: PDF p.3, (3): a discrete local-hidden-state assemblage. The law and Bob states are independent of Alice's input; only her response law sees x. The operator series is evaluated in the bounded-operator norm. The PMF weights and normalized positive states ensure absolute convergence on these witnesses.
-- source:
--   prove2quantum Lean library, module QAlgorithms.Papers.Independent.Advance50.P47

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

/-!
# Fundamental limits on key rates in device-independent quantum key distribution

Paper-local definitions from arXiv:1810.05627v3. All page numbers are PDF pages.
These definitions retain unequal finite alphabets and operator-valued Eve systems
of unrestricted dimension. They do not define N, NQ, S, or a key capacity.
Every assigned result is explicitly deferred in HARD.md and GAPS.json: the
infinite-system information and operational interfaces have not been completed.
In particular, none of the definitions below is a replacement headline theorem.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Advance50.P47

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace State)

-- The accepted finite probability-law predicate is exactly the law used on PDF p.4.
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

/-- PDF p.4, Section 3.1: conditional probabilities, with independently typed
Alice and Bob measurement choices and outcomes. -/
abbrev Box (X Y A B : Type*) := X → Y → A → B → ℝ

/-- PDF p.4, Section 3.1: normalization is required at every input pair. -/
def IsCorrelation {X Y A B : Type*} [Fintype A] [Fintype B]
    (p : Box X Y A B) : Prop :=
  (∀ x y a b, 0 ≤ p x y a b) ∧ ∀ x y, ∑ a, ∑ b, p x y a b = 1

/-- PDF p.5, (11),(12): both scalar no-signaling equalities. Validity as a
conditional probability law is separate, through IsCorrelation. -/
def IsNoSignaling {X Y A B : Type*} [Fintype A] [Fintype B]
    (p : Box X Y A B) : Prop :=
  (∀ x z y b, ∑ a, p x y a b = ∑ a, p z y a b) ∧
  (∀ y z x a, ∑ b, p x y a b = ∑ b, p x z a b)

/-- PDF p.4, (9): a discrete shared hidden variable independent of the inputs.
PMF permits an arbitrary discrete alphabet with countable support; the local
response laws are normalized even on hidden-variable events of zero mass. -/
def HasLocalModel {X Y A B : Type} [Fintype A] [Fintype B]
    (p : Box X Y A B) : Prop :=
  IsCorrelation p ∧ ∃ (L : Type) (mu : PMF L)
    (alice : L → X → A → ℝ) (bob : L → Y → B → ℝ),
    (∀ l x, IsLaw (alice l x)) ∧ (∀ l y, IsLaw (bob l y)) ∧
    ∀ x y a b, p x y a b =
      ∑' l, (mu l).toReal * alice l x a * bob l y b

/-- PDF p.13, Proposition 10: the mixture is computed from its two boxes.
This raw formula is used on 0 <= lambda <= 1 and valid correlations.
The accepted Information100.P47.mixture instead mixes finite complex-matrix
POVM families, so it cannot be applied to these real-valued conditional laws. -/
def correlationMixture {X Y A B : Type*} (p q : Box X Y A B) (lambda : ℝ) : Box X Y A B :=
  fun x y a b => lambda * p x y a b + (1 - lambda) * q x y a b

/-- PDF pp.5–6, (15)–(17): exactly the two independent local boxes printed
in the source. Neither local response accesses the remote party's data.
The two shared-variable laws are fixed independently of all measurement choices. -/
structure TwoLocalBoxes (X Y A B Xf Yf Af Bf L1 L2 : Type*)
    [Fintype X] [Fintype Y] [Fintype Af] [Fintype Bf] where
  inputLaw : PMF L2
  outputLaw : PMF L1
  inputAlice : L2 → Xf → X → ℝ
  inputBob : L2 → Yf → Y → ℝ
  outputAlice : L1 → A → X → Xf → Af → ℝ
  outputBob : L1 → B → Y → Yf → Bf → ℝ
  inputAlice_law : ∀ l xf, IsLaw (inputAlice l xf)
  inputBob_law : ∀ l yf, IsLaw (inputBob l yf)
  outputAlice_law : ∀ l a x xf, IsLaw (outputAlice l a x xf)
  outputBob_law : ∀ l b y yf, IsLaw (outputBob l b y yf)

/-- PDF p.6, (16): the input local box, including the averaging over Lambda2. -/
def inputBox {X Y A B Xf Yf Af Bf L1 L2 : Type*}
    [Fintype X] [Fintype Y] [Fintype Af] [Fintype Bf]
    (L : TwoLocalBoxes X Y A B Xf Yf Af Bf L1 L2) : Box Xf Yf X Y :=
  fun xf yf x y => ∑' l, (L.inputLaw l).toReal *
    L.inputAlice l xf x * L.inputBob l yf y

/-- PDF p.6, (17): the output local box has its own input-independent law. -/
def outputBox {X Y A B Xf Yf Af Bf L1 L2 : Type*}
    [Fintype X] [Fintype Y] [Fintype Af] [Fintype Bf]
    (L : TwoLocalBoxes X Y A B Xf Yf Af Bf L1 L2)
    (a : A) (b : B) (x : X) (y : Y) (xf : Xf) (yf : Yf) (af : Af) (bf : Bf) : ℝ :=
  ∑' l, (L.outputLaw l).toReal *
    L.outputAlice l a x xf af * L.outputBob l b y yf bf

/-- PDF p.5, (15), and pp.9,12, (34),(54): the source's computed LOSR output. -/
def losrTransform {X Y A B Xf Yf Af Bf L1 L2 : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype Af] [Fintype Bf]
    (L : TwoLocalBoxes X Y A B Xf Yf Af Bf L1 L2)
    (p : Box X Y A B) : Box Xf Yf Af Bf :=
  fun xf yf af bf => ∑ a, ∑ b, ∑ x, ∑ y,
    outputBox L a b x y xf yf af bf * p x y a b * inputBox L xf yf x y

/-- PDF p.5, (14): the binary PR-box conditional law. true labels 1. -/
def prBox : Box Bool Bool Bool Bool :=
  fun x y a b => if Bool.xor a b = (x && y) then 1 / 2 else 0

/-- PDF p.7, (19),(20),(22): Eve's positive subnormalized trace-class blocks.
The space H is arbitrary; no Fintype instance or dimension bound is imposed.
The constraints hold for every input, independently of any chosen input law.
Zero-trace blocks are permitted; no conditional state is divided by p(a,b|x,y). -/
structure NSOperatorExtension {X Y A B I H : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (basis : HilbertBasis I ℂ H) (p : Box X Y A B) where
  correlation : IsCorrelation p
  block : X → Y → A → B → (H →L[ℂ] H)
  positive : ∀ x y a b, IsPositive (block x y a b)
  traceClass : ∀ x y a b, IsTraceClass (block x y a b)
  mass : ∀ x y a b, operatorTrace basis (block x y a b) = (p x y a b : ℂ)
  aliceNS : ∀ x z y b, ∑ a, block x y a b = ∑ a, block z y a b
  bobNS : ∀ y z x a, ∑ b, block x y a b = ∑ b, block x z a b

/-- PDF p.3, (1),(2): an assemblage of positive subnormalized Bob operators,
with a common normalized total state. The total is constructed by summation,
and normalization is stated at every input. Zero blocks are allowed. -/
structure Assemblage (X A I H : Type*) [Fintype X] [Fintype A]
    [Nonempty X] [Nonempty A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (basis : HilbertBasis I ℂ H) where
  block : X → A → (H →L[ℂ] H)
  positive : ∀ x a, IsPositive (block x a)
  traceClass : ∀ x a, IsTraceClass (block x a)
  totalMass : ∀ x, operatorTrace basis (∑ a, block x a) = 1
  commonTotal : ∀ x z, ∑ a, block x a = ∑ a, block z a

/-- PDF p.3, (3): a discrete local-hidden-state assemblage. The law and
Bob states are independent of Alice's input; only her response law sees x.
The operator series is evaluated in the bounded-operator norm. The PMF weights
and normalized positive states ensure absolute convergence on these witnesses. -/
def Assemblage.HasLHS {X A I H : Type*} [Fintype X] [Fintype A]
    [Nonempty X] [Nonempty A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {basis : HilbertBasis I ℂ H} (rho : Assemblage X A I H basis) : Prop :=
  ∃ (L : Type) (mu : PMF L) (sigma : L → State basis)
    (response : L → X → A → ℝ),
    (∀ l x, IsLaw (response l x)) ∧
    ∀ x a, rho.block x a =
      ∑' l, (((mu l).toReal * response l x a : ℝ) : ℂ) • (sigma l).val.val

/-! Small sanity examples only. No source result is proved below. -/

example : IsLaw (fun _ : Unit => (1 : ℝ)) := by
  simp [IsLaw]

example : IsCorrelation (fun (_ _ _ _ : Unit) => (1 : ℝ)) := by
  simp [IsCorrelation]

example : IsNoSignaling (fun (_ _ _ _ : Unit) => (1 : ℝ)) := by
  simp [IsNoSignaling]

example {X Y A B : Type*} (p q : Box X Y A B) : correlationMixture p q 0 = q := by
  funext x y a b
  simp [correlationMixture]

example {X Y A B : Type*} (p q : Box X Y A B) : correlationMixture p q 1 = p := by
  funext x y a b
  simp [correlationMixture]

example : prBox true true false false = 0 := by simp [prBox]

example : prBox true true false true = 1 / 2 := by simp [prBox]

example : prBox false false false false = 1 / 2 := by simp [prBox]

example {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (basis : HilbertBasis I ℂ H) (rho : State basis) :
    Nonempty (NSOperatorExtension basis (fun (_ _ _ _ : Unit) => (1 : ℝ))) := by
  refine ⟨{
    correlation := ?_
    block := fun _ _ _ _ => rho.val.val
    positive := ?_
    traceClass := ?_
    mass := ?_
    aliceNS := ?_
    bobNS := ?_
  }⟩
  · simp [IsCorrelation]
  · exact fun _ _ _ _ => rho.property.1
  · exact fun _ _ _ _ => rho.val.property
  · exact fun _ _ _ _ => rho.property.2
  · intro x z y b
    simp
  · intro y z x a
    simp

example {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (basis : HilbertBasis I ℂ H) (rho : State basis) :
    Nonempty (Assemblage Unit Unit I H basis) := by
  refine ⟨{
    block := fun _ _ => rho.val.val
    positive := ?_
    traceClass := ?_
    totalMass := ?_
    commonTotal := ?_
  }⟩
  · exact fun _ _ => rho.property.1
  · exact fun _ _ => rho.val.property
  · intro x
    simpa using rho.property.2
  · intro x z
    simp

end QAlgorithms.Papers.Independent.Advance50.P47


