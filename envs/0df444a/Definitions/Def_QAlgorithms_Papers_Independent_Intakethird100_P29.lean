-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P29
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P29
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T05:04:38.940217+00:00
-- url     : https://prove2.me/theorems/b763701b-1804-4359-b566-68eac443c674
-- title:
--   Definitions for Nonlocality free wirings and the distinguishability between Bell boxes
-- statement:
--   The objects the formalized statements of *Nonlocality free wirings and the distinguishability between Bell boxes* (arXiv:1611.06932) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BellScenario`: PDF p.2, Section II: four independent finite, nonempty alphabets.
--   - `BellScenario.X`: PDF p.2, Section II: finite Alice input alphabet.
--   - `BellScenario.Y`: PDF p.2, Section II: finite Bob input alphabet.
--   - `BellScenario.A`: PDF p.2, Section II: finite Alice output alphabet.
--   - `BellScenario.B`: PDF p.2, Section II: finite Bob output alphabet.
--   - `Behavior`: PDF p.2, (1): raw arrays; validity is `IsCorrelation`, not implicit.
--   - `IsNS`: PDF p.2, (1),(2): normalized conditional laws satisfying both NS identities.
--   - `BellOperation`: Raw extensions are useful for linearity; WPICC is constrained only on NS.
--   - `IsLOSR`: PDF pp.3–4, (7): two local boxes, with independent shared-variable laws. The accepted interface allows arbitrary discrete seeds; no finite-support premise.
--   - `GlobalWiring`: PDF p.4, (10): arbitrary normalized input/output processing kernels. They may be signaling; in particular the output need not belong to NS.
--   - `GlobalWiring.apply`: PDF p.4, (10): one use of the supplied box, with fixed processing rules.
--   - `IsGW`: Membership as an operation on all arrays; used for the direct LOSR inclusion.
--   - `UncorrelatedWiring`: PDF p.15, (G1): four one-party kernels, without a shared hidden variable.
--   - `UncorrelatedWiring.apply`: PDF p.15, (G1): product input and output kernels act on one supplied box.
--   - `AfterAlice`: PDF p.10, Appendix A: after Alice's preparation outcome is communicated, Bob either waits for his final input or measures now and communicates his outcome. The enclosing function of Alice's outcome makes this decision adaptive.
--   - `AfterBob`: PDF p.10, Appendix A: the symmetric continuation after Bob measures first.
--   - `Preparation`: PDF pp.4,10: deterministic preparation tree. All stochastic choices, including later local random choices, are incorporated in the input-independent shared seed. The initial setting is fixed before the final inputs in each first-measurement branch.
--   - `responseIndicator`: Indicator for a deterministic classical response.
--   - `aliceContribution`: PDF pp.10–11, (A1)–(A4): contribution of a first Alice outcome. Joint probabilities avoid division by the probability of an impossible transcript.
--   - `bobContribution`: PDF pp.10–11: symmetric contribution of a first Bob outcome.
--   - `Preparation.apply`: PDF pp.4,10–11: exact action of the operational preparation tree.
--   - `Preparation.isPrepared`: PDF pp.10–11: a branch in which at least one box is measured during preparation. The no-preparation branch of (A5) is separately one fixed LOSR map.
--   - `IsWPICC`: PDF pp.4,10–11: operational WPICC using the proof convention of (A5). The no-preparation branch is one fixed Eq.(7) LOSR map. The other branch averages adaptive trees in which at least one party measures before final inputs. This keeps Eq.(7)'s separate input/output seeds; it does not silently replace its LOSR class by a convex hull of complete no-preparation strategies. Weight, map, seed law and trees precede every supplied behavior. Only NS inputs are constrained. Locality of the prepared action is a theorem conclusion, not part of this definition.
--   - `AgreeOnNS`: Equality on the common physical domain, not on arbitrary raw extensions.
--   - `HasGWRestriction`: PDF p.6, (19): whether any GW has the same action on every NS behavior.
--   - `HasLOSRRestriction`: Whether any LOSR operation agrees on the whole NS domain.
--   - `classicalRelativeEntropyNats`: PDF p.5, (14): extended finite-alphabet KL, in the displayed orientation. Only the total KL is converted to ENNReal; negative individual summands are retained. A positive numerator over zero gives infinity; zero terms give zero.
--   - `sb`: PDF p.5, (16): maximization over one fixed joint input, for all behaviors.
--   - `weightedEntropy`: PDF p.5, (15): same input law for both compared behaviors. ENNReal's zero times infinity is zero, including unused support-mismatch inputs.
--   - `snl`: PDF p.7, (21): all local comparison boxes, on exactly the same alphabets.
--   - `localDistance`: Inner local minimization in (22); extrema are certified in `OptimaAttained`.
--   - `uniformInput`: PDF p.7, (22a): uniform *joint* input distribution. The positive sizes in `BellScenario` exclude division by zero.
--   - `su`: PDF p.7, (22a): uniform-input statistical strength.
--   - `suc`: PDF p.7, (22b): max over product laws, outside the local minimum.
--   - `correlatedInputStrength`: PDF p.7, (22c): max over all joint laws, outside the local minimum.
--   - `OptimaAttained`: Explicit meaning of the source's real-valued min/max notation in (21),(22). Every local minimum and both outer maxima are attained. These are conclusions, not hypotheses restricting the behaviors in any headline theorem.
--   - `Quantity`: Families over every finite Bell scenario; only values on NS are relevant.
--   - `IsNormalizedQuantity`: PDF p.6, Definition 5(i), including finite nonnegative real values on NS.
--   - `IsLOSRMonotone`: PDF p.6, Definition 5: LOSR monotonicity includes vanishing on local boxes.
--   - `IsWPICCMonotone`: PDF p.6, Definition 5: WPICC monotonicity, allowing alphabet changes.
--   - `IsBellMonotone`: PDF p.6, Definition 7: monotonicity for both equivalent choices of free class. The numbered Lemma 6 supplies their equivalence, without convexity.
--   - `singletonScenario`: Singleton scenario used only to check nonempty boundary conventions.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, https://arxiv.org/abs/1611.06932v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P47
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

/-!
# Nonlocality free wirings and the distinguishability between Bell boxes

arXiv:1611.06932v2. Page numbers below are PDF pages. Paper-local interfaces
use the accepted Advance50.P47 conditional laws and arbitrary-discrete LOSR
interface, and Dependency50.P47.Law for finite input distributions.
All four alphabet sizes are independent and strictly positive.

Repair: BellScenario and BellOperation describe classical conditional arrays,
unlike the accepted quantum communication Scenario and complex-matrix Operation.
responseIndicator is a classical response indicator, not a quantum entropy delta.
classicalRelativeEntropyNats is finite classical KL in nats, unlike the accepted
operator entropies and the classicalKL in bits. correlatedInputStrength is (22c),
not the accepted channel success exponent sc. The accepted HasLocalModel and Law
are used directly. ASSESSMENT.json records each local declaration separately.

Extended KL is retained at support mismatches. The optimized quantities are
extended nonnegative reals; `OptimaAttained` and the monotone predicates assert
finiteness on NS, identifying them with the source's nonnegative real values.
No conversion sends infinity to zero. Attainment is a conclusion, never a premise.

WPICC uses Appendix A's proof convention: the no-preparation branch is one
fixed Eq.(7) LOSR map; the prepared branch is a shared-seed average of single-use
adaptive trees followed by local responses. The second preparation measurement
may depend on the first communicated outcome. Equation (8) is a theorem about
these operations: the prepared action is not assumed local in the definition.
Only the NS restriction has meaning. Class separations compare these restrictions.
The no-preparation convention is recorded explicitly in MODERATION-r1.md.

The two ambiguous Appendix C/F quantitative claims are deferred in HARD.md.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intakethird100.P29

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Advance50.P47
  (Box IsCorrelation IsNoSignaling HasLocalModel TwoLocalBoxes losrTransform
   correlationMixture)
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

/-- PDF p.2, Section II: four independent finite, nonempty alphabets. -/
structure BellScenario where
  nX : ℕ
  nY : ℕ
  nA : ℕ
  nB : ℕ
  xPositive : 0 < nX
  yPositive : 0 < nY
  aPositive : 0 < nA
  bPositive : 0 < nB

/-- PDF p.2, Section II: finite Alice input alphabet. -/
abbrev BellScenario.X (s : BellScenario) := Fin s.nX

/-- PDF p.2, Section II: finite Bob input alphabet. -/
abbrev BellScenario.Y (s : BellScenario) := Fin s.nY

/-- PDF p.2, Section II: finite Alice output alphabet. -/
abbrev BellScenario.A (s : BellScenario) := Fin s.nA

/-- PDF p.2, Section II: finite Bob output alphabet. -/
abbrev BellScenario.B (s : BellScenario) := Fin s.nB

/-- PDF p.2, (1): raw arrays; validity is `IsCorrelation`, not implicit. -/
abbrev Behavior (s : BellScenario) := Box s.X s.Y s.A s.B

/-- PDF p.2, (1),(2): normalized conditional laws satisfying both NS identities. -/
def IsNS {s : BellScenario} (p : Behavior s) : Prop :=
  IsCorrelation p ∧ IsNoSignaling p

-- PDF p.2, (4): use the accepted HasLocalModel directly.

/-- Raw extensions are useful for linearity; WPICC is constrained only on NS. -/
abbrev BellOperation (s t : BellScenario) := Behavior s → Behavior t

/-- PDF pp.3–4, (7): two local boxes, with independent shared-variable laws.
The accepted interface allows arbitrary discrete seeds; no finite-support premise. -/
def IsLOSR {s t : BellScenario} (w : BellOperation s t) : Prop :=
  ∃ (L1 L2 : Type)
    (k : TwoLocalBoxes s.X s.Y s.A s.B t.X t.Y t.A t.B L1 L2),
    ∀ p, w p = losrTransform k p

/-- PDF p.4, (10): arbitrary normalized input/output processing kernels.
They may be signaling; in particular the output need not belong to NS. -/
structure GlobalWiring (s t : BellScenario) where
  input : t.X → t.Y → s.X × s.Y → ℝ
  output : s.A → s.B → s.X → s.Y → t.X → t.Y → t.A × t.B → ℝ
  inputLaw : ∀ chi psi, IsLaw (input chi psi)
  outputLaw : ∀ a b x y chi psi, IsLaw (output a b x y chi psi)

/-- PDF p.4, (10): one use of the supplied box, with fixed processing rules. -/
def GlobalWiring.apply {s t : BellScenario} (g : GlobalWiring s t) : BellOperation s t :=
  fun p chi psi alpha beta => ∑ a, ∑ b, ∑ x, ∑ y,
    g.output a b x y chi psi (alpha, beta) * p x y a b * g.input chi psi (x, y)

/-- Membership as an operation on all arrays; used for the direct LOSR inclusion. -/
def IsGW {s t : BellScenario} (w : BellOperation s t) : Prop :=
  ∃ g : GlobalWiring s t, ∀ p, w p = g.apply p

/-- PDF p.15, (G1): four one-party kernels, without a shared hidden variable. -/
structure UncorrelatedWiring (s t : BellScenario) where
  inputAlice : t.X → s.X → ℝ
  inputBob : t.Y → s.Y → ℝ
  outputAlice : s.A → s.X → t.X → t.A → ℝ
  outputBob : s.B → s.Y → t.Y → t.B → ℝ
  inputAliceLaw : ∀ chi, IsLaw (inputAlice chi)
  inputBobLaw : ∀ psi, IsLaw (inputBob psi)
  outputAliceLaw : ∀ a x chi, IsLaw (outputAlice a x chi)
  outputBobLaw : ∀ b y psi, IsLaw (outputBob b y psi)

/-- PDF p.15, (G1): product input and output kernels act on one supplied box. -/
def UncorrelatedWiring.apply {s t : BellScenario} (u : UncorrelatedWiring s t) :
    BellOperation s t :=
  fun p chi psi alpha beta => ∑ a, ∑ b, ∑ x, ∑ y,
    (u.outputAlice a x chi alpha * u.outputBob b y psi beta) * p x y a b *
      (u.inputAlice chi x * u.inputBob psi y)

/-- PDF p.10, Appendix A: after Alice's preparation outcome is communicated,
Bob either waits for his final input or measures now and communicates his outcome.
The enclosing function of Alice's outcome makes this decision adaptive. -/
inductive AfterAlice (s t : BellScenario) where
  | wait (inputBob : t.Y → s.Y) (outputAlice : t.X → t.A)
      (outputBob : t.Y → s.B → t.B)
  | measure (y : s.Y) (outputAlice : s.B → t.X → t.A)
      (outputBob : s.B → t.Y → t.B)

/-- PDF p.10, Appendix A: the symmetric continuation after Bob measures first. -/
inductive AfterBob (s t : BellScenario) where
  | wait (inputAlice : t.X → s.X) (outputAlice : t.X → s.A → t.A)
      (outputBob : t.Y → t.B)
  | measure (x : s.X) (outputAlice : s.A → t.X → t.A)
      (outputBob : s.A → t.Y → t.B)

/-- PDF pp.4,10: deterministic preparation tree. All stochastic choices, including
later local random choices, are incorporated in the input-independent shared seed.
The initial setting is fixed before the final inputs in each first-measurement branch. -/
inductive Preparation (s t : BellScenario) where
  | none (inputAlice : t.X → s.X) (inputBob : t.Y → s.Y)
      (outputAlice : t.X → s.A → t.A) (outputBob : t.Y → s.B → t.B)
  | aliceFirst (x : s.X) (continuation : s.A → AfterAlice s t)
  | bobFirst (y : s.Y) (continuation : s.B → AfterBob s t)

/-- Indicator for a deterministic classical response. -/
def responseIndicator {I : Type*} (i j : I) : ℝ := if i = j then 1 else 0

/-- PDF pp.10–11, (A1)–(A4): contribution of a first Alice outcome.
Joint probabilities avoid division by the probability of an impossible transcript. -/
def aliceContribution {s t : BellScenario} (p : Behavior s) (x : s.X) (a : s.A)
    (c : AfterAlice s t) (chi : t.X) (psi : t.Y) (alpha : t.A) (beta : t.B) : ℝ :=
  match c with
  | .wait iy oa ob => ∑ b, p x (iy psi) a b * responseIndicator alpha (oa chi) *
      responseIndicator beta (ob psi b)
  | .measure y oa ob => ∑ b, p x y a b * responseIndicator alpha (oa b chi) *
      responseIndicator beta (ob b psi)

/-- PDF pp.10–11: symmetric contribution of a first Bob outcome. -/
def bobContribution {s t : BellScenario} (p : Behavior s) (y : s.Y) (b : s.B)
    (c : AfterBob s t) (chi : t.X) (psi : t.Y) (alpha : t.A) (beta : t.B) : ℝ :=
  match c with
  | .wait ix oa ob => ∑ a, p (ix chi) y a b * responseIndicator alpha (oa chi a) *
      responseIndicator beta (ob psi)
  | .measure x oa ob => ∑ a, p x y a b * responseIndicator alpha (oa a chi) *
      responseIndicator beta (ob a psi)

/-- PDF pp.4,10–11: exact action of the operational preparation tree. -/
def Preparation.apply {s t : BellScenario} (r : Preparation s t) : BellOperation s t :=
  fun p chi psi alpha beta =>
    match r with
    | .none ix iy oa ob => ∑ a, ∑ b, p (ix chi) (iy psi) a b *
        responseIndicator alpha (oa chi a) * responseIndicator beta (ob psi b)
    | .aliceFirst x next => ∑ a, aliceContribution p x a (next a) chi psi alpha beta
    | .bobFirst y next => ∑ b, bobContribution p y b (next b) chi psi alpha beta

/-- PDF pp.10–11: a branch in which at least one box is measured during
preparation. The no-preparation branch of (A5) is separately one fixed LOSR map. -/
def Preparation.isPrepared {s t : BellScenario} (r : Preparation s t) : Prop :=
  match r with
  | .none _ _ _ _ => False
  | .aliceFirst _ _ => True
  | .bobFirst _ _ => True

/-- PDF pp.4,10–11: operational WPICC using the proof convention of (A5).
The no-preparation branch is one fixed Eq.(7) LOSR map. The other branch
averages adaptive trees in which at least one party measures before final inputs.
This keeps Eq.(7)'s separate input/output seeds; it does not silently replace its
LOSR class by a convex hull of complete no-preparation strategies. Weight, map,
seed law and trees precede every supplied behavior. Only NS inputs are constrained.
Locality of the prepared action is a theorem conclusion, not part of this definition. -/
def IsWPICC {s t : BellScenario} (w : BellOperation s t) : Prop :=
  ∃ (weight : ℝ), 0 ≤ weight ∧ weight ≤ 1 ∧
    ∃ (v : BellOperation s t), IsLOSR v ∧
      ∃ (L : Type) (mu : PMF L) (r : L → Preparation s t),
        (∀ l, (r l).isPrepared) ∧
        ∀ p, IsNS p → ∀ chi psi alpha beta,
          w p chi psi alpha beta =
            weight * (∑' l, (mu l).toReal * (r l).apply p chi psi alpha beta) +
              (1 - weight) * v p chi psi alpha beta

/-- Equality on the common physical domain, not on arbitrary raw extensions. -/
def AgreeOnNS {s t : BellScenario} (w v : BellOperation s t) : Prop :=
  ∀ p, IsNS p → w p = v p

/-- PDF p.6, (19): whether any GW has the same action on every NS behavior. -/
def HasGWRestriction {s t : BellScenario} (w : BellOperation s t) : Prop :=
  ∃ g : GlobalWiring s t, AgreeOnNS w g.apply

/-- Whether any LOSR operation agrees on the whole NS domain. -/
def HasLOSRRestriction {s t : BellScenario} (w : BellOperation s t) : Prop :=
  ∃ v : BellOperation s t, IsLOSR v ∧ AgreeOnNS w v

/-- PDF p.5, (14): extended finite-alphabet KL, in the displayed orientation.
Only the total KL is converted to ENNReal; negative individual summands are
retained. A positive numerator over zero gives infinity; zero terms give zero. -/
def classicalRelativeEntropyNats {I : Type*} [Fintype I] (p q : I → ℝ) : ℝ≥0∞ :=
  if ∃ i, 0 < p i ∧ q i = 0 then ⊤
  else ENNReal.ofReal (∑ i, p i * Real.log (p i / q i))

/-- PDF p.5, (16): maximization over one fixed joint input, for all behaviors. -/
def sb {s : BellScenario} (p q : Behavior s) : ℝ≥0∞ :=
  ⨆ x : s.X, ⨆ y : s.Y,
    classicalRelativeEntropyNats (fun z : s.A × s.B => p x y z.1 z.2)
      (fun z : s.A × s.B => q x y z.1 z.2)

-- PDF pp.5,7: use the accepted finite Law and its prob/nonneg/total fields.

/-- PDF p.5, (15): same input law for both compared behaviors.
ENNReal's zero times infinity is zero, including unused support-mismatch inputs. -/
def weightedEntropy {s : BellScenario} (p q : Behavior s) (d : s.X × s.Y → ℝ) : ℝ≥0∞ :=
  ∑ z : s.X × s.Y, ENNReal.ofReal (d z) *
    classicalRelativeEntropyNats (fun o : s.A × s.B => p z.1 z.2 o.1 o.2)
      (fun o : s.A × s.B => q z.1 z.2 o.1 o.2)

/-- PDF p.7, (21): all local comparison boxes, on exactly the same alphabets. -/
def snl {s : BellScenario} (p : Behavior s) : ℝ≥0∞ :=
  ⨅ q : {q : Behavior s // HasLocalModel q}, sb p q.val

/-- Inner local minimization in (22); extrema are certified in `OptimaAttained`. -/
def localDistance {s : BellScenario} (p : Behavior s) (d : s.X × s.Y → ℝ) : ℝ≥0∞ :=
  ⨅ q : {q : Behavior s // HasLocalModel q}, weightedEntropy p q.val d

/-- PDF p.7, (22a): uniform *joint* input distribution. The positive sizes
in `BellScenario` exclude division by zero. -/
def uniformInput (s : BellScenario) : s.X × s.Y → ℝ :=
  fun _ => 1 / ((s.nX * s.nY : ℕ) : ℝ)

/-- PDF p.7, (22a): uniform-input statistical strength. -/
def su {s : BellScenario} (p : Behavior s) : ℝ≥0∞ := localDistance p (uniformInput s)

/-- PDF p.7, (22b): max over product laws, outside the local minimum. -/
def suc {s : BellScenario} (p : Behavior s) : ℝ≥0∞ :=
  ⨆ dx : Law s.X, ⨆ dy : Law s.Y,
    localDistance p (fun z => dx.prob z.1 * dy.prob z.2)

/-- PDF p.7, (22c): max over all joint laws, outside the local minimum. -/
def correlatedInputStrength {s : BellScenario} (p : Behavior s) : ℝ≥0∞ :=
  ⨆ d : Law (s.X × s.Y), localDistance p d.prob

/-- Explicit meaning of the source's real-valued min/max notation in (21),(22).
Every local minimum and both outer maxima are attained. These are conclusions,
not hypotheses restricting the behaviors in any headline theorem. -/
def OptimaAttained {s : BellScenario} (p : Behavior s) : Prop :=
  snl p ≠ ⊤ ∧ su p ≠ ⊤ ∧ suc p ≠ ⊤ ∧ correlatedInputStrength p ≠ ⊤ ∧
  (∃ q : Behavior s, HasLocalModel q ∧ sb p q = snl p) ∧
  (∀ d : Law (s.X × s.Y),
    ∃ q : Behavior s, HasLocalModel q ∧ weightedEntropy p q d.prob = localDistance p d.prob) ∧
  (∃ q : Behavior s, HasLocalModel q ∧ weightedEntropy p q (uniformInput s) = su p) ∧
  (∃ (dx : Law s.X) (dy : Law s.Y),
    localDistance p (fun z => dx.prob z.1 * dy.prob z.2) = suc p) ∧
  (∃ d : Law (s.X × s.Y), localDistance p d.prob = correlatedInputStrength p)

/-- Families over every finite Bell scenario; only values on NS are relevant. -/
abbrev Quantity := (s : BellScenario) → Behavior s → ℝ≥0∞

/-- PDF p.6, Definition 5(i), including finite nonnegative real values on NS. -/
def IsNormalizedQuantity (f : Quantity) : Prop :=
  (∀ s p, IsNS p → f s p ≠ ⊤) ∧ (∀ s p, HasLocalModel p → f s p = 0)

/-- PDF p.6, Definition 5: LOSR monotonicity includes vanishing on local boxes. -/
def IsLOSRMonotone (f : Quantity) : Prop :=
  IsNormalizedQuantity f ∧
    ∀ (s t : BellScenario) (w : BellOperation s t), IsLOSR w →
      ∀ p, IsNS p → f t (w p) ≤ f s p

/-- PDF p.6, Definition 5: WPICC monotonicity, allowing alphabet changes. -/
def IsWPICCMonotone (f : Quantity) : Prop :=
  IsNormalizedQuantity f ∧
    ∀ (s t : BellScenario) (w : BellOperation s t), IsWPICC w →
      ∀ p, IsNS p → f t (w p) ≤ f s p

/-- PDF p.6, Definition 7: monotonicity for both equivalent choices of free class.
The numbered Lemma 6 supplies their equivalence, without convexity. -/
def IsBellMonotone (f : Quantity) : Prop := IsLOSRMonotone f ∧ IsWPICCMonotone f

/-! Definition sanity checks: no source result is proved here. -/

/-- Singleton scenario used only to check nonempty boundary conventions. -/
def singletonScenario : BellScenario :=
  ⟨1, 1, 1, 1, by decide, by decide, by decide, by decide⟩

example : IsNS (s := singletonScenario) (fun _ _ _ _ => (1 : ℝ)) := by
  change IsCorrelation (fun (_ _ _ _ : Fin 1) => (1 : ℝ)) ∧
    IsNoSignaling (fun (_ _ _ _ : Fin 1) => (1 : ℝ))
  constructor
  · simp [IsCorrelation]
  · simp [IsNoSignaling]

example : uniformInput singletonScenario ((0 : Fin 1), (0 : Fin 1)) = 1 := by
  change (1 : ℝ) / ((1 * 1 : ℕ) : ℝ) = 1
  norm_num

example {s : BellScenario} (p q : Behavior s) : correlationMixture p q 0 = q := by
  funext x y a b
  simp [correlationMixture]

example {s : BellScenario} (p q : Behavior s) : correlationMixture p q 1 = p := by
  funext x y a b
  simp [correlationMixture]

example : classicalRelativeEntropyNats (fun _ : Unit => (1 : ℝ)) (fun _ => 1) = 0 := by
  simp [classicalRelativeEntropyNats]

example : classicalRelativeEntropyNats (fun _ : Unit => (1 : ℝ)) (fun _ => 0) = ⊤ := by
  simp [classicalRelativeEntropyNats]

example : classicalRelativeEntropyNats (fun _ : Unit => (0 : ℝ)) (fun _ => 0) = 0 := by
  simp [classicalRelativeEntropyNats]

example {s t : BellScenario} (p : Behavior s) (x : s.X) (a : s.A)
    (y : s.Y) (oa : s.B → t.X → t.A) (ob : s.B → t.Y → t.B)
    (chi : t.X) (psi : t.Y) (alpha : t.A) (beta : t.B) :
    aliceContribution p x a (.measure y oa ob) chi psi alpha beta =
      ∑ b, p x y a b * responseIndicator alpha (oa b chi) * responseIndicator beta (ob b psi) := by
  rfl

example {s t : BellScenario} (y : s.Y) (next : s.B → AfterBob s t) :
    (Preparation.bobFirst y next).isPrepared := by
  simp [Preparation.isPrepared]

example {s t : BellScenario} (ix : t.X → s.X) (iy : t.Y → s.Y)
    (oa : t.X → s.A → t.A) (ob : t.Y → s.B → t.B) :
    ¬ (Preparation.none ix iy oa ob).isPrepared := by
  simp [Preparation.isPrepared]

end QAlgorithms.Papers.Independent.Intakethird100.P29


