-- Prove2me | Definitions.Def_OAIQ084L001
-- name    : OAIQ084L001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:21:14.949958+00:00
-- url     : https://prove2.me/theorems/36aee124-fbd9-4f64-bdc4-a80bb0d96032
-- title:
--   Definitions bundle OAIQ084L001 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 85 declarations of OpenAI's Lean: 67 definitions, 9 instances and 9 theorems. The definitions and types are `OAI.LaughlinFock.congruenceLinear`, `OAI.LaughlinFock.couplingPolynomial`, `OAI.LaughlinFock.crossOrbitContinuousENorm`, `OAI.LaughlinFock.directIntegerSum`, `OAI.LaughlinFock.entryNormBound`, `OAI.LaughlinFock.euler`, `OAI.LaughlinFock.fallingRatio`, `OAI.LaughlinFock.fastIntegerCopyPolynomial`, `OAI.LaughlinFock.fastIntegerCoupling`, `OAI.LaughlinFock.fourCommonDenominator`, `OAI.LaughlinFock.fourSpinDegree`, `OAI.LaughlinFock.gramShift`, `OAI.LaughlinFock.instContinuousENormMatrixComplexOfFintype_solutions`, `OAI.LaughlinFock.integerCopyPolynomial`, `OAI.LaughlinFock.integerCoupling`, `OAI.LaughlinFock.limitPairCoefficient`, `OAI.LaughlinFock.localFourScale`, `OAI.LaughlinFock.matrixEntriesDecidable`, `OAI.LaughlinFock.memoIntegerCopyPolynomial`, `OAI.LaughlinFock.memoUnitCoupling`, `OAI.LaughlinFock.modeScale`, `OAI.LaughlinFock.monomialCoefficient`, `OAI.LaughlinFock.monomialWeight`, `OAI.LaughlinFock.pairScale`, `OAI.LaughlinFock.pairTensorNormalizer`, `OAI.LaughlinFock.planarCopyCoefficient`, `OAI.LaughlinFock.planarThreeCoefficient`, `OAI.LaughlinFock.polynomialCouplingCoefficient`, `OAI.LaughlinFock.quadraticEvaluation`, `OAI.LaughlinFock.rationalCopyDiagonal`, `OAI.LaughlinFock.rationalCopyPolynomial`, `OAI.LaughlinFock.rationalCopyWeight`, `OAI.LaughlinFock.rationalCoupling`, `OAI.LaughlinFock.rationalCouplingWeight`, `OAI.LaughlinFock.scaledDescFactorial`, `OAI.LaughlinFock.sphericalPairCoefficient`, `OAI.LaughlinFock.spinRatio`, `OAI.LaughlinFock.tailCoefficient`, `OAI.LaughlinFock.tailTerm`, `OAI.LaughlinFock.tensorSum` and 27 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `LaughlinFock_CouplingTables`, `LaughlinFock_CrossOrbit`, `LaughlinFock_FastCoupling`, `LaughlinFock_FastTrace`, `LaughlinFock_FasterTrace`, `LaughlinFock_FockRotations`, `LaughlinFock_FourCoefficients`, `LaughlinFock_FourCopies`, `LaughlinFock_IntegerCoupling`, `LaughlinFock_IntegerFour`, `LaughlinFock_LDL`, `LaughlinFock_LocalEnergy`, `LaughlinFock_OscillatorLimit`, `LaughlinFock_PairIdentification`, `LaughlinFock_PairNormalization`, `LaughlinFock_PositiveIntegrals`, `LaughlinFock_RationalCoupling`, `LaughlinFock_RationalFour`, `LaughlinFock_RelativePerturbation`, `LaughlinFock_Rotations`, `LaughlinFock_RowTraces`, `LaughlinFock_SphereScaling`, `LaughlinFock_SpinTails`, `LaughlinFock_TableTrace`, `LaughlinFock_TensorBasis`, `LaughlinFock_WedgeLie`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ084L008`, `OAIQ084L009`, `OAIQ084L012`, `OAIQ084L013`, `OAIQ084L014`, `OAIQ084L015`, `OAIQ084L017`, `OAIQ084L018` and `OAIQ084L020`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ084_LF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PairNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Normalization. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
def euler (P : ℝ[X]) : ℝ[X] := X * derivative P
def variance (P : ℝ[X]) : ℝ[X] := euler (euler P) * P - (euler P)^2
end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SphereScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sphere Scaling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology

open Filter Topology

 
def scaledDescFactorial (Q s p : ℕ) : ℝ :=
  ((Q-s).descFactorial p : ℝ) / (Q : ℝ)^p


def modeScale (Q x : ℕ) : ℝ := Real.sqrt (scaledDescFactorial Q 0 x)

 
def pairScale (Q p : ℕ) : ℝ := Real.sqrt ((scaledDescFactorial (2*Q) 2 p)⁻¹)


def limitPairCoefficient (p i j : ℕ) : ℝ :=
  if i+j=p+1 then
    ((i:ℝ)-(j:ℝ)) * Real.sqrt ((p.factorial:ℝ) / (2^p * i.factorial * j.factorial))
  else 0

 
def sphericalPairCoefficient (Q p i j : ℕ) : ℝ :=
  if i+j=p+1 then
    ((i:ℝ)-(j:ℝ)) * Real.sqrt
      (((Q.descFactorial i:ℝ)*(Q.descFactorial j:ℝ)*(p.factorial:ℝ)) /
       ((Q:ℝ)*((2*Q-2).descFactorial p:ℝ)*(i.factorial:ℝ)*(j.factorial:ℝ)))
  else 0

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_LocalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local Energy. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
open Filter Topology



def entryNormBound {ι κ : Type*} [Fintype ι] [Fintype κ] (R : Matrix ι κ ℂ) : ℝ :=
  ∑ i, ∑ j, ‖R i j‖

open Filter Topology

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RelativePerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Perturbation. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
open Filter Topology
open Filter Topology
open scoped Kronecker


def localFourScale (Q p j k : ℕ) : ℝ :=
  pairScale Q p / (modeScale Q j * modeScale Q k)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_OscillatorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Oscillator Limit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators
open Polynomial
open Filter Topology

 

def monomialWeight (T p : ℕ) : ℝ :=
  Real.sqrt ((p.factorial : ℝ) * (T-p).factorial)

def monomialCoefficient (T : ℕ) (P : Polynomial ℝ) (p : ℕ) : ℝ :=
  monomialWeight T p * P.coeff p



def couplingPolynomial (u v : ℝ) (z k : ℕ) : Polynomial ℝ :=
  (C u * X - C v)^z * (C v * X + C u)^k

def polynomialCouplingCoefficient (u v : ℝ) (z k p : ℕ) : ℝ :=
  monomialCoefficient (z+k) (couplingPolynomial u v z k) p /
    Real.sqrt ((z.factorial : ℝ) * k.factorial)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Coefficients. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators
open Filter Topology



def planarCopyCoefficient (D T r p j k : ℕ) : ℝ :=
  if Odd r ∧ r ≤ D ∧ D ≤ T ∧ r ≤ j+k ∧ p+j+k = T then
    Real.sqrt 2 * polynomialCouplingCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) r (j+k-r) j *
      polynomialCouplingCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) (D-r) (T-D) p
  else 0



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_TensorBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor Basis. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators


theorem sum_affine_integer (N : ℕ) (a : ℤ) :
    (∑ z ∈ Finset.range N, (a-2*z)) = (N : ℤ)*a - (N : ℤ)*((N : ℤ)-1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PairIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Identification. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators



def pairTensorNormalizer (Q p : ℕ) : ℝ :=
  Real.sqrt (2*(Q:ℝ)*((2*Q-2).choose p : ℝ))

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SpinTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin Tails. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology

 
def fallingRatio (Q z : ℕ) : ℝ :=
  (Q.descFactorial z : ℝ) / ((2 * Q - 2).descFactorial z : ℝ)

 

def gramShift (Q z : ℕ) : ℝ :=
  (-1 : ℝ)^z * fallingRatio Q z * (3 * z - 1 - z * (z + 1) / Q)


def spinRatio (Q z : ℕ) : ℝ :=
  (3 * Q - 1 - 2 * (z : ℝ)) / (2 * Q - 1)



def tailTerm (Q m : ℕ) : ℝ :=
  let z := 17 + 2*m
  if z ≤ Q then spinRatio Q z * |gramShift Q z| * (z+1) else 0

 
def tailCoefficient (Q : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (Q+1), tailTerm Q m



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RowTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology



def planarThreeCoefficient (z T p : ℕ) : ℝ :=
  if z ≤ T then polynomialCouplingCoefficient (Real.sqrt (1/3)) (Real.sqrt (2/3))
    z (T-z) p else 0

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RationalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open Polynomial

 
def rationalCoupling (c : ℚ) (z k p : ℕ) : ℚ :=
  (((X-1)^z * (C c*X+1)^k) : Polynomial ℚ).coeff p

 

def rationalCouplingWeight (c : ℚ) (z k p : ℕ) : ℚ :=
  c^z * ((p.factorial : ℚ) * (z+k-p).factorial) /
    ((1+c)^(z+k) * c^p * (z.factorial : ℚ) * k.factorial)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RationalFour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Four. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def rationalCopyDiagonal (D r : ℕ) : ℚ :=
  2^r / ((r.factorial : ℚ) * (D-r).factorial)

def rationalCopyPolynomial (D T r p j k : ℕ) : ℚ :=
  if r ≤ j+k then
    rationalCoupling 1 r (j+k-r) j * rationalCoupling 1 (D-r) (T-D) p
  else 0

def rationalCopyWeight (D T p j k : ℕ) : ℚ :=
  2 * (j.factorial : ℚ) * k.factorial * p.factorial /
    (2^(j+k+T) * ((T-D).factorial : ℚ))

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_IntegerCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators
open Polynomial

 
def integerCoupling (c : ℤ) (z k p : ℕ) : ℤ :=
  ∑ h ∈ Finset.range (p+1), (-1)^(z-h) * (z.choose h : ℤ) *
    (k.choose (p-h) : ℤ) * c^(p-h)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_IntegerFour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer Four. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def integerCopyPolynomial (D T r p j k : ℕ) : ℤ :=
  if r ≤ j+k then
    integerCoupling 1 r (j+k-r) j * integerCoupling 1 (D-r) (T-D) p
  else 0

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FastCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
 
def fastIntegerCoupling (c : ℤ) (z k p : ℕ) : ℤ :=
  ∑ h ∈ Finset.range (p+1), (-1)^(z-h) * (Nat.fast_choose z h : ℤ) *
    (Nat.fast_choose k (p-h) : ℤ) * c^(p-h)

def fastIntegerCopyPolynomial (D T r p j k : ℕ) : ℤ :=
  if r ≤ j+k then
    fastIntegerCoupling 1 r (j+k-r) j * fastIntegerCoupling 1 (D-r) (T-D) p
  else 0

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CouplingTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coupling Tables. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
def unitCouplingData_0 : List (List ℤ) := [
  [1, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 1, 0, 0, 0, 0, 0, 0, 0],
  [1, 2, 1, 0, 0, 0, 0, 0, 0],
  [1, 3, 3, 1, 0, 0, 0, 0, 0],
  [1, 4, 6, 4, 1, 0, 0, 0, 0],
  [1, 5, 10, 10, 5, 1, 0, 0, 0],
  [1, 6, 15, 20, 15, 6, 1, 0, 0],
  [1, 7, 21, 35, 35, 21, 7, 1, 0],
  [1, 8, 28, 56, 70, 56, 28, 8, 1],
  [1, 9, 36, 84, 126, 126, 84, 36, 9],
  [1, 10, 45, 120, 210, 252, 210, 120, 45],
  [1, 11, 55, 165, 330, 462, 462, 330, 165],
  [1, 12, 66, 220, 495, 792, 924, 792, 495],
  [1, 13, 78, 286, 715, 1287, 1716, 1716, 1287],
  [1, 14, 91, 364, 1001, 2002, 3003, 3432, 3003],
  [1, 15, 105, 455, 1365, 3003, 5005, 6435, 6435],
  [1, 16, 120, 560, 1820, 4368, 8008, 11440, 12870],
  [1, 17, 136, 680, 2380, 6188, 12376, 19448, 24310],
  [1, 18, 153, 816, 3060, 8568, 18564, 31824, 43758],
  [1, 19, 171, 969, 3876, 11628, 27132, 50388, 75582],
  [1, 20, 190, 1140, 4845, 15504, 38760, 77520, 125970],
  [1, 21, 210, 1330, 5985, 20349, 54264, 116280, 203490],
  [1, 22, 231, 1540, 7315, 26334, 74613, 170544, 319770],
  [1, 23, 253, 1771, 8855, 33649, 100947, 245157, 490314]
]

def unitCouplingData_1 : List (List ℤ) := [
  [-1, 1, 0, 0, 0, 0, 0, 0, 0],
  [-1, 0, 1, 0, 0, 0, 0, 0, 0],
  [-1, -1, 1, 1, 0, 0, 0, 0, 0],
  [-1, -2, 0, 2, 1, 0, 0, 0, 0],
  [-1, -3, -2, 2, 3, 1, 0, 0, 0],
  [-1, -4, -5, 0, 5, 4, 1, 0, 0],
  [-1, -5, -9, -5, 5, 9, 5, 1, 0],
  [-1, -6, -14, -14, 0, 14, 14, 6, 1],
  [-1, -7, -20, -28, -14, 14, 28, 20, 7],
  [-1, -8, -27, -48, -42, 0, 42, 48, 27],
  [-1, -9, -35, -75, -90, -42, 42, 90, 75],
  [-1, -10, -44, -110, -165, -132, 0, 132, 165],
  [-1, -11, -54, -154, -275, -297, -132, 132, 297],
  [-1, -12, -65, -208, -429, -572, -429, 0, 429],
  [-1, -13, -77, -273, -637, -1001, -1001, -429, 429],
  [-1, -14, -90, -350, -910, -1638, -2002, -1430, 0],
  [-1, -15, -104, -440, -1260, -2548, -3640, -3432, -1430],
  [-1, -16, -119, -544, -1700, -3808, -6188, -7072, -4862],
  [-1, -17, -135, -663, -2244, -5508, -9996, -13260, -11934],
  [-1, -18, -152, -798, -2907, -7752, -15504, -23256, -25194],
  [-1, -19, -170, -950, -3705, -10659, -23256, -38760, -48450],
  [-1, -20, -189, -1120, -4655, -14364, -33915, -62016, -87210],
  [-1, -21, -209, -1309, -5775, -19019, -48279, -95931, -149226],
  [-1, -22, -230, -1518, -7084, -24794, -67298, -144210, -245157]
]

def unitCouplingData_2 : List (List ℤ) := [
  [1, -2, 1, 0, 0, 0, 0, 0, 0],
  [1, -1, -1, 1, 0, 0, 0, 0, 0],
  [1, 0, -2, 0, 1, 0, 0, 0, 0],
  [1, 1, -2, -2, 1, 1, 0, 0, 0],
  [1, 2, -1, -4, -1, 2, 1, 0, 0],
  [1, 3, 1, -5, -5, 1, 3, 1, 0],
  [1, 4, 4, -4, -10, -4, 4, 4, 1],
  [1, 5, 8, 0, -14, -14, 0, 8, 5],
  [1, 6, 13, 8, -14, -28, -14, 8, 13],
  [1, 7, 19, 21, -6, -42, -42, -6, 21],
  [1, 8, 26, 40, 15, -48, -84, -48, 15],
  [1, 9, 34, 66, 55, -33, -132, -132, -33],
  [1, 10, 43, 100, 121, 22, -165, -264, -165],
  [1, 11, 53, 143, 221, 143, -143, -429, -429],
  [1, 12, 64, 196, 364, 364, 0, -572, -858],
  [1, 13, 76, 260, 560, 728, 364, -572, -1430],
  [1, 14, 89, 336, 820, 1288, 1092, -208, -2002],
  [1, 15, 103, 425, 1156, 2108, 2380, 884, -2210],
  [1, 16, 118, 528, 1581, 3264, 4488, 3264, -1326],
  [1, 17, 134, 646, 2109, 4845, 7752, 7752, 1938],
  [1, 18, 151, 780, 2755, 6954, 12597, 15504, 9690],
  [1, 19, 169, 931, 3535, 9709, 19551, 28101, 25194],
  [1, 20, 188, 1100, 4466, 13244, 29260, 47652, 53295],
  [1, 21, 208, 1288, 5566, 17710, 42504, 76912, 100947]
]

def unitCouplingData_3 : List (List ℤ) := [
  [-1, 3, -3, 1, 0, 0, 0, 0, 0],
  [-1, 2, 0, -2, 1, 0, 0, 0, 0],
  [-1, 1, 2, -2, -1, 1, 0, 0, 0],
  [-1, 0, 3, 0, -3, 0, 1, 0, 0],
  [-1, -1, 3, 3, -3, -3, 1, 1, 0],
  [-1, -2, 2, 6, 0, -6, -2, 2, 1],
  [-1, -3, 0, 8, 6, -6, -8, 0, 3],
  [-1, -4, -3, 8, 14, 0, -14, -8, 3],
  [-1, -5, -7, 5, 22, 14, -14, -22, -5],
  [-1, -6, -12, -2, 27, 36, 0, -36, -27],
  [-1, -7, -18, -14, 25, 63, 36, -36, -63],
  [-1, -8, -25, -32, 11, 88, 99, 0, -99],
  [-1, -9, -33, -57, -21, 99, 187, 99, -99],
  [-1, -10, -42, -90, -78, 78, 286, 286, 0],
  [-1, -11, -52, -132, -168, 0, 364, 572, 286],
  [-1, -12, -63, -184, -300, -168, 364, 936, 858],
  [-1, -13, -75, -247, -484, -468, 196, 1300, 1794],
  [-1, -14, -88, -322, -731, -952, -272, 1496, 3094],
  [-1, -15, -102, -410, -1053, -1683, -1224, 1224, 4590],
  [-1, -16, -117, -512, -1463, -2736, -2907, 0, 5814],
  [-1, -17, -133, -629, -1975, -4199, -5643, -2907, 5814],
  [-1, -18, -150, -762, -2604, -6174, -9842, -8550, 2907],
  [-1, -19, -168, -912, -3366, -8778, -16016, -18392, -5643],
  [-1, -20, -187, -1080, -4278, -12144, -24794, -34408, -24035]
]

def unitCouplingData_4 : List (List ℤ) := [
  [1, -4, 6, -4, 1, 0, 0, 0, 0],
  [1, -3, 2, 2, -3, 1, 0, 0, 0],
  [1, -2, -1, 4, -1, -2, 1, 0, 0],
  [1, -1, -3, 3, 3, -3, -1, 1, 0],
  [1, 0, -4, 0, 6, 0, -4, 0, 1],
  [1, 1, -4, -4, 6, 6, -4, -4, 1],
  [1, 2, -3, -8, 2, 12, 2, -8, -3],
  [1, 3, -1, -11, -6, 14, 14, -6, -11],
  [1, 4, 2, -12, -17, 8, 28, 8, -17],
  [1, 5, 6, -10, -29, -9, 36, 36, -9],
  [1, 6, 11, -4, -39, -38, 27, 72, 27],
  [1, 7, 17, 7, -43, -77, -11, 99, 99],
  [1, 8, 24, 24, -36, -120, -88, 88, 198],
  [1, 9, 32, 48, -12, -156, -208, 0, 286],
  [1, 10, 41, 80, 36, -168, -364, -208, 286],
  [1, 11, 51, 121, 116, -132, -532, -572, 78],
  [1, 12, 62, 172, 237, -16, -664, -1104, -494],
  [1, 13, 74, 234, 409, 221, -680, -1768, -1598],
  [1, 14, 87, 308, 643, 630, -459, -2448, -3366],
  [1, 15, 101, 395, 951, 1273, 171, -2907, -5814],
  [1, 16, 116, 496, 1346, 2224, 1444, -2736, -8721],
  [1, 17, 132, 612, 1842, 3570, 3668, -1292, -11457],
  [1, 18, 149, 744, 2454, 5412, 7238, 2376, -12749],
  [1, 19, 167, 893, 3198, 7866, 12650, 9614, -10373]
]

def unitCouplingData_5 : List (List ℤ) := [
  [-1, 5, -10, 10, -5, 1, 0, 0, 0],
  [-1, 4, -5, 0, 5, -4, 1, 0, 0],
  [-1, 3, -1, -5, 5, 1, -3, 1, 0],
  [-1, 2, 2, -6, 0, 6, -2, -2, 1],
  [-1, 1, 4, -4, -6, 6, 4, -4, -1],
  [-1, 0, 5, 0, -10, 0, 10, 0, -5],
  [-1, -1, 5, 5, -10, -10, 10, 10, -5],
  [-1, -2, 4, 10, -5, -20, 0, 20, 5],
  [-1, -3, 2, 14, 5, -25, -20, 20, 25],
  [-1, -4, -1, 16, 19, -20, -45, 0, 45],
  [-1, -5, -5, 15, 35, -1, -65, -45, 45],
  [-1, -6, -10, 10, 50, 34, -66, -110, 0],
  [-1, -7, -16, 0, 60, 84, -32, -176, -110],
  [-1, -8, -23, -16, 60, 144, 52, -208, -286],
  [-1, -9, -31, -39, 44, 204, 196, -156, -494],
  [-1, -10, -40, -70, 5, 248, 400, 40, -650],
  [-1, -11, -50, -110, -65, 253, 648, 440, -610],
  [-1, -12, -61, -160, -175, 188, 901, 1088, -170],
  [-1, -13, -73, -221, -335, 13, 1089, 1989, 918],
  [-1, -14, -86, -294, -556, -322, 1102, 3078, 2907],
  [-1, -15, -100, -380, -850, -878, 780, 4180, 5985],
  [-1, -16, -115, -480, -1230, -1728, -98, 4960, 10165],
  [-1, -17, -131, -595, -1710, -2958, -1826, 4862, 15125],
  [-1, -18, -148, -726, -2305, -4668, -4784, 3036, 19987]
]

def unitCouplingData_6 : List (List ℤ) := [
  [1, -6, 15, -20, 15, -6, 1, 0, 0],
  [1, -5, 9, -5, -5, 9, -5, 1, 0],
  [1, -4, 4, 4, -10, 4, 4, -4, 1],
  [1, -3, 0, 8, -6, -6, 8, 0, -3],
  [1, -2, -3, 8, 2, -12, 2, 8, -3],
  [1, -1, -5, 5, 10, -10, -10, 10, 5],
  [1, 0, -6, 0, 15, 0, -20, 0, 15],
  [1, 1, -6, -6, 15, 15, -20, -20, 15],
  [1, 2, -5, -12, 9, 30, -5, -40, -5],
  [1, 3, -3, -17, -3, 39, 25, -45, -45],
  [1, 4, 0, -20, -20, 36, 64, -20, -90],
  [1, 5, 4, -20, -40, 16, 100, 44, -110],
  [1, 6, 9, -16, -60, -24, 116, 144, -66],
  [1, 7, 15, -7, -76, -84, 92, 260, 78],
  [1, 8, 22, 8, -83, -160, 8, 352, 338],
  [1, 9, 30, 30, -75, -243, -152, 360, 690],
  [1, 10, 39, 60, -45, -318, -395, 208, 1050],
  [1, 11, 49, 99, 15, -363, -713, -187, 1258],
  [1, 12, 60, 148, 114, -348, -1076, -900, 1071],
  [1, 13, 72, 208, 262, -234, -1424, -1976, 171],
  [1, 14, 85, 280, 470, 28, -1658, -3400, -1805],
  [1, 15, 99, 365, 750, 498, -1630, -5058, -5205],
  [1, 16, 114, 464, 1115, 1248, -1132, -6688, -10263],
  [1, 17, 130, 578, 1579, 2363, 116, -7820, -16951]
]

def unitCouplingData_7 : List (List ℤ) := [
  [-1, 7, -21, 35, -35, 21, -7, 1, 0],
  [-1, 6, -14, 14, 0, -14, 14, -6, 1],
  [-1, 5, -8, 0, 14, -14, 0, 8, -5],
  [-1, 4, -3, -8, 14, 0, -14, 8, 3],
  [-1, 3, 1, -11, 6, 14, -14, -6, 11],
  [-1, 2, 4, -10, -5, 20, 0, -20, 5],
  [-1, 1, 6, -6, -15, 15, 20, -20, -15],
  [-1, 0, 7, 0, -21, 0, 35, 0, -35],
  [-1, -1, 7, 7, -21, -21, 35, 35, -35],
  [-1, -2, 6, 14, -14, -42, 14, 70, 0],
  [-1, -3, 4, 20, 0, -56, -28, 84, 70],
  [-1, -4, 1, 24, 20, -56, -84, 56, 154],
  [-1, -5, -3, 25, 44, -36, -140, -28, 210],
  [-1, -6, -8, 22, 69, 8, -176, -168, 182],
  [-1, -7, -14, 14, 91, 77, -168, -344, 14],
  [-1, -8, -21, 0, 105, 168, -91, -512, -330],
  [-1, -9, -29, -21, 105, 273, 77, -603, -842],
  [-1, -10, -38, -50, 84, 378, 350, -526, -1445],
  [-1, -11, -48, -88, 34, 462, 728, -176, -1971],
  [-1, -12, -59, -136, -54, 496, 1190, 552, -2147],
  [-1, -13, -71, -195, -190, 442, 1686, 1742, -1595],
  [-1, -14, -84, -266, -385, 252, 2128, 3428, 147],
  [-1, -15, -98, -350, -651, -133, 2380, 5556, 3575],
  [-1, -16, -113, -448, -1001, -784, 2247, 7936, 9131]
]

def unitCouplingData_8 : List (List ℤ) := [
  [1, -8, 28, -56, 70, -56, 28, -8, 1],
  [1, -7, 20, -28, 14, 14, -28, 20, -7],
  [1, -6, 13, -8, -14, 28, -14, -8, 13],
  [1, -5, 7, 5, -22, 14, 14, -22, 5],
  [1, -4, 2, 12, -17, -8, 28, -8, -17],
  [1, -3, -2, 14, -5, -25, 20, 20, -25],
  [1, -2, -5, 12, 9, -30, -5, 40, -5],
  [1, -1, -7, 7, 21, -21, -35, 35, 35],
  [1, 0, -8, 0, 28, 0, -56, 0, 70],
  [1, 1, -8, -8, 28, 28, -56, -56, 70],
  [1, 2, -7, -16, 20, 56, -28, -112, 14],
  [1, 3, -5, -23, 4, 76, 28, -140, -98],
  [1, 4, -2, -28, -19, 80, 104, -112, -238],
  [1, 5, 2, -30, -47, 61, 184, -8, -350],
  [1, 6, 7, -28, -77, 14, 245, 176, -358],
  [1, 7, 13, -21, -105, -63, 259, 421, -182],
  [1, 8, 20, -8, -126, -168, 196, 680, 239],
  [1, 9, 28, 12, -134, -294, 28, 876, 919],
  [1, 10, 37, 40, -122, -428, -266, 904, 1795],
  [1, 11, 47, 77, -82, -550, -694, 638, 2699],
  [1, 12, 58, 124, -5, -632, -1244, -56, 3337],
  [1, 13, 70, 182, 119, -637, -1876, -1300, 3281],
  [1, 14, 83, 252, 301, -518, -2513, -3176, 1981],
  [1, 15, 97, 335, 553, -217, -3031, -5689, -1195]
]

def unitCouplingData_9 : List (List ℤ) := [
  [-1, 9, -36, 84, -126, 126, -84, 36, -9],
  [-1, 8, -27, 48, -42, 0, 42, -48, 27],
  [-1, 7, -19, 21, 6, -42, 42, -6, -21],
  [-1, 6, -12, 2, 27, -36, 0, 36, -27],
  [-1, 5, -6, -10, 29, -9, -36, 36, 9],
  [-1, 4, -1, -16, 19, 20, -45, 0, 45],
  [-1, 3, 3, -17, 3, 39, -25, -45, 45],
  [-1, 2, 6, -14, -14, 42, 14, -70, 0],
  [-1, 1, 8, -8, -28, 28, 56, -56, -70],
  [-1, 0, 9, 0, -36, 0, 84, 0, -126],
  [-1, -1, 9, 9, -36, -36, 84, 84, -126],
  [-1, -2, 8, 18, -27, -72, 48, 168, -42],
  [-1, -3, 6, 26, -9, -99, -24, 216, 126],
  [-1, -4, 3, 32, 17, -108, -123, 192, 342],
  [-1, -5, -1, 35, 49, -91, -231, 69, 534],
  [-1, -6, -6, 34, 84, -42, -322, -162, 603],
  [-1, -7, -12, 28, 118, 42, -364, -484, 441],
  [-1, -8, -19, 16, 146, 160, -322, -848, -43],
  [-1, -9, -27, -3, 162, 306, -162, -1170, -891],
  [-1, -10, -36, -30, 159, 468, 144, -1332, -2061],
  [-1, -11, -46, -66, 129, 627, 612, -1188, -3393],
  [-1, -12, -57, -112, 63, 756, 1239, -576, -4581],
  [-1, -13, -69, -169, -49, 819, 1995, 663, -5157],
  [-1, -14, -82, -238, -218, 770, 2814, 2658, -4494]
]

def unitCouplingData_10 : List (List ℤ) := [
  [1, -10, 45, -120, 210, -252, 210, -120, 45],
  [1, -9, 35, -75, 90, -42, -42, 90, -75],
  [1, -8, 26, -40, 15, 48, -84, 48, 15],
  [1, -7, 18, -14, -25, 63, -36, -36, 63],
  [1, -6, 11, 4, -39, 38, 27, -72, 27],
  [1, -5, 5, 15, -35, -1, 65, -45, -45],
  [1, -4, 0, 20, -20, -36, 64, 20, -90],
  [1, -3, -4, 20, 0, -56, 28, 84, -70],
  [1, -2, -7, 16, 20, -56, -28, 112, 14],
  [1, -1, -9, 9, 36, -36, -84, 84, 126],
  [1, 0, -10, 0, 45, 0, -120, 0, 210],
  [1, 1, -10, -10, 45, 45, -120, -120, 210],
  [1, 2, -9, -20, 35, 90, -75, -240, 90],
  [1, 3, -7, -29, 15, 125, 15, -315, -150],
  [1, 4, -4, -36, -14, 140, 140, -300, -465],
  [1, 5, 0, -40, -50, 126, 280, -160, -765],
  [1, 6, 5, -40, -90, 76, 406, 120, -925],
  [1, 7, 11, -35, -130, -14, 482, 526, -805],
  [1, 8, 18, -24, -165, -144, 468, 1008, -279],
  [1, 9, 26, -6, -189, -309, 324, 1476, 729],
  [1, 10, 35, 20, -195, -498, 15, 1800, 2205],
  [1, 11, 45, 55, -175, -693, -483, 1815, 4005],
  [1, 12, 56, 100, -120, -868, -1176, 1332, 5820],
  [1, 13, 68, 156, -20, -988, -2044, 156, 7152]
]

def unitCouplingData_11 : List (List ℤ) := [
  [-1, 11, -55, 165, -330, 462, -462, 330, -165],
  [-1, 10, -44, 110, -165, 132, 0, -132, 165],
  [-1, 9, -34, 66, -55, -33, 132, -132, 33],
  [-1, 8, -25, 32, 11, -88, 99, 0, -99],
  [-1, 7, -17, 7, 43, -77, 11, 99, -99],
  [-1, 6, -10, -10, 50, -34, -66, 110, 0],
  [-1, 5, -4, -20, 40, 16, -100, 44, 110],
  [-1, 4, 1, -24, 20, 56, -84, -56, 154],
  [-1, 3, 5, -23, -4, 76, -28, -140, 98],
  [-1, 2, 8, -18, -27, 72, 48, -168, -42],
  [-1, 1, 10, -10, -45, 45, 120, -120, -210],
  [-1, 0, 11, 0, -55, 0, 165, 0, -330],
  [-1, -1, 11, 11, -55, -55, 165, 165, -330],
  [-1, -2, 10, 22, -44, -110, 110, 330, -165],
  [-1, -3, 8, 32, -22, -154, 0, 440, 165],
  [-1, -4, 5, 40, 10, -176, -154, 440, 605],
  [-1, -5, 1, 45, 50, -166, -330, 286, 1045],
  [-1, -6, -4, 46, 95, -116, -496, -44, 1331],
  [-1, -7, -10, 42, 141, -21, -612, -540, 1287],
  [-1, -8, -17, 32, 183, 120, -633, -1152, 747],
  [-1, -9, -25, 15, 215, 303, -513, -1785, -405],
  [-1, -10, -34, -10, 230, 518, -210, -2298, -2190],
  [-1, -11, -44, -44, 220, 748, 308, -2508, -4488],
  [-1, -12, -55, -88, 176, 968, 1056, -2200, -6996]
]

def unitCouplingData_12 : List (List ℤ) := [
  [1, -12, 66, -220, 495, -792, 924, -792, 495],
  [1, -11, 54, -154, 275, -297, 132, 132, -297],
  [1, -10, 43, -100, 121, -22, -165, 264, -165],
  [1, -9, 33, -57, 21, 99, -187, 99, 99],
  [1, -8, 24, -24, -36, 120, -88, -88, 198],
  [1, -7, 16, 0, -60, 84, 32, -176, 110],
  [1, -6, 9, 16, -60, 24, 116, -144, -66],
  [1, -5, 3, 25, -44, -36, 140, -28, -210],
  [1, -4, -2, 28, -19, -80, 104, 112, -238],
  [1, -3, -6, 26, 9, -99, 24, 216, -126],
  [1, -2, -9, 20, 35, -90, -75, 240, 90],
  [1, -1, -11, 11, 55, -55, -165, 165, 330],
  [1, 0, -12, 0, 66, 0, -220, 0, 495],
  [1, 1, -12, -12, 66, 66, -220, -220, 495],
  [1, 2, -11, -24, 54, 132, -154, -440, 275],
  [1, 3, -9, -35, 30, 186, -22, -594, -165],
  [1, 4, -6, -44, -5, 216, 164, -616, -759],
  [1, 5, -2, -50, -49, 211, 380, -452, -1375],
  [1, 6, 3, -52, -99, 162, 591, -72, -1827],
  [1, 7, 9, -49, -151, 63, 753, 519, -1899],
  [1, 8, 16, -40, -200, -88, 816, 1272, -1380],
  [1, 9, 24, -24, -240, -288, 728, 2088, -108],
  [1, 10, 33, 0, -264, -528, 440, 2816, 1980],
  [1, 11, 43, 33, -264, -792, -88, 3256, 4796]
]

def unitCouplingData_13 : List (List ℤ) := [
  [-1, 13, -78, 286, -715, 1287, -1716, 1716, -1287],
  [-1, 12, -65, 208, -429, 572, -429, 0, 429],
  [-1, 11, -53, 143, -221, 143, 143, -429, 429],
  [-1, 10, -42, 90, -78, -78, 286, -286, 0],
  [-1, 9, -32, 48, 12, -156, 208, 0, -286],
  [-1, 8, -23, 16, 60, -144, 52, 208, -286],
  [-1, 7, -15, -7, 76, -84, -92, 260, -78],
  [-1, 6, -8, -22, 69, -8, -176, 168, 182],
  [-1, 5, -2, -30, 47, 61, -184, -8, 350],
  [-1, 4, 3, -32, 17, 108, -123, -192, 342],
  [-1, 3, 7, -29, -15, 125, -15, -315, 150],
  [-1, 2, 10, -22, -44, 110, 110, -330, -165],
  [-1, 1, 12, -12, -66, 66, 220, -220, -495],
  [-1, 0, 13, 0, -78, 0, 286, 0, -715],
  [-1, -1, 13, 13, -78, -78, 286, 286, -715],
  [-1, -2, 12, 26, -65, -156, 208, 572, -429],
  [-1, -3, 10, 38, -39, -221, 52, 780, 143],
  [-1, -4, 7, 48, -1, -260, -169, 832, 923],
  [-1, -5, 3, 55, 47, -261, -429, 663, 1755],
  [-1, -6, -2, 58, 102, -214, -690, 234, 2418],
  [-1, -7, -8, 56, 160, -112, -904, -456, 2652],
  [-1, -8, -15, 48, 216, 48, -1016, -1360, 2196],
  [-1, -9, -23, 33, 264, 264, -968, -2376, 836],
  [-1, -10, -32, 10, 297, 528, -704, -3344, -1540]
]

def unitCouplingData_14 : List (List ℤ) := [
  [1, -14, 91, -364, 1001, -2002, 3003, -3432, 3003],
  [1, -13, 77, -273, 637, -1001, 1001, -429, -429],
  [1, -12, 64, -196, 364, -364, 0, 572, -858],
  [1, -11, 52, -132, 168, 0, -364, 572, -286],
  [1, -10, 41, -80, 36, 168, -364, 208, 286],
  [1, -9, 31, -39, -44, 204, -196, -156, 494],
  [1, -8, 22, -8, -83, 160, 8, -352, 338],
  [1, -7, 14, 14, -91, 77, 168, -344, -14],
  [1, -6, 7, 28, -77, -14, 245, -176, -358],
  [1, -5, 1, 35, -49, -91, 231, 69, -534],
  [1, -4, -4, 36, -14, -140, 140, 300, -465],
  [1, -3, -8, 32, 22, -154, 0, 440, -165],
  [1, -2, -11, 24, 54, -132, -154, 440, 275],
  [1, -1, -13, 13, 78, -78, -286, 286, 715],
  [1, 0, -14, 0, 91, 0, -364, 0, 1001],
  [1, 1, -14, -14, 91, 91, -364, -364, 1001],
  [1, 2, -13, -28, 77, 182, -273, -728, 637],
  [1, 3, -11, -41, 49, 259, -91, -1001, -91],
  [1, 4, -8, -52, 8, 308, 168, -1092, -1092],
  [1, 5, -4, -60, -44, 316, 476, -924, -2184],
  [1, 6, 1, -64, -104, 272, 792, -448, -3108],
  [1, 7, 7, -63, -168, 168, 1064, 344, -3556],
  [1, 8, 14, -56, -231, 0, 1232, 1408, -3212],
  [1, 9, 22, -42, -287, -231, 1232, 2640, -1804]
]

def unitCouplingData_15 : List (List ℤ) := [
  [-1, 15, -105, 455, -1365, 3003, -5005, 6435, -6435],
  [-1, 14, -90, 350, -910, 1638, -2002, 1430, 0],
  [-1, 13, -76, 260, -560, 728, -364, -572, 1430],
  [-1, 12, -63, 184, -300, 168, 364, -936, 858],
  [-1, 11, -51, 121, -116, -132, 532, -572, -78],
  [-1, 10, -40, 70, 5, -248, 400, -40, -650],
  [-1, 9, -30, 30, 75, -243, 152, 360, -690],
  [-1, 8, -21, 0, 105, -168, -91, 512, -330],
  [-1, 7, -13, -21, 105, -63, -259, 421, 182],
  [-1, 6, -6, -34, 84, 42, -322, 162, 603],
  [-1, 5, 0, -40, 50, 126, -280, -160, 765],
  [-1, 4, 5, -40, 10, 176, -154, -440, 605],
  [-1, 3, 9, -35, -30, 186, 22, -594, 165],
  [-1, 2, 12, -26, -65, 156, 208, -572, -429],
  [-1, 1, 14, -14, -91, 91, 364, -364, -1001],
  [-1, 0, 15, 0, -105, 0, 455, 0, -1365],
  [-1, -1, 15, 15, -105, -105, 455, 455, -1365],
  [-1, -2, 14, 30, -90, -210, 350, 910, -910],
  [-1, -3, 12, 44, -60, -300, 140, 1260, 0],
  [-1, -4, 9, 56, -16, -360, -160, 1400, 1260],
  [-1, -5, 5, 65, 40, -376, -520, 1240, 2660],
  [-1, -6, 0, 70, 105, -336, -896, 720, 3900],
  [-1, -7, -6, 70, 175, -231, -1232, -176, 4620],
  [-1, -8, -13, 64, 245, -56, -1463, -1408, 4444]
]

def unitCouplingData_16 : List (List ℤ) := [
  [1, -16, 120, -560, 1820, -4368, 8008, -11440, 12870],
  [1, -15, 104, -440, 1260, -2548, 3640, -3432, 1430],
  [1, -14, 89, -336, 820, -1288, 1092, 208, -2002],
  [1, -13, 75, -247, 484, -468, -196, 1300, -1794],
  [1, -12, 62, -172, 237, 16, -664, 1104, -494],
  [1, -11, 50, -110, 65, 253, -648, 440, 610],
  [1, -10, 39, -60, -45, 318, -395, -208, 1050],
  [1, -9, 29, -21, -105, 273, -77, -603, 842],
  [1, -8, 20, 8, -126, 168, 196, -680, 239],
  [1, -7, 12, 28, -118, 42, 364, -484, -441],
  [1, -6, 5, 40, -90, -76, 406, -120, -925],
  [1, -5, -1, 45, -50, -166, 330, 286, -1045],
  [1, -4, -6, 44, -5, -216, 164, 616, -759],
  [1, -3, -10, 38, 39, -221, -52, 780, -143],
  [1, -2, -13, 28, 77, -182, -273, 728, 637],
  [1, -1, -15, 15, 105, -105, -455, 455, 1365],
  [1, 0, -16, 0, 120, 0, -560, 0, 1820],
  [1, 1, -16, -16, 120, 120, -560, -560, 1820],
  [1, 2, -15, -32, 104, 240, -440, -1120, 1260],
  [1, 3, -13, -47, 72, 344, -200, -1560, 140],
  [1, 4, -10, -60, 25, 416, 144, -1760, -1420],
  [1, 5, -6, -70, -35, 441, 560, -1616, -3180],
  [1, 6, -1, -76, -105, 406, 1001, -1056, -4796],
  [1, 7, 5, -77, -181, 301, 1407, -55, -5852]
]

def unitCouplingData_17 : List (List ℤ) := [
  [-1, 17, -136, 680, -2380, 6188, -12376, 19448, -24310],
  [-1, 16, -119, 544, -1700, 3808, -6188, 7072, -4862],
  [-1, 15, -103, 425, -1156, 2108, -2380, 884, 2210],
  [-1, 14, -88, 322, -731, 952, -272, -1496, 3094],
  [-1, 13, -74, 234, -409, 221, 680, -1768, 1598],
  [-1, 12, -61, 160, -175, -188, 901, -1088, -170],
  [-1, 11, -49, 99, -15, -363, 713, -187, -1258],
  [-1, 10, -38, 50, 84, -378, 350, 526, -1445],
  [-1, 9, -28, 12, 134, -294, -28, 876, -919],
  [-1, 8, -19, -16, 146, -160, -322, 848, -43],
  [-1, 7, -11, -35, 130, -14, -482, 526, 805],
  [-1, 6, -4, -46, 95, 116, -496, 44, 1331],
  [-1, 5, 2, -50, 49, 211, -380, -452, 1375],
  [-1, 4, 7, -48, -1, 260, -169, -832, 923],
  [-1, 3, 11, -41, -49, 259, 91, -1001, 91],
  [-1, 2, 14, -30, -90, 210, 350, -910, -910],
  [-1, 1, 16, -16, -120, 120, 560, -560, -1820],
  [-1, 0, 17, 0, -136, 0, 680, 0, -2380],
  [-1, -1, 17, 17, -136, -136, 680, 680, -2380],
  [-1, -2, 16, 34, -119, -272, 544, 1360, -1700],
  [-1, -3, 14, 50, -85, -391, 272, 1904, -340],
  [-1, -4, 11, 64, -35, -476, -119, 2176, 1564],
  [-1, -5, 7, 75, 29, -511, -595, 2057, 3740],
  [-1, -6, 2, 82, 104, -482, -1106, 1462, 5797]
]

def unitCouplingData_18 : List (List ℤ) := [
  [1, -18, 153, -816, 3060, -8568, 18564, -31824, 43758],
  [1, -17, 135, -663, 2244, -5508, 9996, -13260, 11934],
  [1, -16, 118, -528, 1581, -3264, 4488, -3264, -1326],
  [1, -15, 102, -410, 1053, -1683, 1224, 1224, -4590],
  [1, -14, 87, -308, 643, -630, -459, 2448, -3366],
  [1, -13, 73, -221, 335, 13, -1089, 1989, -918],
  [1, -12, 60, -148, 114, 348, -1076, 900, 1071],
  [1, -11, 48, -88, -34, 462, -728, -176, 1971],
  [1, -10, 37, -40, -122, 428, -266, -904, 1795],
  [1, -9, 27, -3, -162, 306, 162, -1170, 891],
  [1, -8, 18, 24, -165, 144, 468, -1008, -279],
  [1, -7, 10, 42, -141, -21, 612, -540, -1287],
  [1, -6, 3, 52, -99, -162, 591, 72, -1827],
  [1, -5, -3, 55, -47, -261, 429, 663, -1755],
  [1, -4, -8, 52, 8, -308, 168, 1092, -1092],
  [1, -3, -12, 44, 60, -300, -140, 1260, 0],
  [1, -2, -15, 32, 104, -240, -440, 1120, 1260],
  [1, -1, -17, 17, 136, -136, -680, 680, 2380],
  [1, 0, -18, 0, 153, 0, -816, 0, 3060],
  [1, 1, -18, -18, 153, 153, -816, -816, 3060],
  [1, 2, -17, -36, 135, 306, -663, -1632, 2244],
  [1, 3, -15, -53, 99, 441, -357, -2295, 612],
  [1, 4, -12, -68, 46, 540, 84, -2652, -1683],
  [1, 5, -8, -80, -22, 586, 624, -2568, -4335]
]

def unitCouplingData_19 : List (List ℤ) := [
  [-1, 19, -171, 969, -3876, 11628, -27132, 50388, -75582],
  [-1, 18, -152, 798, -2907, 7752, -15504, 23256, -25194],
  [-1, 17, -134, 646, -2109, 4845, -7752, 7752, -1938],
  [-1, 16, -117, 512, -1463, 2736, -2907, 0, 5814],
  [-1, 15, -101, 395, -951, 1273, -171, -2907, 5814],
  [-1, 14, -86, 294, -556, 322, 1102, -3078, 2907],
  [-1, 13, -72, 208, -262, -234, 1424, -1976, -171],
  [-1, 12, -59, 136, -54, -496, 1190, -552, -2147],
  [-1, 11, -47, 77, 82, -550, 694, 638, -2699],
  [-1, 10, -36, 30, 159, -468, 144, 1332, -2061],
  [-1, 9, -26, -6, 189, -309, -324, 1476, -729],
  [-1, 8, -17, -32, 183, -120, -633, 1152, 747],
  [-1, 7, -9, -49, 151, 63, -753, 519, 1899],
  [-1, 6, -2, -58, 102, 214, -690, -234, 2418],
  [-1, 5, 4, -60, 44, 316, -476, -924, 2184],
  [-1, 4, 9, -56, -16, 360, -160, -1400, 1260],
  [-1, 3, 13, -47, -72, 344, 200, -1560, -140],
  [-1, 2, 16, -34, -119, 272, 544, -1360, -1700],
  [-1, 1, 18, -18, -153, 153, 816, -816, -3060],
  [-1, 0, 19, 0, -171, 0, 969, 0, -3876],
  [-1, -1, 19, 19, -171, -171, 969, 969, -3876],
  [-1, -2, 18, 38, -152, -342, 798, 1938, -2907],
  [-1, -3, 16, 56, -114, -494, 456, 2736, -969],
  [-1, -4, 13, 72, -58, -608, -38, 3192, 1767]
]

def unitCouplingData_20 : List (List ℤ) := [
  [1, -20, 190, -1140, 4845, -15504, 38760, -77520, 125970],
  [1, -19, 170, -950, 3705, -10659, 23256, -38760, 48450],
  [1, -18, 151, -780, 2755, -6954, 12597, -15504, 9690],
  [1, -17, 133, -629, 1975, -4199, 5643, -2907, -5814],
  [1, -16, 116, -496, 1346, -2224, 1444, 2736, -8721],
  [1, -15, 100, -380, 850, -878, -780, 4180, -5985],
  [1, -14, 85, -280, 470, -28, -1658, 3400, -1805],
  [1, -13, 71, -195, 190, 442, -1686, 1742, 1595],
  [1, -12, 58, -124, -5, 632, -1244, 56, 3337],
  [1, -11, 46, -66, -129, 627, -612, -1188, 3393],
  [1, -10, 35, -20, -195, 498, 15, -1800, 2205],
  [1, -9, 25, 15, -215, 303, 513, -1785, 405],
  [1, -8, 16, 40, -200, 88, 816, -1272, -1380],
  [1, -7, 8, 56, -160, -112, 904, -456, -2652],
  [1, -6, 1, 64, -104, -272, 792, 448, -3108],
  [1, -5, -5, 65, -40, -376, 520, 1240, -2660],
  [1, -4, -10, 60, 25, -416, 144, 1760, -1420],
  [1, -3, -14, 50, 85, -391, -272, 1904, 340],
  [1, -2, -17, 36, 135, -306, -663, 1632, 2244],
  [1, -1, -19, 19, 171, -171, -969, 969, 3876],
  [1, 0, -20, 0, 190, 0, -1140, 0, 4845],
  [1, 1, -20, -20, 190, 190, -1140, -1140, 4845],
  [1, 2, -19, -40, 170, 380, -950, -2280, 3705],
  [1, 3, -17, -59, 130, 550, -570, -3230, 1425]
]

def unitCouplingData_21 : List (List ℤ) := [
  [-1, 21, -210, 1330, -5985, 20349, -54264, 116280, -203490],
  [-1, 20, -189, 1120, -4655, 14364, -33915, 62016, -87210],
  [-1, 19, -169, 931, -3535, 9709, -19551, 28101, -25194],
  [-1, 18, -150, 762, -2604, 6174, -9842, 8550, 2907],
  [-1, 17, -132, 612, -1842, 3570, -3668, -1292, 11457],
  [-1, 16, -115, 480, -1230, 1728, -98, -4960, 10165],
  [-1, 15, -99, 365, -750, 498, 1630, -5058, 5205],
  [-1, 14, -84, 266, -385, -252, 2128, -3428, 147],
  [-1, 13, -70, 182, -119, -637, 1876, -1300, -3281],
  [-1, 12, -57, 112, 63, -756, 1239, 576, -4581],
  [-1, 11, -45, 55, 175, -693, 483, 1815, -4005],
  [-1, 10, -34, 10, 230, -518, -210, 2298, -2190],
  [-1, 9, -24, -24, 240, -288, -728, 2088, 108],
  [-1, 8, -15, -48, 216, -48, -1016, 1360, 2196],
  [-1, 7, -7, -63, 168, 168, -1064, 344, 3556],
  [-1, 6, 0, -70, 105, 336, -896, -720, 3900],
  [-1, 5, 6, -70, 35, 441, -560, -1616, 3180],
  [-1, 4, 11, -64, -35, 476, -119, -2176, 1564],
  [-1, 3, 15, -53, -99, 441, 357, -2295, -612],
  [-1, 2, 18, -38, -152, 342, 798, -1938, -2907],
  [-1, 1, 20, -20, -190, 190, 1140, -1140, -4845],
  [-1, 0, 21, 0, -210, 0, 1330, 0, -5985],
  [-1, -1, 21, 21, -210, -210, 1330, 1330, -5985],
  [-1, -2, 20, 42, -189, -420, 1120, 2660, -4655]
]

def unitCouplingData_22 : List (List ℤ) := [
  [1, -22, 231, -1540, 7315, -26334, 74613, -170544, 319770],
  [1, -21, 209, -1309, 5775, -19019, 48279, -95931, 149226],
  [1, -20, 188, -1100, 4466, -13244, 29260, -47652, 53295],
  [1, -19, 168, -912, 3366, -8778, 16016, -18392, 5643],
  [1, -18, 149, -744, 2454, -5412, 7238, -2376, -12749],
  [1, -17, 131, -595, 1710, -2958, 1826, 4862, -15125],
  [1, -16, 114, -464, 1115, -1248, -1132, 6688, -10263],
  [1, -15, 98, -350, 651, -133, -2380, 5556, -3575],
  [1, -14, 83, -252, 301, 518, -2513, 3176, 1981],
  [1, -13, 69, -169, 49, 819, -1995, 663, 5157],
  [1, -12, 56, -100, -120, 868, -1176, -1332, 5820],
  [1, -11, 44, -44, -220, 748, -308, -2508, 4488],
  [1, -10, 33, 0, -264, 528, 440, -2816, 1980],
  [1, -9, 23, 33, -264, 264, 968, -2376, -836],
  [1, -8, 14, 56, -231, 0, 1232, -1408, -3212],
  [1, -7, 6, 70, -175, -231, 1232, -176, -4620],
  [1, -6, -1, 76, -105, -406, 1001, 1056, -4796],
  [1, -5, -7, 75, -29, -511, 595, 2057, -3740],
  [1, -4, -12, 68, 46, -540, 84, 2652, -1683],
  [1, -3, -16, 56, 114, -494, -456, 2736, 969],
  [1, -2, -19, 40, 170, -380, -950, 2280, 3705],
  [1, -1, -21, 21, 210, -210, -1330, 1330, 5985],
  [1, 0, -22, 0, 231, 0, -1540, 0, 7315],
  [1, 1, -22, -22, 231, 231, -1540, -1540, 7315]
]

def unitCouplingData_23 : List (List ℤ) := [
  [-1, 23, -253, 1771, -8855, 33649, -100947, 245157, -490314],
  [-1, 22, -230, 1518, -7084, 24794, -67298, 144210, -245157],
  [-1, 21, -208, 1288, -5566, 17710, -42504, 76912, -100947],
  [-1, 20, -187, 1080, -4278, 12144, -24794, 34408, -24035],
  [-1, 19, -167, 893, -3198, 7866, -12650, 9614, 10373],
  [-1, 18, -148, 726, -2305, 4668, -4784, -3036, 19987],
  [-1, 17, -130, 578, -1579, 2363, -116, -7820, 16951],
  [-1, 16, -113, 448, -1001, 784, 2247, -7936, 9131],
  [-1, 15, -97, 335, -553, -217, 3031, -5689, 1195],
  [-1, 14, -82, 238, -218, -770, 2814, -2658, -4494],
  [-1, 13, -68, 156, 20, -988, 2044, 156, -7152],
  [-1, 12, -55, 88, 176, -968, 1056, 2200, -6996],
  [-1, 11, -43, 33, 264, -792, 88, 3256, -4796],
  [-1, 10, -32, -10, 297, -528, -704, 3344, -1540],
  [-1, 9, -22, -42, 287, -231, -1232, 2640, 1804],
  [-1, 8, -13, -64, 245, 56, -1463, 1408, 4444],
  [-1, 7, -5, -77, 181, 301, -1407, -55, 5852],
  [-1, 6, 2, -82, 104, 482, -1106, -1462, 5797],
  [-1, 5, 8, -80, 22, 586, -624, -2568, 4335],
  [-1, 4, 13, -72, -58, 608, -38, -3192, 1767],
  [-1, 3, 17, -59, -130, 550, 570, -3230, -1425],
  [-1, 2, 20, -42, -189, 420, 1120, -2660, -4655],
  [-1, 1, 22, -22, -231, 231, 1540, -1540, -7315],
  [-1, 0, 23, 0, -253, 0, 1771, 0, -8855]
]

def unitCouplingData : List (List (List ℤ)) := [unitCouplingData_0, unitCouplingData_1, unitCouplingData_2, unitCouplingData_3, unitCouplingData_4, unitCouplingData_5, unitCouplingData_6, unitCouplingData_7, unitCouplingData_8, unitCouplingData_9, unitCouplingData_10, unitCouplingData_11, unitCouplingData_12, unitCouplingData_13, unitCouplingData_14, unitCouplingData_15, unitCouplingData_16, unitCouplingData_17, unitCouplingData_18, unitCouplingData_19, unitCouplingData_20, unitCouplingData_21, unitCouplingData_22, unitCouplingData_23]

def memoUnitCoupling (z k p : ℕ) : ℤ := (((unitCouplingData.getD z []).getD k []).getD p 0)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PositiveIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive Integrals. -/
noncomputable section
namespace LaughlinFock
open scoped Matrix ComplexOrder BigOperators Matrix.Norms.Elementwise
open MeasureTheory

local instance instContinuousENormMatrixComplexOfFintype_solutions {ι κ : Type*} [Fintype ι] [Fintype κ] :
    ContinuousENorm (Matrix ι κ ℂ) :=
  inferInstanceAs (ContinuousENorm (ι → κ → ℂ))

 
def quadraticEvaluation {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] ℂ where
  toFun M := star x ⬝ᵥ (M *ᵥ x)
  map_add' M N := by simp only [Matrix.add_mulVec, dotProduct_add]
  map_smul' c M := by
    simp only [Matrix.smul_mulVec, dotProduct_smul, RingHom.id_apply]


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Rotations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rotations. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open NormedSpace MeasureTheory Topology


def unitaryConjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  U.val * M * U.valᴴ

theorem unitaryConjugation_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) : unitaryConjugation 1 M = M := by
  simp [unitaryConjugation]

theorem unitaryConjugation_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix.unitaryGroup ι ℂ) (M : Matrix ι ι ℂ) :
    unitaryConjugation (U*V) M = unitaryConjugation U (unitaryConjugation V M) := by
  simp [unitaryConjugation, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FockRotations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fock Rotations. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


def congruenceLinear {ι κ : Type*} [Fintype ι] (C : Matrix κ ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun M := C * M * Cᴴ
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CrossOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cross Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix Matrix.Norms.Elementwise ComplexOrder
open MeasureTheory Topology
local instance crossOrbitContinuousENorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    ContinuousENorm (Matrix ι κ ℂ) :=
  inferInstanceAs (ContinuousENorm (ι → κ → ℂ))

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FastTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourCommonDenominator : ℕ := 2^53 * (23).factorial * 10^18

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_TableTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Table Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def memoIntegerCopyPolynomial (D T r p j k : ℕ) : ℤ :=
  if r ≤ j+k then
    memoUnitCoupling r (j+k-r) j * memoUnitCoupling (D-r) (T-D) p
  else 0

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FasterTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Faster Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def directIntegerSum {α : Type*} (f : α → ℤ) : List α → ℤ
  | [] => 0
  | a::as => f a + directIntegerSum f as

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_WedgeLie
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Wedge Lie. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


def tensorSum {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  Matrix.kronecker X 1 + Matrix.kronecker 1 Y

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Copies. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourSpinDegree (Q D : ℕ) : ℕ := 4*Q-2-2*D



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_LDL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L D L. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def matrixEntriesDecidable {ι : Type*} [Fintype ι] {α : Type*} [DecidableEq α]
    (A B : Matrix ι ι α) : Decidable (∀ i j, A i j = B i j) :=
  @Fintype.decidableForallFintype _ _ (fun _ =>
    @Fintype.decidableForallFintype _ _ (fun _ => inferInstance) _) _


end LaughlinFock
end

end OAI
end


