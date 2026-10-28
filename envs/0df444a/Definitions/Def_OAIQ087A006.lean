-- Prove2me | Definitions.Def_OAIQ087A006
-- name    : OAIQ087A006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:17:50.932138+00:00
-- url     : https://prove2.me/theorems/15a92824-7e0c-4630-8a3c-b2e451b93728
-- title:
--   Definitions bundle OAIQ087A006 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 85 declarations of OpenAI's Lean: 43 definitions, 2 inductive types or structures, 9 instances and 31 theorems. The definitions and types are `OAI.OptimalMaxCut.GaussianBellman.conditionalArg`, `OAI.OptimalMaxCut.GaussianBellman.sigma`, `OAI.OptimalMaxCut.LongCode.Game`, `OAI.OptimalMaxCut.LongCode.Game.Sound`, `OAI.OptimalMaxCut.LongCode.Game.satisfied`, `OAI.OptimalMaxCut.LongCode.Law`, `OAI.OptimalMaxCut.LongCode.Law.avg`, `OAI.OptimalMaxCut.LongCode.Law.bind`, `OAI.OptimalMaxCut.LongCode.Law.fiberConditional`, `OAI.OptimalMaxCut.LongCode.Law.fiberMarginal`, `OAI.OptimalMaxCut.LongCode.Law.fiberSize`, `OAI.OptimalMaxCut.LongCode.Law.grid`, `OAI.OptimalMaxCut.LongCode.Law.gridWeight`, `OAI.OptimalMaxCut.LongCode.Law.push`, `OAI.OptimalMaxCut.LongCode.aggregate`, `OAI.OptimalMaxCut.LongCode.bitPairWeightQ`, `OAI.OptimalMaxCut.LongCode.roundedWeights`, `OAI.OptimalMaxCut.MISProof.clip`, `OAI.OptimalMaxCut.MISProof.interiorClip`, `OAI.OptimalMaxCut.RawGrid.coordinate`, `OAI.OptimalMaxCut.RawGrid.frameValue`, `OAI.OptimalMaxCut.RawGrid.pairing`, `OAI.OptimalMaxCut.Unweighted.Vec`, `OAI.OptimalMaxCut.Unweighted.beta`, `OAI.OptimalMaxCut.Unweighted.blowupGraph`, `OAI.OptimalMaxCut.Unweighted.blowupOutput`, `OAI.OptimalMaxCut.Unweighted.clusterCutCount`, `OAI.OptimalMaxCut.Unweighted.cutFraction`, `OAI.OptimalMaxCut.Unweighted.cutMass`, `OAI.OptimalMaxCut.Unweighted.cutSet`, `OAI.OptimalMaxCut.Unweighted.deterministicOutput`, `OAI.OptimalMaxCut.Unweighted.dot`, `OAI.OptimalMaxCut.Unweighted.dotChar`, `OAI.OptimalMaxCut.Unweighted.fractionalCut`, `OAI.OptimalMaxCut.Unweighted.pairCutCount`, `OAI.OptimalMaxCut.Unweighted.rectangleCount`, `OAI.OptimalMaxCut.Unweighted.residueSet`, `OAI.OptimalMaxCut.Unweighted.searchPrime`, `OAI.OptimalMaxCut.Unweighted.totalWeight`, `OAI.OptimalMaxCut.Unweighted.vecEquiv` and 5 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`MaxCut_Arithmetic_GridWeight`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Arithmetic/GridWeight.lean), [`MaxCut_Encoding_BitPairWeightQ`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Encoding/BitPairWeightQ.lean), [`MaxCut_Estimates_Anchor`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Estimates/Anchor.lean), [`MaxCut_Estimates_Clip`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Estimates/Clip.lean), [`MaxCut_Estimates_Degree`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Estimates/Degree.lean), [`MaxCut_Estimates_Density`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Estimates/Density.lean), [`MaxCut_Estimates_Dictator`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Estimates/Dictator.lean), [`MaxCut_Estimates_Param`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Estimates/Param.lean), [`MaxCut_Estimates_Vec`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Estimates/Vec.lean).
--
--   **Imports.** It imports the published bundle `Def_OptimalMaxCut`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A012`, `OAIQ087A013` and `OAIQ087A020`; the statement `OAI_MaxCutGames_Gadget_EnlargementEndpoint_exists_data`; the proof of `OAI_MaxCutGames_Gadget_EnlargementEndpoint_exists_data`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OptimalMaxCut

section
-- module Solutions.OAIQ087_MC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

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
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.GaussianBellman

open scoped Real Topology NNReal ContDiff
open Set Filter MeasureTheory
open ProbabilityTheory

noncomputable def sigma (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 2)
noncomputable def conditionalArg (t u v : ℝ) : ℝ := (v - t * u) / sigma t

end OptimalMaxCut.GaussianBellman

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Degree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real Walsh analysis on finite Boolean cubes. The basis and inversion
identities are proved from the explicit coordinate characters. -/

noncomputable section

namespace OptimalMaxCut

noncomputable def gwRatio (ρ : ℝ) : ℝ :=
  2 * Real.arccos ρ / (Real.pi * (1 - ρ))

noncomputable def borellCurve (t : ℝ) : ℝ := 2 / Real.pi * Real.arcsin t

@[simp] lemma gwRatio_neg_one : gwRatio (-1) = 1 := by
  simp [gwRatio, Real.arccos_neg_one]
  field_simp
  ring

@[simp] lemma gwRatio_zero : gwRatio 0 = 1 := by
  simp only [gwRatio, Real.arccos_zero, sub_zero, mul_one]
  field_simp

end OptimalMaxCut

end -- noncomputable Walsh/analytic section

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Clip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.MISProof
open scoped BigOperators
open Finset Set GaussianBellman

noncomputable def clip (x : ℝ) : ℝ := max (-1) (min 1 x)

noncomputable def interiorClip (η x : ℝ) : ℝ := η + (1 - 2 * η) * (clip x + 1) / 2

end OptimalMaxCut.MISProof

namespace OptimalMaxCut.LongCode

open scoped BigOperators
open Finset
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

/-- Explicit rational finite probability law. The weighted test below is a
finite rational graph construction, not an oracle distribution. -/
structure Law (I : Type*) [Fintype I] where
  weight : I → ℚ
  nonneg : ∀ i, 0 ≤ weight i
  total : ∑ i, weight i = 1

namespace Law
variable {I J : Type*} [Fintype I] [Fintype J]

def avg (p : Law I) (f : I → ℝ) : ℝ := ∑ i, (p.weight i : ℝ) * f i

@[simp] theorem avg_add (p : Law I) (f g : I → ℝ) :
    p.avg (fun i => f i + g i) = p.avg f + p.avg g := by simp [avg, mul_add, sum_add_distrib]

@[simp] theorem avg_sub (p : Law I) (f g : I → ℝ) :
    p.avg (fun i => f i - g i) = p.avg f - p.avg g := by simp [avg, mul_sub, sum_sub_distrib]

@[simp] theorem avg_mul (p : Law I) (f : I → ℝ) (a : ℝ) :
    p.avg (fun i => f i * a) = p.avg f * a := by simp [avg, sum_mul, mul_assoc]

@[simp] theorem avg_smul (p : Law I) (f : I → ℝ) (a : ℝ) :
    p.avg (fun i => a * f i) = a * p.avg f := by simp [avg, mul_left_comm, mul_sum]

@[simp] theorem avg_div (p : Law I) (f : I → ℝ) (a : ℝ) :
    p.avg (fun i => f i / a) = p.avg f / a := by simp [div_eq_mul_inv]

end Law

/-- The generative presentation of a finite rational weighted Unique Game:
choose a right question, then an incident edge. All actual games have this
presentation after deleting zero-marginal right questions. -/
structure Game (X Y E : Type*) [Fintype X] [Fintype Y] [Fintype E] (q : ℕ) where
  rightLaw : Law Y
  edgeLaw : Y → Law E
  source : E → X
  permutation : E → Equiv.Perm (Fin q)

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q : ℕ}

noncomputable def satisfied (G : Game X Y E q) (lx : X → Fin q) (ly : Y → Fin q) : ℝ :=
  G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
    if G.permutation e (lx (G.source e)) = ly y then 1 else 0))

/-- A semantic bound on this *input* game, not a hypothesis asserting NP-hardness
or an assumed Max-Cut reduction. -/
def Sound (G : Game X Y E q) (δ : ℝ) : Prop := ∀ lx ly, G.satisfied lx ly ≤ δ

end Game

end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BitPairWeightQ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

def bitPairWeightQ (t : ℚ) (a b : Bool) : ℚ :=
  (1 + t * (if a then -1 else 1) * (if b then -1 else 1)) / 4

namespace Law
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Finite conditional sampling; both the law and all output masses are rational. -/
def bind (p : Law I) (q : I → Law J) : Law (I × J) where
  weight x := p.weight x.1 * (q x.1).weight x.2
  nonneg x := mul_nonneg (p.nonneg _) ((q _).nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, Law.total, mul_one]

end Law

end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Vec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace OptimalMaxCut.Unweighted

open Finset
open scoped BigOperators ComplexConjugate

abbrev Vec (p : ℕ) := Fin 6 → ZMod p

def dot {p : ℕ} (x y : Vec p) : ZMod p := ∑ i, x i * y i

variable {p : ℕ} [Fact p.Prime]

@[simp] theorem card_vec : Fintype.card (Vec p) = p ^ 6 := by
  simp [Vec]

omit [Fact (Nat.Prime p)] in
theorem dot_comm (x y : Vec p) : dot x y = dot y x := by
  simp [dot, mul_comm]

@[simp] theorem dot_add_right (x y z : Vec p) :
    dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, sum_add_distrib]

@[simp] theorem dot_sub_left (x y z : Vec p) :
    dot (x - y) z = dot x z - dot y z := by
  simp [dot, sub_mul, sum_sub_distrib]

@[simp] theorem dot_zero_right (x : Vec p) : dot x 0 = 0 := by simp [dot]

noncomputable def dotChar (h : ZMod p) (x : Vec p) : AddChar (Vec p) ℂ where
  toFun y := ZMod.stdAddChar (h * dot x y)
  map_zero_eq_one' := by simp
  map_add_eq_mul' y z := by simp [mul_add, AddChar.map_add_eq_mul]

@[simp] theorem norm_stdChar (a : ZMod p) : ‖ZMod.stdAddChar a‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

@[simp] theorem conj_stdChar (a : ZMod p) :
    conj (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [← Complex.inv_eq_conj (norm_stdChar a), AddChar.map_neg_eq_inv]

/-- Fourier coefficient of the residue indicator, probability normalization. -/
noncomputable def beta (I : Finset (ZMod p)) (h : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ a ∈ I, ZMod.stdAddChar (-(h * a))

@[simp] theorem beta_zero (I : Finset (ZMod p)) :
    beta I 0 = (I.card : ℂ) / p := by simp [beta, div_eq_mul_inv, mul_comm]

def rectangleCount (I : Finset (ZMod p)) (S T : Finset (Vec p)) : ℕ :=
  ∑ x ∈ S, ∑ y ∈ T, if dot x y ∈ I then 1 else 0

def residueSet (w : ℚ) : Finset (ZMod p) :=
  (range ⌊(p : ℚ) * w⌋₊).image (fun j : ℕ => (j : ZMod p))

section Rounding

variable {V : Type*} [Fintype V] [DecidableEq V]

def cutMass (a : V → ℝ) (σ : V → Bool) : ℝ :=
  ∏ i, if σ i then a i else 1 - a i

@[simp] theorem sum_cutMass (a : V → ℝ) : ∑ σ : V → Bool, cutMass a σ = 1 := by
  simp_rw [cutMass]
  rw [← Fintype.prod_sum (fun (i : V) (b : Bool) => if b then a i else 1 - a i)]
  simp []

end Rounding

/-- Weighted cut on unordered distinct vertex pairs, on the original weight scale. -/
def weightedCut {N : ℕ} (w : Fin N → Fin N → ℝ) (σ : Fin N → Bool) : ℝ :=
  ∑ u, ∑ v, if u < v ∧ σ u ≠ σ v then w u v else 0

noncomputable def weightedMax {N : ℕ} (w : Fin N → Fin N → ℝ) : ℝ :=
  (univ.image (weightedCut w)).max' (univ_nonempty.image _)

/-- Expected cut weight under independent randomized rounding. -/
def fractionalCut {N : ℕ} (w : Fin N → Fin N → ℝ) (a : Fin N → ℝ) : ℝ :=
  ∑ u, ∑ v, if u < v then w u v * (a u * (1 - a v) + (1 - a u) * a v) else 0

def vecEquiv : Vec p ≃ Fin (p ^ 6) :=
  (Equiv.arrowCongr (Equiv.refl (Fin 6)) (ZMod.finEquiv p).symm.toEquiv).trans
    finFunctionFinEquiv

/-- Explicit lexicographic indexing of all Np^6 output vertices. -/
def vertexEquiv (N : ℕ) : (Fin N × Vec p) ≃ Fin (N * p ^ 6) :=
  (Equiv.prodCongr (Equiv.refl (Fin N)) vecEquiv).trans finProdFinEquiv

@[simp] theorem vertexEquiv_val {N : ℕ} (u : Fin N) (x : Vec p) :
    (vertexEquiv N (u, x) : ℕ) = (vecEquiv x : ℕ) + p ^ 6 * (u : ℕ) := rfl

/-- The actual simple unweighted finite output graph, not an abstract promise. -/
def blowupGraph {N : ℕ} (w : Fin N → Fin N → ℚ) (hw : ∀ u v, w u v = w v u) : Graph where
  vertices := N * p ^ 6
  adj i j :=
    let a := (vertexEquiv N).symm i
    let b := (vertexEquiv N).symm j
    decide (a.1 ≠ b.1 ∧ dot a.2 b.2 ∈ residueSet (w a.1 b.1))
  symmetric i j := by
    dsimp only
    rw [dot_comm, hw]
    simp only [ne_comm]
  loopless i := by simp

/-- The scale is p^12, not the output number of edges. -/
def blowupOutput {N : ℕ} (w : Fin N → Fin N → ℚ) (hw : ∀ u v, w u v = w v u) : ScaledGraph where
  graph := blowupGraph (p := p) w hw
  scale := p ^ 12
  scale_pos := pow_pos (Fact.out : p.Prime).pos _

@[simp] theorem blowup_adj {N : ℕ} (w : Fin N → Fin N → ℚ)
    (hw : ∀ u v, w u v = w v u) (u v : Fin N) (x y : Vec p) :
    (blowupGraph w hw).adj (vertexEquiv N (u, x)) (vertexEquiv N (v, y)) =
      decide (u ≠ v ∧ dot x y ∈ residueSet (w u v)) := by
  simp [blowupGraph]

/-- A cut expressed in cluster coordinates. -/
def clusterCutCount {N : ℕ} (w : Fin N → Fin N → ℚ) (σ : Fin N → Vec p → Bool) : ℕ :=
  ∑ u, ∑ v, if u < v then
    ∑ x, ∑ y, if dot x y ∈ residueSet (w u v) ∧ σ u x ≠ σ v y then 1 else 0
    else 0

/-- Either side of a cut inside one cluster. -/
def cutSet (σ : Vec p → Bool) (b : Bool) : Finset (Vec p) :=
  univ.filter (fun x => σ x = b)

@[simp] theorem mem_cutSet (σ : Vec p → Bool) (b : Bool) (x : Vec p) :
    x ∈ cutSet σ b ↔ σ x = b := by simp [cutSet]

/-- Fraction of a cluster on the positive side, on the exact p^6 scale. -/
noncomputable def cutFraction (σ : Vec p → Bool) : ℝ := (cutSet σ true).card / (p : ℝ) ^ 6

/-- The exact edge count crossing between two distinct clusters. -/
def pairCutCount (w : ℚ) (σ τ : Vec p → Bool) : ℕ :=
  ∑ x, ∑ y, if dot x y ∈ residueSet w ∧ σ x ≠ τ y then 1 else 0

@[simp] theorem cutFraction_const (b : Bool) :
    cutFraction (p := p) (fun _ => b) = if b then 1 else 0 := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  cases b <;> simp [cutFraction, cutSet, hp]

def totalWeight {N : ℕ} (w : Fin N → Fin N → ℚ) : ℚ :=
  ∑ u, ∑ v, if u < v then w u v else 0

/-- Bounded deterministic prime search. Its bound follows from Bertrand,
not a prime oracle or an unbounded assumed operation. -/
def searchPrime (m : ℕ) : ℕ :=
  ((List.range (2 * (m + 1) + 1)).find? (fun q => decide (m + 1 < q ∧ q.Prime))).getD 2

theorem searchPrime_spec (m : ℕ) :
    (searchPrime m).Prime ∧ m < searchPrime m ∧ searchPrime m ≤ 2 * (m + 1) := by
  obtain ⟨q, hq, hmq, hqbound⟩ := Nat.exists_prime_lt_and_le_two_mul (m + 1) (by omega)
  have hs : ((List.range (2 * (m + 1) + 1)).find?
      (fun q => decide (m + 1 < q ∧ q.Prime))).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨q, List.mem_range.mpr (by omega), by simp [hmq, hq]⟩
  cases hf : ((List.range (2 * (m + 1) + 1)).find?
      (fun q => decide (m + 1 < q ∧ q.Prime))) with
  | none =>
    rw [hf] at hs
    contradiction
  | some q =>
    have hq' : m + 1 < q ∧ q.Prime := by simpa using List.find?_some hf
    have hq'' := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    simpa only [searchPrime, hf, Option.getD_some] using
      (show q.Prime ∧ m < q ∧ q ≤ 2 * (m + 1) from ⟨hq'.2, by omega, by omega⟩)

def deterministicOutput {N : ℕ} (K : ℕ) (w : Fin N → Fin N → ℚ)
    (hw : ∀ u v, w u v = w v u) : ScaledGraph :=
  let p := searchPrime (K * (N + 1) ^ 2)
  haveI : Fact p.Prime := ⟨(searchPrime_spec _).1⟩
  blowupOutput (p := p) w hw

end OptimalMaxCut.Unweighted

/-! Exact tree gate and slice symmetry. Sign values are encoded in ZMod 2:
b encodes (-1)^b. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Dictator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset
open OptimalMaxCut.Unweighted

namespace Law
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

/-- Exact aggregation of rational masses; all collisions are added, not
silently treated as different edges. -/
def push (p : Law I) (f : I → J) : Law J where
  weight j := ∑ i, if f i = j then p.weight i else 0
  nonneg j := sum_nonneg (fun i _ => by split_ifs; exact p.nonneg i; exact le_refl 0)
  total := by
    rw [sum_comm]
    simpa using p.total

end Law

/-- A general finite rational law of ordered test endpoints becomes an ordinary
symmetric rational graph by adding both orientations and deleting loops. -/
def aggregate {N : ℕ} (p : Law (Fin N × Fin N)) (u v : Fin N) : ℚ :=
  if u = v then 0 else p.weight (u,v) + p.weight (v,u)

 theorem aggregate_symm {N : ℕ} (p : Law (Fin N × Fin N)) (u v : Fin N) :
    aggregate p u v = aggregate p v u := by
  simp only [aggregate]
  by_cases h : u = v <;> simp [h, eq_comm, add_comm]

end OptimalMaxCut.LongCode

namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset
namespace Law
attribute [local instance] Classical.propDecidable
variable {E Y : Type} [Fintype E] [Fintype Y] [Nonempty E]
noncomputable def fiberSize (r : E → Y) (y : Y) : ℕ := by
  classical
  exact (univ.filter (fun e => r e = y)).card

omit [Fintype Y] [Nonempty E] in
 theorem fiberSize_eq_sum (r : E → Y) (y : Y) :
    fiberSize r y = ∑ e, if r e = y then 1 else 0 := by
  classical
  simp only [fiberSize, Finset.card_filter]

omit [Nonempty E] in
 theorem sum_fiberSize (r : E → Y) : ∑ y, fiberSize r y = Fintype.card E := by
  classical
  simp_rw [fiberSize_eq_sum]
  rw [sum_comm]
  simp

noncomputable def fiberMarginal (r : E → Y) : Law Y where
  weight y := fiberSize r y / (Fintype.card E : ℚ)
  nonneg y := by positivity
  total := by
    rw [← sum_div, ← Nat.cast_sum, sum_fiberSize]
    exact div_self (by exact_mod_cast Fintype.card_ne_zero)

noncomputable def fiberConditional (r : E → Y) (y : Y) : Law E := by
  classical
  exact {
    weight e := if fiberSize r y = 0 then 1 / (Fintype.card E : ℚ)
      else if r e = y then 1 / (fiberSize r y : ℚ) else 0
    nonneg e := by split_ifs <;> positivity
    total := by
      by_cases h : fiberSize r y = 0
      · simp [h, div_eq_mul_inv]
      · simp only [h, ↓reduceIte]
        rw [← sum_filter]
        simp only [sum_const, nsmul_eq_mul]
        change (fiberSize r y : ℚ) * (1 / (fiberSize r y : ℚ)) = 1
        exact mul_one_div_cancel (by exact_mod_cast h) }

end Law
end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Arithmetic_GridWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset OptimalMaxCut.Unweighted

namespace Law
variable {I : Type} [Fintype I]

/-- Downward rounding is performed BEFORE aggregation. Thus every output mass
has the same polynomially sized integer denominator; no product of all input
vertex degrees has to be represented as a unary integer. -/
noncomputable def gridWeight (P : ℕ) (a : ℚ) : ℚ := (⌊(P : ℚ) * a⌋₊ : ℚ) / P

 theorem gridWeight_nonneg (P : ℕ) (a : ℚ) : 0 ≤ gridWeight P a := by
  unfold gridWeight; positivity

 theorem gridWeight_le (P : ℕ) (hP : 0 < P) (a : ℚ) (ha : 0 ≤ a) :
    gridWeight P a ≤ a := by
  have hPr : (0 : ℚ) < P := by exact_mod_cast hP
  rw [gridWeight, div_le_iff₀ hPr]
  simpa [mul_comm] using Nat.floor_le (mul_nonneg hPr.le ha)

noncomputable def grid (p : Law I) (P : ℕ) (hP : 0 < P) : Law (Option I) where
  weight
    | none => 1 - ∑ i, gridWeight P (p.weight i)
    | some i => gridWeight P (p.weight i)
  nonneg
    | none => by
        have h := sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) =>
          gridWeight_le P hP (p.weight i) (p.nonneg i))
        rw [p.total] at h
        linarith
    | some i => gridWeight_nonneg _ _
  total := by simp [Fintype.sum_option]

end Law

/-- Lost mass becomes a loop, which is deleted by exactly the original
aggregation. It is never renormalized into non-loop edges. -/
noncomputable def roundedWeights {I : Type} [Fintype I] {N : ℕ}
    (p : Law I) (endpoints : I → Fin N × Fin N) (v0 : Fin N)
    (P : ℕ) (hP : 0 < P) : Fin N → Fin N → ℚ :=
  aggregate ((p.grid P hP).push (fun
    | none => (v0,v0)
    | some i => endpoints i))

end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Param
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.RawGrid
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

def coordinate (p i k : ℕ) : ℕ := (i % p^6)/p^k % p
def pairing (p i j : ℕ) : ℕ := (∑ k : Fin 6, coordinate p i k.val * coordinate p j k.val)%p

def frameValue (n i : ℕ) : ℕ :=
  if i<2*n.size then if i%2=0 then 1 else n/2^(i/2)%2 else 0
end OptimalMaxCut.RawGrid

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Anchor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut
open scoped BigOperators
attribute [local instance] Classical.propDecidable

@[simp] theorem Graph.table_length (G : Graph) :
    ((List.finRange G.vertices).flatMap (fun u =>
      (List.finRange G.vertices).map (fun v => G.adj u v))).length = G.vertices^2 := by
  simp [List.length_flatMap, pow_two]

end OptimalMaxCut

end

end OAI
end


