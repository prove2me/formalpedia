-- Prove2me | Definitions.Def_OAIQ262T003
-- name    : OAIQ262T003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:40:59.739+00:00
-- url     : https://prove2.me/theorems/30280100-40d7-45f1-b7fd-f8c2cdc33f73
-- title:
--   Definitions bundle OAIQ262T003 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 106 declarations of OpenAI's Lean: 25 definitions, 1 inductive type or structure, 5 instances and 75 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.bernsteinRows`, `OAI.AtomicTriangular.Construction.complexDeleted`, `OAI.AtomicTriangular.Construction.complexError`, `OAI.AtomicTriangular.Construction.complexTaylor`, `OAI.AtomicTriangular.Construction.freezeParameter`, `OAI.AtomicTriangular.Construction.localBoundary`, `OAI.AtomicTriangular.Construction.localPivot`, `OAI.AtomicTriangular.Construction.nearBase`, `OAI.AtomicTriangular.Construction.nearDisplacement`, `OAI.AtomicTriangular.Construction.nearDisplacementNum`, `OAI.AtomicTriangular.Construction.nearError`, `OAI.AtomicTriangular.Construction.pade0`, `OAI.AtomicTriangular.Construction.pade1`, `OAI.AtomicTriangular.Construction.piHigh`, `OAI.AtomicTriangular.Construction.piLow`, `OAI.AtomicTriangular.Construction.sineLower`, `OAI.AtomicTriangular.Construction.sinePolynomial`, `OAI.AtomicTriangular.Construction.vanishingLower`, `OAI.AtomicTriangular.Envelope.expDeleted`, `OAI.AtomicTriangular.Envelope.expDeletedTaylor`, `OAI.AtomicTriangular.FiniteCertificate.nearNode`, `OAI.AtomicTriangular.GaussianPair`, `OAI.TriangularUniversal.Plane`, `OAI.TriangularUniversal.b`, `OAI.TriangularUniversal.triangularPoint`, `OAI.circleMeasurableSpace`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Auxiliary_ExponentialTail`, `Triangular_Certificate_PolytopeInterval`, `Triangular_Construction_ActualInterpolation`, `Triangular_Construction_FiniteRemainder`, `Triangular_Construction_NodeJets`, `Triangular_Energy_Basic`, `Triangular_Energy_Mixtures`, `Triangular_Schwartz_GaussianPair`, `Triangular_Signs_DeletedAccuracy`, `Triangular_Signs_DeletedExponential`, `Triangular_Signs_DeletedJets`, `Triangular_Signs_Exceptional`, `Triangular_Signs_GaussianDeleted`, `Triangular_Signs_NearSigns`, `Triangular_Signs_SineBarrierBase`, `Triangular_Signs_SineGridCover`, `Triangular_Signs_SineGridDefs`, `Triangular_Taylor_TaylorPhase`, `Triangular_Taylor_TaylorRowsBase`.
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T015`, `OAIQ262T016`, `OAIQ262T018`, `OAIQ262T019` and `OAIQ262T084`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian

section
-- module Solutions.OAIQ262_TG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
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
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
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
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Auxiliary_ExponentialTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Envelope

lemma factorial_term_step {d r : ℝ} {k : ℕ} (hd : 0 ≤ d) (hdr : d ≤ r*(k+1)) :
    d^(k+1)/(k+1).factorial  ≤  r*(d^k/k.factorial) := by
  have hk : (0:ℝ)<k+1 := by positivity
  have hf : (0:ℝ)<k.factorial := by positivity
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  apply (div_le_iff₀ (mul_pos hk hf)).mpr
  have hh := mul_le_mul_of_nonneg_left hdr (pow_nonneg hd k)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
lemma factorial_tail_geometric {d r : ℝ} (N : ℕ) (hd : 0 ≤ d) (hr : 0 ≤ r)
    (hdr : d ≤ r*(N+1)) (i : ℕ) :
    d^(i+N)/(i+N).factorial  ≤  (d^N/N.factorial)*r^i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hni : (N:ℝ)+1 ≤ (i+N:ℕ)+1 := by exact_mod_cast (show N+1 ≤ i+N+1 by omega)
    have hs := factorial_term_step (k:=i+N) hd (hdr.trans (mul_le_mul_of_nonneg_left hni hr))
    calc
      d^(i+1+N)/(i+1+N).factorial = d^(i+N+1)/(i+N+1).factorial := by rw [show i+1+N=i+N+1 by omega]
      _  ≤  r*(d^(i+N)/(i+N).factorial) := hs
      _  ≤  r*((d^N/N.factorial)*r^i) := mul_le_mul_of_nonneg_left ih hr
      _ = _ := by rw [pow_succ]; ring
lemma exp_tail_bound {d r : ℝ} (N : ℕ) (hd : 0 ≤ d) (hr : 0 ≤ r) (hr1 : r<1)
    (hdr : d ≤ r*(N+1)) :
    Real.exp d-(∑ i ∈ Finset.range N, d^i/i.factorial)  ≤  (d^N/N.factorial)/(1-r) := by
  have hf := NormedSpace.expSeries_div_summable d
  have ht : ∑' i : ℕ, d^i/i.factorial = Real.exp d := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp d).tsum_eq
  have he := hf.sum_add_tsum_nat_add N
  rw [ht] at he
  have hh := Summable.tsum_le_tsum (factorial_tail_geometric N hd hr hdr)
    ((summable_nat_add_iff N).mpr hf) ((summable_geometric_of_lt_one hr hr1).mul_left (d^N/N.factorial))
  rw [tsum_mul_left,tsum_geometric_of_lt_one hr hr1] at hh
  rw [div_eq_mul_inv]
  linarith
lemma complex_exp_tail_bound (z : ℂ) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1)
    (hz : ‖z‖ ≤ r*(N+1)) :
    ‖Complex.exp z-∑ i ∈ Finset.range N, z^i/i.factorial‖  ≤ 
      (‖z‖^N/N.factorial)/(1-r) :=
  (Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z N).trans
    (exp_tail_bound N (norm_nonneg z) hr hr1 hz)
end AtomicTriangular.Envelope
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_PolytopeInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def bernsteinRows (n : ℕ) (a : Fin (n+1) → Fin 8 → ℝ)
    (d : Fin (n+1)) (r : Fin 8) : ℝ :=
  ∑ l : Fin (n+1), ((d.val.choose l.val:ℝ)/(n.choose l.val:ℝ))*a l r
lemma bernsteinRows_dot (n : ℕ) (a : Fin (n+1) → Fin 8 → ℝ)
    (d : Fin (n+1)) (e : Fin 8 → ℝ) :
    (∑ r : Fin 8, bernsteinRows n a d r*e r) =
      ∑ l : Fin (n+1), ((d.val.choose l.val:ℝ)/(n.choose l.val:ℝ))*(∑ r : Fin 8, a l r*e r) := by
  simp only [bernsteinRows,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_NodeJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ComplexConjugate
namespace AtomicTriangular.Construction

lemma factor_second_third (g : ℂ → ℂ) (hg : Differentiable ℂ g) (n : ℂ) :
    iteratedDeriv 2 (fun s => (s-n)^2*g s) n = 2*g n ∧
    iteratedDeriv 3 (fun s => (s-n)^2*g s) n = 6*deriv g n := by
  have hp (k : ℕ) : iteratedDeriv k (fun s : ℂ => (s-n)^2) n =
      (2:ℕ).descFactorial k * (n-n)^(2-k) := by
    have hh := congrFun (iteratedDeriv_comp_sub_const k (fun s : ℂ => s^2) n) n
    exact hh.trans (iteratedDeriv_pow 2 k)
  have hpoly : ContDiff ℂ 3 (fun s : ℂ => (s-n)^2) := by fun_prop
  constructor
  · rw [iteratedDeriv_fun_mul (hpoly.of_le (by norm_num)).contDiffAt hg.contDiff.contDiffAt]
    simp [Finset.sum_range_succ,hp,iteratedDeriv_zero]
  · rw [iteratedDeriv_fun_mul hpoly.contDiffAt hg.contDiff.contDiffAt]
    norm_num [Finset.sum_range_succ,hp,iteratedDeriv_one]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction Complex
def nearNode (n : Fin 7) : ℤ := finiteNode ⟨n.val,by omega⟩

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_ActualInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma finiteNode_surj {n : ℤ} (hn : n∈FiniteNodes) : ∃ i : Fin 10,finiteNode i=n := by
  have hall : ∀ n∈FiniteNodes,∃ i : Fin 10,finiteNode i=n := by decide +kernel
  exact hall n hn
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_DeletedExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Envelope
open Complex

def expDeleted (w : ℂ) (m v : ℝ) : ℂ :=
  if v=0 then exp (w*(m:ℂ))*w^2/2
  else (exp (w*((m+v:ℝ):ℂ))-exp (w*(m:ℂ))-(v:ℂ)*w*exp (w*(m:ℂ)))/(v:ℂ)^2
def expDeletedTaylor (w : ℂ) (m v : ℝ) : ℂ :=
  exp (w*(m:ℂ))*w^2*∑ j ∈ Finset.range 21, (w*(v:ℂ))^j/((j+2).factorial:ℂ)
lemma exp_sum_split (z : ℂ) :
    (∑ i ∈ Finset.range 23, z^i/(i.factorial:ℂ)) =
      1+z+z^2*∑ j ∈ Finset.range 21, z^j/((j+2).factorial:ℂ) := by
  rw [show (23:ℕ)=2+21 by norm_num,Finset.sum_range_add]
  rw [show (∑ i ∈ Finset.range 2, z^i/(i.factorial:ℂ))=1+z by
    simp [Finset.sum_range_succ]]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  simp only [Nat.add_comm 2 j]
  ring
lemma expDeleted_zero (w : ℂ) (m : ℝ) : expDeleted w m 0=expDeletedTaylor w m 0 := by
  simp [expDeleted,expDeletedTaylor,Finset.sum_range_succ]
  ring
end AtomicTriangular.Envelope
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_DeletedJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex
namespace AtomicTriangular.Construction

def complexDeleted (F : ℕ → ℝ → ℂ) (m v : ℝ) : ℂ :=
  if v=0 then F 2 m/2 else (F 0 (m+v)-F 0 m-(v:ℂ)*F 1 m)/(v:ℂ)^2
def complexTaylor (F : ℕ → ℝ → ℂ) (m v : ℝ) : ℂ :=
  ∑ j ∈ Finset.range 21,F (j+2) m*(v:ℂ)^j/((j+2).factorial:ℂ)
lemma complexDeleted_add (F G : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexDeleted (fun k s => F k s+G k s) m v=complexDeleted F m v+complexDeleted G m v := by
  unfold complexDeleted
  split_ifs <;> ring
lemma complexDeleted_mul (a : ℂ) (F : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexDeleted (fun k s => a*F k s) m v=a*complexDeleted F m v := by
  unfold complexDeleted
  split_ifs <;> ring
lemma complexTaylor_add (F G : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexTaylor (fun k s => F k s+G k s) m v=complexTaylor F m v+complexTaylor G m v := by
  simp [complexTaylor,add_mul,add_div,Finset.sum_add_distrib]
lemma complexTaylor_mul (a : ℂ) (F : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexTaylor (fun k s => a*F k s) m v=a*complexTaylor F m v := by
  simp [complexTaylor,Finset.mul_sum,mul_assoc,mul_div_assoc]
lemma complexTaylor_sum {ι : Type*} (S : Finset ι) (F : ι → ℕ → ℝ → ℂ) (m v : ℝ) :
    complexTaylor (fun k s => ∑ i∈S,F i k s) m v=∑ i∈S,complexTaylor (F i) m v := by
  simp only [complexTaylor,Finset.sum_mul,Finset.sum_div]
  exact Finset.sum_comm
lemma complexDeleted_exp (w : ℂ) (m v : ℝ) :
    complexDeleted (fun k s => exp (w*(s:ℂ))*w^k) m v=Envelope.expDeleted w m v := by
  unfold complexDeleted Envelope.expDeleted
  split_ifs <;> simp only [pow_zero,pow_one,mul_one]
  ring
lemma complexTaylor_exp (w : ℂ) (m v : ℝ) :
    complexTaylor (fun k s => exp (w*(s:ℂ))*w^k) m v=Envelope.expDeletedTaylor w m v := by
  simp only [complexTaylor,Envelope.expDeletedTaylor,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add,mul_pow]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRowsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def nearDisplacementNum : Fin 7 → Fin 2 → ℤ :=
  ![![-2,2],![-2,1],![-1,3],![-3,2],![-2,3],![-3,1],![-1,3]]
def nearDisplacement (n : Fin 7) (y : Fin 2) : ℝ := nearDisplacementNum n y / 2
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FiniteRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

def complexError (F : ℕ → ℝ → ℂ) (m v : ℝ) : ℂ := complexDeleted F m v-complexTaylor F m v
lemma complexError_add (F G : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexError (fun k s => F k s+G k s) m v=complexError F m v+complexError G m v := by
  simp only [complexError,complexDeleted_add,complexTaylor_add]
  ring
lemma complexError_mul (a : ℂ) (F : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexError (fun k s => a*F k s) m v=a*complexError F m v := by
  simp only [complexError,complexDeleted_mul,complexTaylor_mul]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Energy_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology ENNReal NNReal
open Classical
open Filter

noncomputable section
namespace TriangularUniversal

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def triangularPoint (jk : ℤ × ℤ) : Plane :=
  Real.sqrt (2 / Real.sqrt 3) •
    (EuclideanSpace.single 0 ((jk.1 : ℝ) + (jk.2 : ℝ) / 2) +
     EuclideanSpace.single 1 ((jk.2 : ℝ) * Real.sqrt 3 / 2))

end TriangularUniversal
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Energy_Mixtures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open Classical Filter
namespace TriangularUniversal
def b : ℝ := Real.sqrt 3 / 2

end TriangularUniversal

open scoped BigOperators Topology NNReal ENNReal Polynomial
open Filter Finset MeasureTheory
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineBarrierBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset Set Filter
namespace AtomicTriangular.Construction

def sinePolynomial (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040+x^9/362880-x^11/39916800
lemma sinePolynomial_lower {x : ℝ} (hx : 0≤x) (hx2 : x≤2) : sinePolynomial x≤Real.sin x := by
  have ha : Antitone (fun j : ℕ => x^(2*j+1)/((2*j+1).factorial:ℝ)) := by
    apply antitone_nat_of_succ_le
    intro j
    have hf : (0:ℝ)<((2*j+1).factorial:ℝ) := by positivity
    have hn : (0:ℝ)<(2*j+2:ℕ)*(2*j+3:ℕ) := by positivity
    have hd : (((2*(j+1)+1).factorial:ℕ):ℝ) = ((2*j+3:ℕ):ℝ)*((2*j+2:ℕ):ℝ)*((2*j+1).factorial:ℝ) := by
      rw [show 2*(j+1)+1=(2*j+1)+1+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
      push_cast
      ring
    rw [hd,show 2*(j+1)+1=2*j+1+2 by omega,pow_add]
    apply (div_le_div_iff₀ (by positivity) hf).mpr
    have hb : x^2≤((2*j+3:ℕ):ℝ)*((2*j+2:ℕ):ℝ) := by
      have hj : (0:ℝ)≤j := Nat.cast_nonneg j
      push_cast
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg (pow_nonneg hx (2*j+1)) hf.le)
    nlinarith
  have ht : Tendsto (fun n : ℕ => ∑ j ∈ range n, (-1:ℝ)^j*(x^(2*j+1)/((2*j+1).factorial:ℝ))) atTop (nhds (Real.sin x)) := by
    simpa only [mul_div_assoc] using (Real.hasSum_sin x).tendsto_sum_nat
  have hh := ha.alternating_series_le_tendsto ht 3
  norm_num [sum_range_succ,sinePolynomial] at hh ⊢
  linarith

def piLow : ℚ := 314159265358979/100000000000000
def piHigh : ℚ := 15707963267949/5000000000000

def sineLower (d : ℚ) : ℚ :=
  let l:=piLow*d/36
  let u:=piHigh*d/36
  2*(l-u^3/6+l^5/120-u^7/5040+l^9/362880-u^11/39916800)

def vanishingLower (v : ℚ) : ℚ := 2*(piLow/36-(piHigh/36)^3*v^2/6)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGridDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def localPivot (u : Fin 30) : Fin 15 := ⟨u.val/2,by omega⟩
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Exceptional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def freezeParameter (z : ℝ) (e : Fin 8 → ℝ) : Fin 8 → ℝ :=
  fun r => if r.val=0 then z else e r
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_DeletedAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
def nearBase (n : Fin 7) (y : Fin 2) : Fin 5 := if n.val=0 then (if y.val=0 then 0 else 1) else 2
def nearError (n : Fin 7) (y : Fin 2) : ℝ := if n.val=0 then (if y.val=0 then 18/1000 else 3/1000) else 16/100000
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_GaussianDeleted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction

def pade0 (x : ℝ) := Real.exp (-x)*(6+4*x+x^2)-6+2*x
def pade1 (x : ℝ) := 2-Real.exp (-x)*(2+2*x+x^2)
lemma pade0_deriv (x : ℝ) : HasDerivAt pade0 (pade1 x) x := by
  have he := ((hasDerivAt_id x).neg).exp
  have hp := (((hasDerivAt_const x (6:ℝ)).add ((hasDerivAt_id x).const_mul 4)).add ((hasDerivAt_id x).pow 2))
  have hh := ((he.mul hp).sub_const 6).add ((hasDerivAt_id x).const_mul 2)
  convert hh using 1 <;> first | rfl | (dsimp [pade1]; ring)
lemma pade1_deriv (x : ℝ) : HasDerivAt pade1 (x^2*Real.exp (-x)) x := by
  have he := ((hasDerivAt_id x).neg).exp
  have hp := (((hasDerivAt_const x (2:ℝ)).add ((hasDerivAt_id x).const_mul 2)).add ((hasDerivAt_id x).pow 2))
  have hh := (he.mul hp).const_sub 2
  convert hh using 1 <;> first | rfl | (dsimp; ring)
lemma pade1_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ pade1 x := by
  have hm := monotone_of_hasDerivAt_nonneg pade1_deriv (fun t => mul_nonneg (sq_nonneg t) (Real.exp_pos _).le)
  have hh := hm hx
  simpa [pade1] using hh
lemma pade0_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ pade0 x := by
  have hm : MonotoneOn pade0 (Ici 0) := monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (by unfold pade0; fun_prop) (fun s _ => (pade0_deriv s).differentiableAt.differentiableWithinAt)
    (fun s hs => by rw [(pade0_deriv s).deriv]; exact pade1_nonneg (interior_subset hs))
  have hh := hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  simpa [pade0] using hh
lemma pade_rational {x : ℝ} (hx : 0<x) :
    (3+x)/(6+4*x+x^2) ≤ (Real.exp (-x)-1+x)/x^2 := by
  have hd : 0<6+4*x+x^2 := by positivity
  rw [div_le_div_iff₀ hd (sq_pos_of_pos hx)]
  have hh := pade0_nonneg hx.le
  dsimp [pade0] at hh
  nlinarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_NearSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma near_cell_cover {s : ℝ} (hs : s∈Icc 0 (29/2)) :
    ∃ (n : Fin 7) (y : Fin 2) (τ : ℝ),τ∈Icc 0 1 ∧ s=nearNode n+nearDisplacement n y*τ := by
  by_cases h0 : s ≤ 1
  · refine ⟨0,0,(s-1)/(-1),?_,?_⟩
    · constructor <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (0:Fin 7)=(1:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (0:Fin 7) (0:Fin 2)=(-2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h1 : s ≤ 2
  · refine ⟨0,1,(s-1)/1,?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (0:Fin 7)=(1:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (0:Fin 7) (1:Fin 2)=(2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h2 : s ≤ 3
  · refine ⟨1,0,(s-3)/(-1),?_,?_⟩
    · constructor <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (1:Fin 7)=(3:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (1:Fin 7) (0:Fin 2)=(-2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h3 : s ≤ (7/2)
  · refine ⟨1,1,(s-3)/(1/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (1:Fin 7)=(3:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (1:Fin 7) (1:Fin 2)=(1:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h4 : s ≤ 4
  · refine ⟨2,0,(s-4)/(-1/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (2:Fin 7)=(4:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (2:Fin 7) (0:Fin 2)=(-1:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h5 : s ≤ (11/2)
  · refine ⟨2,1,(s-4)/(3/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (2:Fin 7)=(4:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (2:Fin 7) (1:Fin 2)=(3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h6 : s ≤ 7
  · refine ⟨3,0,(s-7)/(-3/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (3:Fin 7)=(7:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (3:Fin 7) (0:Fin 2)=(-3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h7 : s ≤ 8
  · refine ⟨3,1,(s-7)/1,?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (3:Fin 7)=(7:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (3:Fin 7) (1:Fin 2)=(2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h8 : s ≤ 9
  · refine ⟨4,0,(s-9)/(-1),?_,?_⟩
    · constructor <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (4:Fin 7)=(9:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (4:Fin 7) (0:Fin 2)=(-2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h9 : s ≤ (21/2)
  · refine ⟨4,1,(s-9)/(3/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (4:Fin 7)=(9:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (4:Fin 7) (1:Fin 2)=(3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h10 : s ≤ 12
  · refine ⟨5,0,(s-12)/(-3/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (5:Fin 7)=(12:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (5:Fin 7) (0:Fin 2)=(-3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h11 : s ≤ (25/2)
  · refine ⟨5,1,(s-12)/(1/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (5:Fin 7)=(12:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (5:Fin 7) (1:Fin 2)=(1:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h12 : s ≤ 13
  · refine ⟨6,0,(s-13)/(-1/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (6:Fin 7)=(13:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (6:Fin 7) (0:Fin 2)=(-1:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  refine ⟨6,1,(s-13)/(3/2),?_,?_⟩
  · constructor <;> norm_num <;> linarith [hs.1,hs.2]
  · norm_num only [show nearNode (6:Fin 7)=(13:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (6:Fin 7) (1:Fin 2)=(3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
    ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGridCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
lemma unit_grid_cover {x : ℝ} (hx : x∈Icc 0 1) :
    ∃ k : Fin 100, (k.val:ℝ)/100≤x ∧ x≤(k.val+1:ℝ)/100 := by
  by_cases he : x=1
  · subst x
    exact ⟨99,by norm_num,by norm_num⟩
  · have hx1 : x<1 := lt_of_le_of_ne hx.2 he
    let n : ℕ := ⌊100*x⌋₊
    have hn1 : (n:ℝ)≤100*x := Nat.floor_le (by nlinarith [hx.1])
    have hn2 : 100*x<(n:ℝ)+1 := Nat.lt_floor_add_one _
    have hn : n<100 := by
      by_contra! hh
      have : (100:ℝ)≤n := by exact_mod_cast hh
      nlinarith
    exact ⟨⟨n,hn⟩,by dsimp <;> linarith,by dsimp <;> linarith⟩
def localBoundary (n : ℕ) : ℚ :=
  if hn : n<31 then ![-5/2,0,1/2,1,2,3,7/2,4,11/2,7,8,9,21/2,12,25/2,13,29/2,16,35/2,19,20,21,23,25,26,27,55/2,28,59/2,31,67/2] ⟨n,hn⟩ else 0
lemma local_boundary_end : localBoundary 0= -5/2 ∧ localBoundary 30=67/2 := by decide +kernel
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_GaussianPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped FourierTransform SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular
open Construction

lemma gaussian_radial (α : ℝ) : Radial (gaussian α) := by
  intro x y hxy
  simp only [gaussian,hxy]
lemma realFourier_sub (f g : 𝓢(Plane,ℝ)) (w : Plane) :
    realFourier ((f-g : 𝓢(Plane,ℝ)) : Plane → ℝ) w=realFourier f w-realFourier g w := by
  have hf : Integrable (fun x => (f x:ℂ)) := f.integrable.ofReal
  have hg : Integrable (fun x => (g x:ℂ)) := g.integrable.ofReal
  simp only [realFourier,sub_apply,ofReal_sub,Real.fourier_eq,smul_sub]
  rw [integral_sub ((Real.fourierIntegral_convergent_iff w).mpr hf)
    ((Real.fourierIntegral_convergent_iff w).mpr hg)]

structure GaussianPair (α : ℝ) where
  first : 𝓢(Plane,ℝ)
  second : 𝓢(Plane,ℝ)
  first_radial : Radial first
  second_radial : Radial second
  fourier_first : ∀ w, realFourier first w=(second w:ℂ)
  fourier_second : ∀ w, realFourier second w=(first w:ℂ)
  minorant : ∀ x, first x ≤ gaussian α x
  positive : ∀ x, 0 ≤ second x
  contact : ∀ x (n : Construction.Node), Construction.radial x=n.val → first x=gaussian α x
  zeros : ∀ x (n : Construction.Node), Construction.radial x=n.val → second x=0

end AtomicTriangular
end

end OAI
end


