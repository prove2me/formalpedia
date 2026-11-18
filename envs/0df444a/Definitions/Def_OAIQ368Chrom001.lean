-- Prove2me | Definitions.Def_OAIQ368Chrom001
-- name    : OAIQ368Chrom001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:03:41.763344+00:00
-- url     : https://prove2.me/theorems/05f0dd58-b072-48ce-bde9-ef9044818c4c
-- title:
--   Definitions bundle OAIQ368Chrom001 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 543 declarations of OpenAI's Lean: 173 definitions, 5 inductive types or structures, 8 instances and 357 theorems. The definitions and types are `OAI.ElementaryPositivity.AffineCut.afterSide`, `OAI.ElementaryPositivity.AffineCut.beforeSide`, `OAI.ElementaryPositivity.Deshear.deshear`, `OAI.ElementaryPositivity.FiniteEventTraversal.intervalWord`, `OAI.ElementaryPositivity.FiniteRayGeometry.GenericOffset`, `OAI.ElementaryPositivity.FiniteRayGeometry.forbidden`, `OAI.ElementaryPositivity.FormalLog.log`, `OAI.ElementaryPositivity.FormalLog.logPolynomial`, `OAI.ElementaryPositivity.FormalLog.ncDerivative`, `OAI.ElementaryPositivity.FormalLog.traceSeries`, `OAI.ElementaryPositivity.PlanarRayOrder.slope`, `OAI.ElementaryPositivity.PowerSeriesAdjoint.adjoint`, `OAI.ElementaryPositivity.PowerSeriesDilate.dilate`, `OAI.ElementaryPositivity.PowerSeriesSplit.leftFactor`, `OAI.ElementaryPositivity.PowerSeriesSplit.negativeFactor`, `OAI.ElementaryPositivity.PowerSeriesSplit.pairCoefficients`, `OAI.ElementaryPositivity.PowerSeriesSplit.positiveFactor`, `OAI.ElementaryPositivity.PowerSeriesSplit.rightFactor`, `OAI.ElementaryPositivity.PowerSeriesSplit.zeroFactor`, `OAI.ElementaryPositivity.QuantumTorus.BiBounded`, `OAI.ElementaryPositivity.QuantumTorus.BiSupported`, `OAI.ElementaryPositivity.QuantumTorus.ChamberGeneric`, `OAI.ElementaryPositivity.QuantumTorus.CompletedPositive`, `OAI.ElementaryPositivity.QuantumTorus.FullHomogeneous`, `OAI.ElementaryPositivity.QuantumTorus.GenericLinePath`, `OAI.ElementaryPositivity.QuantumTorus.GenericLinePath.OnCutSide`, `OAI.ElementaryPositivity.QuantumTorus.GenericLinePath.single`, `OAI.ElementaryPositivity.QuantumTorus.GenericLinePath.trans`, `OAI.ElementaryPositivity.QuantumTorus.GenericLineSegment`, `OAI.ElementaryPositivity.QuantumTorus.GenericLineSegment.finish`, `OAI.ElementaryPositivity.QuantumTorus.GenericLineSegment.start`, `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree`, `OAI.ElementaryPositivity.QuantumTorus.LaurentBounded`, `OAI.ElementaryPositivity.QuantumTorus.LexSigns`, `OAI.ElementaryPositivity.QuantumTorus.LineRayData`, `OAI.ElementaryPositivity.QuantumTorus.OnPositiveRay`, `OAI.ElementaryPositivity.QuantumTorus.RayGeneric`, `OAI.ElementaryPositivity.QuantumTorus.RegradeBound`, `OAI.ElementaryPositivity.QuantumTorus.RegularCovector`, `OAI.ElementaryPositivity.QuantumTorus.SeriesGraded` and 138 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_FiniteCovectorPerturbation`, `Chromatic_GradedAlgebra_GradedFormalLog`, `Chromatic_GradedAlgebra_HNSeries`, `Chromatic_GradedAlgebra_KernelTraceLog`, `Chromatic_GradedAlgebra_LaurentDeshear`, `Chromatic_GradedAlgebra_LaurentHomogenize`, `Chromatic_GradedAlgebra_LaurentRegrade`, `Chromatic_GradedAlgebra_MutationCoordinates`, `Chromatic_GradedAlgebra_MutationDegreeBound`, `Chromatic_GradedAlgebra_MutationRootMap`, `Chromatic_GradedAlgebra_NoncommExpand`, `Chromatic_GradedAlgebra_NoncommSeriesCalculus`, `Chromatic_GradedAlgebra_NonpHomogenize`, `Chromatic_GradedAlgebra_NonpRegrade`, `Chromatic_GradedAlgebra_NonpRegradeFaithful`, `Chromatic_GradedAlgebra_PowerSeriesProductLeading`, `Chromatic_GradedAlgebra_PowerSeriesSplit`, `Chromatic_GradedAlgebra_PowerSeriesSplitLeading`, `Chromatic_GradedAlgebra_QuantumTorusAlgebra`, `Chromatic_GradedAlgebra_QuantumTorusSignFactors`, `Chromatic_GradedAlgebra_RationalLaurentFaithful`, `Chromatic_GradedAlgebra_RealRootCoordinates`, `Chromatic_GradedAlgebra_RegradeLog`, `Chromatic_GradedAlgebra_RootCoefficients`, `Chromatic_GradedAlgebra_RootTruncation`, `Chromatic_GradedAlgebra_SimpleBinomial`, `Chromatic_GradedAlgebra_SplitContinuity`, `Chromatic_GradedAlgebra_Strict`, `Chromatic_GradedAlgebra_TraceLogDerivative`, `Chromatic_GradedAlgebra_TruncatedChart`, `Chromatic_GradedAlgebra_WeightedTorusSeries`, `Chromatic_QuantumTorus_IndexedUnit`, `Chromatic_QuantumTorus_MonomialConjugation`, `Chromatic_QuantumTorus_MutationFiberArithmetic`, `Chromatic_QuantumTorus_MutationInfinityBound`, `Chromatic_QuantumTorus_NormalizedMonomialAction`, `Chromatic_QuantumTorus_PureFaceProjection`, `Chromatic_QuantumTorus_PureProductSplit`, `Chromatic_QuantumTorus_QuantumTorus`, `Chromatic_QuantumTorus_RationalFiberTorus`, `Chromatic_QuantumTorus_RationalTorusEmbedding`, `Chromatic_QuantumTorus_SimplePlaneGeometry`, `Chromatic_QuantumTorus_SymplecticTorusMap`, `Chromatic_QuantumTorus_TorusProjection`, `Chromatic_Shuffle_QuantumTorusTrace`, `Chromatic_Walls_AdjointExpansion`, `Chromatic_Walls_AffineCutTelescoping`, `Chromatic_Walls_AllOrderSectionLine`, `Chromatic_Walls_ChartRefinement`, `Chromatic_Walls_ComparisonLine`, `Chromatic_Walls_CompletedBiUnit`, `Chromatic_Walls_CompletedInverse`, `Chromatic_Walls_FiniteElementaryAdjoint`, `Chromatic_Walls_FinitePathPerturbation`, `Chromatic_Walls_FiniteRayGeometry`, `Chromatic_Walls_FiniteSignCharts`, `Chromatic_Walls_GenericLineJoining`, `Chromatic_Walls_GlobalWallPositive`, `Chromatic_Walls_HNTorusFactor`, `Chromatic_Walls_IncomingDisplacement`, `Chromatic_Walls_IncomingRayElement`, `Chromatic_Walls_IncomingSystem`, `Chromatic_Walls_IsolatedPositivePlane`, `Chromatic_Walls_LaurentCompletion`, `Chromatic_Walls_LineOldTransport`, `Chromatic_Walls_MutatedLineCompletion`, `Chromatic_Walls_MutatedNoCutTransport`, `Chromatic_Walls_MutationLaurentCompletion`, `Chromatic_Walls_MutationMonomialAction`, `Chromatic_Walls_NegativeRayCrossing`, `Chromatic_Walls_NonpJoint`, `Chromatic_Walls_OffCutJoint`, `Chromatic_Walls_PlanarJointFactorization`, `Chromatic_Walls_PlanarRayOrder`, `Chromatic_Walls_PlanarRefinement`, `Chromatic_Walls_PolynomialAdjointCoefficients`, `Chromatic_Walls_PowerSeriesThreeFactors`, `Chromatic_Walls_PureCutFactorization`, `Chromatic_Walls_QuantumTorusChartCompletion`, `Chromatic_Walls_QuantumTorusRaySeries`, `Chromatic_Walls_QuantumTorusWallLeading`, `Chromatic_Walls_RationalFiberScale`, `Chromatic_Walls_RayIncomingIdentification`, `Chromatic_Walls_RayLaurentExpansion`, `Chromatic_Walls_RootProducts`, `Chromatic_Walls_SectionRayTransition`, `Chromatic_Walls_SimpleAdjointFiber`, `Chromatic_Walls_SimpleIncomingData`, `Chromatic_Walls_SimpleIncomingElement`, `Chromatic_Walls_TorusAdjointExpansion`, `Chromatic_Walls_TruncatedFactorization`, `Chromatic_Walls_WallLineInitial`, `Chromatic_Walls_WallUnits`, `Chromatic_Walls_WeightedRay`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom003`, `OAIQ368Chrom004`, `OAIQ368Chrom009`, `OAIQ368Chrom010`, `OAIQ368Chrom013`, `OAIQ368Chrom017`, `OAIQ368Chrom018` and `OAIQ368Chrom071`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ368_CHROM.Compat
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
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_QuantumTorus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus

variable {R M : Type*} [CommRing R] [AddCommGroup M]

@[reducible] def Torus (_ : Rˣ) (_ : M →+ M →+ ℤ) := M →₀ R

namespace Torus
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)

noncomputable instance instAddCommGroup : AddCommGroup (Torus v Ω) := inferInstanceAs (AddCommGroup (M →₀ R))

noncomputable def monomial (m : M) (r : R) : Torus v Ω := Finsupp.single m r
noncomputable def multiply (f g : Torus v Ω) : Torus v Ω :=
  Finsupp.sum f fun m a => Finsupp.sum g fun n b =>
    Finsupp.single (m+n) (a*b*↑(v^(Ω m n)))

noncomputable instance instMul : Mul (Torus v Ω) := ⟨multiply v Ω⟩
noncomputable instance instOne : One (Torus v Ω) := ⟨monomial v Ω 0 1⟩

@[simp] lemma monomial_zero (m : M) : monomial v Ω m (0 : R) = 0 := Finsupp.single_zero _
@[simp] lemma monomial_add (m : M) (a b : R) :
    monomial v Ω m (a+b) = monomial v Ω m a + monomial v Ω m b := Finsupp.single_add ..
lemma monomial_smul (m : M) (a b : R) :
    monomial v Ω m (a*b) = a • monomial v Ω m b := by
  simp only [monomial, Finsupp.smul_single, smul_eq_mul]

@[simp] lemma mul_zero (f : Torus v Ω) : f*0 = 0 := by simp [HMul.hMul, Mul.mul, multiply]
@[simp] lemma zero_mul (f : Torus v Ω) : (0 : Torus v Ω)*f = 0 := by
  simp [HMul.hMul, Mul.mul, multiply]

lemma add_mul (f g h : Torus v Ω) : (f+g)*h = f*h+g*h := by
  classical
  change multiply v Ω (f+g) h = multiply v Ω f h + multiply v Ω g h
  simp only [multiply]
  rw [Finsupp.sum_add_index']
  · intro m
    simp
  · intro m a b
    simp only [_root_.add_mul, Finsupp.single_add, Finsupp.sum_add]

lemma mul_add (f g h : Torus v Ω) : f*(g+h) = f*g+f*h := by
  classical
  change multiply v Ω f (g+h) = multiply v Ω f g + multiply v Ω f h
  simp only [multiply]
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro m hm
  rw [Finsupp.sum_add_index']
  · intro n
    simp
  · intro n a b
    simp only [_root_.mul_add, _root_.add_mul, Finsupp.single_add]

@[simp] lemma monomial_mul_monomial (m n : M) (a b : R) :
    monomial v Ω m a * monomial v Ω n b =
      monomial v Ω (m+n) (a*b*↑(v^(Ω m n))) := by
  classical
  change multiply v Ω (Finsupp.single m a) (Finsupp.single n b) = _
  simp only [multiply, monomial, Finsupp.sum_single_index, MulZeroClass.zero_mul,
    MulZeroClass.mul_zero, Finsupp.single_zero]

lemma mul_assoc (f g h : Torus v Ω) : (f*g)*h=f*(g*h) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp only [add_mul, hf, hf']
  | single m a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' hg hg' => simp only [mul_add, add_mul, hg, hg']
    | single n b =>
      induction h using Finsupp.induction_linear with
      | zero => simp
      | add h h' hh hh' => simp only [mul_add, hh, hh']
      | single p c =>
        change (monomial v Ω m a * monomial v Ω n b) * monomial v Ω p c =
          monomial v Ω m a * (monomial v Ω n b * monomial v Ω p c)
        simp only [monomial_mul_monomial, map_add, AddMonoidHom.add_apply, add_assoc]
        congr 1
        simp only [zpow_add, Units.val_mul]
        ring

@[simp] lemma one_mul (f : Torus v Ω) : (1 : Torus v Ω)*f=f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [mul_add, hf, hg]
  | single m a =>
    change monomial v Ω 0 1 * monomial v Ω m a = monomial v Ω m a
    simp only [monomial_mul_monomial, map_zero, AddMonoidHom.zero_apply,
      zero_add, _root_.one_mul, zpow_zero, Units.val_one, _root_.mul_one]

@[simp] lemma mul_one (f : Torus v Ω) : f*(1 : Torus v Ω)=f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [add_mul, hf, hg]
  | single m a =>
    change monomial v Ω m a * monomial v Ω 0 1 = monomial v Ω m a
    simp only [monomial_mul_monomial, map_zero, add_zero, _root_.mul_one, zpow_zero, Units.val_one]

noncomputable instance instRing : Ring (Torus v Ω) :=
  Ring.ofMinimalAxioms _root_.add_assoc _root_.zero_add _root_.neg_add_cancel
    (mul_assoc v Ω) (one_mul v Ω) (mul_one v Ω) (mul_add v Ω) (add_mul v Ω)

noncomputable def X (m : M) : Torus v Ω := monomial v Ω m 1

@[simp] lemma X_zero : X v Ω 0 = 1 := rfl
lemma X_mul_X (m n : M) : X v Ω m * X v Ω n = (↑(v^(Ω m n)) : R) • X v Ω (m+n) := by
  simp only [X, monomial_mul_monomial, _root_.one_mul]
  simpa only [_root_.mul_one] using monomial_smul v Ω (m+n) (↑(v^(Ω m n)) : R) 1

lemma X_mul_X_of_pairing_zero (m n : M) (h : Ω m n = 0) :
    X v Ω m * X v Ω n = X v Ω (m+n) := by
  simp [X_mul_X, h]

end Torus
end ElementaryPositivity.QuantumTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_QuantumTorusAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus.Torus
noncomputable section
variable {S R M : Type*} [CommSemiring S] [CommRing R] [Algebra S R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)

lemma scalar_one (r : S) : r • (1 : Torus v Ω)=monomial v Ω 0 (r • (1:R)) := by
  change r • Finsupp.single 0 (1:R)=Finsupp.single 0 (r • (1:R))
  exact Finsupp.smul_single _ _ _

lemma scalar_one_mul (r : S) (f : Torus v Ω) :
    (r • (1 : Torus v Ω))*f=r • f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [mul_add,hf,hg,smul_add]
  | single m a =>
    change (r • (1 : Torus v Ω))*monomial v Ω m a=r • monomial v Ω m a
    rw [scalar_one,monomial_mul_monomial]
    simp only [map_zero,AddMonoidHom.zero_apply,zpow_zero,Units.val_one,zero_add,_root_.mul_one,
      smul_mul_assoc,_root_.one_mul,monomial,Finsupp.smul_single]

lemma mul_scalar_one (r : S) (f : Torus v Ω) :
    f*(r • (1 : Torus v Ω))=r • f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [add_mul,hf,hg,smul_add]
  | single m a =>
    change monomial v Ω m a*(r • (1 : Torus v Ω))=r • monomial v Ω m a
    rw [scalar_one,monomial_mul_monomial]
    simp only [map_zero,zpow_zero,Units.val_one,add_zero,_root_.mul_one,
      mul_smul_comm,_root_.mul_one,monomial,Finsupp.smul_single]

instance instAlgebra : Algebra S (Torus v Ω) := by
  letI : Module S (Torus v Ω) := inferInstanceAs (Module S (M →₀ R))
  exact @Algebra.ofModule' S (Torus v Ω) _ (Torus.instRing v Ω).toSemiring
    (inferInstanceAs (Module S (M →₀ R)))
    (scalar_one_mul (S:=S) v Ω) (mul_scalar_one (S:=S) v Ω)
end
end ElementaryPositivity.QuantumTorus.Torus
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_QuantumTorusSignFactors
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)

 def supportedSubring (C : AddSubmonoid M) : Subring (Torus v Ω) where
  carrier := {f | ∀m,m∉C → f m=0}
  zero_mem' := by intro m hm; rfl
  one_mem' := by
    intro m hm
    change Finsupp.single 0 (1:R) m=0
    exact Finsupp.single_eq_of_ne (fun he=>hm (he ▸ C.zero_mem))
  add_mem' := by intro f g hf hg m hm; change f m+g m=0; rw [hf m hm,hg m hm,add_zero]
  neg_mem' := by intro f hf m hm; change -f m=0; rw [hf m hm,neg_zero]
  mul_mem' := by
    classical
    intro f g hf hg m hm
    change (Torus.multiply v Ω f g) m=0
    simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro x hx
    apply Finset.sum_eq_zero
    intro y hy
    have hxC : x∈C := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hx) (hf x hn)
    have hyC : y∈C := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hy) (hg y hn)
    apply Finsupp.single_eq_of_ne
    intro he
    apply hm
    exact he ▸ C.add_mem hxC hyC

variable (h : M →+ ℝ)
 def nonpositiveCone : AddSubmonoid M where
  carrier := {m | h m≤0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change h a≤0 at ha
    change h b≤0 at hb
    change h (a+b)≤0
    rw [map_add]
    linarith
 def positiveProject : Torus v Ω →+ Torus v Ω :=
  Finsupp.filterAddHom (fun m=>0<h m)
 def zeroProject : Torus v Ω →+ Torus v Ω :=
  Finsupp.filterAddHom (fun m=>h m=0)

lemma nonpositive_iff (f : Torus v Ω) :
    f∈supportedSubring v Ω (nonpositiveCone h) ↔ positiveProject v Ω h f=0 := by
  classical
  change (∀m,¬h m≤0 → f m=0) ↔ Finsupp.filter (fun m=>0<h m) f=0
  constructor
  · intro hf
    ext m
    simp only [Finsupp.filter_apply,Finsupp.zero_apply]
    split_ifs with hm
    · exact hf m (not_le.mpr hm)
    · rfl
  · intro hf m hm
    have hh:=congrArg (fun f : M →₀ R=>f m) hf
    simpa only [Finsupp.filter_apply,not_le.mp hm,ite_true, if_true,Finsupp.zero_apply] using hh

lemma positiveProject_idem (f : Torus v Ω) :
    positiveProject v Ω h (positiveProject v Ω h f)=positiveProject v Ω h f := by
  classical
  ext m
  change (f.filter (fun m=>0<h m) |>.filter (fun m=>0<h m)) m = (f.filter (fun m=>0<h m)) m
  simp only [Finsupp.filter_apply]
  split_ifs <;> rfl
lemma zeroProject_idem (f : Torus v Ω) :
    zeroProject v Ω h (zeroProject v Ω h f)=zeroProject v Ω h f := by
  classical
  ext m
  change (f.filter (fun m=>h m=0) |>.filter (fun m=>h m=0)) m = (f.filter (fun m=>h m=0)) m
  simp only [Finsupp.filter_apply]
  split_ifs <;> rfl
lemma positive_zero_project (f : Torus v Ω) :
    positiveProject v Ω h (zeroProject v Ω h f)=0 := by
  classical
  ext m
  change (f.filter (fun m=>h m=0) |>.filter (fun m=>0<h m)) m = 0
  simp only [Finsupp.filter_apply]
  split_ifs <;> first | rfl | linarith

end
end ElementaryPositivity.QuantumTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_NoncommSeriesCalculus
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℚ R]

def ncDerivative : PowerSeries R→ₗ[ℚ] PowerSeries R where
  toFun F:=PowerSeries.mk (fun n=>(n+1) • coeff (n+1) F)
  map_add' F G:=by ext n; simp
  map_smul' a F:=by ext n; simp

@[simp] lemma coeff_ncDerivative (F : PowerSeries R) (n : ℕ) :
    coeff n (ncDerivative F)=(n+1) • coeff (n+1) F := by simp [ncDerivative]

@[simp] lemma ncDerivative_one : ncDerivative (1 : PowerSeries R)=0 := by
  ext n
  simp

lemma ncDerivative_mul (F G : PowerSeries R) :
    ncDerivative (F*G)=ncDerivative F*G+F*ncDerivative G := by
  ext n
  simp only [coeff_ncDerivative,coeff_mul,map_add]
  rw [Finset.smul_sum]
  have H : (∑p∈Finset.HasAntidiagonal.antidiagonal (n+1),
      (n+1) • (coeff p.1 F*coeff p.2 G))=
      (∑p∈Finset.HasAntidiagonal.antidiagonal (n+1),
        p.1 • (coeff p.1 F*coeff p.2 G))+
      (∑p∈Finset.HasAntidiagonal.antidiagonal (n+1),
        p.2 • (coeff p.1 F*coeff p.2 G)) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [←add_nsmul,Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
  rw [H,Finset.Nat.sum_antidiagonal_succ,Finset.Nat.sum_antidiagonal_succ']
  simp only [zero_nsmul,zero_add,smul_mul_assoc,mul_smul_comm]

omit [Algebra ℚ R] in
lemma coeff_power_vanish (F : PowerSeries R) (hF : constantCoeff F=0)
    (k n : ℕ) (h : n<k) : coeff n (F^k)=0 := by
  induction k generalizing n with
  | zero=>omega
  | succ k ih=>
    rw [pow_succ,coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    by_cases h0 : p.2=0
    · rw [h0,coeff_zero_eq_constantCoeff,hF,mul_zero]
    · rw [ih p.1 (by omega),zero_mul]

variable {K : Type*} [CommRing K] [Algebra ℚ K]
def traceSeries (τ : R→ₗ[ℚ] K) : PowerSeries R→ₗ[ℚ] PowerSeries K where
  toFun F:=PowerSeries.mk (fun n=>τ (coeff n F))
  map_add' F G:=by ext n; simp
  map_smul' a F:=by ext n; simp

@[simp] lemma coeff_traceSeries (τ : R→ₗ[ℚ] K) (F : PowerSeries R) (n : ℕ) :
    coeff n (traceSeries τ F)=τ (coeff n F) := by simp [traceSeries]

variable (τ : R→ₗ[ℚ] K) (hτ : ∀a b,τ (a*b)=τ (b*a))
include hτ in
lemma traceSeries_cyclic (F G : PowerSeries R) : traceSeries τ (F*G)=traceSeries τ (G*F) := by
  ext n
  simp only [coeff_traceSeries,coeff_mul,map_sum]
  rw [←Finset.Nat.sum_antidiagonal_swap (f:=fun p=>τ (coeff p.1 G*coeff p.2 F))]
  apply Finset.sum_congr rfl
  intro p hp
  exact hτ _ _

include hτ in
lemma trace_derivative_power (F : PowerSeries R) (k l : ℕ) :
    traceSeries τ (ncDerivative (F^(k+1))*F^l)=
      (k+1) • traceSeries τ (ncDerivative F*F^(k+l)) := by
  induction k generalizing l with
  | zero=>simp
  | succ k ih=>
    rw [pow_succ (F) (k+1),ncDerivative_mul,add_mul,map_add]
    have H1 : ncDerivative (F^(k+1))*F*F^l=ncDerivative (F^(k+1))*F^(l+1) := by
      rw [mul_assoc,←pow_succ']
    rw [H1,ih]
    have H2 : traceSeries τ (F^(k+1)*ncDerivative F*F^l)=
        traceSeries τ (ncDerivative F*F^(k+1+l)) := by
      rw [mul_assoc,traceSeries_cyclic τ hτ, mul_assoc,←pow_add]
      rw [Nat.add_comm l (k+1)]
    rw [H2]
    have heq : k+(l+1)=k+1+l := by omega
    simp only [heq,add_nsmul,one_nsmul]

include hτ in
lemma trace_derivative_power' (F : PowerSeries R) (k : ℕ) :
    traceSeries τ (ncDerivative (F^(k+1)))=
      (k+1) • traceSeries τ (ncDerivative F*F^k) := by
  simpa using trace_derivative_power τ hτ F k 0
end
end ElementaryPositivity.FormalLog

end
section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]
lemma inverse_geometric_coeff (F : PowerSeries R) (hF : constantCoeff F=1) (n : ℕ) :
    coeff n (invOfUnit F 1)=coeff n (∑k∈Finset.range (n+1),(-(F-1))^k) := by
  let U:=-(F-1)
  have hU : constantCoeff U=0:=by simp [U,hF]
  have heq : 1-U=F := by dsimp [U]; abel
  have H : (∑k∈Finset.range (n+1),U^k)*F=1-U^(n+1) := by
    rw [←heq]
    exact geom_sum_mul_neg U (n+1)
  have HI : F*invOfUnit F 1=1:=mul_invOfUnit F 1 hF
  have H' := congrArg (fun x : PowerSeries R=>x*invOfUnit F 1) H
  rw [mul_assoc,HI,mul_one,sub_mul,one_mul] at H'
  have Hzero : coeff n (U^(n+1)*invOfUnit F 1)=0 := by
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [coeff_power_vanish U hU (n+1) p.1 (by
      have :=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      omega),zero_mul]
  have HH:=congrArg (coeff n) H'
  rw [map_sub,Hzero,sub_zero] at HH
  exact HH.symm

lemma geometric_mul_coeff (F A : PowerSeries R) (hF : constantCoeff F=1) (n : ℕ) :
    coeff n (A*invOfUnit F 1)=
      coeff n (A*(∑k∈Finset.range (n+1),(-(F-1))^k)) := by
  rw [coeff_mul,coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [inverse_geometric_coeff F hF p.2]
  simp only [map_sum]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hkn
  exact coeff_power_vanish (-(F-1)) (by simp [hF]) k p.2
    (by simp only [Finset.mem_range] at hkn; omega)
end
end ElementaryPositivity.FormalLog

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_PowerSeriesSplit
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.PowerSeriesSplit
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]

def pairCoefficients (P : R →+ R) (f : PowerSeries R) : ℕ → R × R
  | 0 => (1,1)
  | n+1 =>
    let r:=coeff (n+1) f - ∑i : Fin n,
      (pairCoefficients P f (i.val+1)).1 * (pairCoefficients P f (n-i.val)).2
    (P r,r-P r)
termination_by n=>n
decreasing_by all_goals omega

def leftFactor (P : R →+ R) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun n=>(pairCoefficients P f n).1)
def rightFactor (P : R →+ R) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun n=>(pairCoefficients P f n).2)

@[simp] lemma left_constant (P : R →+ R) (f : PowerSeries R) :
    constantCoeff (leftFactor P f)=1 := by
  rw [←coeff_zero_eq_constantCoeff_apply]
  simp only [leftFactor,coeff_mk,pairCoefficients]
@[simp] lemma right_constant (P : R →+ R) (f : PowerSeries R) :
    constantCoeff (rightFactor P f)=1 := by
  rw [←coeff_zero_eq_constantCoeff_apply]
  simp only [rightFactor,coeff_mk,pairCoefficients]

lemma coeff_mul_succ (f g : PowerSeries R) (n : ℕ)
    (hf : constantCoeff f=1) (hg : constantCoeff g=1) :
    coeff (n+1) (f*g)=coeff (n+1) f+coeff (n+1) g+
      ∑i : Fin n,coeff (i.val+1) f * coeff (n-i.val) g := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ,Finset.sum_range_succ']
  simp only [Nat.sub_self,coeff_zero_eq_constantCoeff_apply,hf,hg,mul_one,one_mul,Nat.sub_zero]
  rw [Fin.sum_univ_eq_sum_range (fun i=>coeff (i+1) f*coeff (n-i) g) n]
  simp only [Nat.add_sub_add_right]
  abel

lemma factorization (P : R →+ R) (f : PowerSeries R) (hf : constantCoeff f=1) :
    leftFactor P f * rightFactor P f=f := by
  ext n
  cases n with
  | zero => simp only [coeff_zero_eq_constantCoeff_apply,map_mul,left_constant,right_constant,one_mul,hf]
  | succ n =>
    rw [coeff_mul_succ _ _ n (left_constant P f) (right_constant P f)]
    simp only [leftFactor,rightFactor,coeff_mk]
    rw [pairCoefficients]
    dsimp only
    abel

lemma left_fixed (P : R →+ R) (hP : ∀r,P (P r)=P r) (f : PowerSeries R) (n : ℕ) :
    P (coeff (n+1) (leftFactor P f))=coeff (n+1) (leftFactor P f) := by
  simp only [leftFactor,coeff_mk]
  rw [pairCoefficients]
  exact hP _
lemma right_killed (P : R →+ R) (hP : ∀r,P (P r)=P r) (f : PowerSeries R) (n : ℕ) :
    P (coeff (n+1) (rightFactor P f))=0 := by
  simp only [rightFactor,coeff_mk]
  rw [pairCoefficients]
  simp only [map_sub,hP,sub_self]

lemma uniqueness (P : R →+ R) (f a b : PowerSeries R)
    (ha : constantCoeff a=1) (hb : constantCoeff b=1)
    (hab : a*b=f)
    (hleft : ∀n,P (coeff (n+1) a)=coeff (n+1) a)
    (hright : ∀n,P (coeff (n+1) b)=0) :
    a=leftFactor P f ∧ b=rightFactor P f := by
  have h : ∀n,(coeff n a,coeff n b)=pairCoefficients P f n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simp only [coeff_zero_eq_constantCoeff_apply,ha,hb,pairCoefficients]
      | succ n =>
        have hsum : (∑i : Fin n, coeff (i.val+1) a * coeff (n-i.val) b)=
            ∑i : Fin n,(pairCoefficients P f (i.val+1)).1 *
              (pairCoefficients P f (n-i.val)).2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [←ih (i.val+1) (by omega),←ih (n-i.val) (by omega)]
        have hcoeff := coeff_mul_succ a b n ha hb
        rw [hab,hsum] at hcoeff
        have hres : coeff (n+1) f-∑i : Fin n,
            (pairCoefficients P f (i.val+1)).1 * (pairCoefficients P f (n-i.val)).2 =
            coeff (n+1) a+coeff (n+1) b := by rw [hcoeff]; abel
        rw [pairCoefficients,hres]
        simp only [map_add,hleft,hright,add_zero]
        congr 1
        abel
  constructor
  · ext n
    simpa only [leftFactor,coeff_mk] using congrArg Prod.fst (h n)
  · ext n
    simpa only [rightFactor,coeff_mk] using congrArg Prod.snd (h n)

lemma factors_mem (P : R →+ R) (S : Subring R)
    (hP : ∀r∈S,P r∈S) (f : PowerSeries R) (hf : ∀n,coeff n f∈S) :
    (∀n,coeff n (leftFactor P f)∈S) ∧ (∀n,coeff n (rightFactor P f)∈S) := by
  have h : ∀n,(pairCoefficients P f n).1∈S ∧ (pairCoefficients P f n).2∈S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simpa only [pairCoefficients] using And.intro S.one_mem S.one_mem
      | succ n =>
        have hc : coeff (n+1) f-∑i : Fin n,
            (pairCoefficients P f (i.val+1)).1*(pairCoefficients P f (n-i.val)).2∈S := by
          apply S.sub_mem (hf (n+1))
          apply S.sum_mem
          intro i hi
          exact S.mul_mem (ih (i.val+1) (by omega)).1 (ih (n-i.val) (by omega)).2
        rw [pairCoefficients]
        exact ⟨hP _ hc,S.sub_mem hc (hP _ hc)⟩
  constructor
  · intro n
    simpa only [leftFactor,coeff_mk] using (h n).1
  · intro n
    simpa only [rightFactor,coeff_mk] using (h n).2

lemma mul_mem (S : Subring R) (a b : PowerSeries R)
    (ha : ∀n,coeff n a∈S) (hb : ∀n,coeff n b∈S) : ∀n,coeff n (a*b)∈S := by
  intro n
  rw [coeff_mul]
  exact S.sum_mem (fun p hp=>S.mul_mem (ha p.1) (hb p.2))

lemma factors_graded (P : R →+ R) (A : ℕ → AddSubgroup R)
    (h0 : (1:R)∈A 0)
    (hmul : ∀m n x y,x∈A m → y∈A n → x*y∈A (m+n))
    (hP : ∀n x,x∈A n → P x∈A n)
    (f : PowerSeries R) (hf : ∀n,coeff n f∈A n) :
    (∀n,coeff n (leftFactor P f)∈A n) ∧
    (∀n,coeff n (rightFactor P f)∈A n) := by
  have h : ∀n,(pairCoefficients P f n).1∈A n ∧ (pairCoefficients P f n).2∈A n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simpa only [pairCoefficients] using And.intro h0 h0
      | succ n =>
        have hc : coeff (n+1) f-∑i : Fin n,
            (pairCoefficients P f (i.val+1)).1*(pairCoefficients P f (n-i.val)).2∈A (n+1) := by
          apply (A (n+1)).sub_mem (hf (n+1))
          apply (A (n+1)).sum_mem
          intro i hi
          have hmn : (i.val+1)+(n-i.val)=n+1 := by omega
          rw [←hmn]
          exact hmul _ _ _ _ (ih (i.val+1) (by omega)).1 (ih (n-i.val) (by omega)).2
        rw [pairCoefficients]
        exact ⟨hP _ _ hc,(A _).sub_mem hc (hP _ _ hc)⟩
  constructor
  · intro n
    simpa only [leftFactor,coeff_mk] using (h n).1
  · intro n
    simpa only [rightFactor,coeff_mk] using (h n).2

end
end ElementaryPositivity.PowerSeriesSplit
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PowerSeriesThreeFactors
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.PowerSeriesSplit
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]
variable (P Q : R →+ R) (S : Subring R)
variable (hS : ∀x,x∈S ↔ P x=0)
variable (hP : ∀x,P (P x)=P x) (hQ : ∀x,Q (Q x)=Q x)
variable (hPQ : ∀x,P (Q x)=0)

 def positiveFactor (f : PowerSeries R) := leftFactor P f
 def zeroFactor (f : PowerSeries R) := leftFactor Q (rightFactor P f)
 def negativeFactor (f : PowerSeries R) := rightFactor Q (rightFactor P f)

lemma factor_three (f : PowerSeries R) (hf : constantCoeff f=1) :
    positiveFactor P f * zeroFactor P Q f * negativeFactor P Q f=f := by
  rw [positiveFactor,zeroFactor,negativeFactor,mul_assoc,
    factorization Q _ (right_constant P f),factorization P f hf]

include hS hP hPQ in
lemma zero_negative_nonpositive (f : PowerSeries R) :
    (∀n,coeff n (zeroFactor P Q f)∈S) ∧
    (∀n,coeff n (negativeFactor P Q f)∈S) := by
  apply factors_mem Q S
  · intro x hx
    exact (hS _).mpr (hPQ x)
  · intro n
    cases n with
    | zero => rw [coeff_zero_eq_constantCoeff_apply,right_constant]; exact S.one_mem
    | succ n => exact (hS _).mpr (right_killed P hP f n)

include hS hP hQ hPQ in
lemma three_support (f : PowerSeries R) :
    (∀n,P (coeff (n+1) (positiveFactor P f))=coeff (n+1) (positiveFactor P f)) ∧
    (∀n,P (coeff n (zeroFactor P Q f))=0) ∧
    (∀n,Q (coeff (n+1) (zeroFactor P Q f))=coeff (n+1) (zeroFactor P Q f)) ∧
    (∀n,P (coeff n (negativeFactor P Q f))=0) ∧
    (∀n,Q (coeff (n+1) (negativeFactor P Q f))=0) := by
  have hs:=zero_negative_nonpositive P Q S hS hP hPQ f
  exact ⟨left_fixed P hP f,fun n=>(hS _).mp (hs.1 n),left_fixed Q hQ _,
    fun n=>(hS _).mp (hs.2 n),right_killed Q hQ _⟩

include hS in
lemma three_uniqueness (f a b c : PowerSeries R)
    (ha : constantCoeff a=1) (hb : constantCoeff b=1) (hc : constantCoeff c=1)
    (habc : a*b*c=f)
    (haP : ∀n,P (coeff (n+1) a)=coeff (n+1) a)
    (hbP : ∀n,P (coeff n b)=0) (hcP : ∀n,P (coeff n c)=0)
    (hbQ : ∀n,Q (coeff (n+1) b)=coeff (n+1) b)
    (hcQ : ∀n,Q (coeff (n+1) c)=0) :
    a=positiveFactor P f ∧ b=zeroFactor P Q f ∧ c=negativeFactor P Q f := by
  have hbc : ∀n,P (coeff n (b*c))=0 := by
    intro n
    apply (hS _).mp
    exact mul_mem S b c (fun k=>(hS _).mpr (hbP k))
      (fun k=>(hS _).mpr (hcP k)) n
  have hfirst:=uniqueness P f a (b*c) ha (by simp [hb,hc])
    (by rwa [←mul_assoc]) haP (fun n=>hbc (n+1))
  have hsecond:=uniqueness Q (rightFactor P f) b c hb hc hfirst.2 hbQ hcQ
  exact ⟨hfirst.1,hsecond.1,hsecond.2⟩
end
end ElementaryPositivity.PowerSeriesSplit
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_PowerSeriesSplitLeading
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.PowerSeriesSplit
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]

lemma pair_congr (P : R →+ R) (f g : PowerSeries R) (n : ℕ)
    (h : ∀k≤n,coeff k f=coeff k g) : pairCoefficients P f n=pairCoefficients P g n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [pairCoefficients,pairCoefficients]
    | succ n =>
      have hs : (∑i : Fin n,(pairCoefficients P f (i.val+1)).1*(pairCoefficients P f (n-i.val)).2)=
          ∑i : Fin n,(pairCoefficients P g (i.val+1)).1*(pairCoefficients P g (n-i.val)).2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ih (i.val+1) (by omega) (fun k hk=>h k (by omega)),
          ih (n-i.val) (by omega) (fun k hk=>h k (by omega))]
      rw [pairCoefficients,pairCoefficients,h (n+1) le_rfl,hs]

lemma left_coeff_congr (P : R →+ R) (f g : PowerSeries R) (n : ℕ)
    (h : ∀k≤n,coeff k f=coeff k g) : coeff n (leftFactor P f)=coeff n (leftFactor P g) := by
  simpa only [leftFactor,coeff_mk] using congrArg Prod.fst (pair_congr P f g n h)
lemma right_coeff_congr (P : R →+ R) (f g : PowerSeries R) (n : ℕ)
    (h : ∀k≤n,coeff k f=coeff k g) : coeff n (rightFactor P f)=coeff n (rightFactor P g) := by
  simpa only [rightFactor,coeff_mk] using congrArg Prod.snd (pair_congr P f g n h)

lemma leading_difference (P : R →+ R) (f g : PowerSeries R) (n : ℕ)
    (h : ∀k≤n,coeff k f=coeff k g) :
    coeff (n+1) (leftFactor P f)-coeff (n+1) (leftFactor P g)=P (coeff (n+1) f-coeff (n+1) g) ∧
    coeff (n+1) (rightFactor P f)-coeff (n+1) (rightFactor P g)=
      (coeff (n+1) f-coeff (n+1) g)-P (coeff (n+1) f-coeff (n+1) g) := by
  have hs : (∑i : Fin n,(pairCoefficients P f (i.val+1)).1*(pairCoefficients P f (n-i.val)).2)=
      ∑i : Fin n,(pairCoefficients P g (i.val+1)).1*(pairCoefficients P g (n-i.val)).2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [pair_congr P f g (i.val+1) (fun k hk=>h k (by omega)),
      pair_congr P f g (n-i.val) (fun k hk=>h k (by omega))]
  simp only [leftFactor,rightFactor,coeff_mk]
  rw [pairCoefficients,pairCoefficients,hs]
  simp only [map_sub]
  constructor <;> abel

lemma zero_leading_difference (P Q : R →+ R) (hQP : ∀x,Q (P x)=0)
    (f g : PowerSeries R) (n : ℕ) (h : ∀k≤n,coeff k f=coeff k g) :
    coeff (n+1) (zeroFactor P Q f)-coeff (n+1) (zeroFactor P Q g)=
      Q (coeff (n+1) f-coeff (n+1) g) := by
  have hr : ∀k≤n,coeff k (rightFactor P f)=coeff k (rightFactor P g) := by
    intro k hk
    exact right_coeff_congr P f g k (fun j hj=>h j (hj.trans hk))
  have hl:= (leading_difference Q (rightFactor P f) (rightFactor P g) n hr).1
  rw [(leading_difference P f g n h).2,map_sub,hQP,sub_zero] at hl
  exact hl

lemma zero_coeff_congr (P Q : R →+ R) (f g : PowerSeries R) (n : ℕ)
    (h : ∀k≤n,coeff k f=coeff k g) : coeff n (zeroFactor P Q f)=coeff n (zeroFactor P Q g) := by
  apply left_coeff_congr Q _ _ n
  intro k hk
  exact right_coeff_congr P f g k (fun j hj=>h j (hj.trans hk))
end
end ElementaryPositivity.PowerSeriesSplit
end
section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]

lemma mul_coeff_congr (a b c d : PowerSeries R) (n : ℕ)
    (ha : ∀j≤n,coeff j a=coeff j c) (hb : ∀j≤n,coeff j b=coeff j d) :
    coeff n (a*b)=coeff n (c*d) := by
  rw [coeff_mul,coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hh:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [ha _ (by omega),hb _ (by omega)]

lemma pow_coeff_congr (a b : PowerSeries R) (n k : ℕ)
    (h : ∀j≤n,coeff j a=coeff j b) : coeff n (a^k)=coeff n (b^k) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ a k,pow_succ b k]
    apply mul_coeff_congr
    · intro j hj
      exact ih j (fun i hi=>h i (hi.trans hj))
    · exact h

lemma pow_coeff_congr_of_two_le (a b : PowerSeries R) (n k : ℕ)
    (ha : constantCoeff a=0) (hb : constantCoeff b=0) (hk : 2≤k)
    (h : ∀j<n,coeff j a=coeff j b) : coeff n (a^k)=coeff n (b^k) := by
  obtain ⟨j,rfl⟩:=Nat.exists_eq_add_of_le hk
  rw [show 2+j=(j+1)+1 by omega,pow_succ a (j+1),pow_succ b (j+1)]
  rw [coeff_mul,coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hh:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h0 : p.1=0
  · simp only [h0,coeff_zero_eq_constantCoeff_apply,map_pow,ha,hb,zero_pow (by omega : j+1≠0),zero_mul]
  by_cases h1 : p.2=0
  · simp only [h1,coeff_zero_eq_constantCoeff_apply,ha,hb,mul_zero]
  have hn1 : p.1<n := by omega
  have hn2 : p.2<n := by omega
  rw [pow_coeff_congr a b p.1 (j+1) (fun i hi=>h i (hi.trans_lt hn1)),h _ hn2]

variable [Module ℚ R]

def log (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun n=>∑k∈Finset.range n, ((-1:ℚ)^k/(k+1:ℕ)) • coeff n ((f-1)^(k+1)))

@[simp] lemma log_constant (f : PowerSeries R) : constantCoeff (log f)=0 := by
  rw [←coeff_zero_eq_constantCoeff_apply]
  simp only [log,coeff_mk,Finset.range_zero,Finset.sum_empty]

lemma log_coeff_congr (f g : PowerSeries R) (n : ℕ)
    (h : ∀j≤n,coeff j f=coeff j g) : coeff n (log f)=coeff n (log g) := by
  simp only [log,coeff_mk]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  apply pow_coeff_congr
  intro j hj
  rw [map_sub,map_sub,h j hj]

lemma log_coeff_succ (f : PowerSeries R) (n : ℕ) :
    coeff (n+1) (log f)=coeff (n+1) f+
      ∑k∈Finset.range n,((-1:ℚ)^(k+1)/(k+2:ℕ)) • coeff (n+1) ((f-1)^(k+2)) := by
  simp only [log,coeff_mk]
  rw [Finset.sum_range_succ']
  simp only [pow_zero,Nat.cast_one,one_div,inv_one,zero_add,pow_one,map_sub,
    coeff_one,Nat.succ_ne_zero,ite_false, if_false,sub_zero,one_smul]
  rw [add_comm]

lemma log_leading_difference (f g : PowerSeries R) (n : ℕ)
    (hf : constantCoeff f=1) (hg : constantCoeff g=1)
    (h : ∀j≤n,coeff j f=coeff j g) :
    coeff (n+1) (log f)-coeff (n+1) (log g)=coeff (n+1) f-coeff (n+1) g := by
  rw [log_coeff_succ,log_coeff_succ]
  have hs : (∑k∈Finset.range n,((-1:ℚ)^(k+1)/(k+2:ℕ)) • coeff (n+1) ((f-1)^(k+2)))=
      ∑k∈Finset.range n,((-1:ℚ)^(k+1)/(k+2:ℕ)) • coeff (n+1) ((g-1)^(k+2)) := by
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    apply pow_coeff_congr_of_two_le
    · simp [hf]
    · simp [hg]
    · omega
    · intro j hj
      simp only [map_sub,h j (by omega)]
  rw [hs]
  abel
end
end ElementaryPositivity.FormalLog
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_TraceLogDerivative
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {R K : Type*} [Ring R] [Algebra ℚ R] [CommRing K] [Algebra ℚ K]
variable (τ : R→ₗ[ℚ] K) (hτ : ∀a b,τ (a*b)=τ (b*a))
include hτ in
lemma trace_log_derivative (F : PowerSeries R) (hF : constantCoeff F=1) :
    traceSeries τ (ncDerivative (FormalLog.log F))=
      traceSeries τ (ncDerivative F*invOfUnit F 1) := by
  ext n
  simp only [coeff_traceSeries,coeff_ncDerivative,FormalLog.log,coeff_mk,
    map_nsmul,map_sum,LinearMap.map_smul,Finset.smul_sum]
  rw [geometric_mul_coeff F (ncDerivative F) hF n]
  simp only [Finset.mul_sum,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have H:=congrArg (coeff n) (trace_derivative_power' τ hτ (F-1) k)
  simp only [coeff_traceSeries,coeff_ncDerivative,map_nsmul,
    map_sub,ncDerivative_one,sub_zero] at H
  rw [smul_comm (n+1) ((-1:ℚ)^k/(k+1:ℕ)),H]
  rw [←Nat.cast_smul_eq_nsmul ℚ,smul_smul,div_mul_cancel₀ _ (by positivity : ((k+1:ℕ):ℚ)≠0)]
  have Hpow : (-(F-1))^k=(-1:ℚ)^k • (F-1)^k := by
    rw [←smul_pow]
    simp
  rw [Hpow,mul_smul_comm,coeff_smul,LinearMap.map_smul]
end
end ElementaryPositivity.FormalLog

end
section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {R K : Type*} [Ring R] [Algebra ℚ R] [CommRing K] [Algebra ℚ K]
variable (τ : R→ₗ[ℚ] K) (hτ : ∀a b,τ (a*b)=τ (b*a))
omit [Algebra ℚ R] in
lemma inverse_product (F G : PowerSeries R) (hF : constantCoeff F=1)
    (hG : constantCoeff G=1) : invOfUnit (F*G) 1=invOfUnit G 1*invOfUnit F 1 := by
  have H : (F*G)*(invOfUnit G 1*invOfUnit F 1)=1 := by
    rw [mul_assoc,←mul_assoc G,PowerSeries.mul_invOfUnit G 1 hG,one_mul,
      PowerSeries.mul_invOfUnit F 1 hF]
  have H' :=congrArg (fun x : PowerSeries R=>invOfUnit (F*G) 1*x) H
  rw [←mul_assoc,PowerSeries.invOfUnit_mul (F*G) 1 (by simp [hF,hG]),one_mul,mul_one] at H'
  exact H'.symm

include hτ in
lemma trace_log_product (F G : PowerSeries R) (hF : constantCoeff F=1)
    (hG : constantCoeff G=1) :
    traceSeries τ (FormalLog.log (F*G))=
      traceSeries τ (FormalLog.log F)+traceSeries τ (FormalLog.log G) := by
  have H : traceSeries τ (ncDerivative (FormalLog.log (F*G)))=
      traceSeries τ (ncDerivative (FormalLog.log F))+
      traceSeries τ (ncDerivative (FormalLog.log G)) := by
    rw [trace_log_derivative τ hτ (F*G) (by simp [hF,hG]),ncDerivative_mul,
      inverse_product F G hF hG,add_mul,map_add,
      trace_log_derivative τ hτ F hF,trace_log_derivative τ hτ G hG]
    congr 1
    · simp only [mul_assoc]
      rw [←mul_assoc G,PowerSeries.mul_invOfUnit G 1 hG,one_mul]
    · rw [mul_assoc F,traceSeries_cyclic τ hτ]
      simp only [mul_assoc]
      rw [PowerSeries.invOfUnit_mul F 1 hF,mul_one]
  ext n
  cases n with
  | zero=>simp only [map_add,coeff_traceSeries,coeff_zero_eq_constantCoeff,log_constant,
      map_zero,add_zero]
  | succ n=>
    have HH:=congrArg (coeff n) H
    simp only [map_add,coeff_traceSeries,coeff_ncDerivative,map_nsmul] at HH
    have HHH : ((n+1:ℕ):ℚ) • τ (coeff (n+1) (FormalLog.log (F*G)))=
        ((n+1:ℕ):ℚ) • (τ (coeff (n+1) (FormalLog.log F))+
          τ (coeff (n+1) (FormalLog.log G))) := by
      simpa only [Nat.cast_smul_eq_nsmul,nsmul_add] using HH
    have hnn : ((n+1:ℕ):ℚ)≠0 :=by positivity
    have H4:=congrArg (fun x:K=>(((n+1:ℕ):ℚ)⁻¹) • x) HHH
    simpa only [smul_smul,inv_mul_cancel₀ hnn,one_smul,map_add,coeff_traceSeries] using H4
end
end ElementaryPositivity.FormalLog

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_QuantumTorusTrace
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)
lemma alternating_skew (hΩ : ∀m,Ω m m=0) (a b : M) : Ω a b= -(Ω b a) := by
  have hh:=hΩ (a+b)
  simp only [map_add,AddMonoidHom.add_apply,hΩ] at hh
  omega

lemma coefficient_trace (hΩ : ∀m,Ω m m=0) (r : M) (f g : Torus v Ω)
    (hf : ∀m,Ω m r≠0 → f m=0) : (f*g) r=(g*f) r := by
  classical
  change (Torus.multiply v Ω f g) r=(Torus.multiply v Ω g f) r
  simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases he : a+b=r
  · have har : Ω a r=0 := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp ha) (hf a hn)
    have hab : Ω a b=0 := by
      rw [←he,map_add,hΩ a,zero_add] at har
      exact har
    have hba : Ω b a=0 := by rw [alternating_skew Ω hΩ b a,hab,neg_zero]
    simp only [he,show b+a=r by rwa [add_comm],Finsupp.single_eq_same,hab,hba,
      zpow_zero,Units.val_one,mul_one]
    exact mul_comm _ _
  · have he' : b+a≠r := by rwa [add_comm]
    rw [Finsupp.single_eq_of_ne (Ne.symm he),Finsupp.single_eq_of_ne (Ne.symm he')]
end
end ElementaryPositivity.QuantumTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_KernelTraceLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {A B : Type*} [Ring A] [Ring B] [Algebra ℚ A] [Algebra ℚ B]
lemma log_map (φ : A→ₐ[ℚ] B) (F : PowerSeries A) :
    FormalLog.log (PowerSeries.map φ.toRingHom F)=PowerSeries.map φ.toRingHom (FormalLog.log F) := by
  ext n
  simp only [FormalLog.log,coeff_mk,coeff_map,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [←map_one (PowerSeries.map φ.toRingHom),←map_sub,←map_pow,coeff_map]
  exact (map_smul φ _ _).symm
end
end ElementaryPositivity.FormalLog

end
section
namespace ElementaryPositivity.FormalLog
lemma coeff_sub_one_succ {A : Type*} [Ring A] (F : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff (n+1) (F-1)=PowerSeries.coeff (n+1) F := by
  simp only [map_sub,PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false, if_false,sub_zero]
end ElementaryPositivity.FormalLog
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit
noncomputable section
variable {R M : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M→+M→+ℤ)
local instance kernelTraceLogAddCommGroup : AddCommGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommGroup
local instance kernelTraceLogAddGroup : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup

local instance kernelTraceLogSub_rf9cb96_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
def SupportedOn (V : M→Prop) (f : Torus v Ω) : Prop := ∀m,¬V m→f m=0

omit [Algebra ℚ R] in
lemma SupportedOn.zero (V : M→Prop) : SupportedOn v Ω V 0 := fun _ _=>rfl
omit [Algebra ℚ R] in
lemma SupportedOn.add {V : M→Prop} {f g : Torus v Ω}
    (hf : SupportedOn v Ω V f) (hg : SupportedOn v Ω V g) :
    SupportedOn v Ω V (f+g) := by
  intro m hm
  change f m+g m=0
  rw [hf m hm,hg m hm,add_zero]
lemma SupportedOn.smul {V : M→Prop} {f : Torus v Ω} (hf : SupportedOn v Ω V f) (a : ℚ) :
    SupportedOn v Ω V (a • f) := by
  intro m hm
  change a • f m=0
  rw [hf m hm,smul_zero]
omit [Algebra ℚ R] in
lemma SupportedOn.sum {ι : Type*} (s : Finset ι) (f : ι→Torus v Ω) (V : M→Prop)
    (hf : ∀i∈s,SupportedOn v Ω V (f i)) : SupportedOn v Ω V (∑i∈s,f i) := by
  intro m hm
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero (fun i hi=>hf i hi m hm)
omit [Algebra ℚ R] in
lemma SupportedOn.mul {V : M→Prop} (hV : ∀a b,V a→V b→V (a+b))
    {f g : Torus v Ω} (hf : SupportedOn v Ω V f) (hg : SupportedOn v Ω V g) :
    SupportedOn v Ω V (f*g) := by
  classical
  intro m hm
  change (Torus.multiply v Ω f g) m=0
  simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  have hfa : V a := by by_contra hn; exact (Finsupp.mem_support_iff.mp ha) (hf a hn)
  have hgb : V b := by by_contra hn; exact (Finsupp.mem_support_iff.mp hb) (hg b hn)
  apply Finsupp.single_eq_of_ne
  intro he
  exact hm (he ▸ hV a b hfa hgb)

omit [Algebra ℚ R] in
lemma series_supported_mul {V : M→Prop} (hV : ∀a b,V a→V b→V (a+b))
    {F G : PowerSeries (Torus v Ω)}
    (hF : ∀n,SupportedOn v Ω V (coeff n F)) (hG : ∀n,SupportedOn v Ω V (coeff n G)) :
    ∀n,SupportedOn v Ω V (coeff n (F*G)) := by
  intro n
  rw [coeff_mul]
  exact SupportedOn.sum v Ω _ _ V (fun p hp=>(hF p.1).mul v Ω hV (hG p.2))

lemma strict_log_support {V : M→Prop} (hV : ∀a b,V a→V b→V (a+b))
    (F : PowerSeries (Torus v Ω)) (hF : constantCoeff F=1)
    (hf : ∀n,SupportedOn v Ω V (coeff (n+1) F)) :
    ∀n,SupportedOn v Ω V (coeff n (FormalLog.log F)) := by
  have hu : ∀n,SupportedOn v Ω V (coeff n (F-1)) := by
    intro n
    cases n with
    | zero=>simp only [coeff_zero_eq_constantCoeff,map_sub,hF,constantCoeff_one,sub_self]
            exact SupportedOn.zero v Ω V
    | succ n=>rw [FormalLog.coeff_sub_one_succ]; exact hf n
  have hp : ∀k n,SupportedOn v Ω V (coeff n ((F-1)^(k+1))) := by
    intro k
    induction k with
    | zero=>simpa only [zero_add,pow_one] using hu
    | succ k ih=>simpa only [pow_succ] using series_supported_mul v Ω hV ih hu
  intro n
  simp only [FormalLog.log,coeff_mk]
  exact SupportedOn.sum v Ω _ _ V (fun k hk=>(hp k n).smul v Ω _)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_QuantumTorusChartCompletion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
local instance chartCompletionAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def HasRootDegree (n : ℕ) (m : M) : Prop :=
  ∃d : I → ℕ,(∑i,d i)=n ∧ C (fun i=>(d i:ℤ))=m

lemma rootDegree_zero : HasRootDegree C 0 0 := by
  refine ⟨0,by simp,?_⟩
  change C (0 : I → ℤ)=0
  exact C.map_zero

lemma rootDegree_add {n k : ℕ} {m p : M}
    (hm : HasRootDegree C n m) (hp : HasRootDegree C k p) :
    HasRootDegree C (n+k) (m+p) := by
  obtain ⟨d,hd,hmd⟩:=hm
  obtain ⟨e,he,hpe⟩:=hp
  refine ⟨d+e,by simpa only [Pi.add_apply,Finset.sum_add_distrib] using congrArg₂ (·+·) hd he,?_⟩
  have hh : (fun i=>((d+e) i:ℤ))=(fun i=>(d i:ℤ))+(fun i=>(e i:ℤ)) := by
    ext i; simp
  rw [hh,map_add,hmd,hpe]

def rootGrade (n : ℕ) : AddSubgroup (Torus v Ω) where
  carrier := {f | ∀m,¬HasRootDegree C n m → f m=0}
  zero_mem' := by intro m hm; rfl
  add_mem' := by intro f g hf hg m hm; change f m+g m=0; rw [hf m hm,hg m hm,add_zero]
  neg_mem' := by intro f hf m hm; change -f m=0; rw [hf m hm,neg_zero]

lemma rootGrade_one : (1 : Torus v Ω)∈rootGrade v Ω C 0 := by
  intro m hm
  change Finsupp.single 0 (1:R) m=0
  apply Finsupp.single_eq_of_ne
  intro he
  exact hm (he ▸ rootDegree_zero C)

lemma rootGrade_mul (n k : ℕ) (f g : Torus v Ω)
    (hf : f∈rootGrade v Ω C n) (hg : g∈rootGrade v Ω C k) :
    f*g∈rootGrade v Ω C (n+k) := by
  classical
  intro m hm
  change (Torus.multiply v Ω f g) m=0
  simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have hxC : HasRootDegree C n x := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hx) (hf x hn)
  have hyC : HasRootDegree C k y := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hy) (hg y hn)
  apply Finsupp.single_eq_of_ne
  intro he
  exact hm (he ▸ rootDegree_add C hxC hyC)

lemma rootGrade_filter (p : M → Prop) [DecidablePred p] (n : ℕ) (f : Torus v Ω)
    (hf : f∈rootGrade v Ω C n) : f.filter p∈rootGrade v Ω C n := by
  intro m hm
  simp only [Finsupp.filter_apply,hf m hm,ite_self]

def CompletedPositive := {f : PowerSeries (Torus v Ω) //
  constantCoeff f=1 ∧ ∀n,coeff n f∈rootGrade v Ω C n}

variable (h : M →+ ℝ)
open ElementaryPositivity.PowerSeriesSplit

def chartPositive (f : CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  ⟨positiveFactor (positiveProject v Ω h) f.val,left_constant _ _,
    (factors_graded (positiveProject v Ω h) (rootGrade v Ω C) (rootGrade_one v Ω C)
      (rootGrade_mul v Ω C) (fun n x hx=>rootGrade_filter v Ω C _ n x hx) f.val f.property.2).1⟩
def chartRemainder (f : CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  ⟨rightFactor (positiveProject v Ω h) f.val,right_constant _ _,
    (factors_graded (positiveProject v Ω h) (rootGrade v Ω C) (rootGrade_one v Ω C)
      (rootGrade_mul v Ω C) (fun n x hx=>rootGrade_filter v Ω C _ n x hx) f.val f.property.2).2⟩
def chartZero (f : CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  ⟨leftFactor (zeroProject v Ω h) (chartRemainder v Ω C h f).val,left_constant _ _,
    (factors_graded (zeroProject v Ω h) (rootGrade v Ω C) (rootGrade_one v Ω C)
      (rootGrade_mul v Ω C) (fun n x hx=>rootGrade_filter v Ω C _ n x hx)
      _ (chartRemainder v Ω C h f).property.2).1⟩
def chartNegative (f : CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  ⟨rightFactor (zeroProject v Ω h) (chartRemainder v Ω C h f).val,right_constant _ _,
    (factors_graded (zeroProject v Ω h) (rootGrade v Ω C) (rootGrade_one v Ω C)
      (rootGrade_mul v Ω C) (fun n x hx=>rootGrade_filter v Ω C _ n x hx)
      _ (chartRemainder v Ω C h f).property.2).2⟩

lemma chart_three_factorization (f : CompletedPositive v Ω C) :
    (chartPositive v Ω C h f).val * (chartZero v Ω C h f).val *
      (chartNegative v Ω C h f).val = f.val :=
  factor_three (positiveProject v Ω h) (zeroProject v Ω h) f.val f.property.1

lemma chart_three_support (f : CompletedPositive v Ω C) :
    (∀n m,coeff (n+1) (chartPositive v Ω C h f).val m≠0 → 0<h m) ∧
    (∀n m,coeff (n+1) (chartZero v Ω C h f).val m≠0 → h m=0) ∧
    (∀n m,coeff (n+1) (chartNegative v Ω C h f).val m≠0 → h m<0) := by
  classical
  have ht:=three_support (positiveProject v Ω h) (zeroProject v Ω h)
    (supportedSubring v Ω (nonpositiveCone h)) (nonpositive_iff v Ω h)
    (positiveProject_idem v Ω h) (zeroProject_idem v Ω h) (positive_zero_project v Ω h) f.val
  constructor
  · intro n m hm
    exact (Finsupp.filter_eq_self_iff _ _).mp (ht.1 n) m hm
  constructor
  · intro n m hm
    exact (Finsupp.filter_eq_self_iff _ _).mp (ht.2.2.1 n) m hm
  · intro n m hm
    have hpos:= (Finsupp.filter_eq_zero_iff _ _).mp (ht.2.2.2.1 (n+1)) m
    have hzero:= (Finsupp.filter_eq_zero_iff _ _).mp (ht.2.2.2.2 n) m
    by_contra hn
    have hnm : 0≤h m := le_of_not_gt hn
    rcases lt_or_eq_of_le hnm with hh|hh
    · exact hm (hpos hh)
    · exact hm (hzero hh.symm)

lemma positiveProject_one : positiveProject v Ω h (1 : Torus v Ω)=0 := by
  classical
  change Finsupp.filter (fun m=>0<h m) (Finsupp.single 0 (1:R))=0
  apply (Finsupp.filter_eq_zero_iff _ _).mpr
  intro m hm
  apply Finsupp.single_eq_of_ne
  intro he
  subst m
  simp at hm

lemma chart_three_unique (f a b c : CompletedPositive v Ω C)
    (he : a.val*b.val*c.val=f.val)
    (ha : ∀n m,coeff (n+1) a.val m≠0 → 0<h m)
    (hb : ∀n m,coeff (n+1) b.val m≠0 → h m=0)
    (hc : ∀n m,coeff (n+1) c.val m≠0 → h m<0) :
    a=chartPositive v Ω C h f ∧ b=chartZero v Ω C h f ∧ c=chartNegative v Ω C h f := by
  classical
  have haP : ∀n,positiveProject v Ω h (coeff (n+1) a.val)=coeff (n+1) a.val := by
    intro n
    exact (Finsupp.filter_eq_self_iff _ _).mpr (ha n)
  have hbP : ∀n,positiveProject v Ω h (coeff n b.val)=0 := by
    intro n
    cases n with
    | zero => rw [coeff_zero_eq_constantCoeff_apply,b.property.1]; exact positiveProject_one v Ω h
    | succ n =>
      apply (Finsupp.filter_eq_zero_iff _ _).mpr
      intro m hm
      by_contra hn
      have hh:=hb n m hn
      linarith
  have hcP : ∀n,positiveProject v Ω h (coeff n c.val)=0 := by
    intro n
    cases n with
    | zero => rw [coeff_zero_eq_constantCoeff_apply,c.property.1]; exact positiveProject_one v Ω h
    | succ n =>
      apply (Finsupp.filter_eq_zero_iff _ _).mpr
      intro m hm
      by_contra hn
      have hh:=hc n m hn
      linarith
  have hbQ : ∀n,zeroProject v Ω h (coeff (n+1) b.val)=coeff (n+1) b.val := by
    intro n
    exact (Finsupp.filter_eq_self_iff _ _).mpr (hb n)
  have hcQ : ∀n,zeroProject v Ω h (coeff (n+1) c.val)=0 := by
    intro n
    apply (Finsupp.filter_eq_zero_iff _ _).mpr
    intro m hm
    by_contra hn
    have hh:=hc n m hn
    linarith
  have hu:=three_uniqueness (positiveProject v Ω h) (zeroProject v Ω h)
    (supportedSubring v Ω (nonpositiveCone h)) (nonpositive_iff v Ω h)
    f.val a.val b.val c.val a.property.1 b.property.1 c.property.1 he haP hbP hcP hbQ hcQ
  exact ⟨Subtype.ext hu.1,Subtype.ext hu.2.1,Subtype.ext hu.2.2⟩

end
end ElementaryPositivity.QuantumTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TruncatedFactorization
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesSplit
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]

lemma pair_truncated_unique (P : R→+R) (f a b : PowerSeries R) (N : ℕ)
    (ha : constantCoeff a=1) (hb : constantCoeff b=1)
    (hab : ∀n≤N,coeff n (a*b)=coeff n f)
    (hleft : ∀n,n+1≤N→P (coeff (n+1) a)=coeff (n+1) a)
    (hright : ∀n,n+1≤N→P (coeff (n+1) b)=0) :
    ∀n≤N,coeff n a=coeff n (leftFactor P f) ∧ coeff n b=coeff n (rightFactor P f) := by
  have h : ∀n≤N,(coeff n a,coeff n b)=pairCoefficients P f n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih=>
      intro hn
      cases n with
      | zero=>simp only [coeff_zero_eq_constantCoeff_apply,ha,hb,pairCoefficients]
      | succ n=>
        have hs : (∑i : Fin n,coeff (i.val+1) a*coeff (n-i.val) b)=
            ∑i : Fin n,(pairCoefficients P f (i.val+1)).1*(pairCoefficients P f (n-i.val)).2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [←ih (i.val+1) (by omega) (by omega),←ih (n-i.val) (by omega) (by omega)]
        have hc:=coeff_mul_succ a b n ha hb
        rw [hab (n+1) hn,hs] at hc
        have hr : coeff (n+1) f-∑i : Fin n,
            (pairCoefficients P f (i.val+1)).1*(pairCoefficients P f (n-i.val)).2=
            coeff (n+1) a+coeff (n+1) b :=by rw [hc]; abel
        rw [pairCoefficients,hr]
        simp only [map_add,hleft n hn,hright n hn,add_zero]
        congr 1
        abel
  intro n hn
  constructor
  · simpa only [leftFactor,coeff_mk] using congrArg Prod.fst (h n hn)
  · simpa only [rightFactor,coeff_mk] using congrArg Prod.snd (h n hn)

lemma mul_mem_through (S : Subring R) (a b : PowerSeries R) (N : ℕ)
    (ha : ∀n≤N,coeff n a∈S) (hb : ∀n≤N,coeff n b∈S) :
    ∀n≤N,coeff n (a*b)∈S :=by
  intro n hn
  rw [coeff_mul]
  apply S.sum_mem
  intro p hp
  have hh:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  exact S.mul_mem (ha p.1 (by omega)) (hb p.2 (by omega))

lemma three_truncated_unique (P Q : R→+R) (S : Subring R) (hS : ∀x,x∈S↔P x=0)
    (f a b c : PowerSeries R) (N : ℕ)
    (ha : constantCoeff a=1) (hb : constantCoeff b=1) (hc : constantCoeff c=1)
    (habc : ∀n≤N,coeff n (a*b*c)=coeff n f)
    (haP : ∀n,n+1≤N→P (coeff (n+1) a)=coeff (n+1) a)
    (hbP : ∀n≤N,P (coeff n b)=0) (hcP : ∀n≤N,P (coeff n c)=0)
    (hbQ : ∀n,n+1≤N→Q (coeff (n+1) b)=coeff (n+1) b)
    (hcQ : ∀n,n+1≤N→Q (coeff (n+1) c)=0) :
    ∀n≤N,coeff n a=coeff n (positiveFactor P f) ∧
      coeff n b=coeff n (zeroFactor P Q f) ∧ coeff n c=coeff n (negativeFactor P Q f) :=by
  have hbc : ∀n≤N,P (coeff n (b*c))=0:=fun n hn=>(hS _).mp
    (mul_mem_through S b c N (fun k hk=>(hS _).mpr (hbP k hk))
      (fun k hk=>(hS _).mpr (hcP k hk)) n hn)
  have H:=pair_truncated_unique P f a (b*c) N ha (by simp [hb,hc])
    (fun n hn=>by simpa only [mul_assoc] using habc n hn) haP (fun n hn=>hbc (n+1) hn)
  have H0:=pair_truncated_unique Q (rightFactor P f) b c N hb hc
    (fun n hn=>(H n hn).2) hbQ hcQ
  exact fun n hn=>⟨(H n hn).1,(H0 n hn).1,(H0 n hn).2⟩
end
end ElementaryPositivity.PowerSeriesSplit

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_TruncatedChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit
noncomputable section
variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)

lemma strict_mul_through (V : M→Prop) (hV : ∀a b,V a→V b→V (a+b))
    (a b : PowerSeries (Torus v Ω)) (N : ℕ)
    (ha : constantCoeff a=1) (hb : constantCoeff b=1)
    (hsA : ∀n,n+1≤N→SupportedOn v Ω V (coeff (n+1) a))
    (hsB : ∀n,n+1≤N→SupportedOn v Ω V (coeff (n+1) b)) :
    ∀n,n+1≤N→SupportedOn v Ω V (coeff (n+1) (a*b)) :=by
  intro n hn
  rw [coeff_mul_succ a b n ha hb]
  apply SupportedOn.add v Ω ((hsA n hn).add v Ω (hsB n hn))
  apply SupportedOn.sum v Ω _ _ V
  intro i hi
  apply (hsA i.val (by omega)).mul v Ω hV
  have he : n-i.val=(n-i.val-1)+1:=by omega
  rw [he]
  exact hsB (n-i.val-1) (by omega)

lemma chart_three_truncated_unique (h : M→+ℝ) (f : CompletedPositive v Ω C)
    (a b c : PowerSeries (Torus v Ω)) (N : ℕ)
    (ha0 : constantCoeff a=1) (hb0 : constantCoeff b=1) (hc0 : constantCoeff c=1)
    (he : a*b*c=f.val)
    (ha : ∀n,n+1≤N→∀m,coeff (n+1) a m≠0→0<h m)
    (hb : ∀n,n+1≤N→∀m,coeff (n+1) b m≠0→h m=0)
    (hc : ∀n,n+1≤N→∀m,coeff (n+1) c m≠0→h m<0) :
    ∀n≤N,coeff n a=coeff n (chartPositive v Ω C h f).val ∧
      coeff n b=coeff n (chartZero v Ω C h f).val ∧
      coeff n c=coeff n (chartNegative v Ω C h f).val :=by
  classical
  have haP : ∀n,n+1≤N→positiveProject v Ω h (coeff (n+1) a)=coeff (n+1) a:=by
    intro n hn
    exact (Finsupp.filter_eq_self_iff _ _).mpr (ha n hn)
  have hbP : ∀n≤N,positiveProject v Ω h (coeff n b)=0:=by
    intro n hn
    cases n with
    | zero=>rw [coeff_zero_eq_constantCoeff,hb0]; exact positiveProject_one v Ω h
    | succ n=>
      apply (Finsupp.filter_eq_zero_iff _ _).mpr
      intro m hm
      by_contra hh
      have H:=hb n hn m hh
      linarith
  have hcP : ∀n≤N,positiveProject v Ω h (coeff n c)=0:=by
    intro n hn
    cases n with
    | zero=>rw [coeff_zero_eq_constantCoeff,hc0]; exact positiveProject_one v Ω h
    | succ n=>
      apply (Finsupp.filter_eq_zero_iff _ _).mpr
      intro m hm
      by_contra hh
      have H:=hc n hn m hh
      linarith
  have hbQ : ∀n,n+1≤N→zeroProject v Ω h (coeff (n+1) b)=coeff (n+1) b:=by
    intro n hn
    exact (Finsupp.filter_eq_self_iff _ _).mpr (hb n hn)
  have hcQ : ∀n,n+1≤N→zeroProject v Ω h (coeff (n+1) c)=0:=by
    intro n hn
    apply (Finsupp.filter_eq_zero_iff _ _).mpr
    intro m hm
    by_contra hh
    have H:=hc n hn m hh
    linarith
  exact three_truncated_unique (positiveProject v Ω h) (zeroProject v Ω h)
    (supportedSubring v Ω (nonpositiveCone h)) (nonpositive_iff v Ω h)
    f.val a b c N ha0 hb0 hc0 (fun n hn=>congrArg (coeff n) he) haP hbP hcP hbQ hcQ
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_PowerSeriesProductLeading
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.PowerSeriesSplit
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]

variable {A : Type*} (f g : A → PowerSeries R)

lemma product_coeff_congr (l : List A) (n : ℕ)
    (hfg : ∀a∈l,∀k≤n,coeff k (f a)=coeff k (g a)) :
    coeff n (l.map f).prod=coeff n (l.map g).prod := by
  induction l generalizing n with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,List.prod_cons]
    apply FormalLog.mul_coeff_congr
    · exact hfg a List.mem_cons_self
    · intro k hk
      exact ih k (fun b hb j hj=>hfg b (List.mem_cons_of_mem a hb) j (hj.trans hk))

end
end ElementaryPositivity.PowerSeriesSplit
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_QuantumTorusWallLeading
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries ElementaryPositivity.PowerSeriesSplit
noncomputable section
variable {R M I A : Type*} [CommRing R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (h : M →+ ℝ)

local instance instAddGroupTorus_rf9cb96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorus_rf9cb96_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
omit [Fintype I] in
lemma zero_positive_project (x : Torus v Ω) :
    zeroProject v Ω h (positiveProject v Ω h x)=0 := by
  classical
  ext m
  change (x.filter (fun m=>0<h m) |>.filter (fun m=>h m=0)) m=0
  simp only [Finsupp.filter_apply]
  split_ifs <;> first | rfl | linarith

end
end ElementaryPositivity.QuantumTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IncomingSystem
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries ElementaryPositivity.PowerSeriesSplit
noncomputable section

variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
local instance instAddGroupTorus_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorus_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
local instance instModuleRatTorus : @Module ℚ (Torus v Ω) _ (Torus.instRing v Ω).toAddCommMonoid := by
  let finsuppModule := (inferInstance : Module ℚ (M →₀ R))
  letI : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
  exact
    { smul := finsuppModule.smul
      one_smul := finsuppModule.one_smul
      mul_smul := finsuppModule.mul_smul
      smul_zero := finsuppModule.smul_zero
      smul_add := finsuppModule.smul_add
      add_smul := finsuppModule.add_smul
      zero_smul := finsuppModule.zero_smul }
attribute [local instance] Classical.propDecidable

lemma rootDegree_finite (n : ℕ) : {m | HasRootDegree C n m}.Finite := by
  let F : (I → Fin (n+1)) → M := fun d => C (fun i => (d i : ℤ))
  apply (Set.finite_range F).subset
  rintro m ⟨d,hd,hm⟩
  have hi : ∀i,d i≤n := by
    intro i
    rw [←hd]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
  exact ⟨fun i => ⟨d i,by have := hi i; omega⟩,hm⟩

def incomingCovector (r : M) : M →+ ℝ where
  toFun a := (Ω a r : ℝ)
  map_zero' := by simp
  map_add' := by intro a b; simp

def incomingMiddle (r : M) (f : PowerSeries (Torus v Ω)) : PowerSeries (Torus v Ω) :=
  zeroFactor (positiveProject v Ω (incomingCovector Ω r))
    (zeroProject v Ω (incomingCovector Ω r)) f

omit [Algebra ℚ R] in
lemma incomingMiddle_constant (r : M) (f : PowerSeries (Torus v Ω)) :
    constantCoeff (incomingMiddle v Ω r f)=1 :=
  left_constant _ _

omit [Algebra ℚ R] in
lemma incomingMiddle_coeff_congr (r : M) (f g : PowerSeries (Torus v Ω)) (n : ℕ)
    (h : ∀k≤n,coeff k f=coeff k g) :
    coeff n (incomingMiddle v Ω r f)=coeff n (incomingMiddle v Ω r g) :=
  zero_coeff_congr _ _ _ _ _ h

def incomingCoefficient (n : ℕ) (f : PowerSeries (Torus v Ω)) : Torus v Ω :=
  Finsupp.onFinset (rootDegree_finite C n).toFinset
    (fun m => if HasRootDegree C n m then
      (coeff n (FormalLog.log (incomingMiddle v Ω m f))) m else 0)
    (by
      intro m hm
      rw [Set.Finite.mem_toFinset]
      change HasRootDegree C n m
      by_contra hn
      exact hm (ite_eq_right hn))

lemma incomingCoefficient_apply (n : ℕ) (f : PowerSeries (Torus v Ω)) (m : M) :
    incomingCoefficient v Ω C n f m = if HasRootDegree C n m then
      (coeff n (FormalLog.log (incomingMiddle v Ω m f))) m else 0 := rfl

lemma incomingCoefficient_zero (f : PowerSeries (Torus v Ω)) :
    incomingCoefficient v Ω C 0 f=0 := by
  ext m
  rw [incomingCoefficient_apply]
  simp only [coeff_zero_eq_constantCoeff_apply,FormalLog.log_constant]
  split_ifs <;> rfl

omit [Algebra ℚ R] in
lemma torus_sub_apply (x y : Torus v Ω) (m : M) : (x-y) m=x m-y m := by
  rw [sub_eq_add_neg]
  change x m + -y m = x m-y m
  exact (sub_eq_add_neg _ _).symm

lemma incomingCoefficient_leading (hΩ : ∀m,Ω m m=0)
    (f g : PowerSeries (Torus v Ω)) (n : ℕ)
    (h : ∀k≤n,coeff k f=coeff k g)
    (hf : coeff (n+1) f∈rootGrade v Ω C (n+1))
    (hg : coeff (n+1) g∈rootGrade v Ω C (n+1)) :
    incomingCoefficient v Ω C (n+1) f-incomingCoefficient v Ω C (n+1) g =
      coeff (n+1) f-coeff (n+1) g := by
  classical
  ext m
  rw [torus_sub_apply,torus_sub_apply]
  rw [incomingCoefficient_apply,incomingCoefficient_apply]
  by_cases hm : HasRootDegree C (n+1) m
  · rw [ite_eq_left hm,ite_eq_left hm]
    have hlog := FormalLog.log_leading_difference (incomingMiddle v Ω m f)
      (incomingMiddle v Ω m g) n (incomingMiddle_constant v Ω m f)
      (incomingMiddle_constant v Ω m g)
      (fun k hk => incomingMiddle_coeff_congr v Ω m f g k (fun j hj => h j (hj.trans hk)))
    have hmid := zero_leading_difference (positiveProject v Ω (incomingCovector Ω m))
      (zeroProject v Ω (incomingCovector Ω m))
      (zero_positive_project v Ω (incomingCovector Ω m)) f g n h
    have he := congrArg (fun t : Torus v Ω => t m) (hlog.trans hmid)
    rw [torus_sub_apply] at he
    change _-_=(Finsupp.filter (fun x => incomingCovector Ω m x=0)
      (coeff (n+1) f-coeff (n+1) g)) m at he
    rw [Finsupp.filter_apply] at he
    have hzero : incomingCovector Ω m m=0 := by change (Ω m m : ℝ)=0; rw [hΩ,Int.cast_zero]
    rw [ite_eq_left hzero,torus_sub_apply] at he
    exact he
  · rw [ite_eq_right hm,ite_eq_right hm,hf m hm,hg m hm]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IncomingDisplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)

omit [Algebra ℚ R] in
lemma filter_supported (V : AddSubmonoid M) (P : M→Prop) [DecidablePred P]
    (f : Torus v Ω) (hf : f∈supportedSubring v Ω V) :
    f.filter P∈supportedSubring v Ω V := by
  intro m hm
  simp only [Finsupp.filter_apply,hf m hm,ite_self]

omit [Algebra ℚ R] in
lemma chartThree_supported (h : M→+ℝ) (V : AddSubmonoid M) (F : CompletedPositive v Ω C)
    (hF : ∀n,coeff n F.val∈supportedSubring v Ω V) :
    (∀n,coeff n (chartPositive v Ω C h F).val∈supportedSubring v Ω V) ∧
    (∀n,coeff n (chartZero v Ω C h F).val∈supportedSubring v Ω V) ∧
    (∀n,coeff n (chartNegative v Ω C h F).val∈supportedSubring v Ω V) := by
  classical
  have H:=factors_mem (positiveProject v Ω h) (supportedSubring v Ω V)
    (fun f hf=>filter_supported v Ω V _ f hf) F.val hF
  have H0:=factors_mem (zeroProject v Ω h) (supportedSubring v Ω V)
    (fun f hf=>filter_supported v Ω V _ f hf) (rightFactor (positiveProject v Ω h) F.val) H.2
  exact ⟨H.1,H0.1,H0.2⟩

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ChartRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit
noncomputable section
variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)

lemma chart_root_of_ne (F : CompletedPositive v Ω C) (n : ℕ) (m : M)
    (hm : coeff n F.val m≠0) : HasRootDegree C n m :=by
  by_contra hn
  exact hm (F.property.2 n m hn)

lemma chartZero_supported_kernel (h : M→+ℝ) (F : CompletedPositive v Ω C) :
    ∀n,coeff n (chartZero v Ω C h F).val∈supportedSubring v Ω h.ker.toAddSubmonoid :=by
  intro n m hm
  cases n with
  | zero=>
    rw [coeff_zero_eq_constantCoeff,(chartZero v Ω C h F).property.1]
    change (Finsupp.single 0 (1:R)) m=0
    apply Finsupp.single_eq_of_ne
    intro he
    exact hm (he ▸ h.ker.zero_mem)
  | succ n=>
    by_contra hn
    exact hm ((chart_three_support v Ω C h F).2.1 n m hn)

def LexSigns (h k H : M→+ℝ) (m : M) : Prop :=
  (0<h m→0<H m) ∧ (h m<0→H m<0) ∧
    (h m=0→(0<k m→0<H m) ∧ (k m=0→H m=0) ∧ (k m<0→H m<0))

theorem chart_zero_refinement (h k H : M→+ℝ) (F : CompletedPositive v Ω C) (N : ℕ)
    (hsign : ∀n≤N,∀m,HasRootDegree C n m→LexSigns h k H m) :
    ∀n≤N,coeff n (chartZero v Ω C H F).val=
      coeff n (chartZero v Ω C k (chartZero v Ω C h F)).val :=by
  let A:=chartPositive v Ω C h F
  let B:=chartZero v Ω C h F
  let D:=chartNegative v Ω C h F
  let A0:=chartPositive v Ω C k B
  let B0:=chartZero v Ω C k B
  let D0:=chartNegative v Ω C k B
  have hfact : (A.val*A0.val)*B0.val*(D0.val*D.val)=F.val :=by
    calc
      _=A.val*(A0.val*B0.val*D0.val)*D.val:=by simp only [mul_assoc]
      _=A.val*B.val*D.val:=by rw [chart_three_factorization v Ω C k B]
      _=F.val:=chart_three_factorization v Ω C h F
  have hs:=chart_three_support v Ω C h F
  have hs0:=chart_three_support v Ω C k B
  have hker:=chartThree_supported v Ω C k h.ker.toAddSubmonoid B
    (chartZero_supported_kernel v Ω C h F)
  have hA : ∀n,n+1≤N→SupportedOn v Ω (fun m=>0<H m) (coeff (n+1) A.val):=by
    intro n hn m hm
    by_contra hx
    exact hm ((hsign _ hn m (chart_root_of_ne v Ω C A _ m hx)).1 (hs.1 n m hx))
  have hA0 : ∀n,n+1≤N→SupportedOn v Ω (fun m=>0<H m) (coeff (n+1) A0.val):=by
    intro n hn m hm
    by_contra hx
    have hz : h m=0:=by by_contra hh; exact hx (hker.1 (n+1) m hh)
    exact hm (((hsign _ hn m (chart_root_of_ne v Ω C A0 _ m hx)).2.2 hz).1 (hs0.1 n m hx))
  have hD : ∀n,n+1≤N→SupportedOn v Ω (fun m=>H m<0) (coeff (n+1) D.val):=by
    intro n hn m hm
    by_contra hx
    exact hm ((hsign _ hn m (chart_root_of_ne v Ω C D _ m hx)).2.1 (hs.2.2 n m hx))
  have hD0 : ∀n,n+1≤N→SupportedOn v Ω (fun m=>H m<0) (coeff (n+1) D0.val):=by
    intro n hn m hm
    by_contra hx
    have hz : h m=0:=by by_contra hh; exact hx (hker.2.2 (n+1) m hh)
    exact hm (((hsign _ hn m (chart_root_of_ne v Ω C D0 _ m hx)).2.2 hz).2.2 (hs0.2.2 n m hx))
  have hB0 : ∀n,n+1≤N→∀m,coeff (n+1) B0.val m≠0→H m=0:=by
    intro n hn m hm
    have hz : h m=0:=by by_contra hh; exact hm (hker.2.1 (n+1) m hh)
    exact ((hsign _ hn m (chart_root_of_ne v Ω C B0 _ m hm)).2.2 hz).2.1 (hs0.2.1 n m hm)
  have hAA:=strict_mul_through v Ω (fun m=>0<H m)
    (fun a b ha hb=>by rw [map_add]; linarith) A.val A0.val N A.property.1 A0.property.1 hA hA0
  have hDD:=strict_mul_through v Ω (fun m=>H m<0)
    (fun a b ha hb=>by rw [map_add]; linarith) D0.val D.val N D0.property.1 D.property.1 hD0 hD
  have hu:=chart_three_truncated_unique v Ω C H F (A.val*A0.val) B0.val (D0.val*D.val) N
    (by simp [A.property.1,A0.property.1]) B0.property.1
    (by simp [D0.property.1,D.property.1]) hfact
    (fun n hn m hm=>by by_contra hh; exact hm (hAA n hn m hh)) hB0
    (fun n hn m hm=>by by_contra hh; exact hm (hDD n hn m hh))
  exact fun n hn=>(hu n hn).2.1.symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_FiniteCovectorPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]

lemma real_lex_epsilon (a b : ℝ) : ∃ε>0,∀δ:ℝ,0<δ→δ<ε→
    (0<a→0<a+δ*b) ∧ (a<0→a+δ*b<0) ∧
      (a=0→(0<b→0<a+δ*b) ∧ (b=0→a+δ*b=0) ∧ (b<0→a+δ*b<0)) :=by
  by_cases ha : a=0
  · refine ⟨1,one_pos,?_⟩
    intro δ hδ hδ1
    subst a
    constructor
    · intro h; exact False.elim (lt_irrefl 0 h)
    constructor
    · intro h; exact False.elim (lt_irrefl 0 h)
    · intro h
      exact ⟨fun hb=>by nlinarith,fun hb=>by simp [hb],fun hb=>by nlinarith⟩
  · have hden : 0 < |b|+1:=by positivity
    refine ⟨|a|/(|b|+1),div_pos (abs_pos.mpr ha) hden,?_⟩
    intro δ hδ hδε
    have he:= (lt_div_iff₀ hden).mp hδε
    have hbound : δ*|b| < |a|:=by nlinarith
    have hlo:=mul_le_mul_of_nonneg_left (neg_abs_le b) hδ.le
    have hhi:=mul_le_mul_of_nonneg_left (le_abs_self b) hδ.le
    constructor
    · intro h
      rw [abs_of_pos h] at hbound
      nlinarith
    constructor
    · intro h
      rw [abs_of_neg h] at hbound
      nlinarith
    · exact fun h=>False.elim (ha h)

lemma finite_lex_epsilon (S : Finset M) (h k : M→+ℝ) :
    ∃ε>0,∀δ:ℝ,0<δ→δ<ε→∀m∈S,LexSigns h k (h+δ • k) m :=by
  classical
  induction S using Finset.induction_on with
  | empty=>exact ⟨1,one_pos,fun _ _ _ _ hm=>False.elim (Finset.notMem_empty _ hm)⟩
  | @insert m S hm ih=>
    obtain ⟨ε,hε,Hε⟩:=ih
    obtain ⟨η,hη,Hη⟩:=real_lex_epsilon (h m) (k m)
    refine ⟨min ε η,lt_min hε hη,?_⟩
    intro δ hδ hd x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact Hη δ hδ (lt_of_lt_of_le hd (min_le_right _ _))
    · exact Hε δ hδ (lt_of_lt_of_le hd (min_le_left _ _)) x hx

def rootsThrough (C : (I→ℤ)→+M) (N : ℕ) : Finset M :=
  by
  classical
  exact (Finset.range (N+1)).biUnion (fun n=>(rootDegree_finite C n).toFinset)

lemma mem_rootsThrough (C : (I→ℤ)→+M) (N n : ℕ) (hn : n≤N) (m : M)
    (hm : HasRootDegree C n m) : m∈rootsThrough C N :=by
  classical
  unfold rootsThrough
  apply Finset.mem_biUnion.mpr
  exact ⟨n,Finset.mem_range.mpr (by omega),by simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hm⟩

lemma root_lex_epsilon (C : (I→ℤ)→+M) (N : ℕ) (h k : M→+ℝ) :
    ∃ε>0,∀δ:ℝ,0<δ→δ<ε→∀n≤N,∀m,HasRootDegree C n m→LexSigns h k (h+δ • k) m :=by
  obtain ⟨ε,hε,Hε⟩:=finite_lex_epsilon (rootsThrough C N) h k
  exact ⟨ε,hε,fun δ hδ hd n hn m hm=>Hε δ hδ hd m (mem_rootsThrough C N n hn m hm)⟩

open PowerSeries
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_GradedFormalLog
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
lemma graded_multiply (V : ℕ→AddSubgroup A)
    (hMul : ∀n k a b,a∈V n→b∈V k→a*b∈V (n+k))
    (F G : PowerSeries A) (hF : ∀n,coeff n F∈V n) (hG : ∀n,coeff n G∈V n) :
    ∀n,coeff n (F*G)∈V n := by
  intro n
  rw [coeff_mul]
  apply (V n).sum_mem
  intro p hp
  have he:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [←he]
  exact hMul p.1 p.2 _ _ (hF p.1) (hG p.2)
lemma graded_one (V : ℕ→AddSubgroup A) (hOne : (1:A)∈V 0) :
    ∀n,coeff n (1:PowerSeries A)∈V n := by
  intro n
  rw [coeff_one]
  split_ifs with hn
  · subst n; exact hOne
  · exact (V n).zero_mem

variable [Module ℚ A]

lemma log_graded (V : ℕ→AddSubgroup A) (hOne : (1:A)∈V 0)
    (hMul : ∀n k a b,a∈V n→b∈V k→a*b∈V (n+k))
    (hScalar : ∀n (a : ℚ),∀x∈V n,a • x∈V n)
    (F : PowerSeries A) (hF : ∀n,coeff n F∈V n) :
    ∀n,coeff n (log F)∈V n := by
  have hu : ∀n,coeff n (F-1)∈V n:=by
    intro n
    rw [map_sub]
    exact (V n).sub_mem (hF n) (graded_one V hOne n)
  have hp : ∀k n,coeff n ((F-1)^k)∈V n:=by
    intro k
    induction k with
    | zero=>simpa only [pow_zero] using graded_one V hOne
    | succ k ih=>simpa only [pow_succ] using graded_multiply V hMul _ _ ih hu
  intro n
  simp only [log,coeff_mk]
  apply (V n).sum_mem
  intro k hk
  exact hScalar n _ _ (hp (k+1) n)
end
end ElementaryPositivity.FormalLog

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_WeightedTorusSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (w : I → ℕ) [hw : Fact (∀i,0<w i)]

variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
local instance instRingTorus_rf9cb96_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance instAddCommMonoidTorus : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid

local instance instAddGroupTorus_rf9cb96_2 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma torus_sum_mul {A : Type*} (s : Finset A) (f : A → Torus v Ω) (g : Torus v Ω) :
    (∑i∈s,f i)*g=∑i∈s,f i*g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Torus.zero_mul]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,Torus.add_mul,ih]

lemma torus_mul_sum {A : Type*} (s : Finset A) (f : A → Torus v Ω) (g : Torus v Ω) :
    g*(∑i∈s,f i)=∑i∈s,g*f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Torus.mul_zero]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,Torus.mul_add,ih]

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WallUnits
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.WallUnits
open PowerSeries

section Field
variable {K : Type*} [Field K]

def elementaryCoeff (q u : K) : ℕ → K
  | 0 => 1
  | n + 1 => u * q ^ n * elementaryCoeff q u n / (1 - q ^ (n + 1))

noncomputable def elementary (q u : K) : PowerSeries K :=
  PowerSeries.mk (elementaryCoeff q u)

@[simp] theorem coeff_elementary (q u : K) (n : ℕ) :
    PowerSeries.coeff n (elementary q u) = elementaryCoeff q u n := by
  simp [elementary]

@[simp] theorem constant_elementary (q u : K) :
    PowerSeries.constantCoeff (elementary q u) = 1 := rfl

noncomputable def complete (q u : K) : PowerSeries K := (elementary q (-u))⁻¹

end Field

namespace RationalRay
noncomputable def v : RatFunc ℚ := RatFunc.X
noncomputable def q : RatFunc ℚ := v ^ (-2 : ℤ)
theorem v_nonzero : v ≠ 0 := RatFunc.X_ne_zero

end RationalRay

namespace PositiveRay
open PowerSeries
noncomputable def vUnit : (RatFunc ℚ)ˣ := Units.mk0 RationalRay.v RationalRay.v_nonzero
end PositiveRay

end ElementaryPositivity.WallUnits
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RayLaurentExpansion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.WallUnits
open PowerSeries
open scoped LaurentSeries RatFunc
noncomputable section
namespace LaurentRay
local instance instAlgebraRatRatFunc_solutions : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

lemma reciprocal_transcendental : Transcendental ℚ ((RatFunc.X : RatFunc ℚ)⁻¹) := by
  intro h
  exact (RatFunc.transcendental_X (K:=ℚ)) (IsAlgebraic.inv_iff.mp h)

def reciprocalEval : Polynomial ℚ →ₐ[ℚ] RatFunc ℚ :=
  Polynomial.aeval ((RatFunc.X : RatFunc ℚ)⁻¹)
lemma reciprocalEval_injective : Function.Injective reciprocalEval :=
  transcendental_iff_injective.mp reciprocal_transcendental
lemma reciprocalEval_regular :
    (nonZeroDivisors (Polynomial ℚ)) ≤ (nonZeroDivisors (RatFunc ℚ)).comap reciprocalEval :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ reciprocalEval_injective

def reciprocal : RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.liftRingHom reciprocalEval.toRingHom reciprocalEval_regular
lemma reciprocal_X : reciprocal RatFunc.X=(RatFunc.X : RatFunc ℚ)⁻¹ := by
  have hh:=RatFunc.liftRingHom_apply_div reciprocalEval.toRingHom reciprocalEval_regular Polynomial.X 1
  change reciprocal (algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X /
    algebraMap (Polynomial ℚ) (RatFunc ℚ) 1)=reciprocalEval Polynomial.X/reciprocalEval 1 at hh
  simpa [reciprocalEval] using hh

def atInfinity : RatFunc ℚ →+* LaurentSeries ℚ :=
  (algebraMap (RatFunc ℚ) (LaurentSeries ℚ)).comp reciprocal

lemma atInfinity_v : atInfinity RationalRay.v=HahnSeries.single (-1 : ℤ) (1:ℚ) := by
  change algebraMap (RatFunc ℚ) (LaurentSeries ℚ) (reciprocal RatFunc.X)=_
  rw [reciprocal_X,map_inv₀]
  change ((RatFunc.X : RatFunc ℚ) : LaurentSeries ℚ)⁻¹=_
  rw [RatFunc.coe_X,HahnSeries.inv_single]
  simp only [inv_one]

lemma atInfinity_v_pow (k : ℤ) :
    atInfinity (RationalRay.v^k)=HahnSeries.single (-k) (1:ℚ) := by
  rw [map_zpow₀,atInfinity_v, RatFunc.single_zpow (-1),←zpow_mul,neg_one_mul]
  exact (RatFunc.single_zpow (-k)).symm

lemma atInfinity_q : atInfinity RationalRay.q=HahnSeries.single (2:ℤ) (1:ℚ) := by
  exact atInfinity_v_pow (-2)

lemma map_elementaryCoeff {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (q u : K) (n : ℕ) : φ (elementaryCoeff q u n)=elementaryCoeff (φ q) (φ u) n := by
  induction n with
  | zero => exact map_one φ
  | succ n ih => simp only [elementaryCoeff,map_mul,map_div₀,map_sub,map_one,map_pow,ih]

lemma map_elementary {K L : Type*} [Field K] [Field L] (φ : K →+* L) (q u : K) :
    PowerSeries.map φ (elementary q u)=elementary (φ q) (φ u) := by
  ext n
  rw [coeff_map,coeff_elementary,coeff_elementary,map_elementaryCoeff]

lemma elementary_atInfinity (k : ℤ) :
    PowerSeries.map atInfinity (elementary RationalRay.q (RationalRay.v^k))=
      elementary (HahnSeries.single (2:ℤ) (1:ℚ)) (HahnSeries.single (-k) (1:ℚ)) := by
  rw [map_elementary]
  change elementary (atInfinity RationalRay.q) (atInfinity (RationalRay.v^k))=_
  rw [atInfinity_q,atInfinity_v_pow]

end LaurentRay
end
end ElementaryPositivity.WallUnits
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_IndexedUnit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open WallUnits PowerSeries
open scoped LaurentSeries
noncomputable section

def indexedUnit (a : ℕ) (k : ℤ) : PowerSeries (RatFunc ℚ) :=
  if a=0 then elementary RationalRay.q (RationalRay.v^k)
  else complete RationalRay.q (RationalRay.v^k)

end
end ElementaryPositivity.UnitSelections
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HNSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.QuantumTorus PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I]
variable (w : I → ℕ) [hw : Fact (∀i,0<w i)]

variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

local instance instAddCommMonoidTorus_1_rf9cb96_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
lemma filter_monomial (p : M → Prop) [DecidablePred p] (m : M) (r : R) :
    (Finsupp.filterAddHom p : Torus v Ω →+ Torus v Ω) (Torus.monomial v Ω m r)=
      if p m then Torus.monomial v Ω m r else 0 := by
  classical
  change (Finsupp.single m r).filter p=_
  ext x
  by_cases H : x=m
  · subst x
    by_cases hp : p m <;> simp [Torus.monomial,hp]
  · by_cases hp : p m <;> simp [Torus.monomial,hp,Finsupp.single_eq_of_ne H]

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_NonpHomogenize
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ)
local instance homogenizeRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance homogenizeAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance homogenizeAddGroup_rf9cb96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
def homogenizeMonomial (m : M) : R →+ PowerSeries (Torus v Ω) :=
  (PowerSeries.monomial (δ m).toNat).toAddMonoidHom.comp
    {toFun:=Torus.monomial v Ω m,map_zero':=by simp,map_add':=by intros; simp}
def homogenize : Torus v Ω →+ PowerSeries (Torus v Ω) :=
  Finsupp.liftAddHom (homogenizeMonomial v Ω δ)
@[simp] lemma homogenize_monomial (m : M) (a : R) :
    homogenize v Ω δ (Torus.monomial v Ω m a)=
      PowerSeries.monomial (δ m).toNat (Torus.monomial v Ω m a) :=
  Finsupp.liftAddHom_apply_single _ _ _
lemma torus_sum_monomial (f : Torus v Ω) :
    ∑m∈f.support,Torus.monomial v Ω m (f m)=f := by
  classical
  exact Finsupp.sum_single f
lemma homogenize_coeff (f : Torus v Ω) (d : ℕ) (m : M) :
    coeff d (homogenize v Ω δ f) m=if d=(δ m).toNat then f m else 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>
    rw [_root_.map_add,_root_.map_add]
    simp only [Finsupp.add_apply,hf,hg]
    split_ifs <;> simp
  | single n a=>
    change coeff d (homogenize v Ω δ (Torus.monomial v Ω n a)) m=_
    rw [homogenize_monomial,coeff_monomial]
    by_cases hm : m=n
    · subst n; split_ifs <;> simp [Torus.monomial]
    · split_ifs <;> simp [Torus.monomial,Finsupp.single_eq_of_ne hm]
lemma homo_sum_mul {A : Type*} (s : Finset A) (f : A → Torus v Ω) (g : Torus v Ω) :
    (∑i∈s,f i)*g=∑i∈s,f i*g := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp only [Finset.sum_empty,Torus.zero_mul]
  | @insert a s ha ih=>simp only [Finset.sum_insert ha,Torus.add_mul,ih]
lemma homo_mul_sum {A : Type*} (s : Finset A) (f : A → Torus v Ω) (g : Torus v Ω) :
    g*(∑i∈s,f i)=∑i∈s,g*f i := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp only [Finset.sum_empty,Torus.mul_zero]
  | @insert a s ha ih=>simp only [Finset.sum_insert ha,Torus.mul_add,ih]
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ)
local instance biHomogenizeRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance biHomogenizeAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid

local instance biHomogenizeAddGroup_rf9cb96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
def biHomogenizeMonomial (m : M) : R →+ PowerSeries (PowerSeries (Torus v Ω)) :=
  (PowerSeries.monomial (δ m).toNat).toAddMonoidHom.comp
    ((PowerSeries.monomial (κ m).toNat).toAddMonoidHom.comp
      {toFun:=Torus.monomial v Ω m,map_zero':=by simp,map_add':=by intros; simp})
def biHomogenize : Torus v Ω →+ PowerSeries (PowerSeries (Torus v Ω)) :=
  Finsupp.liftAddHom (biHomogenizeMonomial v Ω δ κ)
@[simp] lemma biHomogenize_monomial (m : M) (a : R) :
    biHomogenize v Ω δ κ (Torus.monomial v Ω m a)=
      monomial (δ m).toNat (monomial (κ m).toNat (Torus.monomial v Ω m a)) :=
  Finsupp.liftAddHom_apply_single _ _ _
lemma biHomogenize_coeff (f : Torus v Ω) (d e : ℕ) (m : M) :
    coeff e (coeff d (biHomogenize v Ω δ κ f)) m=
      if d=(δ m).toNat ∧ e=(κ m).toNat then f m else 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>
    rw [_root_.map_add,_root_.map_add,_root_.map_add]
    simp only [Finsupp.add_apply,hf,hg]
    split_ifs <;> simp
  | single n a=>
    change coeff e (coeff d (biHomogenize v Ω δ κ (Torus.monomial v Ω n a))) m=_
    rw [biHomogenize_monomial,coeff_monomial]
    by_cases hm : m=n
    · subst n
      by_cases hd : d=(δ m).toNat
      · rw [ite_eq_left hd,coeff_monomial]
        by_cases he : e=(κ m).toNat <;> simp [hd,he,Torus.monomial]
      · simp [hd]
    · by_cases hd : d=(δ n).toNat <;> by_cases he : e=(κ n).toNat <;>
        simp [hd,he,Torus.monomial,Finsupp.single_eq_of_ne hm,coeff_monomial]
lemma biHomogenize_monomial_mul (m n : M) (a b : R)
    (hm : 0≤δ m ∧ 0≤κ m) (hn : 0≤δ n ∧ 0≤κ n) :
    biHomogenize v Ω δ κ (Torus.monomial v Ω m a*Torus.monomial v Ω n b)=
      biHomogenize v Ω δ κ (Torus.monomial v Ω m a)*
        biHomogenize v Ω δ κ (Torus.monomial v Ω n b) := by
  rw [Torus.monomial_mul_monomial,biHomogenize_monomial,biHomogenize_monomial,
    biHomogenize_monomial,monomial_mul_monomial,monomial_mul_monomial,
    Torus.monomial_mul_monomial,map_add,map_add,Int.toNat_add hm.1 hn.1,Int.toNat_add hm.2 hn.2]
lemma biHomogenize_mul (f g : Torus v Ω)
    (hf : ∀m,f m≠0 → 0≤δ m ∧ 0≤κ m) (hg : ∀m,g m≠0 → 0≤δ m ∧ 0≤κ m) :
    biHomogenize v Ω δ κ (f*g)=biHomogenize v Ω δ κ f*biHomogenize v Ω δ κ g := by
  classical
  calc
    _ = ∑m∈f.support,∑n∈g.support,
        biHomogenize v Ω δ κ (Torus.monomial v Ω m (f m)*Torus.monomial v Ω n (g n)) := by
      have H (s : Finset M) (a : M → Torus v Ω) :
          biHomogenize v Ω δ κ (∑m∈s,a m)=∑m∈s,biHomogenize v Ω δ κ (a m) :=
        _root_.map_sum (biHomogenize v Ω δ κ) a s
      simp_rw [←H]
      congr 1
      simp_rw [←homo_mul_sum]
      rw [torus_sum_monomial,←homo_sum_mul,torus_sum_monomial]
    _ = ∑m∈f.support,∑n∈g.support,
        biHomogenize v Ω δ κ (Torus.monomial v Ω m (f m))*
        biHomogenize v Ω δ κ (Torus.monomial v Ω n (g n)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact biHomogenize_monomial_mul v Ω δ κ m n _ _ (hf m (Finsupp.mem_support_iff.mp hm))
        (hg n (Finsupp.mem_support_iff.mp hn))
    _ = _ := by
      simp_rw [←Finset.mul_sum]
      rw [←Finset.sum_mul]
      congr 1
      · rw [←_root_.map_sum,torus_sum_monomial]
      · rw [←_root_.map_sum,torus_sum_monomial]
lemma biHomogenize_one : biHomogenize v Ω δ κ 1=1 := by
  change biHomogenize v Ω δ κ (Torus.monomial v Ω 0 1)=_
  rw [biHomogenize_monomial,_root_.map_zero,_root_.map_zero,Int.toNat_zero,monomial_zero_eq_C_apply,monomial_zero_eq_C_apply]
  change C (C (1:Torus v Ω))=1
  simp
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentHomogenize
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries HahnSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ)
local instance laurentHomogenizeRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance laurentHomogenizeAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid

local instance laurentHomogenizeAddGroup_rf9cb96_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
local instance laurentHomogenizeNonUnitalSemiring_rf9cb96_1 : NonUnitalSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalSemiring
local instance laurentHomogenizeNonUnitalNonAssocSemiring_rf9cb96_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
def laurentHomogenizeMonomial (m : M) : R →+ PowerSeries (HahnSeries ℤ (Torus v Ω)) :=
  (PowerSeries.monomial (δ m).toNat).toAddMonoidHom.comp
    {toFun := fun a => HahnSeries.single (κ m) (Torus.monomial v Ω m a)
     map_zero' := by simp
     map_add' a b := by simp only [Torus.monomial_add, HahnSeries.single_add]}

def laurentHomogenize : Torus v Ω →+ PowerSeries (HahnSeries ℤ (Torus v Ω)) :=
  Finsupp.liftAddHom (laurentHomogenizeMonomial v Ω δ κ)

@[simp] lemma laurentHomogenize_monomial (m : M) (a : R) :
    laurentHomogenize v Ω δ κ (Torus.monomial v Ω m a) =
      PowerSeries.monomial (δ m).toNat (HahnSeries.single (κ m) (Torus.monomial v Ω m a)) :=
  Finsupp.liftAddHom_apply_single _ _ _

lemma laurentHomogenize_coeff (f : Torus v Ω) (d : ℕ) (z : ℤ) (m : M) :
    (coeff d (laurentHomogenize v Ω δ κ f)).coeff z m =
      if d = (δ m).toNat ∧ z = κ m then f m else 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [_root_.map_add, _root_.map_add, HahnSeries.coeff_add]
    simp only [Finsupp.add_apply, hf, hg]
    split_ifs <;> simp
  | single n a =>
    change (coeff d (laurentHomogenize v Ω δ κ (Torus.monomial v Ω n a))).coeff z m = _
    rw [laurentHomogenize_monomial, coeff_monomial]
    by_cases hm : m = n
    · subst n
      by_cases hd : d = (δ m).toNat
      · rw [ite_eq_left hd]
        by_cases hz : z = κ m <;> simp [hd, hz, Torus.monomial]
      · simp [hd]
    · by_cases hd : d = (δ n).toNat <;> by_cases hz : z = κ n <;>
        simp [hd, hz, Torus.monomial, Finsupp.single_eq_of_ne hm]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_NonpRegrade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)
local instance regradeSupportRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance regradeSupportAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance regradeSupportAddGroup_rf9cb96_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
lemma torus_product_nonzero (f g : Torus v Ω) (r : M) (h : (f*g) r≠0) :
    ∃m n,f m≠0 ∧ g n≠0 ∧ m+n=r := by
  classical
  by_contra H
  apply h
  change Torus.multiply v Ω f g r=0
  simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  apply Finsupp.single_eq_of_ne
  intro hr
  exact H ⟨m,n,Finsupp.mem_support_iff.mp hm,Finsupp.mem_support_iff.mp hn,hr.symm⟩
lemma nonp_torus_eval_sum {A : Type*} (s : Finset A) (f : A → Torus v Ω) (r : M) :
    (∑a∈s,f a) r=∑a∈s,f a r := by
  classical
  induction s using Finset.induction_on with
  | empty=>rfl
  | @insert a s ha ih=>simp only [Finset.sum_insert ha,Finsupp.add_apply,ih]
lemma series_product_nonzero (f g : PowerSeries (Torus v Ω)) (j : ℕ) (r : M)
    (h : coeff j (f*g) r≠0) :
    ∃a b m n,a+b=j ∧ coeff a f m≠0 ∧ coeff b g n≠0 ∧ m+n=r := by
  classical
  rw [coeff_mul,nonp_torus_eval_sum] at h
  obtain ⟨ab,hab,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨m,n,hm,hn,he⟩:=torus_product_nonzero v Ω _ _ r hz
  exact ⟨ab.1,ab.2,m,n,Finset.HasAntidiagonal.mem_antidiagonal.mp hab,hm,hn,he⟩

def RegradeBound (δ : M →+ ℤ) (B : ℕ) (f : PowerSeries (Torus v Ω)) : Prop :=
  ∀n m,coeff n f m≠0 → 0≤δ m ∧ n≤B*(δ m).toNat
variable (δ : M →+ ℤ) (B : ℕ)
lemma RegradeBound.one : RegradeBound v Ω δ B 1 := by
  intro n m hm
  have hn : n=0:=by by_contra hn; simp [coeff_one,hn] at hm
  subst n
  have hm0 : m=0:=by
    by_contra hm0
    apply hm
    rw [coeff_one,ite_eq_left rfl]
    exact Finsupp.single_eq_of_ne hm0
  subst m
  simp
lemma RegradeBound.mul {f g : PowerSeries (Torus v Ω)} (hf : RegradeBound v Ω δ B f)
    (hg : RegradeBound v Ω δ B g) : RegradeBound v Ω δ B (f*g) := by
  intro j r hr
  obtain ⟨a,b,m,n,hab,hm,hn,rfl⟩:=series_product_nonzero v Ω f g j r hr
  obtain ⟨hm0,hma⟩:=hf a m hm
  obtain ⟨hn0,hnb⟩:=hg b n hn
  refine ⟨by simpa only [map_add] using add_nonneg hm0 hn0,?_⟩
  rw [←hab,map_add,Int.toNat_add hm0 hn0,mul_add]
  exact Nat.add_le_add hma hnb

lemma RegradeBound.homogenize_vanish {f : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (d n : ℕ) (hn : B*d<n) :
    coeff d (homogenize v Ω δ (coeff n f))=0 := by
  ext m
  rw [homogenize_coeff]
  by_cases hd : d=(δ m).toNat
  · rw [ite_eq_left hd]
    by_contra hm
    have HH:=(hf n m hm).2
    rw [←hd] at HH
    exact Nat.not_lt_of_ge HH hn
  · simp [hd]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentRegrade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ) (B : ℕ)
local instance laurentRegradeRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance laurentRegradeAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid

local instance laurentRegradeAddGroup_rf9cb96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
def LaurentBounded (f : PowerSeries (Torus v Ω)) : Prop :=
  ∀ n m, coeff n f m ≠ 0 →
    0 ≤ δ m ∧ -(B : ℤ)*δ m ≤ κ m ∧ (n : ℤ) ≤ κ m + (B+1 : ℤ)*δ m

lemma LaurentBounded.zero : LaurentBounded v Ω δ κ B 0 := by
  intro n m h
  simp at h
lemma LaurentBounded.one : LaurentBounded v Ω δ κ B 1 := by
  intro n m hm
  have hn : n = 0 := by by_contra hn; simp [coeff_one, hn] at hm
  subst n
  have hm0 : m = 0 := by
    by_contra hm0
    apply hm
    rw [coeff_one, ite_eq_left rfl]
    exact Finsupp.single_eq_of_ne hm0
  subst m
  simp
lemma LaurentBounded.add {f g : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hg : LaurentBounded v Ω δ κ B g) :
    LaurentBounded v Ω δ κ B (f+g) := by
  intro n m hm
  have H : coeff n f m ≠ 0 ∨ coeff n g m ≠ 0 := by
    by_contra hh
    push Not at hh
    simp [hh.1, hh.2] at hm
  exact H.elim (hf n m) (hg n m)
lemma LaurentBounded.neg {f : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) : LaurentBounded v Ω δ κ B (-f) := by
  intro n m hm
  apply hf n m
  intro hz
  apply hm
  change -(coeff n f m) = 0
  rw [hz, neg_zero]
lemma LaurentBounded.mul {f g : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hg : LaurentBounded v Ω δ κ B g) :
    LaurentBounded v Ω δ κ B (f*g) := by
  intro n r hr
  obtain ⟨a,b,m,l,hab,hm,hl,rfl⟩ := series_product_nonzero v Ω f g n r hr
  obtain ⟨hdm,hkm,hem⟩ := hf a m hm
  obtain ⟨hdl,hkl,hel⟩ := hg b l hl
  simp only [map_add]
  refine ⟨add_nonneg hdm hdl, ?_, ?_⟩
  · nlinarith
  · rw [←hab, Nat.cast_add]
    nlinarith

lemma LaurentBounded.laurent_vanish {f : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (d n : ℕ) (z : ℤ)
    (hz : z < -(B : ℤ)*(d : ℤ) ∨ z + (B+1 : ℤ)*(d : ℤ) < n) :
    (coeff d (laurentHomogenize v Ω δ κ (coeff n f))).coeff z = 0 := by
  ext m
  rw [laurentHomogenize_coeff]
  split_ifs with hh
  · by_contra hm
    obtain ⟨hd,hk,hn⟩ := hf n m hm
    have hD : δ m = (d : ℤ) := by rw [hh.1, Int.toNat_of_nonneg hd]
    rw [hD, ←hh.2] at hk hn
    rcases hz with hz | hz <;> omega
  · rfl

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ)
local instance laurentRegradeBiRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance laurentRegradeBiAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentRegradeBiAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def BiBounded (f : PowerSeries (Torus v Ω)) : Prop :=
  ∀ n m, coeff n f m ≠ 0 → 0 ≤ δ m ∧ 0 ≤ κ m ∧ (n : ℤ) ≤ δ m + κ m
lemma BiBounded.mul {f g : PowerSeries (Torus v Ω)}
    (hf : BiBounded v Ω δ κ f) (hg : BiBounded v Ω δ κ g) : BiBounded v Ω δ κ (f*g) := by
  intro j r hr
  obtain ⟨a,b,m,n,hab,hm,hn,rfl⟩ := series_product_nonzero v Ω f g j r hr
  obtain ⟨hdm,hkm,hem⟩ := hf a m hm
  obtain ⟨hdn,hkn,hen⟩ := hg b n hn
  simp only [map_add]
  refine ⟨add_nonneg hdm hdn,add_nonneg hkm hkn,?_⟩
  rw [←hab,Nat.cast_add]
  omega
lemma BiBounded.bi_vanish {f : PowerSeries (Torus v Ω)} (hf : BiBounded v Ω δ κ f)
    (d e n : ℕ) (hne : d+e<n) : coeff e (coeff d (biHomogenize v Ω δ κ (coeff n f)))=0 := by
  ext m
  rw [biHomogenize_coeff]
  split_ifs with hh
  · by_contra hz
    obtain ⟨hd,hk,he⟩ := hf n m hz
    have hD : δ m=(d : ℤ) := by rw [hh.1,Int.toNat_of_nonneg hd]
    have hK : κ m=(e : ℤ) := by rw [hh.2,Int.toNat_of_nonneg hk]
    omega
  · rfl
lemma BiBounded.bi_product_vanish {f g : PowerSeries (Torus v Ω)}
    (hf : BiBounded v Ω δ κ f) (hg : BiBounded v Ω δ κ g)
    (d e a b : ℕ) (ha : d+e<a ∨ d+e<b) :
    coeff e (coeff d (biHomogenize v Ω δ κ (coeff a f)*
      biHomogenize v Ω δ κ (coeff b g)))=0 := by
  rw [coeff_mul,map_sum]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro kl hkl
  have H1:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have H2:=Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
  rcases ha with ha|ha
  · rw [hf.bi_vanish v Ω δ κ ij.1 kl.1 a (by omega),Torus.zero_mul]
  · rw [hg.bi_vanish v Ω δ κ ij.2 kl.2 b (by omega),Torus.mul_zero]

def boundedBiRegrade (f : PowerSeries (Torus v Ω)) : PowerSeries (PowerSeries (Torus v Ω)) :=
  PowerSeries.mk fun d => PowerSeries.mk fun e =>
    ∑ n ∈ Finset.range (d+e+1), coeff e (coeff d (biHomogenize v Ω δ κ (coeff n f)))
lemma boundedBiRegrade_coeff (f : PowerSeries (Torus v Ω)) (d e : ℕ) :
    coeff e (coeff d (boundedBiRegrade v Ω δ κ f)) =
      ∑ n ∈ Finset.range (d+e+1), coeff e (coeff d (biHomogenize v Ω δ κ (coeff n f))) := by
  simp only [boundedBiRegrade,coeff_mk]

section Topology
local instance laurentRegradeTopology : TopologicalSpace (Torus v Ω) := ⊥
local instance laurentRegradeDiscreteTopology : DiscreteTopology (Torus v Ω) := ⟨rfl⟩
open scoped PowerSeries.WithPiTopology
lemma boundedBiRegrade_hasSum {f : PowerSeries (Torus v Ω)} (hf : BiBounded v Ω δ κ f) :
    HasSum (fun n => biHomogenize v Ω δ κ (coeff n f)) (boundedBiRegrade v Ω δ κ f) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro e
  rw [boundedBiRegrade_coeff]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  apply hf.bi_vanish v Ω δ κ d e n
  simp only [Finset.mem_range,not_lt] at hn
  omega
lemma boundedBiRegrade_product_summable {f g : PowerSeries (Torus v Ω)}
    (hf : BiBounded v Ω δ κ f) (hg : BiBounded v Ω δ κ g) :
    Summable (fun ab : ℕ×ℕ => biHomogenize v Ω δ κ (coeff ab.1 f)*
      biHomogenize v Ω δ κ (coeff ab.2 g)) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro e
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet ((Finset.range (d+e+1)).product (Finset.range (d+e+1)))).subset
  intro ab hab
  change coeff e (coeff d (biHomogenize v Ω δ κ (coeff ab.1 f)*
    biHomogenize v Ω δ κ (coeff ab.2 g)))≠0 at hab
  change ab∈(Finset.range (d+e+1)) ×ˢ (Finset.range (d+e+1))
  rw [Finset.mem_product,Finset.mem_range,Finset.mem_range]
  by_contra H
  exact hab (hf.bi_product_vanish v Ω δ κ hg d e ab.1 ab.2 (by omega))
lemma boundedBiRegrade_mul {f g : PowerSeries (Torus v Ω)}
    (hf : BiBounded v Ω δ κ f) (hg : BiBounded v Ω δ κ g) :
    boundedBiRegrade v Ω δ κ (f*g) = boundedBiRegrade v Ω δ κ f*boundedBiRegrade v Ω δ κ g := by
  rw [←(boundedBiRegrade_hasSum v Ω δ κ hf).tsum_eq,
    ←(boundedBiRegrade_hasSum v Ω δ κ hg).tsum_eq,
    (boundedBiRegrade_hasSum v Ω δ κ hf).summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
      (boundedBiRegrade_hasSum v Ω δ κ hg).summable (boundedBiRegrade_product_summable v Ω δ κ hf hg),
    ←(boundedBiRegrade_hasSum v Ω δ κ (hf.mul v Ω δ κ hg)).tsum_eq]
  apply tsum_congr
  intro n
  rw [coeff_mul,_root_.map_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  exact biHomogenize_mul v Ω δ κ _ _ (fun m hm => ⟨(hf ab.1 m hm).1,(hf ab.1 m hm).2.1⟩)
    (fun m hm => ⟨(hg ab.2 m hm).1,(hg ab.2 m hm).2.1⟩)
end Topology

lemma boundedBiRegrade_add (f g : PowerSeries (Torus v Ω)) :
    boundedBiRegrade v Ω δ κ (f+g) = boundedBiRegrade v Ω δ κ f+boundedBiRegrade v Ω δ κ g := by
  apply PowerSeries.ext
  intro d
  apply PowerSeries.ext
  intro e
  rw [_root_.map_add, _root_.map_add, boundedBiRegrade_coeff,
    boundedBiRegrade_coeff, boundedBiRegrade_coeff, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [_root_.map_add, _root_.map_add, _root_.map_add, _root_.map_add]
lemma boundedBiRegrade_one : boundedBiRegrade v Ω δ κ 1=1 := by
  apply PowerSeries.ext
  intro d
  apply PowerSeries.ext
  intro e
  rw [boundedBiRegrade_coeff]
  rw [Finset.sum_eq_single 0]
  · simp only [coeff_zero_one,biHomogenize_one]
  · intro n hn hne
    rw [coeff_one,ite_eq_right hne,_root_.map_zero,_root_.map_zero,_root_.map_zero]
  · intro hn
    exact (hn (by simp)).elim
lemma boundedBiRegrade_zero : boundedBiRegrade v Ω δ κ 0=0 := by
  apply PowerSeries.ext
  intro d
  apply PowerSeries.ext
  intro e
  simp only [boundedBiRegrade_coeff,_root_.map_zero,Finset.sum_const_zero]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentDeshear
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.Deshear
open PowerSeries HahnSeries
noncomputable section
variable {R : Type*} [Ring R]
lemma single_central (z : ℤ) (f : HahnSeries ℤ R) :
    single z 1 * f = f * single z 1 := by
  apply HahnSeries.ext
  funext e
  simp only [coeff_single_mul, coeff_mul_single, one_mul, mul_one]
lemma shift_mul (z w : ℤ) (f g : HahnSeries ℤ R) :
    single (z+w) 1 * (f*g) = (single z 1*f)*(single w 1*g) := by
  rw [show (1 : R)=1*1 from (one_mul _).symm, ←single_mul_single]
  simp only [one_mul]
  calc
    _ = single z 1*(single w 1*f)*g := by simp only [mul_assoc]
    _ = single z 1*(f*single w 1)*g := by rw [single_central w f]
    _ = _ := by simp only [mul_assoc]

def deshear (B : ℕ) (f : PowerSeries (PowerSeries R)) : PowerSeries (HahnSeries ℤ R) :=
  PowerSeries.mk fun d => single (-(B : ℤ)*(d : ℤ)) 1 * ofPowerSeries ℤ R (coeff d f)
lemma deshear_coeff (B : ℕ) (f : PowerSeries (PowerSeries R)) (d : ℕ) :
    coeff d (deshear B f) = single (-(B : ℤ)*(d : ℤ)) 1 * ofPowerSeries ℤ R (coeff d f) := by
  rw [deshear, coeff_mk]
lemma deshear_read (B : ℕ) (f : PowerSeries (PowerSeries R)) (d : ℕ) (z : ℤ) :
    (coeff d (deshear B f)).coeff z =
      (ofPowerSeries ℤ R (coeff d f)).coeff (z+(B : ℤ)*(d : ℤ)) := by
  rw [deshear_coeff, coeff_single_mul, one_mul]
  congr 1
  ring
lemma deshear_zero (B : ℕ) : deshear (R:=R) B 0=0 := by
  apply PowerSeries.ext
  intro d
  simp [deshear_coeff]
lemma deshear_one (B : ℕ) : deshear (R:=R) B 1=1 := by
  apply PowerSeries.ext
  intro d
  rw [deshear_coeff]
  by_cases hd : d=0
  · subst d
    simp
  · simp [PowerSeries.coeff_one,hd]
lemma deshear_add (B : ℕ) (f g : PowerSeries (PowerSeries R)) :
    deshear B (f+g)=deshear B f+deshear B g := by
  apply PowerSeries.ext
  intro d
  simp only [deshear_coeff,map_add,mul_add]
lemma deshear_mul (B : ℕ) (f g : PowerSeries (PowerSeries R)) :
    deshear B (f*g)=deshear B f*deshear B g := by
  apply PowerSeries.ext
  intro d
  rw [deshear_coeff,PowerSeries.coeff_mul,PowerSeries.coeff_mul,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [map_mul,deshear_coeff,deshear_coeff]
  have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [←shift_mul]
  congr 2
  rw [←H,Nat.cast_add,mul_add]

end
end ElementaryPositivity.Deshear

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ) (B : ℕ)
local instance laurentDeshearRing : Ring (Torus v Ω) := Torus.instRing v Ω

local instance laurentDeshearAddCommMonoid_rf9cb96_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentDeshearAddGroup_rf9cb96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance laurentDeshearNonUnitalSemiring_rf9cb96_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance laurentDeshearNonUnitalNonAssocSemiring_rf9cb96_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma LaurentBounded.bi_shear {f : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) : BiBounded v Ω δ (κ+B • δ) f := by
  intro n m hm
  obtain ⟨hd,hk,hn⟩:=hf n m hm
  change 0≤δ m ∧ 0≤κ m+(B:ℤ)*δ m ∧ (n:ℤ)≤δ m+(κ m+(B:ℤ)*δ m)
  exact ⟨hd,by nlinarith,by nlinarith⟩

def laurentBoundedSubring : Subring (PowerSeries (Torus v Ω)) where
  carrier := LaurentBounded v Ω δ κ B
  zero_mem' := LaurentBounded.zero v Ω δ κ B
  one_mem' := LaurentBounded.one v Ω δ κ B
  add_mem' := LaurentBounded.add v Ω δ κ B
  neg_mem' := LaurentBounded.neg v Ω δ κ B
  mul_mem' := LaurentBounded.mul v Ω δ κ B

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutationCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (p : I)
def simpleRoot : M := C (Pi.single p 1)
def nonpDegree : M →+ ℤ where
  toFun m:=∑i∈Finset.univ.erase p,coord m i
  map_zero':=by simp
  map_add':=by intro a b; simp [Finset.sum_add_distrib]
def fiberUpper (α : I → ℤ) (σ : ℤ) : M →+ ℤ where
  toFun m:=∑i∈Finset.univ.erase p,max 0 (-σ*α i)*coord m i
  map_zero':=by simp
  map_add':=by intro a b; simp [mul_add,Finset.sum_add_distrib]
def fiberCone (α : I → ℤ) (σ : ℤ) : AddSubmonoid M where
  carrier:={m | 0 ≤ coord m p ∧ coord m p≤fiberUpper coord p α σ m}
  zero_mem':=by simp
  add_mem':=by
    intro a b ha hb
    change 0 ≤ coord (a+b) p ∧ coord (a+b) p≤fiberUpper coord p α σ (a+b)
    simp only [map_add,Pi.add_apply]
    exact ⟨add_nonneg ha.1 hb.1,add_le_add ha.2 hb.2⟩
include hcoord in
omit [DecidableEq I] in
lemma root_coordinates {n : ℕ} {m : M} (hm : HasRootDegree C n m) :
    ∃d : I → ℕ,(∑i,d i)=n ∧ (∀i,coord m i=(d i:ℤ)) ∧ C (fun i=>(d i:ℤ))=m := by
  obtain ⟨d,hd,hm⟩:=hm
  refine ⟨d,hd,?_,hm⟩
  rw [←hm,hcoord]
  exact fun _=>rfl
include hcoord in
lemma nonpDegree_root_nonneg {n : ℕ} {m : M} (hm : HasRootDegree C n m) :
    0≤nonpDegree coord p m := by
  obtain ⟨d,hd,hc,hm⟩:=root_coordinates C coord hcoord hm
  change 0≤∑i∈Finset.univ.erase p,coord m i
  apply Finset.sum_nonneg
  intro i hi
  rw [hc]
  positivity
include hcoord in
lemma nonpDegree_root_eq {n : ℕ} {m : M} (hm : HasRootDegree C n m) :
    nonpDegree coord p m+coord m p=(n:ℤ) := by
  obtain ⟨d,hd,hc,hm⟩:=root_coordinates C coord hcoord hm
  change (∑i∈Finset.univ.erase p,coord m i)+coord m p=(n:ℤ)
  rw [Finset.sum_erase_add _ _ (Finset.mem_univ p)]
  simp only [hc,←Nat.cast_sum,hd]
include hcoord in
lemma nonp_zero_root {n : ℕ} {m : M} (hm : HasRootDegree C n m)
    (hz : nonpDegree coord p m=0) : m=n • simpleRoot C p := by
  obtain ⟨d,hd,hc,he⟩:=root_coordinates C coord hcoord hm
  have hs : ∑i∈Finset.univ.erase p,(d i:ℤ)=0:=by simpa only [nonpDegree,AddMonoidHom.coe_mk,ZeroHom.coe_mk,hc] using hz
  have hz' : ∀i,i≠p → d i=0:=by
    intro i hi
    have HH:=Finset.sum_eq_zero_iff_of_nonneg (fun i (hi : i∈Finset.univ.erase p)=>Int.natCast_nonneg (d i)) |>.mp hs i (Finset.mem_erase.mpr ⟨hi,Finset.mem_univ i⟩)
    exact_mod_cast HH
  have hdp : d p=n:=by
    rw [←hd,Finset.sum_eq_single p]
    · intro i hi hp; exact hz' i hp
    · simp
  have hds : (fun i=>(d i:ℤ))=n • (Pi.single p 1 : I → ℤ):=by
    ext i
    by_cases hi : i=p
    · subst i; simp [hdp]
    · simp [hz' i hi,hi]
  rw [←he,hds,map_nsmul]
  rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_SplitContinuity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries ElementaryPositivity.PowerSeriesSplit
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I → ℤ) →+ M) (l : Filter ι)
attribute [local instance] Classical.propDecidable

local instance instAddGroupTorusLaurentSeriesRat_1_rf9cb96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_1_rf9cb96_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
def SeriesGraded (F : PowerSeries (Torus v Ω)) : Prop :=
  ∀n,coeff n F∈rootGrade v Ω C n

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedInverse
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries ElementaryPositivity.PowerSeriesSplit
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I → ℤ) →+ M) (l : Filter ι)
local instance instAddCommGroupTorusLaurentSeriesRat : AddCommGroup (Torus v Ω) := (Torus.instRing v Ω).toAddCommGroup
attribute [local instance] Classical.propDecidable

local instance instAddGroupTorusLaurentSeriesRat_2_rf9cb96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_2_rf9cb96_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
lemma SeriesGraded.mul {F G : PowerSeries (Torus v Ω)}
    (hF : SeriesGraded v Ω C F) (hG : SeriesGraded v Ω C G) :
    SeriesGraded v Ω C (F*G) := by
  intro n
  rw [coeff_mul]
  apply (rootGrade v Ω C n).sum_mem
  intro p hp
  have H := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [←H]
  exact rootGrade_mul v Ω C p.1 p.2 _ _ (hF p.1) (hG p.2)

lemma SeriesGraded.one : SeriesGraded v Ω C 1 := by
  intro n
  rw [coeff_one]
  split_ifs with h
  · subst n; exact rootGrade_one v Ω C
  · exact (rootGrade v Ω C n).zero_mem

lemma coeff_inverse_one (F : PowerSeries (Torus v Ω)) (n : ℕ) :
    coeff n (PowerSeries.invOfUnit F 1) =
      if n=0 then 1 else -∑p∈Finset.HasAntidiagonal.antidiagonal n,
        if p.2<n then coeff p.1 F*coeff p.2 (PowerSeries.invOfUnit F 1) else 0 := by
  rw [coeff_invOfUnit]
  simp only [inv_one,Units.val_one,neg_mul,one_mul]
  congr 1

lemma SeriesGraded.inverse {F : PowerSeries (Torus v Ω)} (hF : SeriesGraded v Ω C F) :
    SeriesGraded v Ω C (PowerSeries.invOfUnit F 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [coeff_inverse_one]
    split_ifs with hn
    · subst n; exact rootGrade_one v Ω C
    · apply (rootGrade v Ω C n).neg_mem
      intro m hm
      rw [Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro p hp
      split_ifs with hp2
      · have H := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        rw [←H] at hm
        exact rootGrade_mul v Ω C p.1 p.2 _ _ (hF p.1) (ih p.2 hp2) m hm
      · rfl

def completedInverse (F : CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  ⟨PowerSeries.invOfUnit F.val 1, by simp,
    SeriesGraded.inverse v Ω C F.property.2⟩

lemma completedInverse_mul (F : CompletedPositive v Ω C) :
    (completedInverse v Ω C F).val*F.val=1 :=
  PowerSeries.invOfUnit_mul F.val 1 F.property.1
lemma mul_completedInverse (F : CompletedPositive v Ω C) :
    F.val*(completedInverse v Ω C F).val=1 :=
  PowerSeries.mul_invOfUnit F.val 1 F.property.1

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
def adjoint (F X : PowerSeries A) : PowerSeries A := F*X*invOfUnit F 1
@[simp] lemma constant_adjoint (F X : PowerSeries A) (hF : constantCoeff F=1) :
    constantCoeff (adjoint F X)=constantCoeff X := by simp [adjoint,hF]
lemma inverse_coeff_congr (F G : PowerSeries A) (N : ℕ) (h : ∀n≤N,coeff n F=coeff n G) :
    ∀n≤N,coeff n (invOfUnit F 1)=coeff n (invOfUnit G 1) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [coeff_invOfUnit,coeff_invOfUnit]
    split_ifs with h0
    · rfl
    · congr 1
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs with hpn
      · rw [h p.1 (by have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega),ih p.2 hpn (by omega)]
      · rfl
lemma adjoint_coeff_congr (F G X Y : PowerSeries A) (N : ℕ)
    (hFG : ∀n≤N,coeff n F=coeff n G) (hXY : ∀n≤N,coeff n X=coeff n Y) :
    coeff N (adjoint F X)=coeff N (adjoint G Y) := by
  apply FormalLog.mul_coeff_congr
  · intro j hj
    exact FormalLog.mul_coeff_congr F X G Y j (fun k hk=>hFG k (hk.trans hj)) (fun k hk=>hXY k (hk.trans hj))
  · exact inverse_coeff_congr F G N hFG
end
end ElementaryPositivity.PowerSeriesAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_HNTorusFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WallUnits.LaurentRay
noncomputable section
def vUnit : (LaurentSeries ℚ)ˣ := Units.map atInfinity.toMonoidHom PositiveRay.vUnit
end
end ElementaryPositivity.WallUnits.LaurentRay

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_NoncommExpand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesDilate
open PowerSeries
noncomputable section
variable {R : Type*} [Semiring R]
variable (w : ℕ) (hw : 0<w)

def dilate (f : PowerSeries R) : PowerSeries R :=
  mk (fun n=>if w∣n then coeff (n/w) f else 0)

@[simp] lemma coeff_dilate (f : PowerSeries R) (n : ℕ) :
    coeff n (dilate w f)=if w∣n then coeff (n/w) f else 0 := by
  rw [dilate,coeff_mk]

end
end ElementaryPositivity.PowerSeriesDilate

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_QuantumTorusRaySeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)

local instance raySeriesAddGroup_rf9cb96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
noncomputable def raySeries (a : M) (f : PowerSeries R) : PowerSeries (Torus v Ω) :=
  PowerSeries.mk (fun n=>Torus.monomial v Ω (n • a) (coeff n f))
@[simp] lemma coeff_raySeries (a : M) (f : PowerSeries R) (n : ℕ) :
    coeff n (raySeries v Ω a f)=Torus.monomial v Ω (n • a) (coeff n f) := by
  rw [raySeries,coeff_mk]
end
end ElementaryPositivity.QuantumTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WeightedRay
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesDilate
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)

local instance weightedRayAddGroup_rf9cb96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
def weightedRay (w : ℕ) (a : M) (f : PowerSeries R) : PowerSeries (Torus v Ω) :=
  dilate w (raySeries v Ω a f)

@[simp] lemma coeff_weightedRay (w : ℕ) (a : M) (f : PowerSeries R) (n : ℕ) :
    coeff n (weightedRay v Ω w a f)=
      if w∣n then Torus.monomial v Ω ((n/w) • a) (coeff (n/w) f) else 0 := by
  rw [weightedRay,coeff_dilate,coeff_raySeries]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RootProducts
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits UnitSelections
noncomputable section
variable {M J : Type*} [AddCommGroup M] [Fintype J]

structure WallUnitDatum (M : Type*) where
  degree : ℕ
  root : M
  kind : ℕ
  parameter : ℤ

variable (Ω : M→+M→+ℤ) (C : (J→ℤ)→+M)

def WallUnitDatum.value (u : WallUnitDatum M) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  weightedRay LaurentRay.vUnit Ω u.degree u.root
    (PowerSeries.map LaurentRay.atInfinity (indexedUnit u.kind u.parameter))

def WallUnitDatum.Allowed (V : M→Prop) (u : WallUnitDatum M) : Prop :=
  0<u.degree ∧ HasRootDegree C u.degree u.root ∧ V u.root

lemma rootDegree_nsmul {n : ℕ} {p : M} (hp : HasRootDegree C n p) (k : ℕ) :
    HasRootDegree C (k*n) (k • p) := by
  induction k with
  | zero=>simpa using rootDegree_zero C
  | succ k ih=>simpa only [Nat.succ_mul,succ_nsmul] using rootDegree_add C ih hp

lemma weightedRay_graded (n : ℕ) (p : M) (hp : HasRootDegree C n p)
    (F : PowerSeries (LaurentSeries ℚ)) :
    SeriesGraded LaurentRay.vUnit Ω C (weightedRay LaurentRay.vUnit Ω n p F) := by
  intro k m hm
  rw [coeff_weightedRay]
  split_ifs with h
  · change (Finsupp.single ((k/n) • p) (coeff (k/n) F)) m=0
    apply Finsupp.single_eq_of_ne
    intro H
    apply hm
    simpa only [Nat.div_mul_cancel h,H] using rootDegree_nsmul C hp (k/n)
  · rfl

lemma indexedUnit_constant (a : ℕ) (k : ℤ) : constantCoeff (indexedUnit a k)=1 := by
  unfold indexedUnit
  split_ifs
  · exact constant_elementary _ _
  · simp only [complete,constantCoeff_inv,constant_elementary,inv_one]

lemma WallUnitDatum.constant (u : WallUnitDatum M) : constantCoeff (u.value Ω)=1 := by
  rw [←coeff_zero_eq_constantCoeff,WallUnitDatum.value,coeff_weightedRay]
  simp only [dvd_zero,ite_eq_left,Nat.zero_div,zero_nsmul,coeff_map,coeff_zero_eq_constantCoeff,
    indexedUnit_constant,map_one]
  rfl

lemma WallUnitDatum.graded (V : M→Prop) (u : WallUnitDatum M) (hu : u.Allowed C V) :
    SeriesGraded LaurentRay.vUnit Ω C (u.value Ω) :=
  weightedRay_graded Ω C u.degree u.root hu.2.1 _

def literalRootProducts (V : M→Prop) : Set (PowerSeries (Torus LaurentRay.vUnit Ω)) :=
  {F | ∃l : List (WallUnitDatum M),(∀u∈l,u.Allowed C V) ∧ F=(l.map (WallUnitDatum.value Ω)).prod}

lemma literalRootProducts_graded (V : M→Prop) {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : F∈literalRootProducts Ω C V) : SeriesGraded LaurentRay.vUnit Ω C F := by
  obtain ⟨l,hl,rfl⟩:=hF
  induction l with
  | nil=>simpa using SeriesGraded.one LaurentRay.vUnit Ω C
  | cons u l ih=>
    simp only [List.map_cons,List.prod_cons]
    exact (u.graded Ω C V (hl u (by simp))).mul LaurentRay.vUnit Ω C
      (ih (fun v hv=>hl v (by simp [hv])))

lemma literalRootProducts_constant (V : M→Prop) {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : F∈literalRootProducts Ω C V) : constantCoeff F=1 := by
  obtain ⟨l,hl,rfl⟩:=hF
  simp only [map_list_prod,List.map_map]
  have H : l.map (constantCoeff ∘ WallUnitDatum.value Ω)=l.map (fun _=>1) := by
    apply List.map_congr_left
    intro u hu
    exact u.constant Ω
  rw [H]
  simp
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_Strict
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)
lemma predicate_nsmul (P : M→Prop) (hP : ∀a b,P a→P b→P (a+b))
    (m : M) (hm : P m) (n : ℕ) (hn : 0<n) : P (n • m) := by
  induction n with
  | zero=>omega
  | succ n ih=>
    by_cases h0 : n=0
    · subst n; simpa using hm
    · rw [succ_nsmul]
      exact hP _ _ (ih (by omega)) hm
lemma WallUnitDatum.strictSupport (P : M→Prop) (hP : ∀a b,P a→P b→P (a+b))
    (u : WallUnitDatum M) (hu : u.Allowed C P) (n : ℕ) :
    SupportedOn LaurentRay.vUnit Ω P (coeff (n+1) (u.value Ω)) := by
  intro m hm
  rw [WallUnitDatum.value,coeff_weightedRay]
  split_ifs with hd
  · change (Finsupp.single (((n+1)/u.degree) • u.root) _) m=0
    apply Finsupp.single_eq_of_ne
    intro he
    apply hm
    rw [he]
    exact predicate_nsmul P hP u.root hu.2.2 _
      (Nat.div_pos (Nat.le_of_dvd (by omega) hd) hu.1)
  · rfl
lemma literalRootProducts_strictSupport (P : M→Prop) (hP : ∀a b,P a→P b→P (a+b))
    {F : PowerSeries (Torus LaurentRay.vUnit Ω)} (hF : F∈literalRootProducts Ω C P) :
    ∀n,SupportedOn LaurentRay.vUnit Ω P (coeff (n+1) F) := by
  obtain ⟨l,hl,rfl⟩:=hF
  induction l with
  | nil=>
    intro n
    simp only [List.map_nil,List.prod_nil,PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false, if_false]
    exact SupportedOn.zero _ _ P
  | cons u l ih=>
    intro n
    simp only [List.map_cons,List.prod_cons]
    apply strict_mul_through LaurentRay.vUnit Ω P hP _ _ (n+1)
      (u.constant Ω) (literalRootProducts_constant Ω C P ⟨l,fun w hw=>hl w (by simp [hw]),rfl⟩)
      (fun j hj=>u.strictSupport Ω C P hP (hl u (by simp)) j)
      (fun j hj=>ih (fun w hw=>hl w (by simp [hw])) j) n le_rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RootTruncation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
namespace RootTruncation
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
def cut (N : ℕ) (F : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk (fun n => if n≤N then coeff n F else 0)
@[simp] lemma coeff_cut (N n : ℕ) (F : PowerSeries A) :
    coeff n (cut N F)=if n≤N then coeff n F else 0 := coeff_mk _ _
lemma coeff_cut_of_le {N n : ℕ} (F : PowerSeries A) (hn : n≤N) :
    coeff n (cut N F)=coeff n F := by simp [hn]
@[simp] lemma constant_cut (N : ℕ) (F : PowerSeries A) :
    constantCoeff (cut N F)=constantCoeff F := by
  rw [←coeff_zero_eq_constantCoeff,coeff_cut,ite_eq_left (Nat.zero_le _),coeff_zero_eq_constantCoeff]
end
end RootTruncation
namespace QuantumTorus
open PowerSeries RootTruncation
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)
def completedCut (N : ℕ) (F : CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  ⟨cut N F.val,by simpa using F.property.1,by
    intro n
    rw [coeff_cut]
    split_ifs
    · exact F.property.2 n
    · intro m hm; rfl⟩
omit [Algebra ℚ R] in
lemma completedCut_supported (N : ℕ) (F : CompletedPositive v Ω C) (S : AddSubmonoid M)
    (hF : ∀n≤N,coeff n F.val∈supportedSubring v Ω S) :
    ∀n,coeff n (completedCut v Ω C N F).val∈supportedSubring v Ω S := by
  intro n
  change coeff n (cut N F.val)∈_
  rw [coeff_cut]
  split_ifs with hn
  · exact hF n hn
  · exact (supportedSubring v Ω S).zero_mem
end
end QuantumTorus
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_TorusProjection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries ElementaryPositivity.WeightedTorusSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (h : M →+ ℝ)
local instance instAddCommMonoidTorus : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid

lemma sum_monomials (f : Torus v Ω) :
    (∑m∈f.support,Torus.monomial v Ω m (f m))=f := Finsupp.sum_single f

lemma zeroProject_monomial (m : M) (r : R) :
    zeroProject v Ω h (Torus.monomial v Ω m r)=
      if h m=0 then Torus.monomial v Ω m r else 0 := filter_monomial v Ω _ m r

lemma zeroProject_monomial_mul (a b : M) (x y : R) (ha : h a≤0) (hb : h b≤0) :
    zeroProject v Ω h (Torus.monomial v Ω a x*Torus.monomial v Ω b y)=
      zeroProject v Ω h (Torus.monomial v Ω a x)*
      zeroProject v Ω h (Torus.monomial v Ω b y) := by
  classical
  rw [Torus.monomial_mul_monomial]
  simp only [zeroProject_monomial,map_add]
  by_cases ha0 : h a=0
  · by_cases hb0 : h b=0
    · simp only [ha0,hb0,add_zero,ite_true, if_true,Torus.monomial_mul_monomial]
    · have hab : h a+h b≠0 := by simpa only [ha0,zero_add] using hb0
      simp only [ha0,zero_add,hb0,ite_true, if_true,ite_false, if_false,Torus.mul_zero]
  · have hab : h a+h b≠0 := by intro H; exact ha0 (by linarith)
    simp only [ha0,hab,ite_false, if_false,Torus.zero_mul]

lemma zeroProject_mul_nonpositive (f g : Torus v Ω)
    (hf : f∈supportedSubring v Ω (nonpositiveCone h))
    (hg : g∈supportedSubring v Ω (nonpositiveCone h)) :
    zeroProject v Ω h (f*g)=zeroProject v Ω h f*zeroProject v Ω h g := by
  classical
  have H : zeroProject v Ω h ((∑m∈f.support,Torus.monomial v Ω m (f m))*
      (∑n∈g.support,Torus.monomial v Ω n (g n)))=
      zeroProject v Ω h (∑m∈f.support,Torus.monomial v Ω m (f m))*
      zeroProject v Ω h (∑n∈g.support,Torus.monomial v Ω n (g n)) := by
    simp only [torus_sum_mul,torus_mul_sum,map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    apply zeroProject_monomial_mul
    · by_contra H
      exact (Finsupp.mem_support_iff.mp hn) (hf n H)
    · by_contra H
      exact (Finsupp.mem_support_iff.mp hm) (hg m H)
  simpa only [sum_monomials] using H

lemma zeroProject_one : zeroProject v Ω h (1 : Torus v Ω)=1 := by
  classical
  change (Finsupp.filterAddHom (fun m=>h m=0) : Torus v Ω →+ Torus v Ω)
    (Torus.monomial v Ω 0 1)=Torus.monomial v Ω 0 1
  rw [filter_monomial,map_zero,ite_eq_left rfl]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PlanarRayOrder
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.PlanarRayOrder
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
include hB

lemma alternating_swap (x y : E) : B y x= -B x y := by
  have H:=hB (x+y)
  simp only [map_add,LinearMap.add_apply,hB,zero_add,add_zero] at H
  linarith

lemma plane_determinant (L : Module.Dual ℝ E) (r s m n : E)
    (hm : m∈Submodule.span ℝ {r,s}) (hn : n∈Submodule.span ℝ {r,s}) :
    L r*B m n=B m r*L n-L m*B n r := by
  obtain ⟨a,b,rfl⟩:=Submodule.mem_span_pair.mp hm
  obtain ⟨c,d,rfl⟩:=Submodule.mem_span_pair.mp hn
  simp only [map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,hB,
    mul_zero,zero_add,add_zero,alternating_swap B hB s r]
  ring

lemma plane_normalized_eq (L : Module.Dual ℝ E) (r s m p : E) (hrs : B r s≠0)
    (hm : m∈Submodule.span ℝ {r,s}) (hp : p∈Submodule.span ℝ {r,s}) (hmp : B m p=0) :
    L p • m=L m • p := by
  obtain ⟨a,b,rfl⟩:=Submodule.mem_span_pair.mp hm
  obtain ⟨c,d,rfl⟩:=Submodule.mem_span_pair.mp hp
  have he : a*d=b*c:=by
    have hh : (a*d-b*c)*B r s=0:=by
      simp only [map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,hB,
        mul_zero,zero_add,add_zero,alternating_swap B hB r s] at hmp
      nlinarith only [hmp]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hrs)
  simp only [map_add,map_smul,smul_eq_mul,smul_add,smul_smul]
  congr 1
  · congr 1
    calc
      (c*L r+d*L s)*a=(a*c)*L r+(a*d)*L s:=by ring
      _=(a*L r+b*L s)*c:=by rw [he]; ring
  · congr 1
    calc
      (c*L r+d*L s)*b=(b*c)*L r+(b*d)*L s:=by ring
      _=(a*L r+b*L s)*d:=by rw [←he]; ring

def slope (L : Module.Dual ℝ E) (r m : E) : ℝ := B m r/L m

lemma pairing_pos_iff (L : Module.Dual ℝ E) (r s m n : E)
    (hr : 0<L r) (hm : 0<L m) (hn : 0<L n)
    (hmP : m∈Submodule.span ℝ {r,s}) (hnP : n∈Submodule.span ℝ {r,s}) :
    0<B m n ↔ slope B L r n < slope B L r m := by
  rw [slope,slope,div_lt_div_iff₀ hn hm]
  have he:=plane_determinant B hB L r s m n hmP hnP
  constructor <;> intro hh <;> nlinarith

lemma pairing_zero_iff (L : Module.Dual ℝ E) (r s m n : E)
    (hr : 0<L r) (hm : 0<L m) (hn : 0<L n)
    (hmP : m∈Submodule.span ℝ {r,s}) (hnP : n∈Submodule.span ℝ {r,s}) :
    B m n=0 ↔ slope B L r n=slope B L r m := by
  rw [slope,slope,div_eq_div_iff (ne_of_gt hn) (ne_of_gt hm)]
  have he:=plane_determinant B hB L r s m n hmP hnP
  constructor <;> intro hh <;> nlinarith
end
end ElementaryPositivity.PlanarRayOrder

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RayIncomingIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A] [Module ℚ A]
lemma log_injective_through (F G : PowerSeries A) (N : ℕ)
    (hF : constantCoeff F=1) (hG : constantCoeff G=1)
    (h : ∀n≤N,coeff n (log F)=coeff n (log G)) :
    ∀n≤N,coeff n F=coeff n G := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp only [coeff_zero_eq_constantCoeff,hF,hG]
    | succ n =>
      have H:=log_leading_difference F G n hF hG
        (fun j hj=>ih j (by omega) (by omega))
      rw [h (n+1) hn,sub_self] at H
      exact sub_eq_zero.mp H.symm
end
end ElementaryPositivity.FormalLog

namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)

def OnPositiveRay (r m : M) : Prop := ∃a b : ℕ,0<a ∧ 0<b ∧ a • m=b • r

lemma OnPositiveRay.eval {r m : M} (hm : OnPositiveRay r m) (h : M→+ℝ) :
    (0<h m↔0<h r) ∧ (h m=0↔h r=0) ∧ (h m<0↔h r<0) := by
  obtain ⟨a,b,ha,hb,he⟩:=hm
  have H:=congrArg h he
  simp only [map_nsmul,nsmul_eq_mul] at H
  have ha' : (0:ℝ)<a:=by exact_mod_cast ha
  have hb' : (0:ℝ)<b:=by exact_mod_cast hb
  constructor
  · constructor <;> intro h <;> nlinarith
  constructor <;> constructor <;> intro h <;> nlinarith

lemma OnPositiveRay.incomingSigns {r m : M} (hm : OnPositiveRay r m) (x : M) :
    (0 < incomingCovector Ω r x↔0 < incomingCovector Ω m x) ∧
    (incomingCovector Ω r x=0↔incomingCovector Ω m x=0) ∧
    (incomingCovector Ω r x<0↔incomingCovector Ω m x<0) := by
  let h : M→+ℝ := (Int.castAddHom ℝ).comp (Ω x)
  have H:=hm.eval h
  exact ⟨H.1.symm,H.2.1.symm,H.2.2.symm⟩

omit [Algebra ℚ R] in
lemma chart_sign_congr (h k : M→+ℝ) (F : CompletedPositive v Ω C)
    (H : ∀m,(0<h m↔0<k m) ∧ (h m=0↔k m=0) ∧ (h m<0↔k m<0)) :
    chartPositive v Ω C h F=chartPositive v Ω C k F ∧
    chartZero v Ω C h F=chartZero v Ω C k F ∧
    chartNegative v Ω C h F=chartNegative v Ω C k F := by
  have hs:=chart_three_support v Ω C h F
  exact chart_three_unique v Ω C k F _ _ _ (chart_three_factorization v Ω C h F)
    (fun n m hm=>(H m).1.mp (hs.1 n m hm))
    (fun n m hm=>(H m).2.1.mp (hs.2.1 n m hm))
    (fun n m hm=>(H m).2.2.mp (hs.2.2 n m hm))

omit [Algebra ℚ R] in
lemma incoming_same_ray {r m : M} (hm : OnPositiveRay r m) (F : CompletedPositive v Ω C) :
    chartZero v Ω C (incomingCovector Ω r) F=chartZero v Ω C (incomingCovector Ω m) F :=
  (chart_sign_congr v Ω C _ _ F (hm.incomingSigns Ω)).2.1

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (e : M→+E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (L : Module.Dual ℝ E) (r s : E)

include he hB in
lemma positive_ray_of_pairing_zero (C : (I→ℤ)→+M)
    (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
    (hrs : B r s≠0) (m p : M) (n d : ℕ) (hn : 0<n) (hd : 0<d)
    (hm : HasRootDegree C n m) (hp : HasRootDegree C d p)
    (hmP : e m∈Submodule.span ℝ {r,s}) (hpP : e p∈Submodule.span ℝ {r,s})
    (hmp : B (e m) (e p)=0) : OnPositiveRay p m := by
  refine ⟨d,n,hd,hn,he ?_⟩
  have H:=PlanarRayOrder.plane_normalized_eq B hB L r s (e m) (e p) hrs hmP hpP hmp
  simpa only [hdeg n m hm,hdeg d p hp,Nat.cast_smul_eq_nsmul,map_nsmul] using H

include hB in

lemma finite_positive_ray_order (S : Finset M) (hr : 0<L r)
    (hS : ∀m∈S,0<L (e m) ∧ e m∈Submodule.span ℝ {r,s}) :
    ∃l : List M,(∀p∈l,p∈S) ∧ l.Pairwise (fun a b => 0<B (e a) (e b)) ∧
      ∀m∈S,∃p∈l,B (e m) (e p)=0 := by
  classical
  let slope : M → ℝ:=fun m => PlanarRayOrder.slope B L r (e m)
  let T:=S.image slope
  have hchoose (a : ℝ) (ha : a∈T) : ∃m∈S,slope m=a:=Finset.mem_image.mp ha
  let c (a : ℝ) : M:=if ha : a∈T then Classical.choose (hchoose a ha) else 0
  have hc : ∀a∈T,c a∈S ∧ slope (c a)=a:=by
    intro a ha
    dsimp [c]
    rw [dite_eq_left ha]
    exact Classical.choose_spec (hchoose a ha)
  let ts:=T.sort (· ≥ ·)
  have hts : ts.Pairwise (fun a b => b<a):=(T.sortedGT_sort).pairwise
  have hmem : ∀a∈ts,a∈T:=fun a ha => (Finset.mem_sort _).mp ha
  refine ⟨ts.map c,?_,?_,?_⟩
  · intro p hp
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hp
    exact (hc a (hmem a ha)).1
  · rw [List.pairwise_map]
    apply hts.imp_of_mem
    intro a b ha hb hab
    have hca:=hc a (hmem a ha)
    have hcb:=hc b (hmem b hb)
    apply (PlanarRayOrder.pairing_pos_iff B hB L r s (e (c a)) (e (c b)) hr
      (hS _ hca.1).1 (hS _ hcb.1).1 (hS _ hca.1).2 (hS _ hcb.1).2).mpr
    change slope (c b) < slope (c a)
    rw [hca.2,hcb.2]
    exact hab
  · intro m hm
    have ht : slope m∈T:=Finset.mem_image.mpr ⟨m,hm,rfl⟩
    have hh:=hc (slope m) ht
    refine ⟨c (slope m),List.mem_map.mpr ⟨slope m,(Finset.mem_sort _).mpr ht,rfl⟩,?_⟩
    apply (PlanarRayOrder.pairing_zero_iff B hB L r s (e m) (e (c (slope m))) hr
      (hS _ hm).1 (hS _ hh.1).1 (hS _ hm).2 (hS _ hh.1).2).mpr
    exact hh.2
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IsolatedPositivePlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
lemma OnPositiveRay.symm {r p : M} (H : OnPositiveRay r p) : OnPositiveRay p r := by
  obtain ⟨a,b,ha,hb,he⟩:=H
  exact ⟨b,a,hb,ha,he.symm⟩
lemma OnPositiveRay.trans {r p q : M} (H : OnPositiveRay r p) (K : OnPositiveRay p q) :
    OnPositiveRay r q := by
  obtain ⟨a,b,ha,hb,he⟩:=H
  obtain ⟨c,d,hc,hd,hf⟩:=K
  refine ⟨a*c,b*d,Nat.mul_pos ha hc,Nat.mul_pos hb hd,?_⟩
  calc
    (a*c) • q=a • (c • q):=by rw [smul_smul]
    _=a • (d • p):=by rw [hf]
    _=d • (a • p):=by rw [smul_smul,smul_smul,Nat.mul_comm]
    _=d • (b • r):=by rw [he]
    _=(b*d) • r:=by rw [smul_smul,Nat.mul_comm]
lemma OnPositiveRay.eq_pred {r p : M} (H : OnPositiveRay r p) :
    OnPositiveRay r=OnPositiveRay p := by
  funext q
  apply propext
  exact ⟨fun h=>H.symm.trans h,fun h=>H.trans h⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IncomingRayElement
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)

lemma OnPositiveRay.add {r a b : M} (ha : OnPositiveRay r a) (hb : OnPositiveRay r b) :
    OnPositiveRay r (a+b) := by
  obtain ⟨u,v,hu,hv,he⟩:=ha
  obtain ⟨s,t,hs,ht,hf⟩:=hb
  refine ⟨u*s,s*v+u*t,Nat.mul_pos hu hs,by positivity,?_⟩
  calc
    (u*s) • (a+b)=s • (u • a)+u • (s • b):=by
      rw [nsmul_add,mul_nsmul,mul_nsmul];
      congr 1; rw [←mul_nsmul,←mul_nsmul,Nat.mul_comm]
    _=s • (v • r)+u • (t • r):=by rw [he,hf]
    _=(s*v+u*t) • r:=by simp only [smul_smul,add_nsmul]

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)
local instance instAddGroupTorus_2 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

local instance instSubTorus_2_rf9cb96_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
lemma incoming_unique_through (hΩ : ∀m,Ω m m=0)
    (F G : CompletedPositive v Ω C) (N : ℕ)
    (H : ∀n≤N,incomingCoefficient v Ω C n F.val=incomingCoefficient v Ω C n G.val) :
    ∀n≤N,coeff n F.val=coeff n G.val := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih=>
    cases n with
    | zero=>simp only [coeff_zero_eq_constantCoeff,F.property.1,G.property.1]
    | succ n=>
      have hEq:=incomingCoefficient_leading v Ω C hΩ F.val G.val n
        (fun j hj=>ih j (by omega) (by omega)) (F.property.2 _) (G.property.2 _)
      rw [H (n+1) hn,sub_self] at hEq
      exact sub_eq_zero.mp hEq.symm
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I A : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I → ℤ)→+M)

omit [Algebra ℚ R] in
lemma completed_list_constant (l : List A) (F : A → CompletedPositive v Ω C) :
    constantCoeff (l.map (fun a=>(F a).val)).prod=1 := by
  induction l with
  | nil=>simp
  | cons a l ih=>simp only [List.map_cons,List.prod_cons,map_mul,(F a).property.1,ih,one_mul]
omit [Algebra ℚ R] in
lemma completed_list_graded (l : List A) (F : A → CompletedPositive v Ω C) :
    ∀n,coeff n (l.map (fun a=>(F a).val)).prod∈rootGrade v Ω C n := by
  induction l with
  | nil=>simpa using FormalLog.graded_one (rootGrade v Ω C) (rootGrade_one v Ω C)
  | cons a l ih=>
    simpa only [List.map_cons,List.prod_cons] using
      FormalLog.graded_multiply (rootGrade v Ω C) (rootGrade_mul v Ω C) _ _ (F a).property.2 ih

def completedListProduct (l : List A) (F : A → CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  ⟨(l.map (fun a=>(F a).val)).prod,completed_list_constant v Ω C l F,completed_list_graded v Ω C l F⟩

omit [Algebra ℚ R] in
lemma completed_list_supported (l : List A) (F : A → CompletedPositive v Ω C)
    (V : AddSubmonoid M) (H : ∀a∈l,∀n,coeff n (F a).val∈supportedSubring v Ω V) :
    ∀n,coeff n (completedListProduct v Ω C l F).val∈supportedSubring v Ω V := by
  induction l with
  | nil=>
    intro n
    simp only [completedListProduct,List.map_nil,List.prod_nil,coeff_one]
    split_ifs
    · exact (supportedSubring v Ω V).one_mem
    · exact (supportedSubring v Ω V).zero_mem
  | cons a l ih=>
    exact PowerSeriesSplit.mul_mem (supportedSubring v Ω V) _ _ (H a (by simp))
      (ih (fun a ha=>H a (by simp [ha])))

lemma incoming_coefficient_supported (V : AddSubmonoid M) (F : CompletedPositive v Ω C)
    (H : ∀n,coeff n F.val∈supportedSubring v Ω V) (n : ℕ) :
    incomingCoefficient v Ω C n F.val∈supportedSubring v Ω V := by
  intro m hm
  rw [incomingCoefficient_apply]
  split_ifs with hr
  · exact strict_log_support v Ω (V:=fun x=>x∈V) (fun a b ha hb=>V.add_mem ha hb)
      (chartZero v Ω C (incomingCovector Ω m) F).val
      (chartZero v Ω C (incomingCovector Ω m) F).property.1
      (fun j=> (chartThree_supported v Ω C (incomingCovector Ω m) V F H).2.1 (j+1)) n m hm
  · rfl

omit [Algebra ℚ R] in
lemma strict_list_product_through (l : List A) (F : A → CompletedPositive v Ω C)
    (P : M → Prop) (hP : ∀a b,P a → P b → P (a+b)) (N : ℕ)
    (H : ∀a∈l,∀n,n+1≤N → SupportedOn v Ω P (coeff (n+1) (F a).val)) :
    ∀n,n+1≤N → SupportedOn v Ω P (coeff (n+1) (completedListProduct v Ω C l F).val) := by
  induction l with
  | nil=>intro n hn; simp only [completedListProduct,List.map_nil,List.prod_nil,coeff_one,show n+1≠0 by omega,ite_false, if_false]; exact SupportedOn.zero v Ω P
  | cons a l ih=>
    exact strict_mul_through v Ω P hP (F a).val (completedListProduct v Ω C l F).val N
      (F a).property.1 (completed_list_constant v Ω C l F) (H a (by simp))
      (ih (fun a ha=>H a (by simp [ha])))

omit [Algebra ℚ R] in
lemma ordered_ray_middle (hΩ : ∀m,Ω m m=0) (l : List M)
    (F : M → CompletedPositive v Ω C) (N : ℕ)
    (H : ∀p∈l,∀n,n+1≤N → ∀m,coeff (n+1) (F p).val m≠0 → OnPositiveRay p m)
    (hpair : l.Pairwise (fun a b=>0<Ω a b)) (p : M) (hp : p∈l) :
    ∀n≤N,coeff n (F p).val=
      coeff n (chartZero v Ω C (incomingCovector Ω p) (completedListProduct v Ω C l F)).val := by
  classical
  obtain ⟨a,b,he⟩:=List.mem_iff_append.mp hp
  subst l
  have hsplit:=List.pairwise_append.mp hpair
  have hbefore : ∀q∈a,0 < incomingCovector Ω p q:=by
    intro q hq
    change (0:ℝ)<(Ω q p:ℝ)
    exact_mod_cast hsplit.2.2 q hq p (by simp)
  have hafter : ∀q∈b,incomingCovector Ω p q<0:=by
    intro q hq
    have Hpq:=(List.pairwise_cons.mp hsplit.2.1).1 q hq
    have Hsk : Ω q p= -Ω p q:=by
      have hh:=hΩ (p+q)
      simp only [map_add,AddMonoidHom.add_apply,hΩ,zero_add,add_zero] at hh
      omega
    change (Ω q p:ℝ)<0
    rw [Hsk,Int.cast_neg]
    exact neg_neg_of_pos (by exact_mod_cast Hpq)
  let ga:=completedListProduct v Ω C a F
  let gb:=completedListProduct v Ω C b F
  have hA:=strict_list_product_through v Ω C a F (fun x=>0 < incomingCovector Ω p x)
    (fun x y hx hy=>by simpa only [map_add] using add_pos hx hy) N
    (fun q hq j hj m hm=>by
      by_contra hn
      exact hm (((H q (by simp [hq]) j hj m hn).eval (incomingCovector Ω p)).1.mpr (hbefore q hq)))
  have hB:=strict_list_product_through v Ω C b F (fun x=>incomingCovector Ω p x<0)
    (fun x y hx hy=>by simpa only [map_add] using add_neg hx hy) N
    (fun q hq j hj m hm=>by
      by_contra hn
      exact hm (((H q (by simp [hq]) j hj m hn).eval (incomingCovector Ω p)).2.2.mpr (hafter q hq)))
  have heq : ga.val*(F p).val*gb.val=(completedListProduct v Ω C (a++p::b) F).val:=by
    simp only [ga,gb,completedListProduct,List.map_append,List.prod_append,List.map_cons,List.prod_cons,mul_assoc]
  have ht:=chart_three_truncated_unique v Ω C (incomingCovector Ω p)
    (completedListProduct v Ω C (a++p::b) F) ga.val (F p).val gb.val N
    ga.property.1 (F p).property.1 gb.property.1 heq
    (fun j hj m hm=>not_not.mp (fun hh=>hm (hA j hj m hh)))
    (fun j hj m hm=>((H p (by simp) j hj m hm).eval (incomingCovector Ω p)).2.1.mpr
      (by change (Ω p p:ℝ)=0; rw [hΩ,Int.cast_zero]))
    (fun j hj m hm=>not_not.mp (fun hh=>hm (hB j hj m hh)))
  exact fun n hn=>(ht n hn).2.1

theorem joint_recovered_from_incoming (hΩ : ∀m,Ω m m=0)
    (l : List M) (F : CompletedPositive v Ω C) (N : ℕ)
    (V : AddSubmonoid M) (hF : ∀n,coeff n F.val∈supportedSubring v Ω V)
    (hcover : ∀n,0<n → n≤N → ∀m,HasRootDegree C n m → m∈V → ∃p∈l,OnPositiveRay p m)
    (hpair : l.Pairwise (fun a b=>0<Ω a b))
    (hRay : ∀p∈l,∀n,n+1≤N → ∀m,
      coeff (n+1) (chartZero v Ω C (incomingCovector Ω p) F).val m≠0 → OnPositiveRay p m) :
    ∀n≤N,coeff n F.val=coeff n (completedListProduct v Ω C l
      (fun p=>chartZero v Ω C (incomingCovector Ω p) F)).val := by
  let G:=completedListProduct v Ω C l (fun p=>chartZero v Ω C (incomingCovector Ω p) F)
  apply incoming_unique_through v Ω C hΩ F G N
  intro n hn
  by_cases hn0 : n=0
  · subst n; rw [incomingCoefficient_zero,incomingCoefficient_zero]
  apply Finsupp.ext
  intro m
  by_cases hmV : m∈V
  · rw [incomingCoefficient_apply,incomingCoefficient_apply]
    split_ifs with hm
    · obtain ⟨p,hp,hpm⟩:=hcover n (by omega) hn m hm hmV
      have hmid:=ordered_ray_middle v Ω C hΩ l
        (fun p=>chartZero v Ω C (incomingCovector Ω p) F) N hRay hpair p hp
      have Hlog:=FormalLog.log_coeff_congr
        (chartZero v Ω C (incomingCovector Ω p) F).val
        (chartZero v Ω C (incomingCovector Ω p) G).val n (fun j hj=>hmid j (hj.trans hn))
      have hF:=incoming_same_ray v Ω C hpm F
      have hG:=incoming_same_ray v Ω C hpm G
      rw [hF,hG] at Hlog
      exact congrArg (fun x : Torus v Ω=>x m) Hlog
    · rfl
  · rw [incoming_coefficient_supported v Ω C V F hF n m hmV,
      incoming_coefficient_supported v Ω C V G
        (completed_list_supported v Ω C l _ V
          (fun p _=>(chartThree_supported v Ω C (incomingCovector Ω p) V F hF).2.1)) n m hmV]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PlanarJointFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M E I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)
variable (e : M→+E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

def planeRoots (r s : E) : AddSubmonoid M :=
  (Submodule.span ℝ {r,s}).toAddSubmonoid.comap e

lemma rootsThrough_spec {N : ℕ} {m : M} (H : m∈rootsThrough C N) :
    ∃n≤N,HasRootDegree C n m := by
  classical
  obtain ⟨n,hn,hm⟩:=Finset.mem_biUnion.mp H
  refine ⟨n,by have := Finset.mem_range.mp hn; omega,?_⟩
  simpa only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using hm

include he hB hcomp hdeg in

theorem planar_joint_factorization (r s : E) (hr : 0<L r) (hrs : B r s≠0)
    (F : CompletedPositive v Ω C)
    (hF : ∀n,coeff n F.val∈supportedSubring v Ω (planeRoots e r s)) (N : ℕ) :
    ∃l : List M,
      (∀p∈l,∃d,0<d ∧ d≤N ∧ HasRootDegree C d p ∧ p∈planeRoots e r s) ∧
      l.Pairwise (fun a b => 0<Ω a b) ∧
      (∀p∈l,∀n,n+1≤N → ∀m,
        coeff (n+1) (chartZero v Ω C (incomingCovector Ω p) F).val m≠0 → OnPositiveRay p m) ∧
      ∀n≤N,coeff n F.val=coeff n (completedListProduct v Ω C l
        (fun p => chartZero v Ω C (incomingCovector Ω p) F)).val := by
  classical
  let S:=(rootsThrough C N).filter (fun m => 0<L (e m) ∧ e m∈Submodule.span ℝ {r,s})
  have hS : ∀m∈S,0<L (e m) ∧ e m∈Submodule.span ℝ {r,s}:=fun m hm => (Finset.mem_filter.mp hm).2
  have hSmem : ∀m∈S,∃d,0<d ∧ d≤N ∧ HasRootDegree C d m ∧ m∈planeRoots e r s:=by
    intro m hm
    obtain ⟨d,hd,hrd⟩:=rootsThrough_spec C (Finset.mem_filter.mp hm).1
    have hp:= (hS m hm).1
    rw [hdeg d m hrd] at hp
    exact ⟨d,by exact_mod_cast hp,hd,hrd,(hS m hm).2⟩
  obtain ⟨l,hlS,hlpair,hlcover⟩:=finite_positive_ray_order e B hB L r s S hr hS
  have hl : ∀p∈l,∃d,0<d ∧ d≤N ∧ HasRootDegree C d p ∧ p∈planeRoots e r s:=
    fun p hp => hSmem p (hlS p hp)
  have hpair : l.Pairwise (fun a b => 0<Ω a b):=by
    apply hlpair.imp
    intro a b h
    rw [hcomp] at h
    exact_mod_cast h
  have hcover : ∀n,0<n → n≤N → ∀m,HasRootDegree C n m → m∈planeRoots e r s →
      ∃p∈l,OnPositiveRay p m:=by
    intro n hn hnN m hm hmP
    have hmS : m∈S:=Finset.mem_filter.mpr ⟨mem_rootsThrough C N n hnN m hm,
      by rw [hdeg n m hm]; exact ⟨by exact_mod_cast hn,hmP⟩⟩
    obtain ⟨p,hp,hmp⟩:=hlcover m hmS
    obtain ⟨d,hd,hdN,hdp,hpP⟩:=hl p hp
    exact ⟨p,hp,positive_ray_of_pairing_zero e he B hB L r s C hdeg hrs m p n d hn hd hm hdp hmP hpP hmp⟩
  have hRay : ∀p∈l,∀n,n+1≤N → ∀m,
      coeff (n+1) (chartZero v Ω C (incomingCovector Ω p) F).val m≠0 → OnPositiveRay p m:=by
    intro p hp n hn m hm
    obtain ⟨d,hd,hdN,hdp,hpP⟩:=hl p hp
    have hmr : HasRootDegree C (n+1) m:=by
      by_contra hh
      exact hm ((chartZero v Ω C (incomingCovector Ω p) F).property.2 (n+1) m hh)
    have hmP : m∈planeRoots e r s:=by
      by_contra hh
      exact hm ((chartThree_supported v Ω C (incomingCovector Ω p) (planeRoots e r s) F hF).2.1 (n+1) m hh)
    have hmp : B (e m) (e p)=0:=by
      rw [hcomp]
      exact (chart_three_support v Ω C (incomingCovector Ω p) F).2.1 n m hm
    exact positive_ray_of_pairing_zero e he B hB L r s C hdeg hrs m p (n+1) d
      (by omega) hd hmr hdp hmP hpP hmp
  have hΩ : ∀m,Ω m m=0:=by
    intro m
    have H:=hB (e m)
    rw [hcomp] at H
    exact_mod_cast H
  exact ⟨l,hl,hpair,hRay,joint_recovered_from_incoming v Ω C hΩ l F N (planeRoots e r s) hF hcover hpair hRay⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteSignCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit RootTruncation
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
omit [Algebra ℚ R] in
lemma chartZero_congr_through (h : M →+ ℝ) (F G : CompletedPositive v Ω C) (N : ℕ)
    (he : ∀n ≤ N,coeff n F.val=coeff n G.val) :
    ∀n ≤ N,coeff n (chartZero v Ω C h F).val=coeff n (chartZero v Ω C h G).val := by
  intro n hn
  exact zero_coeff_congr _ _ _ _ n (fun j hj => he j (hj.trans hn))
omit [Algebra ℚ R] in
lemma chart_sign_congr_through (h k : M →+ ℝ) (F : CompletedPositive v Ω C) (N : ℕ)
    (hs : ∀n,0 < n → n ≤ N → ∀m,HasRootDegree C n m →
      (0 < h m → 0 < k m) ∧ (h m=0 → k m=0) ∧ (h m < 0 → k m < 0)) :
    ∀n ≤ N,coeff n (chartZero v Ω C h F).val=coeff n (chartZero v Ω C k F).val := by
  have H:=chart_three_support v Ω C h F
  have HU:=chart_three_truncated_unique v Ω C k F
    (chartPositive v Ω C h F).val (chartZero v Ω C h F).val (chartNegative v Ω C h F).val N
    (chartPositive v Ω C h F).property.1 (chartZero v Ω C h F).property.1
    (chartNegative v Ω C h F).property.1 (chart_three_factorization v Ω C h F)
    (fun n hn m hm => (hs (n+1) (by omega) hn m
      (chart_root_of_ne v Ω C _ _ _ hm)).1 (H.1 n m hm))
    (fun n hn m hm => (hs (n+1) (by omega) hn m
      (chart_root_of_ne v Ω C _ _ _ hm)).2.1 (H.2.1 n m hm))
    (fun n hn m hm => (hs (n+1) (by omega) hn m
      (chart_root_of_ne v Ω C _ _ _ hm)).2.2 (H.2.2 n m hm))
  exact fun n hn => (HU n hn).2.1

def RayGeneric (N : ℕ) (r : M) (h : M →+ ℝ) : Prop :=
  h r=0 ∧ ∀n,0 < n → n ≤ N → ∀m,HasRootDegree C n m → h m=0 → OnPositiveRay r m
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteRayGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FiniteRayGeometry
noncomputable section
open Module
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma dual_avoid_in_annihilator (r : E) (W : Finset E)
    (hW : ∀w∈W,w∉Submodule.span ℝ {r}) :
    ∃g : Module.Dual ℝ E,g r=0 ∧ ∀w∈W,g w≠0 := by
  let P:=Submodule.span ℝ {r}
  let q:=P.mkQ
  have H : ∀w : W,q w.val≠0:=by
    intro w hw
    exact hW w.val w.property ((Submodule.Quotient.mk_eq_zero P).mp hw)
  obtain ⟨f,hf⟩:=Module.exists_dual_forall_apply_ne_zero (K:=ℝ) (fun w : W=>q w.val) H
  refine ⟨f.comp q,?_,?_⟩
  · have hr : r∈P:=Submodule.subset_span (Set.mem_singleton r)
    simp only [LinearMap.comp_apply,show q r=0 from (Submodule.Quotient.mk_eq_zero P).mpr hr,map_zero]
  · intro w hw
    exact hf ⟨w,hw⟩

lemma scalar_sign_epsilon (a b : ℝ) : ∃ε>0,∀δ:ℝ,0<δ → δ<ε →
    (0<a → 0<a+δ*b) ∧ (a<0 → a+δ*b<0) ∧ (a=0 → b≠0 → a+δ*b≠0) := by
  by_cases ha : a=0
  · refine ⟨1,one_pos,?_⟩
    intro δ hd _
    simp [ha,ne_of_gt hd]
  · have hp : 0 < |b|+1:=by positivity
    refine ⟨|a|/(|b|+1),div_pos (abs_pos.mpr ha) hp,?_⟩
    intro δ hd he
    have H:=(lt_div_iff₀ hp).mp he
    have hlo:=mul_le_mul_of_nonneg_left (neg_abs_le b) hd.le
    have hhi:=mul_le_mul_of_nonneg_left (le_abs_self b) hd.le
    refine ⟨?_,?_,fun h=>False.elim (ha h)⟩
    · intro h; rw [abs_of_pos h] at H; nlinarith
    · intro h; rw [abs_of_neg h] at H; nlinarith

lemma preserve_finite_signs (S : Finset E) (k g : Module.Dual ℝ E) :
    ∃ε>0,∀δ:ℝ,0<δ → δ<ε → ∀s∈S,
      (0<k s → 0<(k+δ • g) s) ∧ (k s<0 → (k+δ • g) s<0) ∧
      (k s=0 → g s≠0 → (k+δ • g) s≠0) := by
  classical
  induction S using Finset.induction_on with
  | empty=>exact ⟨1,one_pos,fun _ _ _ _ hs=>False.elim (Finset.notMem_empty _ hs)⟩
  | @insert s S hs ih=>
    obtain ⟨ε,he,Hε⟩:=ih
    obtain ⟨η,hh,Hη⟩:=scalar_sign_epsilon (k s) (g s)
    refine ⟨min ε η,lt_min he hh,?_⟩
    intro δ hd hδε x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact Hη δ hd (lt_of_lt_of_le hδε (min_le_right _ _))
    · exact Hε δ hd (lt_of_lt_of_le hδε (min_le_left _ _)) x hx

lemma generic_offset (r : E) (W S : Finset E) (k : Module.Dual ℝ E)
    (hk : k r=0) (hW : ∀w∈W,w∉Submodule.span ℝ {r}) :
    ∃h : Module.Dual ℝ E,h r=0 ∧ (∀w∈W,h w≠0) ∧
      ∀s∈S,(0<k s → 0<h s) ∧ (k s<0 → h s<0) := by
  classical
  obtain ⟨g,hgr,hg⟩:=dual_avoid_in_annihilator r W hW
  obtain ⟨ε,he,Hε⟩:=preserve_finite_signs (W∪S) k g
  let δ:=ε/2
  have hd : 0<δ:=by dsimp [δ] <;> positivity
  have hδε : δ<ε:=by dsimp [δ] <;> linarith
  refine ⟨k+δ • g,by simp [hk,hgr],?_,?_⟩
  · intro w hw
    have H:=Hε δ hd hδε w (Finset.mem_union_left _ hw)
    rcases lt_trichotomy (k w) 0 with hh|hh|hh
    · exact ne_of_lt (H.2.1 hh)
    · exact H.2.2 hh (hg w hw)
    · exact ne_of_gt (H.1 hh)
  · intro s hs
    have H:=Hε δ hd hδε s (Finset.mem_union_right _ hs)
    exact ⟨H.1,H.2.1⟩

def forbidden (S : Finset E) (r : E) (v : Module.Dual ℝ E) : Finset E := by
  classical
  exact (S ∪ (S×ˢS).image (fun st=>v st.1 • st.2-v st.2 • st.1)).filter
    (fun w=>w∉Submodule.span ℝ {r})

structure GenericOffset (S : Finset E) (r : E) (v h : Module.Dual ℝ E) : Prop where
  on_ray : h r=0
  avoid : ∀s∈S,s∉Submodule.span ℝ {r} → h s≠0
  distinct : ∀s∈S,∀t∈S,v s • t-v t • s∉Submodule.span ℝ {r} →
    h (v s • t-v t • s)≠0

lemma exists_generic_offset (S : Finset E) (r : E) (v k : Module.Dual ℝ E)
    (hk : k r=0) : ∃h : Module.Dual ℝ E,GenericOffset S r v h ∧
      ∀s∈S,(0<k s → 0<h s) ∧ (k s<0 → h s<0) := by
  classical
  obtain ⟨h,hr,hW,hS⟩:=generic_offset r (forbidden S r v) S k hk
    (fun w hw=>(Finset.mem_filter.mp hw).2)
  refine ⟨h,⟨hr,?_,?_⟩,hS⟩
  · intro s hs hn
    exact hW s (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hs,hn⟩)
  · intro s hs t ht hn
    exact hW _ (Finset.mem_filter.mpr ⟨Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(s,t),Finset.mem_product.mpr ⟨hs,ht⟩,rfl⟩),hn⟩)

lemma GenericOffset.joint_plane {S : Finset E} {r : E} {v h : Module.Dual ℝ E}
    (H : GenericOffset S r v h) {s t : E} (hs : s∈S) (ht : t∈S) (hv : v s≠0)
    (a : ℝ) (hsa : (h+a • v) s=0) (hta : (h+a • v) t=0) :
    t∈Submodule.span ℝ {r,s} := by
  classical
  have hw : v s • t-v t • s∈Submodule.span ℝ {r}:=by
    by_contra hn
    apply H.distinct s hs t ht hn
    simp only [map_sub,map_smul,smul_eq_mul]
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] at hsa hta
    have hs0 : h s = -a * v s := by linarith
    have ht0 : h t = -a * v t := by linarith
    rw [hs0,ht0]
    ring
  have hw' : v s • t-v t • s∈Submodule.span ℝ {r,s}:=
    (Submodule.span_mono (by simp : ({r}:Set E)⊆{r,s})) hw
  have hs' : s∈Submodule.span ℝ {r,s}:=Submodule.subset_span (by simp)
  have Hst:= (Submodule.span ℝ {r,s}).add_mem hw'
    ((Submodule.span ℝ {r,s}).smul_mem (v t) hs')
  simp only [sub_add_cancel] at Hst
  exact ((Submodule.span ℝ {r,s}).smul_mem_iff hv).mp Hst

end
end ElementaryPositivity.FiniteRayGeometry

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (e : M →+ E) (he : Function.Injective e) (C : (I → ℤ) →+ M)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

def lineEvents (S : Finset E) (v h : Module.Dual ℝ E) : Finset ℝ := by
  classical
  exact (S.filter (fun s => v s≠0)).image (fun s => -h s/v s)
lemma mem_lineEvents_iff (S : Finset E) (v h : Module.Dual ℝ E) (a : ℝ) :
    a∈lineEvents S v h ↔ ∃s∈S,v s≠0 ∧ (h+a • v) s=0 := by
  classical
  constructor
  · rintro ha
    obtain ⟨s,hs,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨hs,hn⟩:=Finset.mem_filter.mp hs
    refine ⟨s,hs,hn,?_⟩
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
    field_simp
    ring
  · rintro ⟨s,hs,hn,H⟩
    apply Finset.mem_image.mpr
    refine ⟨s,Finset.mem_filter.mpr ⟨hs,hn⟩,?_⟩
    apply (div_eq_iff hn).mpr
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] at H
    linarith

def realRootsThrough (N : ℕ) : Finset E := by
  classical
  exact (rootsThrough C N).image e
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PlanarRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry RootTruncation
noncomputable section
variable {R M E I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include hcomp in
lemma real_perturbed_covector (k : Module.Dual ℝ E) (p : M) (δ : ℝ) :
    (k+δ • B.flip (e p)).toAddMonoidHom.comp e=
      k.toAddMonoidHom.comp e+δ • incomingCovector Ω p := by
  ext m
  change k (e m)+δ*B (e m) (e p)=k (e m)+δ*(Ω m p:ℝ)
  rw [hcomp]
lemma linear_zero_on_plane (k : Module.Dual ℝ E) (r s m : E)
    (hr : k r=0) (hs : k s=0) (hm : m∈Submodule.span ℝ {r,s}) : k m=0 := by
  obtain ⟨a,b,rfl⟩:=Submodule.mem_span_pair.mp hm
  simp only [map_add,map_smul,hr,hs,smul_zero,add_zero]
omit [Algebra ℚ R] in
include he hB hcomp hdeg in
lemma planar_refinement_generic (N : ℕ) (r s : E) (hrs : B r s≠0)
    (k : Module.Dual ℝ E) (hkr : k r=0) (hks : k s=0)
    (hzero : ∀n,n ≤ N → ∀m,HasRootDegree C n m → k (e m)=0 → e m∈Submodule.span ℝ {r,s})
    (p : M) (d : ℕ) (hd : 0 < d) (hp : HasRootDegree C d p)
    (hpP : e p∈Submodule.span ℝ {r,s}) (F : CompletedPositive v Ω C) :
    ∃ε > 0,∀δ : ℝ,0 < δ → δ < ε →
      RayGeneric C N p ((k+δ • B.flip (e p)).toAddMonoidHom.comp e) ∧
      ∀n ≤ N,coeff n (chartZero v Ω C ((k+δ • B.flip (e p)).toAddMonoidHom.comp e) F).val=
        coeff n (chartZero v Ω C (incomingCovector Ω p)
          (chartZero v Ω C (k.toAddMonoidHom.comp e) F)).val := by
  let kM:=k.toAddMonoidHom.comp e
  obtain ⟨ε,heps,Hε⟩:=root_lex_epsilon C N kM (incomingCovector Ω p)
  refine ⟨ε,heps,?_⟩
  intro δ hdδ hδε
  rw [real_perturbed_covector Ω e B hcomp]
  constructor
  · constructor
    · change k (e p)+δ*(Ω p p:ℝ)=0
      have hpp : (Ω p p:ℝ)=0:=by rw [←hcomp,hB]
      rw [hpp,linear_zero_on_plane k r s (e p) hkr hks hpP,mul_zero,add_zero]
    · intro n hn hnN m hm hm0
      have Hs:=Hε δ hdδ hδε n hnN m hm
      have hz : kM m=0:=by
        rcases lt_trichotomy (kM m) 0 with hh|hh|hh
        · exact False.elim (ne_of_lt (Hs.2.1 hh) hm0)
        · exact hh
        · exact False.elim (ne_of_gt (Hs.1 hh) hm0)
      have hmp : B (e m) (e p)=0:=by
        rw [hcomp]
        change kM m+δ*(Ω m p:ℝ)=0 at hm0
        rw [hz,zero_add] at hm0
        exact (mul_eq_zero.mp hm0).resolve_left (ne_of_gt hdδ)
      exact positive_ray_of_pairing_zero e he B hB L r s C hdeg hrs m p n d hn hd hm hp
        (hzero n hnN m hm hz) hpP hmp
  · exact chart_zero_refinement v Ω C kM (incomingCovector Ω p) _ F N (Hε δ hdδ hδε)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WallLineInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FiniteEventTraversal
noncomputable section
lemma finite_gap (S : Finset ℝ) (a : ℝ) :
    ∃ε > 0,∀s∈S,s≠a  →  ε < |s-a| := by
  classical
  induction S using Finset.induction_on with
  | empty=>exact ⟨1,one_pos,by simp⟩
  | @insert s S hs ih=>
    obtain ⟨ε,he,H⟩:=ih
    by_cases hsa : s=a
    · refine ⟨ε,he,?_⟩
      intro x hx hn
      rcases Finset.mem_insert.mp hx with rfl|hx
      · exact False.elim (hn hsa)
      · exact H x hx hn
    · refine ⟨min ε (|s-a|/2),lt_min he (by have := abs_pos.mpr (sub_ne_zero.mpr hsa); positivity),?_⟩
      intro x hx hn
      rcases Finset.mem_insert.mp hx with rfl|hx
      · exact lt_of_le_of_lt (min_le_right _ _) (by have := abs_pos.mpr (sub_ne_zero.mpr hsa); linarith)
      · exact lt_of_le_of_lt (min_le_left _ _) (H x hx hn)
lemma near_not_mem (S : Finset ℝ) (a δ ε : ℝ) (hd : 0 < δ) (hde : δ < ε)
    (H : ∀s∈S,s≠a  →  ε < |s-a|) : a+δ∉S ∧ a-δ∉S := by
  constructor
  · intro hs
    have hx:=H (a+δ) hs (by linarith)
    rw [add_sub_cancel_left,abs_of_pos hd] at hx
    linarith
  · intro hs
    have hx:=H (a-δ) hs (by linarith)
    have he : a-δ-a= -δ:=by ring
    rw [he,abs_neg,abs_of_pos hd] at hx
    linarith

theorem descend (S : Finset ℝ) (P : ℝ → Prop)
    (initial : ∃b,0 ≤ b ∧ (∀s∈S,s < b) ∧ P b)
    (cell : ∀a b,0 ≤ a  →  0 ≤ b  →  a∉S  →  b∉S  →
      (∀s∈S,a < s↔b < s)  →  P a  →  P b)
    (step : ∀a∈S,0 < a  →  ∃ε > 0,∀δ,0 < δ  →  δ < ε  →  P (a+δ)  →  P (a-δ))
    (t : ℝ) (ht : 0 ≤ t) (htS : t∉S) : P t := by
  classical
  suffices ∀k,∀t:ℝ,0 ≤ t  →  t∉S  →  (S.filter (fun s=>t < s)).card=k  →  P t from
    this _ t ht htS rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih=>
    intro t ht htS hk
    let U:=S.filter (fun s=>t < s)
    by_cases hU : U.Nonempty
    · let a:=U.min' hU
      have haU : a∈U:=Finset.min'_mem _ _
      have haS : a∈S:=(Finset.mem_filter.mp haU).1
      have hta : t < a:=(Finset.mem_filter.mp haU).2
      obtain ⟨ε,he,Hε⟩:=step a haS (lt_of_le_of_lt ht hta)
      obtain ⟨η,hh,Hη⟩:=finite_gap S a
      let δ:=min (min ε η) (a-t)/2
      have hd : 0 < δ:=by dsimp [δ]; exact div_pos (lt_min (lt_min he hh) (sub_pos.mpr hta)) (by norm_num)
      have hδsmall : δ < min (min ε η) (a-t):=by
        have hp : 0 < min (min ε η) (a-t):=lt_min (lt_min he hh) (sub_pos.mpr hta)
        dsimp [δ] <;> linarith
      have hδε : δ < ε:=lt_of_lt_of_le hδsmall ((min_le_left _ _).trans (min_le_left _ _))
      have hδη : δ < η:=lt_of_lt_of_le hδsmall ((min_le_left _ _).trans (min_le_right _ _))
      have hδt : δ < a-t:=lt_of_lt_of_le hδsmall (min_le_right _ _)
      have hnS:=near_not_mem S a δ η hd hδη Hη
      have hsub : S.filter (fun s=>a+δ < s) ⊂ U:=by
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · intro x hx
          obtain ⟨hx,hxx⟩:=Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨hx,by linarith⟩
        · intro heq
          have hx : a∈S.filter (fun s=>a+δ < s):=heq.symm ▸ haU
          have := (Finset.mem_filter.mp hx).2
          linarith
      have hcard : (S.filter (fun s=>a+δ < s)).card < k:=by
        rw [←hk]; exact Finset.card_lt_card hsub
      have hb : P (a+δ):=ih _ hcard (a+δ) (by linarith) hnS.1 rfl
      have hc : P (a-δ):=Hε δ hd hδε hb
      apply cell (a-δ) t (by linarith) ht hnS.2 htS _ hc
      intro s hs
      constructor
      · intro hcs
        by_contra hts
        linarith
      · intro hts
        have hsu : s∈U:=Finset.mem_filter.mpr ⟨hs,hts⟩
        have has : a ≤ s:=Finset.min'_le _ _ hsu
        linarith
    · obtain ⟨b,hb,hbS,hPb⟩:=initial
      have hbN : b∉S:=fun hbmem=>lt_irrefl b (hbS b hbmem)
      apply cell b t hb ht hbN htS _ hPb
      intro s hs
      have hts : ¬t < s:=fun h=>hU ⟨s,Finset.mem_filter.mpr ⟨hs,h⟩⟩
      exact iff_of_false (not_lt_of_ge (hbS s hs).le) hts
end
end ElementaryPositivity.FiniteEventTraversal

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_GlobalWallPositive
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
attribute [local instance] Classical.propDecidable
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)

def literalIncomingRay (l : List (WallUnitDatum M)) (r : M) :
    PowerSeries (Torus LaurentRay.vUnit Ω) := by
  classical
  exact ((l.filter (fun u => OnPositiveRay r u.root)).map (WallUnitDatum.value Ω)).prod
lemma literalIncomingRay_mem (l : List (WallUnitDatum M))
    (hl : ∀u∈l,u.Allowed C (fun _=>True)) (r : M) :
    literalIncomingRay Ω l r∈literalRootProducts Ω C (OnPositiveRay r) := by
  classical
  refine ⟨l.filter (fun u => OnPositiveRay r u.root),?_,rfl⟩
  intro u hu
  have H:=List.mem_filter.mp hu
  exact ⟨(hl u H.1).1,(hl u H.1).2.1,by simpa using H.2⟩
lemma literalIncomingRay_eq (l : List (WallUnitDatum M)) {r m : M}
    (hm : OnPositiveRay r m) : literalIncomingRay Ω l r=literalIncomingRay Ω l m := by
  classical
  unfold literalIncomingRay
  rw [hm.eq_pred]
def literalIncomingCompleted (l : List (WallUnitDatum M))
    (hl : ∀u∈l,u.Allowed C (fun _=>True)) (r : M) : CompletedPositive LaurentRay.vUnit Ω C :=
  ⟨literalIncomingRay Ω l r,
    literalRootProducts_constant Ω C _ (literalIncomingRay_mem Ω C l hl r),
    literalRootProducts_graded Ω C _ (literalIncomingRay_mem Ω C l hl r)⟩

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_NonpJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation
noncomputable section
variable {R M E I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)

omit [Algebra ℚ R] in
lemma completedListProduct_congr_through {A : Type*} (l : List A)
    (F G : A → CompletedPositive v Ω C) (N : ℕ)
    (H : ∀a∈l,∀j≤N,coeff j (F a).val=coeff j (G a).val) :
    ∀j≤N,coeff j (completedListProduct v Ω C l F).val=
      coeff j (completedListProduct v Ω C l G).val := by
  intro j hj
  exact PowerSeriesSplit.product_coeff_congr _ _ l j (fun a ha i hi=>H a ha i (hi.trans hj))

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_OffCutJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation
noncomputable section
variable {R M E I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [AddCommGroup E] [Module ℝ E] [Fintype I] [DecidableEq I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))

def cutSide (pos : Bool) (h : M →+ ℝ) (p : M) : Prop := if pos then 0<h p else h p<0

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SimpleIncomingData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d)

def simpleDatum (i : I) : WallUnitDatum M := ⟨1,simpleRoot C i,0,-1⟩
def simpleIncomingList : List (WallUnitDatum M) := (Finset.univ.toList).map (simpleDatum C)

omit [Fintype I] in
include hcoord in
lemma simpleRoot_coordinates (i j : I) : coord (simpleRoot C i) j= (Pi.single i 1 : I → ℤ) j := by
  exact congrFun (hcoord _) j
include hcoord in
lemma nonpDegree_simple_self (pc : I) : nonpDegree coord pc (simpleRoot C pc)=0 := by
  change (∑i∈Finset.univ.erase pc,coord (simpleRoot C pc) i)=0
  apply Finset.sum_eq_zero
  intro i hi
  rw [simpleRoot_coordinates C coord hcoord]
  simp [(Finset.mem_erase.mp hi).1]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_MutationFiberArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
def mutationPairing : I → ℤ := fun i=>Ω (simpleRoot C pc) (simpleRoot C i)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_SymplecticTorusMap
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus.Torus
noncomputable section
variable {K M N : Type*} [CommRing K] [AddCommGroup M] [AddCommGroup N]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (Ω' : N →+ N →+ ℤ)
variable (L : M →+ N) (hL : ∀a b,Ω' (L a) (L b)=Ω a b)
def pushAdd : Torus v Ω →+ Torus v Ω' where
  toFun:=Finsupp.mapDomain L
  map_zero':=Finsupp.mapDomain_zero
  map_add' _ _:=Finsupp.mapDomain_add
@[simp] lemma pushAdd_monomial (m : M) (a : K) :
    pushAdd v Ω Ω' L (monomial v Ω m a)=monomial v Ω' (L m) a := Finsupp.mapDomain_single
include hL in
lemma pushAdd_mul (f g : Torus v Ω) :
    pushAdd v Ω Ω' L (f*g)=pushAdd v Ω Ω' L f*pushAdd v Ω Ω' L g := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [add_mul,map_add,hf,hg]
  | single m a=>
    induction g using Finsupp.induction_linear with
    | zero=>simp
    | add f g hf hg=>simp only [mul_add,map_add,hf,hg]
    | single n b=>
      change pushAdd v Ω Ω' L (monomial v Ω m a*monomial v Ω n b)=
        pushAdd v Ω Ω' L (monomial v Ω m a)*pushAdd v Ω Ω' L (monomial v Ω n b)
      rw [monomial_mul_monomial,pushAdd_monomial,pushAdd_monomial,pushAdd_monomial,
        monomial_mul_monomial,hL,map_add]
def push : Torus v Ω →+* Torus v Ω' where
  __:=pushAdd v Ω Ω' L
  map_one':=by change pushAdd v Ω Ω' L (monomial v Ω 0 1)=monomial v Ω' 0 1; rw [pushAdd_monomial,map_zero]
  map_mul':=pushAdd_mul v Ω Ω' L hL
@[simp] lemma push_monomial (m : M) (a : K) :
    push v Ω Ω' L hL (monomial v Ω m a)=monomial v Ω' (L m) a := pushAdd_monomial v Ω Ω' L m a
@[simp] lemma push_X (m : M) : push v Ω Ω' L hL (X v Ω m)=X v Ω' (L m) := push_monomial v Ω Ω' L hL m 1
end
end ElementaryPositivity.QuantumTorus.Torus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalFiberScale
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open Polynomial
noncomputable section
open scoped LaurentSeries RatFunc
variable {K : Type*} [Field K]
def polynomialScale (a : Kˣ) : K[X] ≃ₐ[K] K[X] :=
  Polynomial.algEquivOfCompEqX (C (a:K)*X) (C (↑(a⁻¹):K)*X)
    (by simp [Polynomial.mul_comp,←mul_assoc,←map_mul])
    (by simp [Polynomial.mul_comp,←mul_assoc,←map_mul])
@[simp] lemma polynomialScale_apply (a : Kˣ) (f : K[X]) :
    polynomialScale a f=f.comp (C (a:K)*X) := by
  simp [polynomialScale,Polynomial.comp_eq_aeval]
def scaleEval (a : Kˣ) : K[X] →+* RatFunc K :=
  (algebraMap K[X] (RatFunc K)).comp (polynomialScale a).toRingHom
lemma scaleEval_injective (a : Kˣ) : Function.Injective (scaleEval a) :=
  (RatFunc.algebraMap_injective (K:=K)).comp (polynomialScale a).injective
lemma scaleEval_regular (a : Kˣ) :
    (nonZeroDivisors K[X]) ≤ (nonZeroDivisors (RatFunc K)).comap (scaleEval a) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (scaleEval_injective a)
def scale (a : Kˣ) : RatFunc K →+* RatFunc K :=
  RatFunc.liftRingHom (scaleEval a) (scaleEval_regular a)
@[simp] lemma scale_polynomial (a : Kˣ) (f : K[X]) :
    scale a (algebraMap K[X] (RatFunc K) f)=
      algebraMap K[X] (RatFunc K) (f.comp (C (a:K)*X)) := by
  rw [scale,RatFunc.liftRingHom_algebraMap]
  simp [scaleEval]
lemma ratFunc_hom_ext {L : Type*} [Field L] (f g : RatFunc K →+* L)
    (hpoly : ∀p : K[X],f (algebraMap K[X] (RatFunc K) p)=g (algebraMap K[X] (RatFunc K) p)) : f=g := by
  apply RingHom.ext
  intro x
  induction x using RatFunc.induction_on with
  | f p q hq=>simp only [map_div₀,hpoly]
@[simp] lemma scale_one : scale (1:Kˣ)=RingHom.id (RatFunc K) := by
  apply ratFunc_hom_ext
  intro p
  simp
lemma scale_mul (a b : Kˣ) : (scale a).comp (scale b)=scale (a*b) := by
  apply ratFunc_hom_ext
  intro p
  simp only [RingHom.comp_apply,scale_polynomial]
  congr 1
  rw [Polynomial.comp_assoc]
  congr 1
  simp only [Polynomial.mul_comp,Polynomial.C_comp,Polynomial.X_comp,Units.val_mul]
  rw [←mul_assoc,←map_mul,mul_comm (b:K) (a:K)]
@[simp] lemma scale_constant (a : Kˣ) (b : K) :
    scale a (RatFunc.C b)=RatFunc.C b := by
  change scale a (algebraMap K[X] (RatFunc K) (C b))=algebraMap K[X] (RatFunc K) (C b)
  rw [scale_polynomial,Polynomial.C_comp]
@[simp] lemma scale_X (a : Kˣ) : scale a RatFunc.X=RatFunc.C (a:K)*RatFunc.X := by
  change scale a (algebraMap K[X] (RatFunc K) X)=_
  rw [scale_polynomial,Polynomial.X_comp,map_mul]
  rfl
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_RationalFiberTorus
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
@[reducible] def FiberTorus (_v : Kˣ) (_Ω : M →+ M →+ ℤ) (_α : M →+ ℤ) := M →₀ RatFunc K
namespace FiberTorus
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (α : M →+ ℤ)
def monomial (m : M) (a : RatFunc K) : FiberTorus v Ω α := Finsupp.single m a
def twist (m : M) : RatFunc K →+* RatFunc K := scale (v^(-2*α m))
lemma twist_add (m n : M) (a : RatFunc K) : twist v α (m+n) a=twist v α m (twist v α n a) := by
  change scale (v^(-2*α (m+n))) a=((scale (v^(-2*α m))).comp (scale (v^(-2*α n)))) a
  rw [scale_mul,map_add,_root_.mul_add,zpow_add]
@[simp] lemma twist_constant (m : M) (a : K) : twist v α m (RatFunc.C a)=RatFunc.C a := scale_constant _ _
@[simp] lemma twist_zero (a : RatFunc K) : twist v α 0 a=a := by simp [twist]
def multiply (f g : FiberTorus v Ω α) : FiberTorus v Ω α :=
  Finsupp.sum f fun m a=>Finsupp.sum g fun n b=>
    Finsupp.single (m+n) (a*twist v α m b*RatFunc.C (↑(v^(Ω m n)):K))
instance instMul : Mul (FiberTorus v Ω α) := ⟨multiply v Ω α⟩
instance instOne : One (FiberTorus v Ω α) := ⟨monomial v Ω α 0 1⟩
@[simp] lemma monomial_zero (m : M) : monomial v Ω α m 0=0 := Finsupp.single_zero _
@[simp] lemma monomial_add (m : M) (a b : RatFunc K) :
    monomial v Ω α m (a+b)=monomial v Ω α m a+monomial v Ω α m b := Finsupp.single_add ..
@[simp] lemma mul_zero (f : FiberTorus v Ω α) : f*0=0 := by simp [HMul.hMul,Mul.mul,multiply]
@[simp] lemma zero_mul (f : FiberTorus v Ω α) : (0 : FiberTorus v Ω α)*f=0 := by simp [HMul.hMul,Mul.mul,multiply]
lemma add_mul (f g h : FiberTorus v Ω α) : (f+g)*h=f*h+g*h := by
  classical
  change multiply v Ω α (f+g) h=multiply v Ω α f h+multiply v Ω α g h
  simp only [multiply]
  rw [Finsupp.sum_add_index']
  · intro m; simp
  · intro m a b
    simp only [_root_.add_mul,Finsupp.single_add,Finsupp.sum_add]
lemma mul_add (f g h : FiberTorus v Ω α) : f*(g+h)=f*g+f*h := by
  classical
  change multiply v Ω α f (g+h)=multiply v Ω α f g+multiply v Ω α f h
  simp only [multiply]
  rw [←Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro m ha
  rw [Finsupp.sum_add_index']
  · intro n; simp
  · intro n a b
    simp only [map_add,_root_.mul_add,_root_.add_mul,Finsupp.single_add]
@[simp] lemma monomial_mul (m n : M) (a b : RatFunc K) :
    monomial v Ω α m a*monomial v Ω α n b=
      monomial v Ω α (m+n) (a*twist v α m b*RatFunc.C (↑(v^(Ω m n)):K)) := by
  classical
  change multiply v Ω α (Finsupp.single m a) (Finsupp.single n b)=_
  simp only [multiply,monomial,Finsupp.sum_single_index,MulZeroClass.zero_mul,
    MulZeroClass.mul_zero,map_zero,Finsupp.single_zero]
lemma mul_assoc (f g h : FiberTorus v Ω α) : (f*g)*h=f*(g*h) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f f' hf hf'=>simp only [add_mul,hf,hf']
  | single m a=>
    induction g using Finsupp.induction_linear with
    | zero=>simp
    | add g g' hg hg'=>simp only [mul_add,add_mul,hg,hg']
    | single n b=>
      induction h using Finsupp.induction_linear with
      | zero=>simp
       | add h h' hh hh'=>simp only [mul_add,hh,hh']
      | single p c=>
        change (monomial v Ω α m a*monomial v Ω α n b)*monomial v Ω α p c=
          monomial v Ω α m a*(monomial v Ω α n b*monomial v Ω α p c)
        simp only [monomial_mul,map_add,AddMonoidHom.add_apply,add_assoc]
        congr 1
        simp only [zpow_add,Units.val_mul,map_mul,twist_constant,twist_add]
        ring
@[simp] lemma one_mul (f : FiberTorus v Ω α) : (1 : FiberTorus v Ω α)*f=f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>rw [mul_add,hf,hg]
  | single m a=>
    change monomial v Ω α 0 1*monomial v Ω α m a=monomial v Ω α m a
    simp only [monomial_mul,map_zero,AddMonoidHom.zero_apply,zero_add,
      _root_.one_mul,zpow_zero,Units.val_one,map_one,_root_.mul_one,twist_zero]
@[simp] lemma mul_one (f : FiberTorus v Ω α) : f*(1 : FiberTorus v Ω α)=f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>rw [add_mul,hf,hg]
  | single m a=>
    change monomial v Ω α m a*monomial v Ω α 0 1=monomial v Ω α m a
    simp only [monomial_mul,map_zero,add_zero,_root_.mul_one,zpow_zero,Units.val_one,map_one]
instance instRing : Ring (FiberTorus v Ω α) :=
  Ring.ofMinimalAxioms _root_.add_assoc _root_.zero_add _root_.neg_add_cancel
    (mul_assoc v Ω α) (one_mul v Ω α) (mul_one v Ω α) (mul_add v Ω α) (add_mul v Ω α)
end FiberTorus
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
def off : M →+ k.ker where
  toFun m:=⟨m-(k m) • p,by simp [map_sub,map_zsmul,hp]⟩
  map_zero':=by ext; simp
  map_add' m n:=by ext; simp [map_add,add_smul]; abel
@[simp] lemma off_val (m : M) : (off k p hp m : M)=m-k m • p := rfl
lemma split_sum (m : M) : k m • p+(off k p hp m : M)=m := by rw [off_val]; abel
@[simp] lemma off_p : off k p hp p=0 := by ext; simp [hp]
@[simp] lemma off_complement (m : k.ker) : off k p hp m=m := by
  ext
  have hm : k m=0:=m.property
  simp [hm]
def complementAlpha (Ω : M →+ M →+ ℤ) : k.ker →+ ℤ := (Ω p).comp k.ker.subtype
def complementOmega (Ω : M →+ M →+ ℤ) : k.ker →+ k.ker →+ ℤ where
  toFun m:=(Ω m).comp k.ker.subtype
  map_zero':=by ext; simp
  map_add' m n:=by ext; simp
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
include hΩ in
lemma split_pairing (m n : M) : Ω m n=
    k m*complementAlpha k p Ω (off k p hp n)-
      k n*complementAlpha k p Ω (off k p hp m)+
      complementOmega k Ω (off k p hp m) (off k p hp n) := by
  have hs (a b : M) : Ω a b= -Ω b a := by
    have H:=hΩ (a+b)
    simp only [map_add,AddMonoidHom.add_apply,hΩ] at H
    omega
  change Ω m n=k m*Ω p (off k p hp n)-k n*Ω p (off k p hp m)+
    Ω (off k p hp m : M) (off k p hp n : M)
  conv_lhs=>rw [←split_sum k p hp m,←split_sum k p hp n]
  simp only [map_add,AddMonoidHom.add_apply,map_zsmul,AddMonoidHom.zsmul_apply,hΩ,
    smul_eq_mul]
  rw [hs (off k p hp m : M) p]
  ring

def centeredScalar (v : Kˣ) (n a : ℤ) : RatFunc K :=
  RatFunc.C (↑(v^(-n*a)):K)*RatFunc.X^n
lemma centeredScalar_mul (v : Kˣ) (n l a b c : ℤ) :
    centeredScalar v n a*scale (v^(-2*a)) (centeredScalar v l b)*
      RatFunc.C (↑(v^c):K)=
    RatFunc.C (↑(v^(n*b-l*a+c)):K)*centeredScalar v (n+l) (a+b) := by
  have hv : (v:K)≠0:=Units.ne_zero v
  have hz : (RatFunc.X : RatFunc K)≠0:=RatFunc.X_ne_zero
  simp only [centeredScalar,map_mul,scale_constant,map_zpow₀,scale_X,mul_zpow]
  simp only [←map_zpow₀,←Units.val_zpow_eq_zpow_val,←zpow_mul]
  have hleft :
      RatFunc.C (↑(v^(-n*a)):K)*RatFunc.X^n*
        (RatFunc.C (↑(v^(-l*b)):K)*(RatFunc.C (↑(v^(-2*a*l)):K)*RatFunc.X^l))*
        RatFunc.C (↑(v^c):K)=
      RatFunc.C (↑(v^(-n*a)):K)*RatFunc.C (↑(v^(-l*b)):K)*
        RatFunc.C (↑(v^(-2*a*l)):K)*RatFunc.C (↑(v^c):K)*
        (RatFunc.X^n*RatFunc.X^l) := by ring
  rw [hleft,←map_mul,←map_mul,←map_mul,←Units.val_mul,←Units.val_mul,←Units.val_mul,
    ←zpow_add,←zpow_add,←zpow_add,←zpow_add₀ hz]
  rw [←mul_assoc,←map_mul,←Units.val_mul,←zpow_add]
  congr 3
  ring_nf
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutationRootMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

def mutatedCoefficientMap (α : I → ℤ) : (I → ℤ) →+ (I → ℤ) where
  toFun d:=fun i=>if i=pc then -d pc+∑j∈Finset.univ.erase pc,max 0 (-α j)*d j else d i
  map_zero':=by ext i; simp
  map_add':=by
    intro a b; ext i
    by_cases hi : i=pc
    · subst i; simp only [ite_true, if_true,Pi.add_apply,neg_add,mul_add,Finset.sum_add_distrib] <;> ring
    · simp [hi]

@[simp] lemma mutatedCoefficientMap_off (α : I → ℤ) (d : I → ℤ) (i : I) (hi : i≠pc) :
    mutatedCoefficientMap pc α d i=d i := by simp [mutatedCoefficientMap,hi]
@[simp] lemma mutatedCoefficientMap_at (α : I → ℤ) (d : I → ℤ) :
    mutatedCoefficientMap pc α d pc= -d pc+∑j∈Finset.univ.erase pc,max 0 (-α j)*d j := by
  simp [mutatedCoefficientMap]

lemma mutatedCoefficientMap_involutive (α : I → ℤ) :
    Function.Involutive (mutatedCoefficientMap pc α) := by
  intro d; ext i
  by_cases hi : i=pc
  · subst i
    rw [mutatedCoefficientMap_at,mutatedCoefficientMap_at]
    have HH : (∑j∈Finset.univ.erase pc,max 0 (-α j)*mutatedCoefficientMap pc α d j)=
        ∑j∈Finset.univ.erase pc,max 0 (-α j)*d j:=by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mutatedCoefficientMap_off pc α d j (Finset.mem_erase.mp hj).1]
    rw [HH]; ring
  · rw [mutatedCoefficientMap_off pc α _ i hi,mutatedCoefficientMap_off pc α _ i hi]

def mutatedRoots : (I → ℤ) →+ M := C.comp (mutatedCoefficientMap pc (mutationPairing Ω C pc))
def mutatedCoordinates : M →+ (I → ℤ) :=
  (mutatedCoefficientMap pc (mutationPairing Ω C pc)).comp coord

include hcoord in
lemma mutatedCoordinates_retraction (d : I → ℤ) :
    mutatedCoordinates Ω C coord pc (mutatedRoots Ω C pc d)=d := by
  change mutatedCoefficientMap pc (mutationPairing Ω C pc)
    (coord (C (mutatedCoefficientMap pc (mutationPairing Ω C pc) d)))=d
  rw [hcoord]
  exact mutatedCoefficientMap_involutive pc _ d

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteElementaryAdjoint
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WallUnits
open PowerSeries
noncomputable section
variable {R : Type*} [CommRing R]
def DegreeBound (d : ℕ) (f : PowerSeries R) : Prop := ∀ n,d<n → coeff n f=0
end
end ElementaryPositivity.WallUnits

end
section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
lemma inverse_inverse (F : PowerSeries A) (hF : constantCoeff F=1) :
    invOfUnit (invOfUnit F 1) 1=F := by
  have hI : constantCoeff (invOfUnit F 1)=1:=by simp
  calc
    _=invOfUnit (invOfUnit F 1) 1*((invOfUnit F 1)*F):=by rw [invOfUnit_mul F 1 hF,mul_one]
    _=(invOfUnit (invOfUnit F 1) 1*(invOfUnit F 1))*F:=by rw [mul_assoc]
    _=F:=by rw [invOfUnit_mul _ 1 hI,one_mul]
lemma adjoint_inverse (F X : PowerSeries A) (hF : constantCoeff F=1) :
    adjoint (invOfUnit F 1) X=invOfUnit F 1*X*F := by rw [adjoint,inverse_inverse F hF]
end
end ElementaryPositivity.PowerSeriesAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_SimpleBinomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
def normalizedSimple (p : M) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  raySeries LaurentRay.vUnit Ω p
    (elementary (HahnSeries.single (2:ℤ) (1:ℚ)) (HahnSeries.single (1:ℤ) (1:ℚ)))
omit [Fintype I] in
lemma simpleDatum_value (pc : I) : (simpleDatum C pc).value Ω=normalizedSimple Ω (simpleRoot C pc) := by
  apply PowerSeries.ext
  intro n
  rw [WallUnitDatum.value,coeff_weightedRay]
  simp only [simpleDatum,one_dvd,Nat.div_one,UnitSelections.indexedUnit,↓reduceIte,
    LaurentRay.elementary_atInfinity,neg_neg,coeff_raySeries,normalizedSimple]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_AdjointExpansion
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries RootTruncation
noncomputable section
variable {A : Type*} [Ring A]
lemma cut_eq_monomial_sum (X : PowerSeries A) (N : ℕ) :
    cut N X=∑j∈Finset.range (N+1),monomial j (coeff j X) := by
  classical
  ext n
  rw [coeff_cut,map_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range,Nat.lt_succ_iff]
lemma adjoint_sum {J : Type*} (F : PowerSeries A) (s : Finset J) (X : J → PowerSeries A) :
    adjoint F (∑j∈s,X j)=∑j∈s,adjoint F (X j) := by
  simp only [adjoint,Finset.mul_sum,Finset.sum_mul]
lemma monomial_C_X (j : ℕ) (a : A) : monomial j a=PowerSeries.C a*PowerSeries.X^j := by
  ext n
  rw [coeff_monomial,coeff_C_mul_X_pow]
lemma adjoint_X_pow (F X : PowerSeries A) (j : ℕ) :
    adjoint F (X*PowerSeries.X^j)=adjoint F X*PowerSeries.X^j := by
  simp only [adjoint,mul_assoc]
  rw [X_pow_mul]
lemma adjoint_monomial (F : PowerSeries A) (j : ℕ) (a : A) :
    adjoint F (monomial j a)=adjoint F (PowerSeries.C a)*PowerSeries.X^j := by
  rw [monomial_C_X,adjoint_X_pow]
lemma coeff_adjoint_expansion (F X : PowerSeries A) (N : ℕ) :
    coeff N (adjoint F X)=∑j∈Finset.range (N+1),coeff (N-j) (adjoint F (PowerSeries.C (coeff j X))) := by
  classical
  rw [adjoint_coeff_congr F F X (cut N X) N (fun _ _=>rfl)
    (fun j hj=>(coeff_cut_of_le X hj).symm),cut_eq_monomial_sum,adjoint_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [adjoint_monomial,coeff_mul_X_pow',ite_eq_left (by have H:=Finset.mem_range.mp hj; omega)]
end
end ElementaryPositivity.PowerSeriesAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TorusAdjointExpansion
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ)
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddCommGroupTorusLaurentSeriesRatVUnit_rf9cb96_1 : AddCommGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommGroup
local instance instAddGroupTorusLaurentSeriesRatVUnit_1_rf9cb96_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance instSubTorusLaurentSeriesRatVUnit_rf9cb96_1 : Sub (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toSub
lemma torus_ring_eval_sum {J : Type*} (s : Finset J) (f : J → Torus LaurentRay.vUnit Ω) (r : M) :
    (∑j∈s,f j) r=∑j∈s,f j r := by
  classical
  induction s using Finset.induction_on with
  | empty=>rfl
  | @insert j s hj ih=>
    rw [Finset.sum_insert hj,Finset.sum_insert hj]
    change f j r+(∑j∈s,f j) r=_
    rw [ih]
lemma torus_eq_sum_X (f : Torus LaurentRay.vUnit Ω) :
    f=∑m∈f.support,f m • Torus.X LaurentRay.vUnit Ω m := by
  classical
  change f=∑m∈f.support,f m • Finsupp.single m 1
  simpa only [Finsupp.smul_single,smul_eq_mul,mul_one,Finsupp.sum] using (Finsupp.sum_single f).symm
lemma adjoint_torus_expansion (F : PowerSeries (Torus LaurentRay.vUnit Ω))
    (f : Torus LaurentRay.vUnit Ω) (N : ℕ) (r : M) :
    coeff N (adjoint F (PowerSeries.C f)) r=
      ∑m∈f.support,f m*(coeff N (adjoint F (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)))) r := by
  classical
  conv_lhs => rw [torus_eq_sum_X Ω f]
  rw [map_sum]
  change (coeff N (adjoint F (∑m∈f.support,(PowerSeries.C (f m • Torus.X LaurentRay.vUnit Ω m) : PowerSeries (Torus LaurentRay.vUnit Ω))))) r=_
  simp only [adjoint,Finset.mul_sum,Finset.sum_mul,map_sum]
  change (∑m∈f.support,(coeff N (F*PowerSeries.C (f m • Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1) : Torus LaurentRay.vUnit Ω)) r=_
  rw [torus_ring_eval_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have HC : PowerSeries.C (f m • Torus.X LaurentRay.vUnit Ω m)=
      f m • (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m) : PowerSeries (Torus LaurentRay.vUnit Ω)) := by
    ext n
    rw [coeff_C,coeff_smul,coeff_C]
    split_ifs <;> simp
  rw [HC,mul_smul_comm,smul_mul_assoc,coeff_smul]
  rfl

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SimpleAdjointFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

def sideSign (pos : Bool) : ℤ := if pos then 1 else -1
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_PureFaceProjection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance pureFaceProjectionAddCommGroup_rf9cb96_1 : AddCommGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommGroup
local instance pureFaceProjectionAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid

def pureFaceCovector : M →+ ℝ := -(Int.castAddHom ℝ).comp (nonpDegree coord pc)
lemma pureFaceCovector_apply (m : M) : pureFaceCovector coord pc m= -(nonpDegree coord pc m : ℝ) := rfl
lemma pureFaceCovector_zero_iff (m : M) : pureFaceCovector coord pc m=0 ↔ nonpDegree coord pc m=0 := by
  rw [pureFaceCovector_apply,neg_eq_zero,Int.cast_eq_zero]

local instance pureFaceProjectionAddGroup_rf9cb96_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureFaceProjectionSub_rf9cb96_1 : Sub (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toSub
def pureFaceSeries (F : PowerSeries (Torus LaurentRay.vUnit Ω)) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  PowerSeries.mk (fun n=>zeroProject LaurentRay.vUnit Ω (pureFaceCovector coord pc) (coeff n F))
lemma coeff_pureFaceSeries (F : PowerSeries (Torus LaurentRay.vUnit Ω)) (n : ℕ) :
    coeff n (pureFaceSeries Ω coord pc F)=zeroProject LaurentRay.vUnit Ω (pureFaceCovector coord pc) (coeff n F) := coeff_mk _ _
lemma pureFaceSeries_apply (F : PowerSeries (Torus LaurentRay.vUnit Ω)) (n : ℕ) (m : M) :
    coeff n (pureFaceSeries Ω coord pc F) m=if nonpDegree coord pc m=0 then coeff n F m else 0 := by
  rw [coeff_pureFaceSeries]
  change (coeff n F).filter (fun m=>pureFaceCovector coord pc m=0) m=_
  simp only [Finsupp.filter_apply,pureFaceCovector_zero_iff]
include hcoord in
lemma rootGrade_nonpositive_face (n : ℕ) (x : Torus LaurentRay.vUnit Ω)
    (hx : x∈rootGrade LaurentRay.vUnit Ω C n) :
    x∈supportedSubring LaurentRay.vUnit Ω (nonpositiveCone (pureFaceCovector coord pc)) := by
  intro m hm
  by_contra hh
  have hroot : HasRootDegree C n m:=by by_contra hk; exact hh (hx m hk)
  have hpos:=nonpDegree_root_nonneg C coord hcoord pc hroot
  exact hm (show pureFaceCovector coord pc m≤0 by rw [pureFaceCovector_apply]; exact neg_nonpos.mpr (by exact_mod_cast hpos))
include hcoord in
lemma pureFaceSeries_mul (F G : PowerSeries (Torus LaurentRay.vUnit Ω))
    (hF : ∀n,coeff n F∈rootGrade LaurentRay.vUnit Ω C n)
    (hG : ∀n,coeff n G∈rootGrade LaurentRay.vUnit Ω C n) :
    pureFaceSeries Ω coord pc (F*G)=pureFaceSeries Ω coord pc F*pureFaceSeries Ω coord pc G := by
  apply PowerSeries.ext
  intro n
  rw [coeff_pureFaceSeries,coeff_mul,coeff_mul,map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [coeff_pureFaceSeries,coeff_pureFaceSeries]
  exact zeroProject_mul_nonpositive _ _ _ _ _
    (rootGrade_nonpositive_face Ω C coord hcoord pc _ _ (hF _))
    (rootGrade_nonpositive_face Ω C coord hcoord pc _ _ (hG _))
lemma pureFaceSeries_graded (F : PowerSeries (Torus LaurentRay.vUnit Ω))
    (hF : ∀n,coeff n F∈rootGrade LaurentRay.vUnit Ω C n) :
    ∀n,coeff n (pureFaceSeries Ω coord pc F)∈rootGrade LaurentRay.vUnit Ω C n := by
  intro n m hm
  rw [pureFaceSeries_apply]
  split_ifs <;> simp only [hF n m hm]
def pureFace (F : CompletedPositive LaurentRay.vUnit Ω C) : CompletedPositive LaurentRay.vUnit Ω C :=
  ⟨pureFaceSeries Ω coord pc F.val,by
    constructor
    · rw [←coeff_zero_eq_constantCoeff_apply,coeff_pureFaceSeries,coeff_zero_eq_constantCoeff_apply,F.property.1]
      exact zeroProject_one _ _ _
    · exact pureFaceSeries_graded Ω C coord pc F.val F.property.2⟩
include hcoord in
lemma pureFaceSeries_chart_sides (h : M →+ ℝ) (hp : h (simpleRoot C pc)=0)
    (F : CompletedPositive LaurentRay.vUnit Ω C) :
    (pureFace Ω C coord pc (chartPositive LaurentRay.vUnit Ω C h F)).val=1 ∧
    (pureFace Ω C coord pc (chartNegative LaurentRay.vUnit Ω C h F)).val=1 := by
  have HS:=chart_three_support LaurentRay.vUnit Ω C h F
  constructor
  all_goals
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simpa only [coeff_zero_eq_constantCoeff_apply,map_one] using (pureFace _ _ _ _ _).property.1
    | succ n =>
      rw [coeff_one,ite_eq_right (by omega)]
      apply Finsupp.ext
      intro m
      change coeff (n+1) (pureFaceSeries Ω coord pc _) m=0
      rw [pureFaceSeries_apply]
      split_ifs with hz
      · by_contra hh
        have hm : HasRootDegree C (n+1) m:=by
          by_contra hn
          first | exact hh ((chartPositive _ _ _ _ F).property.2 _ m hn) | exact hh ((chartNegative _ _ _ _ F).property.2 _ m hn)
        have hm0 : h m=0:=by rw [nonp_zero_root C coord hcoord pc hm hz,map_nsmul,hp,nsmul_zero]
        first
        | have he:=HS.1 n m hh; rw [hm0] at he; exact lt_irrefl _ he
        | have he:=HS.2.2 n m hh; rw [hm0] at he; exact lt_irrefl _ he
      · rfl
include hcoord in
lemma pureFace_chartZero (h : M →+ ℝ) (hp : h (simpleRoot C pc)=0)
    (F : CompletedPositive LaurentRay.vUnit Ω C) :
    pureFace Ω C coord pc (chartZero LaurentRay.vUnit Ω C h F)=pureFace Ω C coord pc F := by
  apply Subtype.ext
  have H:=congrArg (pureFaceSeries Ω coord pc) (chart_three_factorization LaurentRay.vUnit Ω C h F)
  rw [pureFaceSeries_mul Ω C coord hcoord pc _ _
    (FormalLog.graded_multiply _ (rootGrade_mul LaurentRay.vUnit Ω C) _ _
      (chartPositive _ _ _ _ F).property.2 (chartZero _ _ _ _ F).property.2)
    (chartNegative _ _ _ _ F).property.2,
    pureFaceSeries_mul Ω C coord hcoord pc _ _
      (chartPositive _ _ _ _ F).property.2 (chartZero _ _ _ _ F).property.2] at H
  have HH:=pureFaceSeries_chart_sides Ω C coord hcoord pc h hp F
  change (pureFace _ _ _ _ (chartPositive _ _ _ _ F)).val*
    (pureFace _ _ _ _ (chartZero _ _ _ _ F)).val*
    (pureFace _ _ _ _ (chartNegative _ _ _ _ F)).val=(pureFace _ _ _ _ F).val at H
  simpa only [HH.1,HH.2,one_mul,mul_one] using H
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SimpleIncomingElement
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
omit [Fintype I] in
include hcoord in
lemma simpleRoot_ray_iff (i : I) : OnPositiveRay (simpleRoot C pc) (simpleRoot C i) ↔ i=pc := by
  constructor
  · rintro ⟨a,b,ha,hb,he⟩
    by_contra hi
    have HH:=congrArg (fun m=>coord m pc) he
    simp only [map_nsmul,Pi.smul_apply,simpleRoot_coordinates C coord hcoord] at HH
    simp only [Pi.single_eq_of_ne (Ne.symm hi),Pi.single_eq_same,nsmul_eq_mul,mul_one] at HH
    omega
  · rintro rfl
    exact ⟨1,1,by omega,by omega,rfl⟩
include hcoord in
lemma literalIncoming_simple :
    literalIncomingRay Ω (simpleIncomingList C) (simpleRoot C pc)=normalizedSimple Ω (simpleRoot C pc) := by
  classical
  unfold literalIncomingRay simpleIncomingList
  rw [List.filter_map]
  have hf : (Finset.univ.toList : List I).filter
      ((fun u : WallUnitDatum M=>decide (OnPositiveRay (simpleRoot C pc) u.root)) ∘ simpleDatum C)=[pc] := by
    apply List.perm_singleton.mp
    apply (List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).filter _) (by simp)).mpr
    intro i
    simp only [List.mem_filter,Finset.mem_toList,Finset.mem_univ,true_and,Function.comp_apply,
      simpleDatum,List.mem_singleton]
    constructor
    · intro hh; exact (simpleRoot_ray_iff C coord hcoord pc i).mp (of_decide_eq_true hh)
    · intro hh; exact decide_eq_true ((simpleRoot_ray_iff C coord hcoord pc i).mpr hh)
  rw [hf,List.map_singleton,List.map_singleton,List.prod_singleton,simpleDatum_value]
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

lemma pureFaceSeries_eq_through (F : PowerSeries (Torus LaurentRay.vUnit Ω)) (N : ℕ)
    (hF : ∀j≤N,∀m,coeff j F m≠0 → nonpDegree coord pc m=0) :
    ∀j≤N,coeff j (pureFaceSeries Ω coord pc F)=coeff j F := by
  intro j hj
  apply Finsupp.ext
  intro m
  rw [pureFaceSeries_apply]
  split_ifs with hh
  · rfl
  · exact (not_ne_iff.mp (fun he=>hh (hF j hj m he))).symm

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
def completedMul (F G : CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  ⟨F.val*G.val,by simp only [map_mul,F.property.1,G.property.1,mul_one],
    FormalLog.graded_multiply _ (rootGrade_mul v Ω C) _ _ F.property.2 G.property.2⟩
def completedConjugate (F G : CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  completedMul v Ω C (completedMul v Ω C F G) (completedInverse v Ω C F)
lemma chartZero_right_negative (h : M →+ ℝ) (G H : CompletedPositive v Ω C) (N : ℕ)
    (hH : ∀j,j+1≤N → ∀m,coeff (j+1) H.val m≠0 → h m<0) :
    ∀j≤N,coeff j (chartZero v Ω C h (completedMul v Ω C G H)).val=
      coeff j (chartZero v Ω C h G).val := by
  have HG:=chart_three_support v Ω C h G
  have HU:=chart_three_truncated_unique v Ω C h (completedMul v Ω C G H)
    (chartPositive v Ω C h G).val (chartZero v Ω C h G).val
    ((chartNegative v Ω C h G).val*H.val) N
    (chartPositive v Ω C h G).property.1 (chartZero v Ω C h G).property.1
    (by simp only [map_mul,(chartNegative v Ω C h G).property.1,H.property.1,mul_one])
    (by change _*(_*H.val)=G.val*H.val; rw [←mul_assoc,chart_three_factorization])
    (fun j _=>HG.1 j) (fun j _=>HG.2.1 j) (by
      intro j hj m hm
      by_contra hh
      exact hm (strict_mul_through v Ω (fun m=>h m<0)
        (fun a b ha hb=>by simpa only [map_add] using add_neg ha hb)
        (chartNegative v Ω C h G).val H.val N
        (chartNegative v Ω C h G).property.1 H.property.1
        (fun j hj m hm=>by by_contra hv; exact hm (HG.2.2 j m hv))
        (fun j hj m hm=>by by_contra hv; exact hm (hH j hj m hv)) j hj m hh))
  exact fun j hj=>(HU j hj).2.1.symm
lemma chartZero_left_positive (h : M →+ ℝ) (H G : CompletedPositive v Ω C) (N : ℕ)
    (hH : ∀j,j+1≤N → ∀m,coeff (j+1) H.val m≠0 → 0<h m) :
    ∀j≤N,coeff j (chartZero v Ω C h (completedMul v Ω C H G)).val=
      coeff j (chartZero v Ω C h G).val := by
  have HG:=chart_three_support v Ω C h G
  have HU:=chart_three_truncated_unique v Ω C h (completedMul v Ω C H G)
    (H.val*(chartPositive v Ω C h G).val) (chartZero v Ω C h G).val
    (chartNegative v Ω C h G).val N
    (by simp only [map_mul,H.property.1,(chartPositive v Ω C h G).property.1,mul_one])
    (chartZero v Ω C h G).property.1 (chartNegative v Ω C h G).property.1
    (by change _*_*_=H.val*G.val; rw [mul_assoc,mul_assoc,←mul_assoc (chartPositive _ _ _ _ _).val,
      chart_three_factorization])
    (by
      intro j hj m hm
      by_contra hh
      exact hm (strict_mul_through v Ω (fun m=>0<h m)
        (fun a b ha hb=>by simpa only [map_add] using add_pos ha hb)
        H.val (chartPositive v Ω C h G).val N
        H.property.1 (chartPositive v Ω C h G).property.1
        (fun j hj m hm=>by by_contra hv; exact hm (hH j hj m hv))
        (fun j hj m hm=>by by_contra hv; exact hm (HG.1 j m hv)) j hj m hh))
    (fun j _=>HG.2.1 j) (fun j _=>HG.2.2 j)
  exact fun j hj=>(HU j hj).2.1.symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_PureProductSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

lemma ordered_filter_partition {A : Type*} (P : A → Prop) [DecidablePred P] (l : List A)
    (hl : l.Pairwise (fun a b=>P b → P a)) :
    l.filter (fun a=>decide (P a)) ++ l.filter (fun a=>decide (¬P a))=l := by
  induction l with
  | nil=>rfl
  | cons a l ih=>
    have HH:=List.pairwise_cons.mp hl
    by_cases ha : P a
    · simpa [List.filter_cons,ha] using congrArg (List.cons a) (ih HH.2)
    · have hz : l.filter (fun a=>decide (P a))=[]:=by
        apply List.filter_eq_nil_iff.mpr
        intro b hb
        simpa using (fun hp=>ha (HH.1 b hb hp) : ¬ P b)
      have IH:=ih HH.2
      rw [hz,List.nil_append] at IH
      simp [ha,hz]
      intro b hb hp
      exact ha (HH.1 b hb hp)
lemma alternating_int_swap (hΩ : ∀m,Ω m m=0) (a b : M) : Ω a b= -Ω b a := by
  have H:=hΩ (a+b)
  simp only [map_add,AddMonoidHom.add_apply,hΩ,zero_add,add_zero] at H
  omega
include hcoord in
lemma ordered_pure_partition (hΩ : ∀m,Ω m m=0) (pos : Bool) (l : List M)
    (hl : l.Pairwise (fun a b=>0<Ω a b))
    (hroot : ∀q∈l,∃d,0<d ∧ HasRootDegree C d q)
    (htrend : ∀q∈l,0≤ sideSign pos*Ω (simpleRoot C pc) q) :
    (if pos then
      l.filter (fun q=>decide (nonpDegree coord pc q=0)) ++
        l.filter (fun q=>decide (nonpDegree coord pc q≠0))
     else
      l.filter (fun q=>decide (nonpDegree coord pc q≠0)) ++
        l.filter (fun q=>decide (nonpDegree coord pc q=0)))=l := by
  cases pos
  · simp only [Bool.false_eq_true,ite_false, if_false]
    suffices H : l.Pairwise (fun a b => nonpDegree coord pc b ≠ 0 →
        nonpDegree coord pc a ≠ 0) from by
      simpa only [not_not] using ordered_filter_partition (fun q=>nonpDegree coord pc q≠0) l H
    apply hl.imp_of_mem
    intro a b ha hb hab hnb hpa
    obtain ⟨d,hd,hr⟩:=hroot a ha
    rw [nonp_zero_root C coord hcoord pc hr hpa,map_nsmul] at hab
    have HH:=htrend b hb
    simp only [sideSign,Bool.false_eq_true,ite_false, if_false,neg_one_mul] at HH
    have hdZ : 0<(d:ℤ):=by exact_mod_cast hd
    change 0<(d:ℤ)*Ω (simpleRoot C pc) b at hab
    nlinarith
  · simp only [ite_true, if_true]
    apply ordered_filter_partition (fun q=>nonpDegree coord pc q=0) l
    apply hl.imp_of_mem
    intro a b ha hb hab hpb
    obtain ⟨d,hd,hr⟩:=hroot b hb
    rw [nonp_zero_root C coord hcoord pc hr hpb,map_nsmul] at hab
    have HH:=htrend a ha
    simp only [sideSign,ite_true, if_true,one_mul] at HH
    rw [alternating_int_swap Ω hΩ a (simpleRoot C pc)] at hab
    have hdZ : 0<(d:ℤ):=by exact_mod_cast hd
    change 0<(d:ℤ)*(-Ω (simpleRoot C pc) a) at hab
    exact (by nlinarith : False).elim

lemma ray_nonp_zero {q m : M} (hq : nonpDegree coord pc q=0) (hm : OnPositiveRay q m) :
    nonpDegree coord pc m=0 := by
  obtain ⟨a,b,ha,hb,he⟩:=hm
  have H:=congrArg (nonpDegree coord pc) he
  rw [map_nsmul,map_nsmul,hq,nsmul_zero,nsmul_eq_mul] at H
  exact (mul_eq_zero.mp H).resolve_left (by exact_mod_cast Nat.ne_of_gt ha)
lemma ray_nonp_pos {q m : M} (hq : 0<nonpDegree coord pc q) (hm : OnPositiveRay q m) :
    0<nonpDegree coord pc m := by
  obtain ⟨a,b,ha,hb,he⟩:=hm
  have H:=congrArg (nonpDegree coord pc) he
  simp only [map_nsmul,nsmul_eq_mul] at H
  have haZ : 0<(a:ℤ):=by exact_mod_cast ha
  have hbZ : 0<(b:ℤ):=by exact_mod_cast hb
  nlinarith
lemma pureFace_of_strict_positive (F : CompletedPositive LaurentRay.vUnit Ω C)
    (hF : ∀j m,coeff (j+1) F.val m≠0 → 0<nonpDegree coord pc m) :
    (pureFace Ω C coord pc F).val=1 := by
  apply PowerSeries.ext
  intro j
  cases j with
  | zero=>simpa only [coeff_zero_eq_constantCoeff_apply,map_one] using (pureFace _ _ _ _ F).property.1
  | succ j=>
    rw [coeff_one,ite_eq_right (by omega)]
    apply Finsupp.ext
    intro m
    change coeff (j+1) (pureFaceSeries Ω coord pc F.val) m=0
    rw [pureFaceSeries_apply]
    split_ifs with hh
    · by_contra hn
      have HG:=hF j m hn
      omega
    · rfl
lemma pureFace_of_strict_zero (F : CompletedPositive LaurentRay.vUnit Ω C)
    (hF : ∀j m,coeff (j+1) F.val m≠0 → nonpDegree coord pc m=0) :
    (pureFace Ω C coord pc F).val=F.val := by
  apply PowerSeries.ext
  intro j
  apply pureFaceSeries_eq_through Ω coord pc F.val j ?_ j le_rfl
  intro k hk m hm
  cases k with
  | zero=>
    rw [coeff_zero_eq_constantCoeff_apply,F.property.1] at hm
    have hm0 : m=0:=by by_contra hh; exact hm (Finsupp.single_eq_of_ne hh)
    rw [hm0,map_zero]
  | succ k=>exact hF k m hm

lemma pureFace_list_nonpure (_hcoord : ∀d,coord (C d)=d) (pc : I)
    (l : List M) (F : M → CompletedPositive LaurentRay.vUnit Ω C)
    (hl : ∀q∈l,0<nonpDegree coord pc q)
    (hF : ∀q∈l,∀j m,coeff (j+1) (F q).val m≠0 → OnPositiveRay q m) :
    (pureFace Ω C coord pc (completedListProduct LaurentRay.vUnit Ω C l F)).val=1 := by
  apply pureFace_of_strict_positive Ω C coord pc
  intro j m hm
  by_contra hn
  apply hm
  apply strict_list_product_through LaurentRay.vUnit Ω C l F
    (fun m=>0<nonpDegree coord pc m)
    (fun a b ha hb=>by simpa only [map_add] using add_pos ha hb) (j+1) ?_ j le_rfl m hn
  intro q hq k hk m hm
  by_contra hv
  exact hm (ray_nonp_pos coord pc (hl q hq) (hF q hq k m hv))
lemma pureFace_list_pure (_hcoord : ∀d,coord (C d)=d) (pc : I)
    (l : List M) (F : M → CompletedPositive LaurentRay.vUnit Ω C)
    (hl : ∀q∈l,nonpDegree coord pc q=0)
    (hF : ∀q∈l,∀j m,coeff (j+1) (F q).val m≠0 → OnPositiveRay q m) :
    (pureFace Ω C coord pc (completedListProduct LaurentRay.vUnit Ω C l F)).val=
      (completedListProduct LaurentRay.vUnit Ω C l F).val := by
  apply pureFace_of_strict_zero Ω C coord pc
  intro j m hm
  by_contra hn
  apply hm
  apply strict_list_product_through LaurentRay.vUnit Ω C l F
    (fun m=>nonpDegree coord pc m=0)
    (fun a b ha hb=>by simp only [map_add,ha,hb,add_zero]) (j+1) ?_ j le_rfl m hn
  intro q hq k hk m hm
  by_contra hv
  exact hm (ray_nonp_zero coord pc (hl q hq) (hF q hq k m hv))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PureCutFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
include hcoord in
lemma ordered_pure_factor_through (hΩ : ∀m,Ω m m=0) (pos : Bool) (l : List M)
    (K : M → CompletedPositive LaurentRay.vUnit Ω C)
    (hl : l.Pairwise (fun a b=>0<Ω a b))
    (hroot : ∀q∈l,∃d,0<d ∧ HasRootDegree C d q)
    (htrend : ∀q∈l,0≤ sideSign pos*Ω (simpleRoot C pc) q)
    (hRay : ∀q∈l,∀j m,coeff (j+1) (K q).val m≠0 → OnPositiveRay q m)
    (F D : CompletedPositive LaurentRay.vUnit Ω C) (N : ℕ)
    (hprod : ∀j≤N,coeff j F.val=coeff j (completedListProduct LaurentRay.vUnit Ω C l K).val)
    (hface : ∀j≤N,coeff j (pureFace Ω C coord pc F).val=coeff j D.val) :
    let A:=completedListProduct LaurentRay.vUnit Ω C
      (l.filter (fun q=>decide (nonpDegree coord pc q≠0))) K
    ∀j≤N,coeff j F.val=coeff j (if pos then D.val*A.val else A.val*D.val) := by
  classical
  let lP:=l.filter (fun q=>decide (nonpDegree coord pc q=0))
  let lA:=l.filter (fun q=>decide (nonpDegree coord pc q≠0))
  let P:=completedListProduct LaurentRay.vUnit Ω C lP K
  let A:=completedListProduct LaurentRay.vUnit Ω C lA K
  let W:=completedListProduct LaurentRay.vUnit Ω C l K
  have hPW : W.val=if pos then P.val*A.val else A.val*P.val:=by
    have H:=congrArg (fun L : List M=>(L.map (fun q=>(K q).val)).prod)
      (ordered_pure_partition Ω C coord hcoord pc hΩ pos l hl hroot htrend)
    cases pos <;> simpa only [W,P,A,lP,lA,completedListProduct,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,List.map_append,List.prod_append] using H.symm
  have hPA : (pureFace Ω C coord pc A).val=1:=by
    apply pureFace_list_nonpure Ω C coord hcoord pc lA K
    · intro q hq
      have H:=List.mem_filter.mp hq
      have hn : nonpDegree coord pc q≠0:=of_decide_eq_true H.2
      obtain ⟨d,hd,hr⟩:=hroot q H.1
      have hp:=nonpDegree_root_nonneg C coord hcoord pc hr
      omega
    · intro q hq
      exact hRay q (List.mem_filter.mp hq).1
  have hPP : (pureFace Ω C coord pc P).val=P.val:=by
    apply pureFace_list_pure Ω C coord hcoord pc lP K
    · intro q hq; exact of_decide_eq_true (List.mem_filter.mp hq).2
    · intro q hq; exact hRay q (List.mem_filter.mp hq).1
  have hWP : (pureFace Ω C coord pc W).val=P.val:=by
    change pureFaceSeries Ω coord pc W.val=P.val
    rw [hPW]
    cases pos <;> simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
    · rw [pureFaceSeries_mul Ω C coord hcoord pc _ _ A.property.2 P.property.2]
      change (pureFace _ _ _ _ A).val*(pureFace _ _ _ _ P).val=P.val
      rw [hPA,hPP,one_mul]
    · rw [pureFaceSeries_mul Ω C coord hcoord pc _ _ P.property.2 A.property.2]
      change (pureFace _ _ _ _ P).val*(pureFace _ _ _ _ A).val=P.val
      rw [hPA,hPP,mul_one]
  have hPD : ∀j≤N,coeff j P.val=coeff j D.val:=by
    intro j hj
    rw [←hWP,←hface j hj]
    change coeff j (pureFaceSeries Ω coord pc W.val)=coeff j (pureFaceSeries Ω coord pc F.val)
    rw [coeff_pureFaceSeries,coeff_pureFaceSeries,hprod j hj]
  change ∀j≤N,coeff j F.val=coeff j (if pos then D.val*A.val else A.val*D.val)
  intro j hj
  rw [hprod j hj]
  change coeff j W.val=coeff j (if pos then D.val*A.val else A.val*D.val)
  rw [hPW]
  cases pos <;> simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  · exact FormalLog.mul_coeff_congr A.val P.val A.val D.val j (fun _ _=>rfl)
      (fun k hk=>hPD k (hk.trans hj))
  · exact FormalLog.mul_coeff_congr P.val A.val D.val A.val j
      (fun k hk=>hPD k (hk.trans hj)) (fun _ _=>rfl)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint RootTruncation WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

def boundedNonpFrame (w : M →+ ℤ) (P : AddSubmonoid M) (n : ℤ) : AddSubmonoid M where
  carrier:={m | 0≤w m ∧ (w m≤n → m∈P)}
  zero_mem':=⟨by simp,fun _=>P.zero_mem⟩
  add_mem':=by
    intro a b ha hb
    refine ⟨by simpa only [map_add] using add_nonneg ha.1 hb.1,?_⟩
    intro hh
    have ha0 : 0≤w a:=ha.1
    have hb0 : 0≤w b:=hb.1
    have hh' : w a+w b≤n:=by simpa only [map_add] using hh
    exact P.add_mem (ha.2 (by omega)) (hb.2 (by omega))

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_SimplePlaneGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
include he hB hcomp in
lemma plane_lattice_relation (p r q : M) (hq : e q∈Submodule.span ℝ {e p,e r}) :
    (Ω p r) • q=(Ω q r) • p+(Ω p q) • r := by
  apply he
  rw [map_zsmul,map_add,map_zsmul,map_zsmul]
  simp only [←Int.cast_smul_eq_zsmul ℝ]
  rw [←hcomp,←hcomp,←hcomp]
  obtain ⟨a,b,hq⟩:=Submodule.mem_span_pair.mp hq
  rw [←hq]
  simp only [map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,hB,
    mul_zero,zero_add,add_zero,smul_add,smul_smul]
  congr 1 <;> congr 1 <;> ring
include hcoord he hB hcomp in
lemma plane_nonp_relation (r q : M) (hq : q∈planeRoots e (e (simpleRoot C pc)) (e r)) :
    Ω (simpleRoot C pc) r*nonpDegree coord pc q=
      Ω (simpleRoot C pc) q*nonpDegree coord pc r := by
  have H:=congrArg (nonpDegree coord pc)
    (plane_lattice_relation Ω e he B hB hcomp (simpleRoot C pc) r q hq)
  simpa only [map_add,map_zsmul,smul_eq_mul,nonpDegree_simple_self C coord hcoord,mul_zero,zero_add] using H
include hcoord he hB hcomp in
lemma plane_simple_pairing_sign (pos : Bool) (r q : M)
    (hr : 0<nonpDegree coord pc r)
    (htrend : 0 < sideSign pos*Ω (simpleRoot C pc) r)
    (hq : q∈planeRoots e (e (simpleRoot C pc)) (e r)) :
    (0≤nonpDegree coord pc q → 0≤ sideSign pos*Ω (simpleRoot C pc) q) ∧
    (0<nonpDegree coord pc q → 0 < sideSign pos*Ω (simpleRoot C pc) q) ∧
    (nonpDegree coord pc q=0 ↔ Ω (simpleRoot C pc) q=0) := by
  have H:=plane_nonp_relation Ω C coord hcoord pc e he B hB hcomp r q hq
  have HE : (sideSign pos*Ω (simpleRoot C pc) r)*nonpDegree coord pc q=
      (sideSign pos*Ω (simpleRoot C pc) q)*nonpDegree coord pc r:=by
    calc
      _=sideSign pos*(Ω (simpleRoot C pc) r*nonpDegree coord pc q):=by ring
      _=sideSign pos*(Ω (simpleRoot C pc) q*nonpDegree coord pc r):=by rw [H]
      _=_:=by ring
  refine ⟨fun hh=>by nlinarith,fun hh=>by nlinarith,?_⟩
  have ht : Ω (simpleRoot C pc) r≠0:=by intro hz; rw [hz,mul_zero] at htrend; omega
  constructor
  · intro hh
    rw [hh,mul_zero] at H
    exact (mul_eq_zero.mp H.symm).resolve_right (ne_of_gt hr)
  · intro hh
    rw [hh,zero_mul] at H
    exact (mul_eq_zero.mp H).resolve_left ht
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutationDegreeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

def mutationSize : ℕ := (Finset.univ.erase pc).sup fun i=>(mutationPairing Ω C pc i).natAbs

lemma mutationSize_bound (i : I) (hi : i≠pc) :
    |mutationPairing Ω C pc i|≤(mutationSize Ω C pc:ℤ) := by
  have HH : (mutationPairing Ω C pc i).natAbs ≤ mutationSize Ω C pc:=
    Finset.le_sup (f:=fun i=>(mutationPairing Ω C pc i).natAbs) (Finset.mem_erase.mpr ⟨hi,Finset.mem_univ i⟩)
  simpa only [Int.natCast_natAbs] using (show ((mutationPairing Ω C pc i).natAbs:ℤ)≤(mutationSize Ω C pc:ℤ) from by exact_mod_cast HH)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_NonpRegradeFaithful
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ) (B : ℕ)
local instance regradeFaithfulRing : Ring (Torus v Ω) := Torus.instRing v Ω

local instance regradeFaithfulAddCommMonoid_rf9cb96_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance regradeFaithfulAddGroup_rf9cb96_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
def FullHomogeneous (τ : M →+ ℤ) (f : PowerSeries (Torus v Ω)) : Prop :=
  ∀n m,coeff n f m≠0 → τ m=(n:ℤ)

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ) (B : ℕ)
local instance regradeNegationRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance regradeNegationAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance regradeNegationAddGroup : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
lemma torus_neg_one_mul (f : Torus v Ω) : (-1 : Torus v Ω)*f= -f := by
  have H:=Torus.add_mul v Ω (-1) 1 f
  rw [neg_add_cancel,Torus.zero_mul,Torus.one_mul] at H
  exact eq_neg_of_add_eq_zero_left H.symm
lemma RegradeBound.invOfUnit {f : PowerSeries (Torus v Ω)} (hf : RegradeBound v Ω δ B f) :
    RegradeBound v Ω δ B (PowerSeries.invOfUnit f 1) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih=>
    intro m hm
    by_cases hn : n=0
    · subst n
      rw [coeff_invOfUnit,ite_eq_left rfl] at hm
      have hm0 : m=0:=by
        by_contra HH
        apply hm
        change Finsupp.single 0 (1:R) m=0
        exact Finsupp.single_eq_of_ne HH
      subst m
      simp
    · rw [coeff_invOfUnit,ite_eq_right hn] at hm
      simp only [inv_one,Units.val_one] at hm
      rw [torus_neg_one_mul] at hm
      change -(∑ab∈Finset.HasAntidiagonal.antidiagonal n,
        if ab.2<n then coeff ab.1 f*coeff ab.2 (PowerSeries.invOfUnit f 1) else 0) m≠0 at hm
      have HH:=neg_ne_zero.mp hm
      rw [nonp_torus_eval_sum] at HH
      obtain ⟨ab,hab,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero HH
      have hb : ab.2<n:=by by_contra hh; simp [hh] at hz
      rw [ite_eq_left hb] at hz
      obtain ⟨a,b,ha,hb',he⟩:=torus_product_nonzero v Ω _ _ m hz
      obtain ⟨ha0,han⟩:=hf ab.1 a ha
      obtain ⟨hb0,hbn⟩:=ih ab.2 hb b hb'
      have hsum:=Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      rw [←he,_root_.map_add,Int.toNat_add ha0 hb0,mul_add]
      exact ⟨add_nonneg ha0 hb0,hsum ▸ Nat.add_le_add han hbn⟩

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_RationalTorusEmbedding
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)

def embeddedMonomial (m : M) : K →+
    FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) where
  toFun a:=FiberTorus.monomial v _ _ (off k p hp m)
    (RatFunc.C a*centeredScalar v (k m) (complementAlpha k p Ω (off k p hp m)))
  map_zero':=by simp
  map_add' a b:=by simp [add_mul]
def embedAdd : Torus v Ω →+
    FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) :=
  Finsupp.liftAddHom (embeddedMonomial v Ω k p hp)
@[simp] lemma embedAdd_monomial (m : M) (a : K) :
    embedAdd v Ω k p hp (Torus.monomial v Ω m a)=
      FiberTorus.monomial v _ _ (off k p hp m)
        (RatFunc.C a*centeredScalar v (k m) (complementAlpha k p Ω (off k p hp m))) :=
  Finsupp.liftAddHom_apply_single _ _ _
include hΩ in
lemma embeddedMonomial_mul (m n : M) (a b : K) :
    embedAdd v Ω k p hp (Torus.monomial v Ω m a*Torus.monomial v Ω n b)=
      embedAdd v Ω k p hp (Torus.monomial v Ω m a)*
      embedAdd v Ω k p hp (Torus.monomial v Ω n b) := by
  rw [Torus.monomial_mul_monomial,embedAdd_monomial,embedAdd_monomial,embedAdd_monomial,
    FiberTorus.monomial_mul]
  simp only [map_add]
  congr 1
  simp only [map_mul,FiberTorus.twist_constant]
  let am:=complementAlpha k p Ω (off k p hp m)
  let an:=complementAlpha k p Ω (off k p hp n)
  let c:=complementOmega k Ω (off k p hp m) (off k p hp n)
  change RatFunc.C a*RatFunc.C b*RatFunc.C (↑(v^(Ω m n)):K)*
    centeredScalar v (k m+k n) (am+an)=
    (RatFunc.C a*centeredScalar v (k m) am)*
      (RatFunc.C b*scale (v^(-2*am)) (centeredScalar v (k n) an))*RatFunc.C (↑(v^c):K)
  have H:=centeredScalar_mul v (k m) (k n) am an c
  rw [←split_pairing k p hp Ω hΩ m n] at H
  calc
    _ = RatFunc.C a*RatFunc.C b*(RatFunc.C (↑(v^(Ω m n)):K)*
      centeredScalar v (k m+k n) (am+an)) := by ring
    _ = RatFunc.C a*RatFunc.C b*(centeredScalar v (k m) am*
      scale (v^(-2*am)) (centeredScalar v (k n) an)*RatFunc.C (↑(v^c):K)) := by rw [H]
    _ = _ := by ring
include hΩ in
lemma embedAdd_mul (f g : Torus v Ω) :
    embedAdd v Ω k p hp (f*g)=embedAdd v Ω k p hp f*embedAdd v Ω k p hp g := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f f' hf hf'=>simp only [add_mul,map_add,hf,hf']
  | single m a=>
    induction g using Finsupp.induction_linear with
    | zero=>simp
    | add g g' hg hg'=>simp only [mul_add,map_add,hg,hg']
    | single n b=>exact embeddedMonomial_mul v Ω hΩ k p hp m n a b
lemma embedAdd_one : embedAdd v Ω k p hp 1=1 := by
  change embedAdd v Ω k p hp (Torus.monomial v Ω 0 1)=FiberTorus.monomial v _ _ 0 1
  simp [embedAdd_monomial,centeredScalar]
def embed : Torus v Ω →+* FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) where
  __:=embedAdd v Ω k p hp
  map_one':=embedAdd_one v Ω k p hp
  map_mul':=embedAdd_mul v Ω hΩ k p hp
@[simp] lemma embed_monomial (m : M) (a : K) :
    embed v Ω hΩ k p hp (Torus.monomial v Ω m a)=
      FiberTorus.monomial v _ _ (off k p hp m)
        (RatFunc.C a*centeredScalar v (k m) (complementAlpha k p Ω (off k p hp m))) :=
  embedAdd_monomial v Ω k p hp m a
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalLaurentFaithful
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ)
local instance biSupportedRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance biSupportedAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid

local instance biSupportedAddGroup_rf9cb96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
def BiSupported (f : PowerSeries (Torus v Ω)) : Prop :=
  ∀n m,coeff n f m≠0 → 0≤δ m ∧ 0≤κ m ∧ (n:ℤ)=δ m+κ m
lemma BiSupported.zero : BiSupported v Ω δ κ 0 := by intro n m h; simp at h
lemma BiSupported.one : BiSupported v Ω δ κ 1 := by
  intro n m hm
  have hn : n=0:=by by_contra hn; simp [coeff_one,hn] at hm
  subst n
  have hm0 : m=0:=by
    by_contra hm0
    apply hm
    rw [coeff_one,ite_eq_left rfl]
    exact Finsupp.single_eq_of_ne hm0
  subst m
  simp
lemma BiSupported.add {f g : PowerSeries (Torus v Ω)} (hf : BiSupported v Ω δ κ f)
    (hg : BiSupported v Ω δ κ g) : BiSupported v Ω δ κ (f+g) := by
  intro n m hm
  have H : coeff n f m≠0 ∨ coeff n g m≠0:=by
    by_contra hh
    push Not at hh
    simp [hh.1,hh.2] at hm
  exact H.elim (hf n m) (hg n m)
lemma BiSupported.mul {f g : PowerSeries (Torus v Ω)} (hf : BiSupported v Ω δ κ f)
    (hg : BiSupported v Ω δ κ g) : BiSupported v Ω δ κ (f*g) := by
  intro j r hr
  obtain ⟨a,b,m,n,hab,hm,hn,rfl⟩:=series_product_nonzero v Ω f g j r hr
  obtain ⟨hdm,hkm,hem⟩:=hf a m hm
  obtain ⟨hdn,hkn,hen⟩:=hg b n hn
  simp only [map_add]
  exact ⟨add_nonneg hdm hdn,add_nonneg hkm hkn,by rw [←hab,Nat.cast_add,hem,hen]; ring⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RealRootCoordinates
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)

lemma coefficient_simple_expansion (a:I → ℤ) : C a=∑i,a i • simpleRoot C i := by
  have ha : a=∑i,a i • (Pi.single i 1:I → ℤ):=by
    ext j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij; simp [Ne.symm hij]
    · simp
  conv_lhs=>rw [ha,map_sum]
  simp only [map_zsmul,simpleRoot]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RegradeLog
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A] [Algebra ℚ A]
def logPolynomial (F : PowerSeries A) (N : ℕ) : PowerSeries A :=
  ∑k∈Finset.range N,((-1:ℚ)^k/(k+1:ℕ)) • (F-1)^(k+1)
end
end ElementaryPositivity.FormalLog

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RootCoefficients
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M:Type*} [CommRing R] [AddCommGroup M]
variable (v:Rˣ) (Ω:M →+ M →+ ℤ)
local instance rootCoefficientsRing : Ring (Torus v Ω) := Torus.instRing v Ω

local instance rootCoefficientsAddCommMonoid_rf9cb96_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance rootCoefficientsAddGroup_rf9cb96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
def actualRootCoefficient (τ:M →+ ℤ) (f:PowerSeries (Torus v Ω)) (m:M) : R :=
  if 0≤τ m then coeff (τ m).toNat f m else 0

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_MonomialConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {K M:Type*} [Field K] [AddCommGroup M]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
local instance monomialConjugationRing : Ring (Torus v Ω) := Torus.instRing v Ω

include hΩ

local instance monomialConjugationAddCommMonoid_rf9cb96_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance monomialConjugationAddGroup_rf9cb96_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
def monomialConjugate (b:M) (f:PowerSeries (Torus v Ω)) : PowerSeries (Torus v Ω):=
  PowerSeries.C (Torus.X v Ω b)*f*PowerSeries.C (Torus.X v Ω (-b))

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentCompletion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries HahnSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ)
local instance laurentCompletionRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance laurentCompletionAddCommMonoid_rf9cb96_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance laurentCompletionAddGroup_rf9cb96_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
local instance laurentCompletionNonUnitalSemiring_rf9cb96_1 : NonUnitalSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalSemiring
local instance laurentCompletionNonUnitalNonAssocSemiring_rf9cb96_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma BiSupported.neg {f : PowerSeries (Torus v Ω)} (hf : BiSupported v Ω δ κ f) :
    BiSupported v Ω δ κ (-f) := by
  intro n m hm
  apply hf n m
  intro hzero
  apply hm
  change -(coeff n f m)=0
  rw [hzero,neg_zero]
def biSupportedSubring : Subring (PowerSeries (Torus v Ω)) where
  carrier:=BiSupported v Ω δ κ
  zero_mem':=BiSupported.zero v Ω δ κ
  one_mem':=BiSupported.one v Ω δ κ
  add_mem':=BiSupported.add v Ω δ κ
  mul_mem':=BiSupported.mul v Ω δ κ
  neg_mem':=BiSupported.neg v Ω δ κ

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
def pureDegree : M →+ ℤ where
  toFun m:=coord m pc
  map_zero':=by simp
  map_add' a b:=by simp
include hcoord in
lemma completed_biSupported (f : CompletedPositive v Ω C) :
    BiSupported v Ω (nonpDegree coord pc) (pureDegree coord pc) f.val := by
  intro n m hm
  have hr : HasRootDegree C n m:=by
    by_contra hh
    exact hm (f.property.2 n m hh)
  have hn:=nonpDegree_root_nonneg C coord hcoord pc hr
  have he:=nonpDegree_root_eq C coord hcoord pc hr
  obtain ⟨d,hd,hc,hC⟩:=root_coordinates C coord hcoord hr
  exact ⟨hn,by change 0 ≤ coord m pc; rw [hc]; positivity,he.symm⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_MutationInfinityBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
include hcoord in
lemma mutation_infinity_lower_bound {n : ℕ} {m : M}
    (hm : HasRootDegree (mutatedRoots Ω C pc) n m) :
    -(mutationSize Ω C pc:ℤ)*nonpDegree (mutatedCoordinates Ω C coord pc) pc m ≤
      -pureDegree coord pc m := by
  obtain ⟨d,hd,hc,hC⟩:=root_coordinates (mutatedRoots Ω C pc)
    (mutatedCoordinates Ω C coord pc)
    (mutatedCoordinates_retraction Ω C coord hcoord pc) hm
  have hn (i : I) : 0 ≤ mutatedCoordinates Ω C coord pc m i := by
    rw [hc]
    exact Int.natCast_nonneg _
  have hs : (∑i∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc i)*
      mutatedCoordinates Ω C coord pc m i) ≤
      (mutationSize Ω C pc:ℤ)*nonpDegree (mutatedCoordinates Ω C coord pc) pc m := by
    change _ ≤ (mutationSize Ω C pc:ℤ)*(∑i∈Finset.univ.erase pc,
      mutatedCoordinates Ω C coord pc m i)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right _ (hn i)
    exact (max_le (abs_nonneg _) (neg_le_abs _)).trans
      (mutationSize_bound Ω C pc i (Finset.mem_erase.mp hi).1)
  have hk : pureDegree coord pc m = -mutatedCoordinates Ω C coord pc m pc+
      ∑i∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc i)*
        mutatedCoordinates Ω C coord pc m i := by
    have H:=congrArg (fun f : I → ℤ => f pc)
      (mutatedCoefficientMap_involutive pc (mutationPairing Ω C pc) (coord m))
    rw [mutatedCoefficientMap_at] at H
    exact H.symm
  have hp:=hn pc
  nlinarith
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_NormalizedMonomialAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {K M:Type*} [Field K] [AddCommGroup M]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
local instance instRingTorus_1 : Ring (Torus v Ω) := Torus.instRing v Ω

local instance instAddCommMonoidTorus_2_rf9cb96_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_rf9cb96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
def normalizedMonomialAction (f:PowerSeries (Torus v Ω)) (b:M) : PowerSeries (Torus v Ω):=
  f*monomialConjugate v Ω b (invOfUnit f 1)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_AffineCutTelescoping
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.AffineCut
noncomputable section

def beforeSide (u v t : ℝ) : Bool :=
  decide (0 < u+t*v ∨ (u+t*v=0 ∧ v<0))
def afterSide (u v t : ℝ) : Bool :=
  decide (0 < u+t*v ∨ (u+t*v=0 ∧ 0<v))

end
end ElementaryPositivity.AffineCut

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FinitePathPerturbation
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FiniteRayGeometry
open Module Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma dense_annihilator_avoid (r w : E) (hw : w∉Submodule.span ℝ {r}) :
    Dense {h : (ContinuousLinearMap.apply ℝ ℝ r).ker | h.val w≠0} := by
  classical
  let A:=(ContinuousLinearMap.apply ℝ ℝ r).ker
  let f : A →ₗ[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ w).toLinearMap.comp A.subtype
  have hf : f≠0:=by
    obtain ⟨g,hgr,hgw⟩:=dual_avoid_in_annihilator r {w} (by simpa using hw)
    let gc : E →L[ℝ] ℝ:=LinearMap.toContinuousLinearMap g
    let a : A:=⟨gc,by change g r=0; exact hgr⟩
    intro hz
    have H:=LinearMap.congr_fun hz a
    change g w=0 at H
    exact hgw w (Finset.mem_singleton_self w) H
  have hi : interior (f.ker:Set A)=∅:=by
    by_contra hh
    exact hf (LinearMap.ker_eq_top.mp (Submodule.eq_top_of_nonempty_interior' f.ker
      (Set.nonempty_iff_ne_empty.mpr hh)))
  exact interior_eq_empty_iff_dense_compl.mp hi

lemma countable_avoid_with_probes (W : Set E) (hW : W.Countable) (r : E)
    (hproper : ∀w∈W,w∉Submodule.span ℝ {r})
    (P : Finset (ℝ×E)) (v k : Module.Dual ℝ E) (hk : k r=0) :
    ∃h : Module.Dual ℝ E,h r=0 ∧ (∀w∈W,h w≠0) ∧ ∀as∈P,
      (0<(k+as.1 • v) as.2 → 0<(h+as.1 • v) as.2) ∧
      ((k+as.1 • v) as.2<0 → (h+as.1 • v) as.2<0) := by
  classical
  let A:=(ContinuousLinearMap.apply ℝ ℝ r).ker
  let U : Set A:={h|∀as∈P,
    (0<(k+as.1 • v) as.2 → 0<h.val as.2+as.1*v as.2) ∧
    ((k+as.1 • v) as.2<0 → h.val as.2+as.1*v as.2<0)}
  have hU : IsOpen U:=by
    have H : ∀as : ℝ×E,IsOpen {h:A|
        (0<(k+as.1 • v) as.2 → 0<h.val as.2+as.1*v as.2) ∧
        ((k+as.1 • v) as.2<0 → h.val as.2+as.1*v as.2<0)}:=by
      intro as
      have hc : Continuous (fun h:A=>h.val as.2+as.1*v as.2):=
        ((ContinuousLinearMap.apply ℝ ℝ as.2).continuous.comp continuous_subtype_val).add continuous_const
      by_cases hp : 0<(k+as.1 • v) as.2 <;>
      by_cases hn : (k+as.1 • v) as.2<0 <;>
        simp only [hp,hn,IsEmpty.forall_iff,forall_const,true_and,and_true]
      · exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
      · exact isOpen_lt continuous_const hc
      · exact isOpen_lt hc continuous_const
      · exact isOpen_univ
    convert isOpen_biInter_finset (s:=P) (fun as _=>H as) using 1
    all_goals try with_reducible_and_instances rfl
    ext h; simp only [U,Set.mem_ofPred_eq,Set.mem_iInter]
  have hnU : U.Nonempty:=by
    let kc : E →L[ℝ] ℝ:=LinearMap.toContinuousLinearMap k
    refine ⟨⟨kc,by change k r=0; exact hk⟩,?_⟩
    intro as _
    exact ⟨fun H=>H,fun H=>H⟩
  have Hd : Dense (⋂w∈W,{h:A|h.val w≠0}):=dense_biInter_of_isOpen
    (fun w _=>isOpen_ne_fun ((ContinuousLinearMap.apply ℝ ℝ w).continuous.comp continuous_subtype_val)
      continuous_const) hW (fun w hw=>dense_annihilator_avoid r w (hproper w hw))
  obtain ⟨h,hhU,hh⟩:=Hd.inter_open_nonempty U hU hnU
  refine ⟨h.val.toLinearMap,by exact h.property,?_,?_⟩
  · change ∀w∈W,h.val w≠0
    simpa only [Set.mem_iInter,Set.mem_ofPred_eq] using hh
  · exact hhU

end
end ElementaryPositivity.FiniteRayGeometry

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SectionRayTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry PowerSeriesSplit PowerSeriesAdjoint
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
def ChamberGeneric (N : ℕ) (h : M →+ ℝ) : Prop :=
  ∀n,0<n → n≤N → ∀m,HasRootDegree C n m → h m≠0
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_AllOrderSectionLine
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

variable (u : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
lemma chamber_chart_trivial (F : CompletedPositive u Ω C) (N : ℕ)
    (h : M →+ ℝ) (H : ChamberGeneric C N h) :
    ∀n≤N,coeff n (chartZero u Ω C h F).val=coeff n 1 := by
  intro n hn
  cases n with
  | zero=>simpa only [coeff_zero_eq_constantCoeff,map_one] using
      (chartZero u Ω C h F).property.1
  | succ n=>
    rw [coeff_one,ite_eq_right (Nat.succ_ne_zero n)]
    apply Finsupp.ext
    intro m
    by_contra hm
    have hm' : coeff (n+1) (chartZero u Ω C h F).val m≠0:=hm
    exact H (n+1) (by omega) hn m
      (chart_root_of_ne u Ω C (chartZero u Ω C h F) (n+1) m hm')
      ((chart_three_support u Ω C h F).2.1 n m hm')

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedBiUnit
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (u : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance completedBiUnitRing : Ring (Torus u Ω) := Torus.instRing u Ω

local instance completedBiUnitAddCommMonoid_rf9cb96_1 : AddCommMonoid (Torus u Ω) :=
  (Torus.instRing u Ω).toAddCommMonoid
local instance completedBiUnitAddGroup_rf9cb96_1 : AddGroup (Torus u Ω) := (Torus.instRing u Ω).toAddGroup
local instance completedBiUnitNonUnitalSemiring_rf9cb96_1 : NonUnitalSemiring (Torus u Ω) :=
  (Torus.instRing u Ω).toNonUnitalSemiring
local instance completedBiUnitNonUnitalNonAssocSemiring_rf9cb96_1 : NonUnitalNonAssocSemiring (Torus u Ω) :=
  (Torus.instRing u Ω).toNonUnitalNonAssocSemiring
def completedBiUnit (F : CompletedPositive u Ω C) :
    (biSupportedSubring u Ω (nonpDegree coord pc) (pureDegree coord pc))ˣ where
  val:=⟨F.val,completed_biSupported u Ω C coord hcoord pc F⟩
  inv:=⟨(completedInverse u Ω C F).val,
    completed_biSupported u Ω C coord hcoord pc (completedInverse u Ω C F)⟩
  val_inv:=Subtype.ext (mul_completedInverse u Ω C F)
  inv_val:=Subtype.ext (completedInverse_mul u Ω C F)

@[simp] lemma completedBiUnit_val (F : CompletedPositive u Ω C) :
    (completedBiUnit u Ω C coord hcoord pc F).val.val=F.val := rfl
@[simp] lemma completedBiUnit_inv (F : CompletedPositive u Ω C) :
    (completedBiUnit u Ω C coord hcoord pc F).inv.val=invOfUnit F.val 1 := rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ComparisonLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
structure LineRayData (v k : Module.Dual ℝ E) (a : ℝ) where
  root : M
  degree : ℕ
  degree_pos : 0<degree
  root_degree : HasRootDegree C degree root
  transverse : v (e root)≠0
  generic : ∀N,RayGeneric C N root ((k+a • v).toAddMonoidHom.comp e)

variable (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

lemma cutSide_decide (h : M →+ ℝ) (p : M) (hp : h p≠0) :
    cutSide (decide (0<h p)) h p := by
  classical
  by_cases hh : 0<h p
  · simp only [hh,decide_true,cutSide,↓reduceIte]
  · simpa [hh,cutSide] using lt_of_le_of_ne (le_of_not_gt hh) hp
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedLineCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries
noncomputable section
variable {A J : Type*} [Ring A]
lemma filter_product_coeff_congr (l : List J) (p : J → Bool) (f : J → PowerSeries A) (D : ℕ)
    (h : ∀a∈l,p a=false → ∀n≤D,coeff n (f a)=coeff n 1) :
    ∀n≤D,coeff n ((l.filter p).map f).prod=coeff n (l.map f).prod := by
  induction l with
  | nil=>exact fun _ _=>rfl
  | cons a l ih=>
    have ih':=ih (fun x hx hp=>h x (List.mem_cons_of_mem a hx) hp)
    by_cases hp : p a=true
    · simp only [List.filter_cons,hp,↓reduceIte,List.map_cons,List.prod_cons]
      intro n hn
      exact FormalLog.mul_coeff_congr _ _ _ _ n (fun _ _=>rfl)
        (fun j hj=>ih' j (hj.trans hn))
    · have hp' : p a=false:=Bool.eq_false_iff.mpr hp
      simp only [List.filter_cons,hp',Bool.false_eq_true,ite_false, if_false,List.map_cons,List.prod_cons]
      intro n hn
      rw [←one_mul (((l.filter p).map f).prod)]
      exact FormalLog.mul_coeff_congr _ _ _ _ n
        (fun j hj=>(h a (by simp) hp' j (hj.trans hn)).symm)
        (fun j hj=>ih' j (hj.trans hn))
end
end ElementaryPositivity.PowerSeriesAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationMonomialAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I) (pos:Bool)

local instance instRingTorusLaurentSeriesRatVUnit_3_rf9cb96_1 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_6_rf9cb96_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_6_rf9cb96_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
def actualMonomialAdjointCoefficient (τ:M →+ ℤ) (f:PowerSeries (Torus LaurentRay.vUnit Ω)) (b m:M) :
    LaurentSeries ℚ :=
  actualRootCoefficient LaurentRay.vUnit Ω τ (normalizedMonomialAction LaurentRay.vUnit Ω f b) (m-b)*
    (↑(LaurentRay.vUnit^(Ω (m-b) b)):LaurentSeries ℚ)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_NegativeRayCrossing
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FiniteEventTraversal
noncomputable section
variable {A : Type*} [Monoid A]

def intervalWord (S : Finset ℝ) (lo hi : ℝ) (L : ℝ → A) : A := by
  classical
  exact (((S.filter (fun a=>lo<a ∧ a<hi)).sort (· ≥ ·)).map L).prod

end
end ElementaryPositivity.FiniteEventTraversal

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LineOldTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
structure GenericLineSegment where
  direction : Module.Dual ℝ E
  offset : Module.Dual ℝ E
  lo : ℝ
  hi : ℝ
  ordered : lo<hi
  generic : ∀N,GenericOffset (realRootsThrough e C N) 0 direction offset
  start_regular : ∀N,lo∉lineEvents (realRootsThrough e C N) direction offset
  finish_regular : ∀N,hi∉lineEvents (realRootsThrough e C N) direction offset

def GenericLineSegment.start (s : GenericLineSegment C e) : Module.Dual ℝ E :=
  s.offset+s.lo • s.direction

def GenericLineSegment.finish (s : GenericLineSegment C e) : Module.Dual ℝ E :=
  s.offset+s.hi • s.direction

inductive GenericLinePath : Module.Dual ℝ E → Module.Dual ℝ E → Type _ where
  | nil (a : Module.Dual ℝ E) : GenericLinePath a a
  | append {a : Module.Dual ℝ E} (s : GenericLineSegment C e)
      (p : GenericLinePath a (s.start C e)) : GenericLinePath a (s.finish C e)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_GenericLineJoining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FiniteRayGeometry
open Module
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma wedge_ne_of_difference_ne (a h : Module.Dual ℝ E) (s t : E)
    (ha : s≠0 → a s≠0) (hw : (h-a) s • t-(h-a) t • s≠0) :
    a s • t-a t • s≠0 := by
  intro hz
  by_cases hs : s=0
  · apply hw
    simp only [hs,map_zero,zero_smul,smul_zero,sub_self]
  · have has:=ha hs
    have ht : t=(a t/a s) • s:=by
      calc
        t=(a s)⁻¹ • (a s • t):=(inv_smul_smul₀ has t).symm
        _=(a t/a s) • s:=by rw [sub_eq_zero.mp hz,smul_smul]; congr 1; ring
    apply hw
    rw [ht]
    simp only [map_smul,smul_smul,smul_eq_mul,mul_comm,sub_self]

lemma GenericOffset.join {T : Finset E} {a h : Module.Dual ℝ E}
    (H : GenericOffset T 0 a h) (ha : ∀s∈T,s≠0 → a s≠0) :
    GenericOffset T 0 (h-a) a := by
  refine ⟨map_zero _,?_,?_⟩
  · intro s hs hn
    exact ha s hs (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn)
  · intro s hs t ht hn
    have hw : (h-a) s • t-(h-a) t • s≠0:=by
      simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn
    have hz:=H.distinct s hs t ht (by
      simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using
        wedge_ne_of_difference_ne a h s t (ha s hs) hw)
    intro hh
    apply hz
    simp only [map_sub,map_smul,smul_eq_mul,LinearMap.sub_apply] at hh ⊢
    nlinarith

lemma GenericOffset.join_reverse {T : Finset E} {a h : Module.Dual ℝ E}
    (H : GenericOffset T 0 a h) (ha : ∀s∈T,s≠0 → a s≠0) :
    GenericOffset T 0 (a-h) h := by
  refine ⟨map_zero _,H.avoid,?_⟩
  intro s hs t ht hn
  have hw : (h-a) s • t-(h-a) t • s≠0:=by
    intro hz
    apply hn
    have he : (a-h) s • t-(a-h) t • s= -((h-a) s • t-(h-a) t • s):=by
      simp only [LinearMap.sub_apply,neg_sub,sub_smul]
      abel
    rw [he,hz,neg_zero]
    exact (Submodule.span ℝ {(0:E)}).zero_mem
  have hz:=H.distinct s hs t ht (by
    simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using
      wedge_ne_of_difference_ne a h s t (ha s hs) hw)
  intro hh
  apply hz
  simp only [map_sub,map_smul,smul_eq_mul,LinearMap.sub_apply] at hh ⊢
  nlinarith
end

section Simultaneous
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
noncomputable section
lemma generic_for_two_directions (T : ℕ → Finset E) (a b k : Module.Dual ℝ E)
    (P : Finset E) :
    ∃h : Module.Dual ℝ E,(∀N,GenericOffset (T N) 0 a h) ∧
      (∀N,GenericOffset (T N) 0 b h) ∧
      ∀s∈P,(0<k s → 0<h s) ∧ (k s<0 → h s<0) := by
  classical
  let W : Set E:=⋃N,↑(forbidden (T N) 0 a∪forbidden (T N) 0 b)
  have hc : W.Countable:=Set.countable_iUnion (fun N=>(forbidden (T N) 0 a∪forbidden (T N) 0 b).countable_toSet)
  have hp : ∀w∈W,w∉Submodule.span ℝ {(0:E)}:=by
    intro w hw
    obtain ⟨N,hN⟩:=Set.mem_iUnion.mp hw
    rcases Finset.mem_union.mp hN with hh|hh
    · exact (Finset.mem_filter.mp hh).2
    · exact (Finset.mem_filter.mp hh).2
  obtain ⟨h,h0,havoid,hprobe⟩:=countable_avoid_with_probes W hc 0 hp
    (P.image (fun s=>((0:ℝ),s))) 0 k (map_zero k)
  have hGa : ∀N,GenericOffset (T N) 0 a h:=by
    intro N
    refine ⟨h0,?_,?_⟩
    · intro s hs hn
      exact havoid s (Set.mem_iUnion.mpr ⟨N,Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hs,hn⟩)⟩)
    · intro s hs t ht hn
      exact havoid _ (Set.mem_iUnion.mpr ⟨N,Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(s,t),Finset.mem_product.mpr ⟨hs,ht⟩,rfl⟩),hn⟩)⟩)
  have hGb : ∀N,GenericOffset (T N) 0 b h:=by
    intro N
    refine ⟨h0,?_,?_⟩
    · intro s hs hn
      exact havoid s (Set.mem_iUnion.mpr ⟨N,Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hs,hn⟩)⟩)
    · intro s hs t ht hn
      exact havoid _ (Set.mem_iUnion.mpr ⟨N,Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(s,t),Finset.mem_product.mpr ⟨hs,ht⟩,rfl⟩),hn⟩)⟩)
  refine ⟨h,hGa,hGb,?_⟩
  intro s hs
  simpa only [zero_smul,add_zero] using hprobe (0,s) (Finset.mem_image.mpr ⟨s,hs,rfl⟩)
end
end Simultaneous
end ElementaryPositivity.FiniteRayGeometry

end
section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
def RegularCovector (a : Module.Dual ℝ E) : Prop :=
  ∀N,∀s∈realRootsThrough e C N,s≠0 → a s≠0

def segmentBetween (a b : Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 (b-a) a) :
    GenericLineSegment C e where
  direction:=b-a
  offset:=a
  lo:=0
  hi:=1
  ordered:=zero_lt_one
  generic:=H
  start_regular:=by
    intro N hh
    obtain ⟨s,hs,hv,hsa⟩:=(mem_lineEvents_iff _ _ _ _).mp hh
    exact HA N s hs (fun hz=>hv (by rw [hz,map_zero])) (by simpa only [zero_smul,add_zero] using hsa)
  finish_regular:=by
    intro N hh
    obtain ⟨s,hs,hv,hsa⟩:=(mem_lineEvents_iff _ _ _ _).mp hh
    exact HB N s hs (fun hz=>hv (by rw [hz,map_zero])) (by simpa only [one_smul,add_sub_cancel] using hsa)

@[simp] lemma segmentBetween_start (a b : Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 (b-a) a) :
    (segmentBetween C e a b HA HB H).start C e=a := by
  simp only [segmentBetween,GenericLineSegment.start,zero_smul,add_zero]
@[simp] lemma segmentBetween_finish (a b : Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 (b-a) a) :
    (segmentBetween C e a b HA HB H).finish C e=b := by
  simp only [segmentBetween,GenericLineSegment.finish,one_smul,add_sub_cancel]

def GenericLinePath.single (s : GenericLineSegment C e) :
    GenericLinePath C e (s.start C e) (s.finish C e) :=
  .append s (.nil _)

def GenericLinePath.trans {a b c : Module.Dual ℝ E}
    (p : GenericLinePath C e a b) (q : GenericLinePath C e b c) :
    GenericLinePath C e a c :=
  match q with
  | .nil _=>p
  | .append s q=>.append s (p.trans q)
end

end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedNoCutTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

def GenericLinePath.OnCutSide (pos : Bool) {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) : Prop :=
  match p with
  | .nil _=>True
  | .append s p=>(∀t,s.lo<t → t < s.hi →
      cutSide pos ((s.offset+t • s.direction).toAddMonoidHom.comp e) (simpleRoot C pc)) ∧
      GenericLinePath.OnCutSide pos p

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationLaurentCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
include hcoord in
lemma mutation_infinity_full_bound {n : ℕ} {m : M}
    (hm : HasRootDegree (mutatedRoots Ω C pc) n m) :
    (n:ℤ) ≤ -pureDegree coord pc m+(mutationSize Ω C pc+1:ℤ)*
      nonpDegree (mutatedCoordinates Ω C coord pc) pc m := by
  obtain ⟨d,hd,hc,hC⟩:=root_coordinates (mutatedRoots Ω C pc)
    (mutatedCoordinates Ω C coord pc)
    (mutatedCoordinates_retraction Ω C coord hcoord pc) hm
  have hn (i : I) : 0 ≤ mutatedCoordinates Ω C coord pc m i := by
    rw [hc]
    exact Int.natCast_nonneg _
  have hs : (∑i∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc i)*
      mutatedCoordinates Ω C coord pc m i) ≤
      (mutationSize Ω C pc:ℤ)*nonpDegree (mutatedCoordinates Ω C coord pc) pc m := by
    change _ ≤ (mutationSize Ω C pc:ℤ)*(∑i∈Finset.univ.erase pc,
      mutatedCoordinates Ω C coord pc m i)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right _ (hn i)
    exact (max_le (abs_nonneg _) (neg_le_abs _)).trans
      (mutationSize_bound Ω C pc i (Finset.mem_erase.mp hi).1)
  have hk : pureDegree coord pc m = -mutatedCoordinates Ω C coord pc m pc+
      ∑i∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc i)*
        mutatedCoordinates Ω C coord pc m i := by
    have H:=congrArg (fun f : I → ℤ => f pc)
      (mutatedCoefficientMap_involutive pc (mutationPairing Ω C pc) (coord m))
    rw [mutatedCoefficientMap_at] at H
    exact H.symm
  have he:=nonpDegree_root_eq (mutatedRoots Ω C pc)
    (mutatedCoordinates Ω C coord pc)
    (mutatedCoordinates_retraction Ω C coord hcoord pc) pc hm
  nlinarith

variable (v : (LaurentSeries ℚ)ˣ)

local instance mutationLaurentCompletionRing_rf9cb96_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance mutationLaurentCompletionAddCommMonoid_rf9cb96_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance mutationLaurentCompletionAddGroup_rf9cb96_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
include hcoord in
lemma mutated_series_laurentBounded {f : PowerSeries (Torus v Ω)}
    (hf : SeriesGraded v Ω (mutatedRoots Ω C pc) f) :
    LaurentBounded v Ω (nonpDegree (mutatedCoordinates Ω C coord pc) pc)
      (-pureDegree coord pc) (mutationSize Ω C pc) f := by
  intro n m hn
  have hm : HasRootDegree (mutatedRoots Ω C pc) n m := by
    by_contra h
    exact hn (hf n m h)
  exact ⟨nonpDegree_root_nonneg (mutatedRoots Ω C pc)
      (mutatedCoordinates Ω C coord pc)
      (mutatedCoordinates_retraction Ω C coord hcoord pc) pc hm,
    mutation_infinity_lower_bound Ω C coord hcoord pc hm,
    mutation_infinity_full_bound Ω C coord hcoord pc hm⟩

def completedInfinityUnit (F : CompletedPositive v Ω (mutatedRoots Ω C pc)) :
    (laurentBoundedSubring v Ω (nonpDegree (mutatedCoordinates Ω C coord pc) pc)
      (-pureDegree coord pc) (mutationSize Ω C pc))ˣ where
  val:=⟨F.val,mutated_series_laurentBounded Ω C coord hcoord pc v F.property.2⟩
  inv:=⟨(completedInverse v Ω (mutatedRoots Ω C pc) F).val,
    mutated_series_laurentBounded Ω C coord hcoord pc v
      (completedInverse v Ω (mutatedRoots Ω C pc) F).property.2⟩
  val_inv:=Subtype.ext (mul_completedInverse v Ω (mutatedRoots Ω C pc) F)
  inv_val:=Subtype.ext (completedInverse_mul v Ω (mutatedRoots Ω C pc) F)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PolynomialAdjointCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)

local instance polynomialAdjointCoefficientsRing_rf9cb96_1 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance polynomialAdjointCoefficientsAddCommMonoid_rf9cb96_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialAdjointCoefficientsAddGroup_rf9cb96_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
def actualPolynomialAdjointCoefficient (τ:M →+ ℤ) (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (F:Torus LaurentRay.vUnit Ω) (m:M) : LaurentSeries ℚ :=
  F.sum (fun b c=>c*actualMonomialAdjointCoefficient Ω τ f b m)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end


