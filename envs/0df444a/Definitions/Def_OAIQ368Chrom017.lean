-- Prove2me | Definitions.Def_OAIQ368Chrom017
-- name    : OAIQ368Chrom017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:08:17.919285+00:00
-- url     : https://prove2.me/theorems/14d48783-caa1-4172-bfcc-d850f25ab44d
-- title:
--   Definitions bundle OAIQ368Chrom017 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 365 declarations of OpenAI's Lean: 149 definitions, 4 instances and 212 theorems. The definitions and types are `OAI.ElementaryPositivity.CommonTranslation.D`, `OAI.ElementaryPositivity.CommonTranslation.taylor`, `OAI.ElementaryPositivity.Homogeneity.degreeSet`, `OAI.ElementaryPositivity.LaurentAtInfinity.affineUnit`, `OAI.ElementaryPositivity.LaurentAtInfinity.mapLinear`, `OAI.ElementaryPositivity.LaurentAtInfinity.mapRing`, `OAI.ElementaryPositivity.LaurentAtInfinity.mulPolynomial`, `OAI.ElementaryPositivity.LaurentAtInfinity.mulPolynomialCoeff`, `OAI.ElementaryPositivity.LaurentAtInfinity.oneSubUnit`, `OAI.ElementaryPositivity.LaurentAtInfinity.polynomial`, `OAI.ElementaryPositivity.LaurentAtInfinity.polynomialLinear`, `OAI.ElementaryPositivity.LaurentAtInfinity.zUnit`, `OAI.ElementaryPositivity.LinearDetection.additiveTensorFiltration`, `OAI.ElementaryPositivity.PackConvolution.Cut`, `OAI.ElementaryPositivity.PackConvolution.LeftIndex`, `OAI.ElementaryPositivity.PackConvolution.Pack`, `OAI.ElementaryPositivity.PackConvolution.RightIndex`, `OAI.ElementaryPositivity.PackConvolution.distribute`, `OAI.ElementaryPositivity.PackConvolution.grid`, `OAI.ElementaryPositivity.PackConvolution.kernel`, `OAI.ElementaryPositivity.PackConvolution.left`, `OAI.ElementaryPositivity.PackConvolution.rebracket`, `OAI.ElementaryPositivity.PackConvolution.right`, `OAI.ElementaryPositivity.PackConvolution.shuffle`, `OAI.ElementaryPositivity.PackEnumeration.Split`, `OAI.ElementaryPositivity.PackEnumeration.embedding`, `OAI.ElementaryPositivity.PackEnumeration.mapEquiv`, `OAI.ElementaryPositivity.PackEnumeration.sizedSplitEquiv`, `OAI.ElementaryPositivity.PackEnumeration.split`, `OAI.ElementaryPositivity.PackEnumeration.splitEquiv`, `OAI.ElementaryPositivity.QuantumTorus.instSubTorus`, `OAI.ElementaryPositivity.QuantumTorus.instSubTorusLaurentSeriesRat`, `OAI.ElementaryPositivity.QuantumTorus.orderedPlaneProducts`, `OAI.ElementaryPositivity.RawShuffle.B`, `OAI.ElementaryPositivity.RawShuffle.CellGroup`, `OAI.ElementaryPositivity.RawShuffle.CellVars`, `OAI.ElementaryPositivity.RawShuffle.ColumnDimensionGrid`, `OAI.ElementaryPositivity.RawShuffle.Cut`, `OAI.ElementaryPositivity.RawShuffle.CutShape`, `OAI.ElementaryPositivity.RawShuffle.DimensionSplit` and 109 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_DegreeSet`, `Chromatic_GradedAlgebra_IntegerHomogeneous`, `Chromatic_GradedAlgebra_LaurentInfinity`, `Chromatic_QuantumTorus_TorusContinuity`, `Chromatic_Shuffle_CanonicalCard`, `Chromatic_Shuffle_CellVars`, `Chromatic_Shuffle_CrossDifference`, `Chromatic_Shuffle_Cut`, `Chromatic_Shuffle_Diagonal`, `Chromatic_Shuffle_DimensionGrid`, `Chromatic_Shuffle_EulerForm`, `Chromatic_Shuffle_GridShapeTensor`, `Chromatic_Shuffle_InputOrderedEnergy`, `Chromatic_Shuffle_LabeledPolynomial`, `Chromatic_Shuffle_PackSplit`, `Chromatic_Shuffle_QuotientAlg`, `Chromatic_Shuffle_Realization`, `Chromatic_Shuffle_RenameFraction`, `Chromatic_Shuffle_RestrictSplit`, `Chromatic_Shuffle_ReynoldsS`, `Chromatic_Shuffle_SameDen`, `Chromatic_Shuffle_Split`, `Chromatic_Shuffle_SumPackCut`, `Chromatic_Shuffle_SymmetricSpace`, `Chromatic_Shuffle_TargetEmbedding`, `Chromatic_Walls_Average`, `Chromatic_Walls_Grid`, `Chromatic_Walls_LaurentPolynomialAction`, `Chromatic_Walls_Mass`, `Chromatic_Walls_OrderedRootReordering`, `Chromatic_Walls_Pack`, `Chromatic_Walls_QuantumTorusWallLeading`, `Chromatic_Walls_RationalTensorDetection`, `Chromatic_Walls_ShuffleTensorLinear`, `Chromatic_Walls_Taylor`.
--
--   **Imports.** It imports the bundle `OAIQ368Chrom001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom019`, `OAIQ368Chrom020`, `OAIQ368Chrom021` and `OAIQ368Chrom072`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom001

section
-- module Solutions.OAIQ368_CHROM.Compat
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_DegreeSet
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.Homogeneity
open MvPolynomial
variable {σ τ R : Type*} [CommRing R] {w : σ → ℤ}

lemma component_mul (p q : MvPolynomial σ R) {m : ℤ}
    (hp : p.IsWeightedHomogeneous w m) (n : ℤ) :
    weightedHomogeneousComponent w (m+n) (p*q) =
      p * weightedHomogeneousComponent w n q := by
  classical
  conv_lhs => rw [← q.support_sum_monomial_coeff]
  conv_rhs => rw [← q.support_sum_monomial_coeff]
  simp only [Finset.mul_sum,map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hm := isWeightedHomogeneous_monomial w d (q.coeff d) rfl
  by_cases hn : Finsupp.weight w d = n
  · rw [hn] at hm
    rw [(hp.mul hm).weightedHomogeneousComponent_same,hm.weightedHomogeneousComponent_same]
  · rw [(hp.mul hm).weightedHomogeneousComponent_ne (m+n) (by omega),
      hm.weightedHomogeneousComponent_ne n (Ne.symm hn),mul_zero]

lemma of_mul [IsDomain R] (p q : MvPolynomial σ R) {m k : ℤ}
    (hp : p.IsWeightedHomogeneous w m) (hp0 : p≠0)
    (hpq : (p*q).IsWeightedHomogeneous w k) :
    q.IsWeightedHomogeneous w (k-m) := by
  have h : p * weightedHomogeneousComponent w (k-m) q = p*q := by
    rw [← component_mul p q hp,show m+(k-m)=k by omega,
      hpq.weightedHomogeneousComponent_same]
  have hh := mul_left_cancel₀ hp0 h
  rw [← hh]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

lemma constantWeight_rename (f : σ → τ) (p : MvPolynomial σ R) {m : ℤ}
    (hp : p.IsWeightedHomogeneous (fun _=> (1:ℤ)) m) :
    (rename f p).IsWeightedHomogeneous (fun _=>(1:ℤ)) m := by
  classical
  rw [← p.support_sum_monomial_coeff,map_sum]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [rename_monomial]
  apply isWeightedHomogeneous_monomial
  have h := hp (mem_support_iff.mp hd)
  simp only [Finsupp.weight_apply,nsmul_eq_mul,mul_one] at h ⊢
  exact (Finsupp.sum_mapDomain_index_addMonoidHom (f:=f) (s:=d)
    (fun _=> Nat.castAddMonoidHom ℤ)).trans h

lemma constantWeight_component_rename (f : σ → τ) (p : MvPolynomial σ R) (n : ℤ) :
    rename f (weightedHomogeneousComponent (fun _=>(1:ℤ)) n p) =
    weightedHomogeneousComponent (fun _=>(1:ℤ)) n (rename f p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have hd := isWeightedHomogeneous_monomial (fun _ : σ=>(1:ℤ)) d c rfl
    have hrename := constantWeight_rename f (monomial d c) hd
    rw [weightedHomogeneousComponent_of_mem hd,
      weightedHomogeneousComponent_of_mem hrename]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add,hp,hq]

noncomputable def degreeSet (p : MvPolynomial σ R) : Finset ℤ :=
  p.support.image (Finsupp.weight (fun _=>(1:ℤ)))

lemma sum_components (p : MvPolynomial σ R) :
    ∑ k ∈ degreeSet p, weightedHomogeneousComponent (fun _=>(1:ℤ)) k p = p := by
  classical
  ext d
  simp only [coeff_sum,coeff_weightedHomogeneousComponent]
  rw [Finset.sum_eq_single (Finsupp.weight (fun _=>(1:ℤ)) d)]
  · simp
  · intro k hk hne
    rw [ite_eq_right (Ne.symm hne)]
  · intro hnot
    rw [ite_eq_left rfl]
    by_contra hne
    exact hnot (Finset.mem_image.mpr ⟨d,mem_support_iff.mpr hne,rfl⟩)

end ElementaryPositivity.Homogeneity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_IntegerHomogeneous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.Homogeneity
open MvPolynomial
variable {σ R : Type*} [CommRing R]
lemma constantWeight_eq_zero (d : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ=>(1:ℤ)) d=0 ↔ d=0 := by
  classical
  simp only [Finsupp.weight_apply,nsmul_eq_mul,mul_one,Finsupp.sum]
  constructor
  · intro h
    ext i
    by_cases hi : i∈d.support
    · have he := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j∈d.support)=>Int.natCast_nonneg (d j))).mp h i hi
      exact_mod_cast he
    · exact Finsupp.notMem_support_iff.mp hi
  · intro h
    subst d
    simp

lemma constantWeight_component_zero (p : MvPolynomial σ R) :
    weightedHomogeneousComponent (fun _=>(1:ℤ)) 0 p=C (constantCoeff p) := by
  classical
  ext d
  simp only [coeff_weightedHomogeneousComponent,constantWeight_eq_zero,coeff_C]
  by_cases hd : d=0
  · subst d
    rfl
  · simp [hd,Ne.symm hd]
end ElementaryPositivity.Homogeneity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentInfinity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R S : Type*} [CommRing R] [CommRing S]

def mapRing (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom

@[simp] lemma mapRing_coeff (f : R →+* S) (x : LaurentSeries R) (n : ℤ) :
    (mapRing f x).coeff n=f (x.coeff n) := rfl

@[simp] lemma mapRing_single (f : R →+* S) (n : ℤ) (r : R) :
    mapRing f (single n r)=single n (f r) := by
  ext k
  by_cases h : k=n <;> simp [h]

@[simp] lemma mapRing_C (f : R →+* S) (r : R) : mapRing f (C r)=C (f r) :=
  mapRing_single f 0 r

lemma mapRing_injective (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (mapRing f) := by
  intro x y h
  ext k
  exact hf (congrArg (fun z : LaurentSeries S=>z.coeff k) h)

section Linear
variable {K V W : Type*} [Semiring K] [AddCommMonoid V] [AddCommMonoid W]
  [Module K V] [Module K W]

def mapLinear (f : V →ₗ[K] W) : LaurentSeries V →ₗ[K] LaurentSeries W where
  toFun x := x.map f
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom
  map_smul' r x := by ext k; exact f.map_smul r (x.coeff k)

@[simp] lemma mapLinear_coeff (f : V →ₗ[K] W) (x : LaurentSeries V) (k : ℤ) :
    (mapLinear f x).coeff k=f (x.coeff k) := rfl
end Linear

noncomputable def zUnit (n : ℤ) : (LaurentSeries R)ˣ where
  val := single (-n) 1
  inv := single n 1
  val_inv := by simp [single_mul_single]
  inv_val := by simp [single_mul_single]

@[simp] lemma zUnit_val (n : ℤ) : (zUnit (R:=R) n : LaurentSeries R)=single (-n) 1 := rfl

@[simp] lemma zUnit_map (f : R →+* S) (n : ℤ) :
    Units.map (mapRing f).toMonoidHom (zUnit n)=zUnit n := by
  apply Units.ext
  simp

noncomputable def oneSubUnit (c : R) : (PowerSeries R)ˣ :=
  (PowerSeries.isUnit_iff_constantCoeff (φ:=1-PowerSeries.C c*PowerSeries.X) |>.mpr (by simp)).unit

@[simp] lemma oneSubUnit_val (c : R) :
    (oneSubUnit c : PowerSeries R)=1-PowerSeries.C c*PowerSeries.X := by
  exact IsUnit.unit_spec _

noncomputable def affineUnit (c : R) : (LaurentSeries R)ˣ :=
  -zUnit (R:=R) 1 * Units.map (ofPowerSeries ℤ R).toMonoidHom (oneSubUnit c)

@[simp] lemma affineUnit_val (c : R) :
    (affineUnit c : LaurentSeries R)=C c-(zUnit (R:=R) 1 : LaurentSeries R) := by
  change -(single (-1:ℤ) (1:R)) * ((ofPowerSeries ℤ R) (oneSubUnit c : PowerSeries R)) = _
  rw [oneSubUnit_val,PowerSeries.coe_sub,PowerSeries.coe_one,PowerSeries.coe_mul,
    PowerSeries.coe_C,PowerSeries.coe_X,zUnit_val]
  rw [mul_sub,mul_one,neg_mul]
  have h : single (-1:ℤ) (1:R) * (C c * single 1 1)=C c := by
    rw [← mul_assoc]
    change single (-1:ℤ) (1:R) * single 0 c * single 1 1=single 0 c
    simp [single_mul_single]
  rw [h]
  ring

@[simp] lemma affineUnit_map (f : R →+* S) (c : R) :
    Units.map (mapRing f).toMonoidHom (affineUnit c)=affineUnit (f c) := by
  apply Units.ext
  simp

noncomputable def polynomial : Polynomial R →+* LaurentSeries R :=
  Polynomial.eval₂RingHom C (zUnit (R:=R) 1 : LaurentSeries R)

@[simp] lemma polynomial_C (r : R) : polynomial (Polynomial.C r)=C r := by
  simp [polynomial]

@[simp] lemma polynomial_X : polynomial (Polynomial.X : Polynomial R)=(zUnit (R:=R) 1 : LaurentSeries R) := by
  simp [polynomial]

lemma polynomial_monomial (n : ℕ) (r : R) :
    polynomial (Polynomial.monomial n r)=single (-(n:ℤ)) r := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,polynomial_C,polynomial_X,zUnit_val,
    single_pow]
  change single 0 r * single _ _=_
  simp [single_mul_single]

end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_QuantumTorusWallLeading
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
local instance instAddGroupTorus_r4e6ab0_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorus : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub

end
end ElementaryPositivity.QuantumTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_TorusContinuity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
local instance instAddGroupTorusLaurentSeriesRat_r4e6ab0_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
attribute [local instance] Classical.propDecidable

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Diagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.ShufflePolynomiality

open MvPolynomial

variable {α : Type*} [DecidableEq α]

noncomputable def diagonal (i j : α) : MvPolynomial α ℚ := X j - X i

def merge (i j x : α) : α := if x = j then i else x

noncomputable def identify (i j : α) : MvPolynomial α ℚ →ₐ[ℚ] MvPolynomial α ℚ :=
  rename (merge i j)

@[simp] lemma merge_left (i j : α) : merge i j i = i := by
  simp [merge]

@[simp] lemma merge_right (i j : α) : merge i j j = i := by
  simp [merge]

@[simp] lemma identify_diagonal (i j : α) : identify i j (diagonal i j) = 0 := by
  simp [identify, diagonal]

lemma diagonal_dvd_sub_identify (i j : α) (f : MvPolynomial α ℚ) :
    diagonal i j ∣ f - identify i j f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [identify]
  | add p q hp hq =>
    convert dvd_add hp hq using 1
    all_goals try with_reducible_and_instances rfl
    simp only [map_add]
    ring
  | mul_X p k hp =>
    have hx : diagonal i j ∣ X k - identify i j (X k) := by
      by_cases hk : k = j
      · subst k
        simp [identify, diagonal]
      · simp [identify, merge, hk]
    convert dvd_add (dvd_mul_of_dvd_left hp (X k))
      (dvd_mul_of_dvd_right hx (identify i j p)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [map_mul]
    ring

lemma diagonal_dvd_iff_identify_eq_zero (i j : α) (f : MvPolynomial α ℚ) :
    diagonal i j ∣ f ↔ identify i j f = 0 := by
  constructor
  · intro h
    simpa using map_dvd (identify i j) h
  · intro h
    simpa [h] using diagonal_dvd_sub_identify i j f

lemma ker_identify (i j : α) :
    RingHom.ker (identify i j) = Ideal.span {diagonal i j} := by
  ext f
  simp [RingHom.mem_ker, Ideal.mem_span_singleton, diagonal_dvd_iff_identify_eq_zero]

omit [DecidableEq α] in
lemma diagonal_ne_zero {i j : α} (hij : i ≠ j) : diagonal i j ≠ 0 := by
  simpa [diagonal, sub_eq_zero, MvPolynomial.X_inj] using hij.symm

lemma diagonal_prime {i j : α} (hij : i ≠ j) : Prime (diagonal i j) := by
  apply (Ideal.span_singleton_prime (diagonal_ne_zero hij)).mp
  rw [← ker_identify]
  exact RingHom.ker_isPrime _

lemma merge_swap (i j : α) : merge i j ∘ Equiv.swap i j = merge i j := by
  funext x
  by_cases hi : x = i
  · subst x
    simp
  · by_cases hj : x = j
    · subst x
      simp
    · simp [Equiv.swap_apply_of_ne_of_ne hi hj, Function.comp_apply]

theorem diagonal_dvd_of_antisymmetric (i j : α) (f : MvPolynomial α ℚ)
    (hf : rename (Equiv.swap i j) f = -f) : diagonal i j ∣ f := by
  apply (diagonal_dvd_iff_identify_eq_zero i j f).mpr
  have h := congrArg (identify i j) hf
  simp only [identify, MvPolynomial.rename_rename, merge_swap, map_neg] at h
  have hh : (2 : ℚ) • (rename (merge i j) f) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr h
  exact (smul_eq_zero.mp hh).resolve_left (by norm_num)

section UnorderedPairs

lemma merge_equal_pair {i j a b : α} (hab : a ≠ b)
    (h : merge i j a = merge i j b) :
    (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
  by_cases ha : a = j
  · subst a
    by_cases hb : b = j
    · exact (hab hb.symm).elim
    · simp only [merge, ite_eq_right hb] at h
      exact Or.inr ⟨rfl, h.symm⟩
  · by_cases hb : b = j
    · subst b
      simp only [merge, ite_eq_right ha] at h
      exact Or.inl ⟨h, rfl⟩
    · simp only [merge, ite_eq_right ha, ite_eq_right hb] at h
      exact (hab h).elim

lemma independent_diagonals {i j a b : α} (hij : i ≠ j) (hab : a ≠ b)
    (h₁ : (i,j) ≠ (a,b)) (h₂ : (i,j) ≠ (b,a)) :
    IsRelPrime (diagonal i j) (diagonal a b) := by
  apply (diagonal_prime hij).irreducible.isRelPrime_iff_not_dvd.mpr
  intro hd
  have hz := (diagonal_dvd_iff_identify_eq_zero i j _).mp hd
  have he : merge i j b = merge i j a := by
    simpa [identify, diagonal, sub_eq_zero, MvPolynomial.X_inj] using hz
  obtain (⟨ha,hb⟩ | ⟨ha,hb⟩) := merge_equal_pair hab he.symm
  · exact h₁ (by simp [ha, hb])
  · exact h₂ (by simp [ha, hb])

end UnorderedPairs

section Packs

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (V : I → Type*) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

def packAction : (∀ i, Equiv.Perm (V i)) →* Equiv.Perm (Σ i, V i) where
  toFun g := Equiv.sigmaCongrRight g
  map_one' := by apply Equiv.ext; rintro ⟨i,a⟩; rfl
  map_mul' g h := by apply Equiv.ext; rintro ⟨i,a⟩; rfl

def packSign (E : I → Prop) [DecidablePred E] :
    (∀ i, Equiv.Perm (V i)) →* ℤˣ where
  toFun g := ∏ i, if E i then Equiv.Perm.sign (g i) else 1
  map_one' := by simp
  map_mul' g h := by
    simp only [Pi.mul_apply, map_mul]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> simp

omit [Fintype I] [∀ i, Fintype (V i)] in
lemma packAction_transposition (i : I) (a b : V i) :
    packAction V (Function.update 1 i (Equiv.swap a b)) =
      Equiv.swap (⟨i,a⟩ : Σ i,V i) ⟨i,b⟩ := by
  apply Equiv.ext
  rintro ⟨j,c⟩
  by_cases hj : j = i
  · subst j
    change (⟨i, (Function.update (1 : ∀ i, Equiv.Perm (V i)) i (Equiv.swap a b)) i c⟩ : Σ i,V i) = _
    rw [Function.update_self]
    simp only [Equiv.swap_apply_def, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    split_ifs <;> rfl
  · change (⟨j, (Function.update (1 : ∀ i, Equiv.Perm (V i)) i (Equiv.swap a b)) j c⟩ : Σ i,V i) = _
    rw [Function.update_of_ne hj]
    exact (Equiv.swap_apply_of_ne_of_ne
      (fun h => hj (congrArg Sigma.fst h))
      (fun h => hj (congrArg Sigma.fst h))).symm

lemma packSign_transposition (E : I → Prop) [DecidablePred E]
    (i : I) (a b : V i) (hi : E i) (hab : a ≠ b) :
    packSign V E (Function.update 1 i (Equiv.swap a b)) = -1 := by
  change (∏ j, if E j then
    Equiv.Perm.sign ((Function.update (1 : ∀ i, Equiv.Perm (V i)) i
      (Equiv.swap a b)) j) else 1) = -1
  rw [Fintype.prod_eq_single i]
  · simp [hi, Equiv.Perm.sign_swap hab]
  · intro j hji
    simp [Function.update_of_ne hji]

end Packs

section FinPacks
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (n : I → ℕ) (E : I → Prop) [DecidablePred E]

noncomputable def naturalVandermonde : MvPolynomial (Σ i, Fin (n i)) ℚ :=
  ∏ i, if E i then (Matrix.vandermonde (fun a : Fin (n i) =>
    (X ⟨i,a⟩ : MvPolynomial (Σ i, Fin (n i)) ℚ))).det else 1

def finPackPair (a : Σ i, Fin (n i) × Fin (n i)) :
    (Σ i, Fin (n i)) × (Σ i, Fin (n i)) :=
  (⟨a.1,a.2.1⟩, ⟨a.1,a.2.2⟩)

omit [Fintype I] [DecidableEq I] in
lemma finPackPair_injective : Function.Injective (finPackPair n) := by
  rintro ⟨i,a,b⟩ ⟨j,c,d⟩ h
  have hij : i = j := congrArg (fun p => p.1.1) h
  subst j
  simp only [finPackPair, Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  obtain ⟨rfl,rfl⟩ := h
  rfl

noncomputable def naturalPairs : Finset (Σ i, Fin (n i) × Fin (n i)) :=
  Finset.univ.sigma (fun i => (Finset.univ ×ˢ Finset.univ).filter
    (fun ab : Fin (n i) × Fin (n i) => E i ∧ ab.1 < ab.2))

omit [DecidableEq I] in
lemma naturalVandermonde_product : naturalVandermonde n E =
    ∏ a ∈ naturalPairs n E, diagonal (finPackPair n a).1 (finPackPair n a).2 := by
  rw [naturalVandermonde, naturalPairs, Finset.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : E i
  · simp only [hi, ite_true, if_true, Matrix.det_vandermonde, true_and]
    rw [Finset.prod_filter, Finset.prod_product]
    apply Finset.prod_congr rfl
    intro a _
    simp only [← Finset.filter_lt_eq_Ioi, Finset.prod_filter, diagonal, finPackPair]
  · simp [hi]

omit [DecidableEq I] in
lemma rename_naturalVandermonde (g : ∀ i, Equiv.Perm (Fin (n i))) :
    rename (packAction (fun i => Fin (n i)) g) (naturalVandermonde n E) =
      (packSign (fun i => Fin (n i)) E g : ℤ) • naturalVandermonde n E := by
  rw [naturalVandermonde, map_prod]
  simp only [packSign, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod,
    zsmul_eq_mul, Int.cast_prod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : E i
  · simp only [hi, ite_true, if_true]
    change ((rename (packAction (fun i => Fin (n i)) g)).toRingHom)
      (Matrix.vandermonde (fun a : Fin (n i) => X ⟨i,a⟩)).det = _
    rw [RingHom.map_det]
    have hm : (rename (packAction (fun i => Fin (n i)) g)).toRingHom.mapMatrix
        (Matrix.vandermonde (fun a : Fin (n i) =>
          (X ⟨i,a⟩ : MvPolynomial (Σ i, Fin (n i)) ℚ))) =
        (Matrix.vandermonde (fun a : Fin (n i) =>
          (X ⟨i,a⟩ : MvPolynomial (Σ i, Fin (n i)) ℚ))).submatrix (g i) id := by
      ext a b
      simp [Matrix.vandermonde, Matrix.submatrix_apply, packAction]
    rw [hm, Matrix.det_permute]
  · simp [hi]

end FinPacks

end ElementaryPositivity.ShufflePolynomiality
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_RenameFraction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.ShufflePolynomiality
open MvPolynomial
variable {α : Type*} [DecidableEq α]
section FractionRename
variable {α : Type*} [DecidableEq α]

noncomputable def renameFraction (σ : Equiv.Perm α) :
    FractionRing (MvPolynomial α ℚ) →+* FractionRing (MvPolynomial α ℚ) :=
  IsFractionRing.lift (g := (algebraMap (MvPolynomial α ℚ)
    (FractionRing (MvPolynomial α ℚ))).comp (rename σ).toRingHom)
      ((IsFractionRing.injective (MvPolynomial α ℚ)
        (FractionRing (MvPolynomial α ℚ))).comp (rename_injective σ σ.injective))

omit [DecidableEq α] in
@[simp] lemma renameFraction_algebraMap (σ : Equiv.Perm α) (f : MvPolynomial α ℚ) :
    renameFraction σ (algebraMap (MvPolynomial α ℚ) (FractionRing (MvPolynomial α ℚ)) f) =
      algebraMap (MvPolynomial α ℚ) (FractionRing (MvPolynomial α ℚ)) (rename σ f) :=
  IsFractionRing.lift_algebraMap _ _

end FractionRename

section RationalAverage
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (n : I → ℕ) (E : I → Prop) [DecidablePred E]

omit [DecidableEq I] in
lemma naturalVandermonde_ne_zero : naturalVandermonde n E ≠ 0 := by
  rw [naturalVandermonde_product, Finset.prod_ne_zero_iff]
  rintro ⟨i,a,b⟩ ha
  simp only [naturalPairs, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
    Finset.mem_product, true_and] at ha
  apply diagonal_ne_zero
  simpa [finPackPair] using ha.2.ne

end RationalAverage

section InvariantPoles
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (n : I → ℕ)
local notation "P" => MvPolynomial (Σ i, Fin (n i)) ℚ
local notation "K" => FractionRing P

lemma packed_pairs_product_dvd
    (s : ∀ i, Finset (Fin (n i) × Fin (n i))) (f : P)
    (hne : ∀ i ab, ab ∈ s i → ab.1 ≠ ab.2)
    (hrev : ∀ i ab, ab ∈ s i → (ab.2, ab.1) ∉ s i)
    (hf : ∀ i ab, ab ∈ s i → diagonal ⟨i,ab.1⟩ ⟨i,ab.2⟩ ∣ f) :
    (∏ i, ∏ ab ∈ s i, diagonal ⟨i,ab.1⟩ ⟨i,ab.2⟩) ∣ f := by
  suffices h : (∏ a ∈ Finset.univ.sigma s,
      diagonal (finPackPair n a).1 (finPackPair n a).2) ∣ f by
    simpa only [Finset.prod_sigma, finPackPair] using h
  apply Finset.prod_dvd_of_isRelPrime
  · rintro ⟨i,a,b⟩ hi ⟨j,c,d⟩ hj hdiff
    change (⟨i,(a,b)⟩ : Σ i, Fin (n i) × Fin (n i)) ∈ Finset.univ.sigma s at hi
    change (⟨j,(c,d)⟩ : Σ i, Fin (n i) × Fin (n i)) ∈ Finset.univ.sigma s at hj
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hi hj
    apply independent_diagonals
      (by simpa [finPackPair] using hne i (a,b) hi) (by simpa [finPackPair] using hne j (c,d) hj)
    · exact fun h => hdiff (finPackPair_injective n h)
    · intro hr
      have hij : i = j := congrArg (fun p => p.1.1) hr
      subst j
      simp only [finPackPair, Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hr
      obtain ⟨rfl,rfl⟩ := hr
      exact hrev i (a,b) hi hj
  · rintro ⟨i,a,b⟩ hi
    exact hf i (a,b) (Finset.mem_sigma.mp hi).2

omit [DecidableEq I] in
lemma diagonal_dvd_naturalVandermonde (i : I) (a b : Fin (n i)) (hab : a ≠ b) :
    diagonal ⟨i,a⟩ ⟨i,b⟩ ∣ naturalVandermonde n (fun _ => True) := by
  have hlt (x y : Fin (n i)) (hxy : x < y) :
      diagonal ⟨i,x⟩ ⟨i,y⟩ ∣ naturalVandermonde n (fun _ => True) := by
    rw [naturalVandermonde_product]
    exact Finset.dvd_prod_of_mem
      (fun a : Σ i,Fin (n i) × Fin (n i) => diagonal (finPackPair n a).1 (finPackPair n a).2)
      (a := ⟨i,(x,y)⟩) (by simp only [naturalPairs, Finset.mem_sigma, Finset.mem_univ,
        Finset.mem_filter, Finset.mem_product, true_and]; exact hxy)
  rcases lt_or_gt_of_ne hab with h|h
  · exact hlt a b h
  · have hd := hlt b a h
    have he : diagonal (⟨i,a⟩ : Σi,Fin (n i)) ⟨i,b⟩ = -diagonal ⟨i,b⟩ ⟨i,a⟩ := by
      simp only [diagonal] <;> ring
    rw [he]
    exact neg_dvd.mpr hd

theorem invariant_fraction_regular (F : K)
    (hsym : ∀ g : ∀i, Equiv.Perm (Fin (n i)),
      renameFraction (packAction (fun i => Fin (n i)) g) F = F)
    (hreg : ∃ N : P, algebraMap P K (naturalVandermonde n (fun _ => True)) * F =
      algebraMap P K N) :
    ∃ q : P, F = algebraMap P K q := by
  obtain ⟨N,hN⟩ := hreg
  let V := fun i => Fin (n i)
  let D := naturalVandermonde n (fun _ => True)
  have hDK : algebraMap P K D ≠ 0 := by
    intro h
    apply naturalVandermonde_ne_zero n (fun _ => True)
    exact (IsFractionRing.injective P K) (by simpa using h)
  have hanti (i : I) (a b : Fin (n i)) (hab : a ≠ b) :
      rename (Equiv.swap (⟨i,a⟩ : Σi,Fin (n i)) ⟨i,b⟩) N = -N := by
    let t : ∀i, Equiv.Perm (V i) := Function.update 1 i (Equiv.swap a b)
    have ht := congrArg (renameFraction (packAction V t)) hN
    rw [map_mul, renameFraction_algebraMap, renameFraction_algebraMap, hsym] at ht
    have hsign : packSign V (fun _ => True) t = -1 :=
      packSign_transposition V (fun _ => True) i a b trivial hab
    rw [rename_naturalVandermonde, hsign] at ht
    simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, map_neg, neg_mul] at ht
    rw [hN] at ht
    have hpoly : rename (packAction V t) N = -N :=
      (IsFractionRing.injective P K) (by simpa using ht.symm)
    simpa only [t, V, packAction_transposition] using hpoly
  have hd : D ∣ N := by
    change naturalVandermonde n (fun _ => True) ∣ N
    rw [naturalVandermonde_product]
    apply Finset.prod_dvd_of_isRelPrime
    · rintro ⟨i,a,b⟩ hi ⟨j,c,d⟩ hj hdiff
      change (⟨i,(a,b)⟩ : Σ i,Fin (n i) × Fin (n i)) ∈ naturalPairs n (fun _ => True) at hi
      change (⟨j,(c,d)⟩ : Σ i,Fin (n i) × Fin (n i)) ∈ naturalPairs n (fun _ => True) at hj
      simp only [naturalPairs, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
        Finset.mem_product, true_and] at hi hj
      apply independent_diagonals (by simpa [finPackPair] using hi.ne) (by simpa [finPackPair] using hj.ne)
      · exact fun h => hdiff (finPackPair_injective n h)
      · intro hr
        have hij : i = j := congrArg (fun p => p.1.1) hr
        subst j
        simp only [finPackPair, Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hr
        obtain ⟨rfl,rfl⟩ := hr
        exact lt_asymm hi hj
    · rintro ⟨i,a,b⟩ hi
      simp only [naturalPairs, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
        Finset.mem_product, true_and] at hi
      exact diagonal_dvd_of_antisymmetric _ _ N (hanti i a b hi.ne)
  obtain ⟨q,hq⟩ := hd
  refine ⟨q, ?_⟩
  apply mul_left_cancel₀ hDK
  change algebraMap P K D * F = _
  rw [hN, hq, map_mul]

end InvariantPoles

end ElementaryPositivity.ShufflePolynomiality

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Cut
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality

variable {I : Type*} [Fintype I] [DecidableEq I]

def Cut (d e : I → ℕ) := ∀ i, {s : Finset (Fin (d i + e i)) // s.card = d i}

instance instFintypeCut (d e : I → ℕ) : Fintype (Cut d e) := by unfold Cut; infer_instance

variable {d e : I → ℕ}

noncomputable def cutPerm (g : ∀ i, Equiv.Perm (Fin (d i + e i))) : Cut d e ≃ Cut d e :=
  Equiv.piCongrRight (fun i => (g i).finsetCongr.subtypeEquiv (fun s => by
    simp [Equiv.finsetCongr_apply]))

omit [Fintype I] [DecidableEq I] in
@[simp] lemma cutPerm_val (g : ∀ i, Equiv.Perm (Fin (d i + e i))) (A : Cut d e) (i : I) :
    (cutPerm g A i).val = (A i).val.map (g i).toEmbedding := rfl

omit [Fintype I] [DecidableEq I] in
@[simp] lemma mem_cutPerm (g : ∀ i, Equiv.Perm (Fin (d i + e i))) (A : Cut d e)
    (i : I) (a : Fin (d i + e i)) :
    g i a ∈ (cutPerm g A i).val ↔ a ∈ (A i).val := by
  simp

noncomputable def leftEnum (A : Cut d e) (i : I) : Fin (d i) ≃ (A i).val :=
  ((A i).val.orderIsoOfFin (A i).property).toEquiv

omit [Fintype I] [DecidableEq I] in
lemma right_card (A : Cut d e) (i : I) : (A i).valᶜ.card = e i := by
  rw [Finset.card_compl, Fintype.card_fin, (A i).property, Nat.add_sub_cancel_left]

noncomputable def rightEnum (A : Cut d e) (i : I) : Fin (e i) ≃ ↥((A i).valᶜ) :=
  ((A i).valᶜ.orderIsoOfFin (right_card A i)).toEquiv

noncomputable def leftInput (A : Cut d e) : (Σ i,Fin (d i)) → (Σ i,Fin (d i + e i)) :=
  fun a => ⟨a.1, leftEnum A a.1 a.2⟩

noncomputable def rightInput (A : Cut d e) : (Σ i,Fin (e i)) → (Σ i,Fin (d i + e i)) :=
  fun a => ⟨a.1, rightEnum A a.1 a.2⟩

noncomputable def leftImageEquiv (g : ∀ i, Equiv.Perm (Fin (d i + e i)))
    (A : Cut d e) (i : I) : (A i).val ≃ (cutPerm g A i).val :=
  (g i).subtypeEquiv (fun _ => (mem_cutPerm g A i _).symm)

noncomputable def rightImageEquiv (g : ∀ i, Equiv.Perm (Fin (d i + e i)))
    (A : Cut d e) (i : I) : ↥((A i).valᶜ) ≃ ↥((cutPerm g A i).valᶜ) :=
  (g i).subtypeEquiv (by intro a; simp only [Finset.mem_compl, mem_cutPerm])

noncomputable def leftReindex (g : ∀ i, Equiv.Perm (Fin (d i + e i)))
    (A : Cut d e) (i : I) : Equiv.Perm (Fin (d i)) :=
  (leftEnum A i).trans ((leftImageEquiv g A i).trans (leftEnum (cutPerm g A) i).symm)

noncomputable def rightReindex (g : ∀ i, Equiv.Perm (Fin (d i + e i)))
    (A : Cut d e) (i : I) : Equiv.Perm (Fin (e i)) :=
  (rightEnum A i).trans ((rightImageEquiv g A i).trans (rightEnum (cutPerm g A) i).symm)

omit [Fintype I] [DecidableEq I] in
lemma leftInput_reindex (g : ∀ i, Equiv.Perm (Fin (d i + e i))) (A : Cut d e) :
    leftInput (cutPerm g A) ∘ packAction (fun i => Fin (d i)) (leftReindex g A) =
      packAction (fun i => Fin (d i + e i)) g ∘ leftInput A := by
  funext ⟨i,a⟩
  change (⟨i, ↑(leftEnum (cutPerm g A) i (leftReindex g A i a))⟩ : Σi,Fin (d i + e i)) =
    ⟨i,g i ↑(leftEnum A i a)⟩
  simp only [leftReindex, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma rightInput_reindex (g : ∀ i, Equiv.Perm (Fin (d i + e i))) (A : Cut d e) :
    rightInput (cutPerm g A) ∘ packAction (fun i => Fin (e i)) (rightReindex g A) =
      packAction (fun i => Fin (d i + e i)) g ∘ rightInput A := by
  funext ⟨i,a⟩
  change (⟨i, ↑(rightEnum (cutPerm g A) i (rightReindex g A i a))⟩ : Σi,Fin (d i + e i)) =
    ⟨i,g i ↑(rightEnum A i a)⟩
  simp only [rightReindex, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

def PackSymmetric (d : I → ℕ) (f : MvPolynomial (Σ i,Fin (d i)) ℚ) : Prop :=
  ∀ g : ∀i, Equiv.Perm (Fin (d i)), rename (packAction (fun i => Fin (d i)) g) f = f

omit [Fintype I] [DecidableEq I] in
lemma rename_leftInput (f : MvPolynomial (Σ i,Fin (d i)) ℚ) (hf : PackSymmetric d f)
    (g : ∀ i, Equiv.Perm (Fin (d i + e i))) (A : Cut d e) :
    rename (packAction (fun i => Fin (d i + e i)) g) (rename (leftInput A) f) =
      rename (leftInput (cutPerm g A)) f := by
  rw [MvPolynomial.rename_rename, ← leftInput_reindex, ← MvPolynomial.rename_rename, hf]

omit [Fintype I] [DecidableEq I] in
lemma rename_rightInput (f : MvPolynomial (Σ i,Fin (e i)) ℚ) (hf : PackSymmetric e f)
    (g : ∀ i, Equiv.Perm (Fin (d i + e i))) (A : Cut d e) :
    rename (packAction (fun i => Fin (d i + e i)) g) (rename (rightInput A) f) =
      rename (rightInput (cutPerm g A)) f := by
  rw [MvPolynomial.rename_rename, ← rightInput_reindex, ← MvPolynomial.rename_rename, hf]

omit [Fintype I] [DecidableEq I] in
@[simp] lemma cutPerm_compl (g : ∀ i, Equiv.Perm (Fin (d i + e i)))
    (A : Cut d e) (i : I) :
    (cutPerm g A i).valᶜ = (A i).valᶜ.map (g i).toEmbedding := by
  ext b
  obtain ⟨a,rfl⟩ := (g i).surjective b
  simp

local notation "P" => MvPolynomial (Σ i, Fin (d i + e i)) ℚ
local notation "K" => FractionRing (MvPolynomial (Σ i, Fin (d i + e i)) ℚ)

noncomputable def cutFactor (A : Cut d e) (i j : I) (k : ℕ) : P :=
  ∏ a ∈ (A i).val, ∏ b ∈ (A j).valᶜ, (diagonal ⟨i,a⟩ ⟨j,b⟩)^k

omit [Fintype I] [DecidableEq I] in
lemma rename_cutFactor (g : ∀ i, Equiv.Perm (Fin (d i + e i)))
    (A : Cut d e) (i j : I) (k : ℕ) :
    rename (packAction (fun i => Fin (d i + e i)) g) (cutFactor A i j k) =
      cutFactor (cutPerm g A) i j k := by
  simp only [cutFactor]
  rw [cutPerm_compl, cutPerm_val]
  simp only [map_prod, map_pow, diagonal, map_sub, rename_X,
    Finset.prod_map, Function.Embedding.coeFn_mk]
  rfl

noncomputable def cutDenominator (A : Cut d e) : P := ∏ i, cutFactor A i i 1

noncomputable def cutNumerator (a : I → I → ℕ) (A : Cut d e)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) : P :=
  rename (leftInput A) f * rename (rightInput A) g * ∏ i, ∏ j, cutFactor A i j (a i j)

omit [DecidableEq I] in
lemma rename_cutDenominator (g : ∀ i, Equiv.Perm (Fin (d i + e i))) (A : Cut d e) :
    rename (packAction (fun i => Fin (d i + e i)) g) (cutDenominator A) =
      cutDenominator (cutPerm g A) := by
  simp only [cutDenominator, map_prod, rename_cutFactor]

omit [DecidableEq I] in
lemma rename_cutNumerator (a : I → I → ℕ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (hf : PackSymmetric d f)
    (g : MvPolynomial (Σi,Fin (e i)) ℚ) (hg : PackSymmetric e g)
    (σ : ∀ i, Equiv.Perm (Fin (d i + e i))) (A : Cut d e) :
    rename (packAction (fun i => Fin (d i + e i)) σ) (cutNumerator a A f g) =
      cutNumerator a (cutPerm σ A) f g := by
  simp only [cutNumerator, map_mul, map_prod, rename_cutFactor,
    rename_leftInput f hf, rename_rightInput g hg]

lemma cutDenominator_dvd (A : Cut d e) :
    cutDenominator A ∣ naturalVandermonde (fun i => d i + e i) (fun _ => True) := by
  change (∏i,cutFactor A i i 1) ∣ _
  have he : ∀ i, cutFactor A i i 1 =
      ∏ ab ∈ ((A i).val ×ˢ (A i).valᶜ), diagonal (⟨i,ab.1⟩ : Σi,Fin (d i+e i)) ⟨i,ab.2⟩ := by
    intro i
    simp only [cutFactor, pow_one, Finset.prod_product]
  simp_rw [he]
  apply packed_pairs_product_dvd
  · intro i ab hab heq
    have hm := Finset.mem_product.mp hab
    exact (Finset.mem_compl.mp hm.2) (heq ▸ hm.1)
  · intro i ab hab hba
    have h1 := Finset.mem_product.mp hab
    have h2 := Finset.mem_product.mp hba
    exact (Finset.mem_compl.mp h1.2) h2.1
  · intro i ab hab
    apply diagonal_dvd_naturalVandermonde
    intro heq
    have hm := Finset.mem_product.mp hab
    exact (Finset.mem_compl.mp hm.2) (heq ▸ hm.1)

lemma cutDenominator_ne_zero (A : Cut d e) : cutDenominator A ≠ 0 :=
  ne_zero_of_dvd_ne_zero (naturalVandermonde_ne_zero _ (fun _ => True))
    (cutDenominator_dvd A)

noncomputable def rawShuffle (a : I → I → ℕ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) : K :=
  ∑ A : Cut d e, algebraMap P K (cutNumerator a A f g) /
    algebraMap P K (cutDenominator A)

lemma rawShuffle_symmetric (a : I → I → ℕ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (hf : PackSymmetric d f)
    (g : MvPolynomial (Σi,Fin (e i)) ℚ) (hg : PackSymmetric e g)
    (σ : ∀ i, Equiv.Perm (Fin (d i + e i))) :
    renameFraction (packAction (fun i => Fin (d i + e i)) σ) (rawShuffle a f g) =
      rawShuffle a f g := by
  simp only [rawShuffle, map_sum, map_div₀, renameFraction_algebraMap,
    rename_cutNumerator a f hf g hg, rename_cutDenominator]
  exact Equiv.sum_comp (cutPerm σ) (fun A : Cut d e =>
    algebraMap P K (cutNumerator a A f g) / algebraMap P K (cutDenominator A))

lemma rawShuffle_regular (a : I → I → ℕ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    ∃ N : P, algebraMap P K (naturalVandermonde (fun i => d i + e i) (fun _ => True)) *
      rawShuffle a f g = algebraMap P K N := by
  have hterms (A : Cut d e) : ∃ N : P,
      algebraMap P K (naturalVandermonde (fun i => d i + e i) (fun _ => True)) *
        (algebraMap P K (cutNumerator a A f g) / algebraMap P K (cutDenominator A)) =
      algebraMap P K N := by
    obtain ⟨b,hb⟩ := cutDenominator_dvd A
    refine ⟨b * cutNumerator a A f g, ?_⟩
    have hne : algebraMap P K (cutDenominator A) ≠ 0 :=
      by
        intro hz
        apply cutDenominator_ne_zero A
        exact (IsFractionRing.injective P K) (by simpa using hz)
    rw [hb, map_mul, map_mul]
    field_simp
  choose N hN using hterms
  refine ⟨∑A,N A, ?_⟩
  simp only [rawShuffle, Finset.mul_sum, hN, map_sum]

theorem rawShuffle_polynomial (a : I → I → ℕ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (hf : PackSymmetric d f)
    (g : MvPolynomial (Σi,Fin (e i)) ℚ) (hg : PackSymmetric e g) :
    ∃ h : P, PackSymmetric (fun i => d i + e i) h ∧
      rawShuffle a f g = algebraMap P K h := by
  obtain ⟨h,hh⟩ := invariant_fraction_regular _ (rawShuffle a f g)
    (rawShuffle_symmetric a f hf g hg) (rawShuffle_regular a f g)
  refine ⟨h,?_,hh⟩
  intro σ
  apply IsFractionRing.injective P K
  rw [← renameFraction_algebraMap, ← hh, rawShuffle_symmetric a f hf g hg σ]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SymmetricSpace
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]

def symmetricSpace (d : I → ℕ) : Subalgebra ℚ (MvPolynomial (Σi, Fin (d i)) ℚ) where
  carrier := {f | PackSymmetric d f}
  mul_mem' := by intro f g hf hg σ; simp only [map_mul, hf σ, hg σ]
  one_mem' := by intro σ; exact map_one _
  add_mem' := by intro f g hf hg σ; simp only [map_add, hf σ, hg σ]
  zero_mem' := by intro σ; exact map_zero _
  algebraMap_mem' := by intro r σ; simp

abbrev S (d : I → ℕ) := ↥(symmetricSpace d)

noncomputable def shufflePolynomial (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g : S e) : S (d+e) :=
  ⟨Classical.choose (rawShuffle_polynomial a f.val f.property g.val g.property),
    (Classical.choose_spec (rawShuffle_polynomial a f.val f.property g.val g.property)).1⟩

lemma shufflePolynomial_eq (a : I → I → ℕ) {d e : I → ℕ} (f : S d) (g : S e) :
    algebraMap _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
      (shufflePolynomial a f g).val = rawShuffle a f.val g.val :=
  (Classical.choose_spec (rawShuffle_polynomial a f.val f.property g.val g.property)).2.symm

lemma rawShuffle_add_left (a : I → I → ℕ) {d e : I → ℕ}
    (f f' : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    rawShuffle a (f+f') g = rawShuffle a f g + rawShuffle a f' g := by
  simp only [rawShuffle, cutNumerator, map_add, add_mul, add_div,
    Finset.sum_add_distrib]

lemma rawShuffle_add_right (a : I → I → ℕ) {d e : I → ℕ}
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g g' : MvPolynomial (Σi,Fin (e i)) ℚ) :
    rawShuffle a f (g+g') = rawShuffle a f g + rawShuffle a f g' := by
  simp only [rawShuffle, cutNumerator, map_add, mul_add, add_mul, add_div,
    Finset.sum_add_distrib]

lemma rawShuffle_smul_left (a : I → I → ℕ) {d e : I → ℕ} (r : ℚ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    rawShuffle a (r • f) g = r • rawShuffle a f g := by
  let : DistribSMul ℚ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ)) :=
    (inferInstance : Module ℚ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))).toDistribMulAction.toDistribSMul
  simp only [rawShuffle, cutNumerator, map_smul, map_rat_smul, smul_mul_assoc,
    div_eq_mul_inv, smul_mul_assoc, Finset.smul_sum]

lemma rawShuffle_smul_right (a : I → I → ℕ) {d e : I → ℕ} (r : ℚ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    rawShuffle a f (r • g) = r • rawShuffle a f g := by
  let : DistribSMul ℚ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ)) :=
    (inferInstance : Module ℚ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))).toDistribMulAction.toDistribSMul
  simp only [rawShuffle, cutNumerator, map_smul, map_rat_smul, mul_smul_comm, smul_mul_assoc,
    div_eq_mul_inv, smul_mul_assoc, Finset.smul_sum]

@[simp] lemma shufflePolynomial_add_left (a : I → I → ℕ) {d e : I → ℕ}
    (f f' : S d) (g : S e) :
    shufflePolynomial a (f+f') g = shufflePolynomial a f g + shufflePolynomial a f' g := by
  apply Subtype.ext
  apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
  simp only [Subalgebra.coe_add, map_add, shufflePolynomial_eq, rawShuffle_add_left]

@[simp] lemma shufflePolynomial_add_right (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g g' : S e) :
    shufflePolynomial a f (g+g') = shufflePolynomial a f g + shufflePolynomial a f g' := by
  apply Subtype.ext
  apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
  simp only [Subalgebra.coe_add, map_add, shufflePolynomial_eq, rawShuffle_add_right]

@[simp] lemma shufflePolynomial_smul_left (a : I → I → ℕ) {d e : I → ℕ} (r : ℚ)
    (f : S d) (g : S e) : shufflePolynomial a (r • f) g = r • shufflePolynomial a f g := by
  apply Subtype.ext
  apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
  simp only [Subalgebra.coe_smul, map_rat_smul, shufflePolynomial_eq, rawShuffle_smul_left]

@[simp] lemma shufflePolynomial_smul_right (a : I → I → ℕ) {d e : I → ℕ} (r : ℚ)
    (f : S d) (g : S e) : shufflePolynomial a f (r • g) = r • shufflePolynomial a f g := by
  apply Subtype.ext
  apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
  simp only [Subalgebra.coe_smul, map_rat_smul, shufflePolynomial_eq, rawShuffle_smul_right]

noncomputable def shuffleLinear (a : I → I → ℕ) (d e : I → ℕ) :
    S d →ₗ[ℚ] S e →ₗ[ℚ] S (d+e) where
  toFun f :=
    { toFun := shufflePolynomial a f
      map_add' := shufflePolynomial_add_right a f
      map_smul' := fun r g => shufflePolynomial_smul_right a r f g }
  map_add' f f' := by apply LinearMap.ext; intro g; exact shufflePolynomial_add_left a f f' g
  map_smul' r f := by apply LinearMap.ext; intro g; exact shufflePolynomial_smul_left a r f g

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def translation {α : Type*} (t : ℚ) :
    MvPolynomial α ℚ →ₐ[ℚ] MvPolynomial α ℚ :=
  aeval fun i => X i + C t

@[simp] lemma translation_X {α : Type*} (t : ℚ) (i : α) :
    translation t (X i) = X i + C t := by simp [translation]
@[simp] lemma translation_C {α : Type*} (t r : ℚ) :
    translation (α := α) t (C r) = C r := by simp [translation]

lemma translation_rename {α β : Type*} (t : ℚ) (f : α → β) (p : MvPolynomial α ℚ) :
    translation t (rename f p) = rename f (translation t p) := by
  have h : (translation t).comp (rename f) = (rename f).comp (translation t) := by
    ext i; simp
  exact DFunLike.congr_fun h p

@[simp] lemma translation_zero {α : Type*} (p : MvPolynomial α ℚ) :
    translation 0 p = p := by
  have h : translation (α := α) 0 = AlgHom.id ℚ _ := by ext i; simp
  exact DFunLike.congr_fun h p

noncomputable def translationEquiv {α : Type*} (t : ℚ) :
    MvPolynomial α ℚ ≃ₐ[ℚ] MvPolynomial α ℚ :=
  AlgEquiv.ofAlgHom (translation t) (translation (-t))
    (by ext p; simp [AlgHom.comp_apply])
    (by ext p; simp [AlgHom.comp_apply])

noncomputable def translationFraction {α : Type*} (t : ℚ) :
    FractionRing (MvPolynomial α ℚ) →+* FractionRing (MvPolynomial α ℚ) :=
  IsFractionRing.lift (g := (algebraMap _ _).comp (translation (α := α) t).toRingHom)
    ((IsFractionRing.injective _ (FractionRing (MvPolynomial α ℚ))).comp
      (translationEquiv t).injective)

@[simp] lemma translationFraction_algebraMap {α : Type*} (t : ℚ) (p : MvPolynomial α ℚ) :
    translationFraction t (algebraMap _ (FractionRing (MvPolynomial α ℚ)) p) =
      algebraMap _ (FractionRing (MvPolynomial α ℚ)) (translation t p) := by
  apply IsFractionRing.lift_algebraMap

@[simp] lemma translation_diagonal {α : Type*} (t : ℚ) (i j : α) :
    translation t (diagonal i j) = diagonal i j := by
  simp [diagonal]

omit [Fintype I] [DecidableEq I] in
lemma translation_cutFactor {d e : I → ℕ} (t : ℚ) (A : Cut d e) (i j : I) (k : ℕ) :
    translation t (cutFactor A i j k) = cutFactor A i j k := by
  simp [cutFactor]

omit [DecidableEq I] in
lemma translation_cutDenominator {d e : I → ℕ} (t : ℚ) (A : Cut d e) :
    translation t (cutDenominator A) = cutDenominator A := by
  simp [cutDenominator, translation_cutFactor]

omit [DecidableEq I] in
lemma translation_cutNumerator (a : I → I → ℕ) {d e : I → ℕ} (t : ℚ) (A : Cut d e)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    translation t (cutNumerator a A f g) =
      cutNumerator a A (translation t f) (translation t g) := by
  simp [cutNumerator, translation_rename, translation_cutFactor]

lemma translation_rawShuffle (a : I → I → ℕ) {d e : I → ℕ} (t : ℚ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    translationFraction t (rawShuffle a f g) =
      rawShuffle a (translation t f) (translation t g) := by
  simp only [rawShuffle, map_sum, map_div₀, translationFraction_algebraMap,
    translation_cutNumerator, translation_cutDenominator]

omit [Fintype I] [DecidableEq I] in
lemma translation_symmetric {d : I → ℕ} (t : ℚ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (hf : PackSymmetric d f) :
    PackSymmetric d (translation t f) := by
  intro σ
  rw [← translation_rename, hf σ]

noncomputable def translationS (d : I → ℕ) (t : ℚ) : S d →ₗ[ℚ] S d :=
  { toFun := fun f => ⟨translation t f.val, translation_symmetric t f.val f.property⟩
    map_add' := by intros; apply Subtype.ext; apply map_add
    map_smul' := by intros; apply Subtype.ext; apply map_smul }

lemma translation_shufflePolynomial (a : I → I → ℕ) {d e : I → ℕ} (t : ℚ)
    (f : S d) (g : S e) :
    translationS (d+e) t (shufflePolynomial a f g) =
      shufflePolynomial a (translationS d t f) (translationS e t g) := by
  apply Subtype.ext
  apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
  change algebraMap _ _ (translation t (shufflePolynomial a f g).val) = _
  calc
    _ = translationFraction t
        (algebraMap _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
          (shufflePolynomial a f g).val) :=
      (translationFraction_algebraMap t (shufflePolynomial a f g).val).symm
    _ = _ := by
      rw [shufflePolynomial_eq, translation_rawShuffle, shufflePolynomial_eq]
      rfl

noncomputable def dimensionCast {d e : I → ℕ} (h : d = e) : S d →ₗ[ℚ] S e :=
  h ▸ LinearMap.id

omit [Fintype I] [DecidableEq I] in
@[simp] lemma dimensionCast_rfl (d : I → ℕ) (f : S d) :
    dimensionCast rfl f = f := rfl

omit [Fintype I] [DecidableEq I] in
lemma translation_dimensionCast {d e : I → ℕ} (h : d = e) (t : ℚ) (f : S d) :
    translationS e t (dimensionCast h f) = dimensionCast h (translationS d t f) := by
  subst e; rfl

def destabilizingGenerators (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) : Set (S d) :=
  { F | ∃ (u v : I → ℕ) (h : u+v=d) (f : S u) (g : S v),
      u ≠ 0 ∧ v ≠ 0 ∧ μ u > μ d ∧ F = dimensionCast h (shufflePolynomial a f g) }

noncomputable def destabilizingSpace (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    Submodule ℚ (S d) := Submodule.span ℚ (destabilizingGenerators a μ d)

lemma translation_generator (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (t : ℚ) {f : S d} (hf : f ∈ destabilizingGenerators a μ d) :
    translationS d t f ∈ destabilizingGenerators a μ d := by
  obtain ⟨u,v,h,f,g,hu,hv,hμ,rfl⟩ := hf
  refine ⟨u,v,h,translationS u t f,translationS v t g,hu,hv,hμ,?_⟩
  rw [translation_dimensionCast, translation_shufflePolynomial]

lemma translation_destabilizing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (t : ℚ) :
    destabilizingSpace a μ d ≤
      (destabilizingSpace a μ d).comap (translationS d t) := by
  apply Submodule.span_le.mpr
  intro f hf
  exact Submodule.subset_span (translation_generator a μ d t hf)

abbrev B (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :=
  S d ⧸ destabilizingSpace a μ d

noncomputable def translationB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (t : ℚ) : B a μ d →ₗ[ℚ] B a μ d :=
  (destabilizingSpace a μ d).mapQ (destabilizingSpace a μ d) (translationS d t)
    (translation_destabilizing a μ d t)

@[simp] lemma translationB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (t : ℚ) (f : S d) :
    translationB a μ d t ((destabilizingSpace a μ d).mkQ f) =
      (destabilizingSpace a μ d).mkQ (translationS d t f) := rfl

omit [Fintype I] [DecidableEq I] in
@[simp] lemma translationS_zero (d : I → ℕ) (f : S d) : translationS d 0 f = f := by
  apply Subtype.ext
  exact translation_zero f.val

@[simp] lemma translationB_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (f : B a μ d) : translationB a μ d 0 f = f := by
  induction f using Submodule.Quotient.induction_on with
  | H f => exact congrArg (destabilizingSpace a μ d).mkQ (translationS_zero d f)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_Average
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SeparatedSymmetry
open MvPolynomial

variable {α β G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]

noncomputable def average (ρ : G →* Equiv.Perm α) :
    MvPolynomial α ℚ →ₗ[ℚ] MvPolynomial α ℚ :=
  (Fintype.card G : ℚ)⁻¹ • ∑ g : G, (rename (ρ g)).toLinearMap

lemma average_apply (ρ : G →* Equiv.Perm α) (p : MvPolynomial α ℚ) :
    average ρ p = (Fintype.card G : ℚ)⁻¹ • ∑ g : G, rename (ρ g) p := by
  simp [average]

lemma rename_average (ρ : G →* Equiv.Perm α) (g : G) (p : MvPolynomial α ℚ) :
    rename (ρ g) (average ρ p) = average ρ p := by
  rw [average_apply, map_smul, map_sum]
  congr 1
  calc
    _ = ∑ h : G, rename (ρ (g*h)) p := by
      apply Finset.sum_congr rfl
      intro h _
      rw [rename_rename]
      congr 1
      ext a
      simp
    _ = _ := Function.Bijective.sum_comp (Group.mulLeft_bijective g) (fun h => rename (ρ h) p)

lemma average_fixed (ρ : G →* Equiv.Perm α) (p : MvPolynomial α ℚ)
    (hp : ∀ g, rename (ρ g) p = p) : average ρ p = p := by
  rw [average_apply]
  simp only [hp, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero

def sumAction (ρ : G →* Equiv.Perm α) (τ : H →* Equiv.Perm β) :
    G × H →* Equiv.Perm (α ⊕ β) where
  toFun g := Equiv.sumCongr (ρ g.1) (τ g.2)
  map_one' := by ext x; cases x <;> simp
  map_mul' := by intro g h; ext x; cases x <;> simp

omit [Fintype G] [Fintype H] in
lemma rename_sumAction_left (ρ : G →* Equiv.Perm α) (τ : H →* Equiv.Perm β)
    (g : G) (h : H) (p : MvPolynomial α ℚ) :
    rename (sumAction ρ τ (g,h)) (rename Sum.inl p) = rename Sum.inl (rename (ρ g) p) := by
  simp only [rename_rename]
  rfl

omit [Fintype G] [Fintype H] in
lemma rename_sumAction_right (ρ : G →* Equiv.Perm α) (τ : H →* Equiv.Perm β)
    (g : G) (h : H) (p : MvPolynomial β ℚ) :
    rename (sumAction ρ τ (g,h)) (rename Sum.inr p) = rename Sum.inr (rename (τ h) p) := by
  simp only [rename_rename]
  rfl

lemma average_separated (ρ : G →* Equiv.Perm α) (τ : H →* Equiv.Perm β)
    (f : MvPolynomial α ℚ) (g : MvPolynomial β ℚ) :
    average (sumAction ρ τ) (rename Sum.inl f * rename Sum.inr g) =
      rename Sum.inl (average ρ f) * rename Sum.inr (average τ g) := by
  simp only [average_apply, map_mul, Fintype.sum_prod_type,
    rename_sumAction_left, rename_sumAction_right, map_smul, map_sum,
    Fintype.card_prod, Nat.cast_mul, mul_inv_rev, smul_mul_smul_comm,
    Finset.sum_mul, Finset.mul_sum]
  rw [mul_comm (Fintype.card H : ℚ)⁻¹ (Fintype.card G : ℚ)⁻¹]
  congr 1
  exact Finset.sum_comm

lemma separated_span (p : MvPolynomial (α ⊕ β) ℚ) :
    p ∈ Submodule.span ℚ {q | ∃ (f : MvPolynomial α ℚ) (g : MvPolynomial β ℚ),
      q = rename Sum.inl f * rename Sum.inr g} := by
  let V : Submodule ℚ (MvPolynomial (α ⊕ β) ℚ) := Submodule.span ℚ
    {q | ∃ (f : MvPolynomial α ℚ) (g : MvPolynomial β ℚ),
      q = rename Sum.inl f * rename Sum.inr g}
  change p ∈ V
  induction p using MvPolynomial.induction_on with
  | C r => exact Submodule.subset_span ⟨C r, 1, by simp⟩
  | add p q hp hq => exact V.add_mem hp hq
  | mul_X p x hp =>
    induction hp using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨f,g,rfl⟩ := hq
      cases x with
      | inl a =>
        apply Submodule.subset_span
        exact ⟨f * X a, g, by simp <;> ring⟩
      | inr b =>
        apply Submodule.subset_span
        exact ⟨f, g * X b, by simp [mul_assoc]⟩
    | zero => simp
    | add q r hq hr ihq ihr => simpa [add_mul] using V.add_mem ihq ihr
    | smul c q hq ih => simpa [smul_mul_assoc] using V.smul_mem c ih

theorem invariant_separated_span (ρ : G →* Equiv.Perm α) (τ : H →* Equiv.Perm β)
    (p : MvPolynomial (α ⊕ β) ℚ)
    (hp : ∀ x, rename (sumAction ρ τ x) p = p) :
    p ∈ Submodule.span ℚ {q | ∃ (f : MvPolynomial α ℚ) (g : MvPolynomial β ℚ),
      (∀ x, rename (ρ x) f = f) ∧ (∀ y, rename (τ y) g = g) ∧
      q = rename Sum.inl f * rename Sum.inr g} := by
  rw [← average_fixed (sumAction ρ τ) p hp]
  clear hp
  have h := separated_span p
  induction h using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨f,g,rfl⟩ := hq
    rw [average_separated]
    exact Submodule.subset_span ⟨average ρ f, average τ g,
      fun x => rename_average ρ x f, fun y => rename_average τ y g, rfl⟩
  | zero => simp
  | add q r hq hr ihq ihr => simpa using (Submodule.span ℚ _).add_mem ihq ihr
  | smul c q hq ih => simpa using (Submodule.span ℚ _).smul_mem c ih

end ElementaryPositivity.SeparatedSymmetry

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PackSplit
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
open ElementaryPositivity.SeparatedSymmetry
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {d e : I → ℕ}

noncomputable def packSplit (A : Cut d e) (i : I) :
    Fin (d i) ⊕ Fin (e i) ≃ Fin (d i+e i) :=
  (Equiv.sumCongr (leftEnum A i) ((rightEnum A i).trans
    ((Equiv.refl _).subtypeEquiv (by intro x; simp only [Finset.mem_compl, Equiv.refl_apply])))).trans
      (Equiv.sumCompl fun x => x ∈ (A i).val)

omit [Fintype I] [DecidableEq I] in
@[simp] lemma packSplit_inl (A : Cut d e) (i : I) (x : Fin (d i)) :
    packSplit A i (Sum.inl x) = leftEnum A i x := rfl
omit [Fintype I] [DecidableEq I] in
@[simp] lemma packSplit_inr (A : Cut d e) (i : I) (x : Fin (e i)) :
    packSplit A i (Sum.inr x) = rightEnum A i x := rfl

noncomputable def cutSplit (A : Cut d e) :
    ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ≃ (Σi,Fin (d i+e i)) :=
  (Equiv.sigmaSumDistrib _ _).symm.trans (Equiv.sigmaCongrRight (packSplit A))

omit [Fintype I] [DecidableEq I] in
@[simp] lemma cutSplit_inl (A : Cut d e) (x : Σi,Fin (d i)) :
    cutSplit A (Sum.inl x) = leftInput A x := rfl
omit [Fintype I] [DecidableEq I] in
@[simp] lemma cutSplit_inr (A : Cut d e) (x : Σi,Fin (e i)) :
    cutSplit A (Sum.inr x) = rightInput A x := rfl

omit [Fintype I] [DecidableEq I] in
lemma cutSplit_change (A B : Cut d e) :
    (cutSplit A).symm.trans (cutSplit B) =
      packAction (fun i => Fin (d i+e i)) (fun i => (packSplit A i).symm.trans (packSplit B i)) := by
  apply Equiv.ext
  intro x
  obtain ⟨y,rfl⟩ := (cutSplit A).surjective x
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  cases y with
  | inl x =>
    rcases x with ⟨i,x⟩
    change (⟨i,packSplit B i (Sum.inl x)⟩ : Σi,Fin (d i+e i)) =
      ⟨i,packSplit B i ((packSplit A i).symm (packSplit A i (Sum.inl x)))⟩
    rw [Equiv.symm_apply_apply]
  | inr x =>
    rcases x with ⟨i,x⟩
    change (⟨i,packSplit B i (Sum.inr x)⟩ : Σi,Fin (d i+e i)) =
      ⟨i,packSplit B i ((packSplit A i).symm (packSplit A i (Sum.inr x)))⟩
    rw [Equiv.symm_apply_apply]

omit [Fintype I] [DecidableEq I] in
lemma split_symmetric_independent (A B : Cut d e) (F : S (d+e)) :
    rename (cutSplit B) (rename (cutSplit A).symm F.val) = F.val := by
  rw [rename_rename]
  change rename ((cutSplit A).symm.trans (cutSplit B)) F.val = _
  rw [cutSplit_change]
  exact F.property _

omit [Fintype I] [DecidableEq I] in
lemma cutSplit_action (A : Cut d e)
    (σ : (∀i,Equiv.Perm (Fin (d i))) × (∀i,Equiv.Perm (Fin (e i)))) :
    (cutSplit A).symm.trans ((sumAction (packAction (fun i=>Fin (d i)))
      (packAction (fun i=>Fin (e i))) σ).trans (cutSplit A)) =
      packAction (fun i=>Fin (d i+e i)) (fun i =>
        (packSplit A i).symm.trans ((Equiv.sumCongr (σ.1 i) (σ.2 i)).trans (packSplit A i))) := by
  apply Equiv.ext
  intro x
  obtain ⟨y,rfl⟩ := (cutSplit A).surjective x
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  cases y with
  | inl x =>
    rcases x with ⟨i,x⟩
    change (⟨i,packSplit A i (Sum.inl (σ.1 i x))⟩ : Σi,Fin (d i+e i)) =
      ⟨i,packSplit A i ((Equiv.sumCongr (σ.1 i) (σ.2 i))
        ((packSplit A i).symm (packSplit A i (Sum.inl x))))⟩
    rw [Equiv.symm_apply_apply]; rfl
  | inr x =>
    rcases x with ⟨i,x⟩
    change (⟨i,packSplit A i (Sum.inr (σ.2 i x))⟩ : Σi,Fin (d i+e i)) =
      ⟨i,packSplit A i ((Equiv.sumCongr (σ.1 i) (σ.2 i))
        ((packSplit A i).symm (packSplit A i (Sum.inr x))))⟩
    rw [Equiv.symm_apply_apply]; rfl

omit [Fintype I] [DecidableEq I] in
lemma split_symmetric (A : Cut d e) (F : S (d+e)) :
    ∀ σ, rename (sumAction (packAction (fun i=>Fin (d i))) (packAction (fun i=>Fin (e i))) σ)
      (rename (cutSplit A).symm F.val) = rename (cutSplit A).symm F.val := by
  intro σ
  apply rename_injective (cutSplit A) (cutSplit A).injective
  simp only [rename_rename]
  have h := F.property (fun i => (packSplit A i).symm.trans
    ((Equiv.sumCongr (σ.1 i) (σ.2 i)).trans (packSplit A i)))
  change rename (packAction (fun i=>Fin (d i+e i)) (fun i => (packSplit A i).symm.trans
    ((Equiv.sumCongr (σ.1 i) (σ.2 i)).trans (packSplit A i)))) F.val = F.val at h
  rw [← cutSplit_action A σ] at h
  convert h using 1
  · rfl
  · simp

lemma split_symmetric_span (A : Cut d e) (F : S (d+e)) :
    rename (cutSplit A).symm F.val ∈ Submodule.span ℚ
      {q | ∃ (f : S d) (g : S e), q = rename Sum.inl f.val * rename Sum.inr g.val} := by
  have h := invariant_separated_span (packAction (fun i=>Fin (d i)))
    (packAction (fun i=>Fin (e i))) (rename (cutSplit A).symm F.val) (split_symmetric A F)
  apply Submodule.span_mono _ h
  rintro q ⟨f,g,hf,hg,rfl⟩
  exact ⟨⟨f,hf⟩,⟨g,hg⟩,rfl⟩

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {d e : I → ℕ}

noncomputable def firstCut (d e : I → ℕ) : Cut d e := fun i =>
  ⟨Finset.univ.map (Fin.castAddEmb (e i)), by simp⟩

noncomputable def localizeS (d : I → ℕ) :
    S d →ₗ[ℚ] FractionRing (MvPolynomial (Σi,Fin (d i)) ℚ) where
  toFun f := algebraMap _ _ f.val
  map_add' := by intro f g; exact map_add _ f.val g.val
  map_smul' := by
    intro r f
    change algebraMap _ _ (r • f.val) = r • algebraMap _ _ f.val
    exact map_rat_smul (algebraMap (MvPolynomial (Σi,Fin (d i)) ℚ)
      (FractionRing (MvPolynomial (Σi,Fin (d i)) ℚ))) r f.val

omit [Fintype I] [DecidableEq I] in
@[simp] lemma localizeS_apply (d : I → ℕ) (f : S d) :
    localizeS d f = algebraMap _ (FractionRing (MvPolynomial (Σi,Fin (d i)) ℚ)) f.val := rfl

omit [Fintype I] [DecidableEq I] in
lemma localizeS_injective (d : I → ℕ) : Function.Injective (localizeS d) := by
  intro f g h
  apply Subtype.ext
  exact IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,Fin (d i)) ℚ)) h

noncomputable def shuffleImage (a : I → I → ℕ) (d e : I → ℕ) : Submodule ℚ (S (d+e)) :=
  Submodule.span ℚ {q | ∃ (f : S d) (g : S e), q = shufflePolynomial a f g}

lemma rawShuffle_mem_localized_image (a : I → I → ℕ) (f : S d) (g : S e) :
    rawShuffle a f.val g.val ∈ (shuffleImage a d e).map (localizeS (d+e)) := by
  apply Submodule.mem_map.mpr
  exact ⟨shufflePolynomial a f g, Submodule.subset_span ⟨f,g,rfl⟩,
    shufflePolynomial_eq a f g⟩

noncomputable def tensorShuffle (a : I → I → ℕ) :
    MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ →ₗ[ℚ]
      FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ) where
  toFun p := ∑ A : Cut d e,
    algebraMap _ _ (rename (cutSplit A) p * ∏ i, ∏ j, cutFactor A i j (a i j)) /
      algebraMap _ _ (cutDenominator A)
  map_add' := by
    intro p q
    simp only [map_add, add_mul, add_div, Finset.sum_add_distrib]
  map_smul' := by
    let : DistribSMul ℚ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ)) :=
      (inferInstance : Module ℚ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))).toDistribMulAction.toDistribSMul
    intro r p
    simp only [map_smul, map_rat_smul, smul_mul_assoc, div_eq_mul_inv,
      Finset.smul_sum, RingHom.id_apply]

lemma tensorShuffle_decomposable (a : I → I → ℕ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    tensorShuffle a (rename Sum.inl f * rename Sum.inr g) = rawShuffle a f g := by
  simp only [tensorShuffle, LinearMap.coe_mk, AddHom.coe_mk, map_mul, rename_rename,
    rawShuffle, cutNumerator]
  rfl

lemma tensorShuffle_restricted_mul (a : I → I → ℕ) (A₀ : Cut d e) (F : S (d+e))
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    tensorShuffle a (rename (cutSplit A₀).symm F.val *
      (rename Sum.inl f * rename Sum.inr g)) =
      localizeS (d+e) F * rawShuffle a f g := by
  dsimp only [Pi.add_apply] at *
  simp only [tensorShuffle, LinearMap.coe_mk, AddHom.coe_mk, map_mul,
    split_symmetric_independent, localizeS_apply, rawShuffle, cutNumerator,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  simp only [rename_rename]
  change (algebraMap _ _ F.val *
      (algebraMap _ _ (rename (leftInput A) f) * algebraMap _ _ (rename (rightInput A) g)) *
      algebraMap _ _ (∏ i, ∏ j, cutFactor A i j (a i j))) / algebraMap _ _ (cutDenominator A) = _
  simp only [mul_assoc, mul_div_assoc]
  rfl

theorem mul_shuffle_mem (a : I → I → ℕ) (F : S (d+e)) (f : S d) (g : S e) :
    F * shufflePolynomial a f g ∈ shuffleImage a d e := by
  let V := (shuffleImage a d e).map (localizeS (d+e))
  let T : MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ →ₗ[ℚ]
      FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ) :=
    (tensorShuffle a).comp (LinearMap.mulRight ℚ (rename Sum.inl f.val * rename Sum.inr g.val))
  have hT : Submodule.span ℚ
      {q | ∃ (f' : S d) (g' : S e), q = rename Sum.inl f'.val * rename Sum.inr g'.val}
      ≤ V.comap T := by
    apply Submodule.span_le.mpr
    rintro q ⟨f',g',rfl⟩
    change T (rename Sum.inl f'.val * rename Sum.inr g'.val) ∈ V
    dsimp only [T, LinearMap.comp_apply, LinearMap.mulRight_apply]
    have he : (rename Sum.inl f'.val * rename Sum.inr g'.val) *
        (rename Sum.inl f.val * rename Sum.inr g.val) =
        rename Sum.inl (f'*f).val * rename Sum.inr (g'*g).val := by
      simp only [Subalgebra.coe_mul, map_mul]
      ring
    rw [he, tensorShuffle_decomposable]
    exact rawShuffle_mem_localized_image a (f'*f) (g'*g)
  have h := hT (split_symmetric_span (firstCut d e) F)
  simp only [Submodule.mem_comap, T, LinearMap.comp_apply, LinearMap.mulRight_apply] at h
  rw [tensorShuffle_restricted_mul] at h
  obtain ⟨q,hq,he⟩ := Submodule.mem_map.mp h
  have eq : q = F * shufflePolynomial a f g := by
    apply localizeS_injective (d+e)
    rw [he]
    change _ = algebraMap _ _ (F.val * (shufflePolynomial a f g).val)
    rw [map_mul]
    exact congrArg (fun x => localizeS (d+e) F * x) (shufflePolynomial_eq a f g).symm
  exact eq ▸ hq

theorem destabilizing_mul_mem (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (F : S d) {q : S d} (hq : q ∈ destabilizingSpace a μ d) :
    F*q ∈ destabilizingSpace a μ d := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨u,v,h,f,g,hu,hv,hμ,rfl⟩ := hq
    subst d
    have hs : shuffleImage a u v ≤ destabilizingSpace a μ (u+v) := by
      apply Submodule.span_le.mpr
      rintro q ⟨f',g',rfl⟩
      exact Submodule.subset_span ⟨u,v,rfl,f',g',hu,hv,hμ,rfl⟩
    exact hs (mul_shuffle_mem a F f g)
  | zero => simp
  | add q r hq hr ihq ihr =>
    simpa [mul_add] using (destabilizingSpace a μ d).add_mem ihq ihr
  | smul c q hq ih =>
    simpa [mul_smul_comm] using (destabilizingSpace a μ d).smul_mem c ih

noncomputable def destabilizingIdeal (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    Ideal (S d) where
  carrier := destabilizingSpace a μ d
  zero_mem' := (destabilizingSpace a μ d).zero_mem
  add_mem' := (destabilizingSpace a μ d).add_mem
  smul_mem' := destabilizing_mul_mem a μ d

@[simp] lemma mem_destabilizingIdeal (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (f : S d) : f ∈ destabilizingIdeal a μ d ↔ f ∈ destabilizingSpace a μ d := Iff.rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ReynoldsS
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def reynoldsS (d : I → ℕ) :
    MvPolynomial (Σi,Fin (d i)) ℚ →ₗ[ℚ] S d where
  toFun f := ⟨average (packAction (fun i=>Fin (d i))) f,
    fun σ => rename_average _ σ f⟩
  map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
  map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _

@[simp] lemma reynoldsS_val (d : I → ℕ) (f : S d) : reynoldsS d f.val = f := by
  apply Subtype.ext
  exact average_fixed _ f.val f.property

lemma tensorEquivSum_tmul {α β : Type*} (f : MvPolynomial α ℚ) (g : MvPolynomial β ℚ) :
    tensorEquivSum ℚ α β ℚ (f ⊗ₜ[ℚ] g) = rename Sum.inl f * rename Sum.inr g := by
  let H := tensorEquivSum ℚ α β ℚ
  have hL : H.toAlgHom.comp Algebra.TensorProduct.includeLeft = rename (R:=ℚ) Sum.inl := by
    ext i
    simp [H]
  have hR : H.toAlgHom.comp Algebra.TensorProduct.includeRight = rename (R:=ℚ) Sum.inr := by
    ext i
    simp [H]
  change H (f ⊗ₜ[ℚ] g) = _
  have ht : f ⊗ₜ[ℚ] g = (f ⊗ₜ[ℚ] (1 : MvPolynomial β ℚ)) * ((1 : MvPolynomial α ℚ) ⊗ₜ[ℚ] g) := by
    simp
  rw [ht, map_mul]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun hL f) (DFunLike.congr_fun hR g)

noncomputable def tensorValue (d e : I → ℕ) :
    S d ⊗[ℚ] S e →ₗ[ℚ] MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ :=
  (tensorEquivSum ℚ _ _ ℚ).toLinearMap ∘ₗ
    TensorProduct.map (symmetricSpace d).val.toLinearMap (symmetricSpace e).val.toLinearMap

omit [Fintype I] [DecidableEq I] in
@[simp] lemma tensorValue_tmul (d e : I → ℕ) (f : S d) (g : S e) :
    tensorValue d e (f ⊗ₜ[ℚ] g) = rename Sum.inl f.val * rename Sum.inr g.val := by
  exact tensorEquivSum_tmul f.val g.val

noncomputable def separateTensor (d e : I → ℕ) :
    MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ →ₗ[ℚ] S d ⊗[ℚ] S e :=
  TensorProduct.map (reynoldsS d) (reynoldsS e) ∘ₗ
    (tensorEquivSum ℚ _ _ ℚ).symm.toLinearMap

@[simp] lemma separateTensor_product (d e : I → ℕ) (f : S d) (g : S e) :
    separateTensor d e (rename Sum.inl f.val * rename Sum.inr g.val) = f ⊗ₜ[ℚ] g := by
  rw [← tensorEquivSum_tmul]
  simp [separateTensor]

@[simp] lemma separateTensor_tensorValue (d e : I → ℕ) (f : S d ⊗[ℚ] S e) :
    separateTensor d e (tensorValue d e f) = f := by
  induction f using OAI.tensorInductionOn with
  | tmul f g => simp
  | add x y hx hy => simp [hx,hy]

lemma tensorValue_injective (d e : I → ℕ) : Function.Injective (tensorValue d e) := by
  intro f g h
  simpa using congrArg (separateTensor d e) h

lemma tensorValue_separateTensor (d e : I → ℕ)
    (f : MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ)
    (hf : ∀ σ, rename (sumAction (packAction (fun i=>Fin (d i)))
      (packAction (fun i=>Fin (e i))) σ) f = f) :
    tensorValue d e (separateTensor d e f) = f := by
  have h := invariant_separated_span (packAction (fun i=>Fin (d i)))
    (packAction (fun i=>Fin (e i))) f hf
  clear hf
  induction h using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨f,g,hf,hg,rfl⟩ := hp
    change tensorValue d e (separateTensor d e
      (rename Sum.inl (⟨f,hf⟩ : S d).val * rename Sum.inr (⟨g,hg⟩ : S e).val)) = _
    rw [separateTensor_product,tensorValue_tmul]
  | zero => simp
  | add x y hx hy ihx ihy => simp [ihx,ihy]
  | smul c x hx ih => simp [ih]

noncomputable def restrictTensor {d e : I → ℕ} (A : Cut d e) : S (d+e) →ₗ[ℚ] S d ⊗[ℚ] S e :=
  separateTensor d e ∘ₗ (rename (cutSplit A).symm).toLinearMap ∘ₗ
    (symmetricSpace (d+e)).val.toLinearMap

@[simp] lemma tensorValue_restrictTensor {d e : I → ℕ} (A : Cut d e) (f : S (d+e)) :
    tensorValue d e (restrictTensor A f) = rename (cutSplit A).symm f.val := by
  exact tensorValue_separateTensor d e _ (split_symmetric A f)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_Taylor
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.CommonTranslation

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem coefficients_mem {N : ℕ} (U : Submodule ℚ V) (v : Fin N → V)
    (h : ∀ t : ℚ, ∑ n : Fin N, t^(n:ℕ) • v n ∈ U) (n : Fin N) : v n ∈ U := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U (v n)).mp
  intro φ hφ
  let p : Polynomial ℚ := ∑ k : Fin N, Polynomial.monomial (k:ℕ) (φ (v k))
  have hp : p = 0 := by
    apply Polynomial.zero_of_eval_zero
    intro t
    have hz : φ (∑ k : Fin N, t^(k:ℕ) • v k) = 0 := ((Submodule.mem_dualAnnihilator φ).mp hφ) _ (h t)
    simpa [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      map_sum, map_smul, mul_comm] using hz
  have hc := congrArg (fun p : Polynomial ℚ => p.coeff (n:ℕ)) hp
  simpa [p, Polynomial.coeff_sum, Polynomial.coeff_monomial,
    ← Fin.ext_iff] using hc

variable {A : Type*} [CommRing A] [Algebra ℚ A]

theorem polynomial_coeff_mem (U : Submodule ℚ A) (p : Polynomial A)
    (h : ∀ t : ℚ, p.eval (algebraMap ℚ A t) ∈ U) (n : ℕ) : p.coeff n ∈ U := by
  by_cases hn : n < p.natDegree+1
  · apply coefficients_mem U (fun k : Fin (p.natDegree+1) => p.coeff k.val) ?_ ⟨n,hn⟩
    intro t
    convert h t using 1
    all_goals try with_reducible_and_instances rfl
    rw [Polynomial.eval_eq_sum_range]
    simp only [Algebra.smul_def, map_pow]
    rw [Fin.sum_univ_eq_sum_range (fun i => (algebraMap ℚ A t)^i * p.coeff i)]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact U.zero_mem

section Polynomials
open MvPolynomial
variable {α β : Type*}

noncomputable def taylor : MvPolynomial α ℚ →ₐ[ℚ] Polynomial (MvPolynomial α ℚ) :=
  aeval fun i => Polynomial.C (X i) + Polynomial.X

@[simp] lemma taylor_X (i : α) :
    taylor (X i) = Polynomial.C (X i) + Polynomial.X := by simp [taylor]

@[simp] lemma taylor_C (r : ℚ) :
    taylor (C r : MvPolynomial α ℚ) = Polynomial.C (C r) := by
  simp [taylor, Polynomial.algebraMap_apply]

lemma taylor_eval (p : MvPolynomial α ℚ) (t : ℚ) :
    (taylor p).eval (C t) = aeval (fun i => X i + C t) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp]

@[simp] lemma taylor_coeff_zero (p : MvPolynomial α ℚ) : (taylor p).coeff 0 = p := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have h := taylor_eval p 0
  simpa [show (aeval fun i : α => X i + C (0:ℚ)) = AlgHom.id ℚ _ by ext; simp] using h

noncomputable def D : Derivation ℚ (MvPolynomial α ℚ) (MvPolynomial α ℚ) :=
  mkDerivation ℚ fun _ => 1

@[simp] lemma D_X (i : α) : D (X i) = 1 := mkDerivation_X ℚ _ i
@[simp] lemma D_C (r : ℚ) : D (C r : MvPolynomial α ℚ) = 0 := derivation_C _ _
lemma D_mul (p q : MvPolynomial α ℚ) : D (p*q) = D p*q + p*D q := by
  simp [smul_eq_mul, mul_comm, add_comm]

lemma taylor_derivative (p : MvPolynomial α ℚ) :
    Polynomial.derivative (taylor p) = taylor (D p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.derivative_mul, taylor_X,
      Polynomial.derivative_C, Polynomial.derivative_X, zero_add, mul_one, hp,
      D_mul, D_X, map_add]

@[simp] lemma taylor_coeff_one (p : MvPolynomial α ℚ) : (taylor p).coeff 1 = D p := by
  have h := congrArg (fun q : Polynomial (MvPolynomial α ℚ) => q.coeff 0) (taylor_derivative p)
  simpa [Polynomial.coeff_derivative] using h

end Polynomials

end ElementaryPositivity.CommonTranslation

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_QuotientAlg
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.CommonTranslation
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable instance quotientCommRing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    CommRing (B a μ d) := inferInstanceAs (CommRing (S d ⧸ destabilizingIdeal a μ d))
noncomputable instance quotientAlgebra (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    Algebra ℚ (B a μ d) := inferInstanceAs (Algebra ℚ (S d ⧸ destabilizingIdeal a μ d))

noncomputable def quotientAlg (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    S d →ₐ[ℚ] B a μ d := Ideal.Quotient.mkₐ ℚ (destabilizingIdeal a μ d)

@[simp] lemma quotientAlg_apply (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (f : S d) :
    quotientAlg a μ d f = (destabilizingSpace a μ d).mkQ f := rfl

noncomputable def tensorValueAlg (d e : I → ℕ) :
    S d ⊗[ℚ] S e →ₐ[ℚ] MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ :=
  (tensorEquivSum ℚ _ _ ℚ).toAlgHom.comp
    (Algebra.TensorProduct.map (symmetricSpace d).val (symmetricSpace e).val)

omit [Fintype I] [DecidableEq I] in
@[simp] lemma tensorValueAlg_apply (d e : I → ℕ) (f : S d ⊗[ℚ] S e) :
    tensorValueAlg d e f = tensorValue d e f := rfl

omit [Fintype I] [DecidableEq I] in
lemma tensorValue_mul (d e : I → ℕ) (f g : S d ⊗[ℚ] S e) :
    tensorValue d e (f*g) = tensorValue d e f * tensorValue d e g :=
  (tensorValueAlg d e).map_mul f g

noncomputable def restrictTensorAlg {d e : I → ℕ} (A : Cut d e) : S (d+e) →ₐ[ℚ] S d ⊗[ℚ] S e where
  toFun := restrictTensor A
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    apply tensorValue_injective
    rw [tensorValue_restrictTensor]
    change rename (cutSplit A).symm 1 = tensorValueAlg d e 1
    exact (map_one (rename (R:=ℚ) (cutSplit A).symm)).trans
      (map_one (tensorValueAlg d e)).symm
  map_mul' f g := by
    apply tensorValue_injective
    rw [tensorValue_restrictTensor,tensorValue_mul,tensorValue_restrictTensor,tensorValue_restrictTensor]
    exact map_mul _ _ _
  commutes' q := by
    apply tensorValue_injective
    rw [tensorValue_restrictTensor]
    change rename (cutSplit A).symm (algebraMap ℚ _ q) =
      tensorValueAlg d e (algebraMap ℚ _ q)
    rw [(tensorValueAlg d e).commutes,(rename (cutSplit A).symm).commutes]

omit [Fintype I] [DecidableEq I] in
lemma taylorS_exists (d : I → ℕ) (f : S d) :
    ∃ q : Polynomial (S d), Polynomial.map (symmetricSpace d).val.toRingHom q = taylor f.val := by
  apply (Polynomial.mem_lifts _).mp
  apply (Polynomial.lifts_iff_coeff_lifts _).mpr
  intro n
  have h : (taylor f.val).coeff n ∈ (symmetricSpace d).toSubmodule := by
    apply polynomial_coeff_mem (symmetricSpace d).toSubmodule (taylor f.val)
    intro t
    change (taylor f.val).eval (C t) ∈ (symmetricSpace d).toSubmodule
    rw [taylor_eval]
    exact translation_symmetric t f.val f.property
  exact ⟨⟨_,h⟩,rfl⟩

noncomputable def taylorSValue (d : I → ℕ) (f : S d) : Polynomial (S d) :=
  (taylorS_exists d f).choose

omit [Fintype I] [DecidableEq I] in
@[simp] lemma map_taylorSValue (d : I → ℕ) (f : S d) :
    Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d f) = taylor f.val :=
  (taylorS_exists d f).choose_spec

omit [Fintype I] [DecidableEq I] in
lemma polynomial_symmetric_injective (d : I → ℕ) :
    Function.Injective (Polynomial.map (symmetricSpace d).val.toRingHom) :=
  Polynomial.map_injective _ Subtype.val_injective

noncomputable def taylorS (d : I → ℕ) : S d →ₐ[ℚ] Polynomial (S d) where
  toFun := taylorSValue d
  map_zero' := by
    apply polynomial_symmetric_injective d
    change Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d 0) =
      Polynomial.map (symmetricSpace d).val.toRingHom 0
    exact (map_taylorSValue d 0).trans (by simp)
  map_one' := by
    apply polynomial_symmetric_injective d
    change Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d 1) =
      Polynomial.map (symmetricSpace d).val.toRingHom 1
    exact (map_taylorSValue d 1).trans (by simp)
  map_add' f g := by
    apply polynomial_symmetric_injective d
    rw [Polynomial.map_add]
    change Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d (f+g)) =
      Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d f) +
      Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d g)
    rw [map_taylorSValue,map_taylorSValue,map_taylorSValue]
    exact map_add _ _ _
  map_mul' f g := by
    apply polynomial_symmetric_injective d
    rw [Polynomial.map_mul]
    change Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d (f*g)) =
      Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d f) *
      Polynomial.map (symmetricSpace d).val.toRingHom (taylorSValue d g)
    rw [map_taylorSValue,map_taylorSValue,map_taylorSValue]
    exact map_mul _ _ _
  commutes' q := by
    apply polynomial_symmetric_injective d
    change Polynomial.map (symmetricSpace d).val.toRingHom
      (taylorSValue d (algebraMap ℚ (S d) q)) =
      Polynomial.map (symmetricSpace d).val.toRingHom (Polynomial.C (algebraMap ℚ (S d) q))
    rw [map_taylorSValue,Polynomial.map_C]
    change taylor (C q : MvPolynomial (Σi,Fin (d i)) ℚ) = Polynomial.C (C q)
    exact taylor_C q

omit [Fintype I] [DecidableEq I] in
@[simp] lemma map_taylorS (d : I → ℕ) (f : S d) :
    Polynomial.map (symmetricSpace d).val.toRingHom (taylorS d f) = taylor f.val :=
  map_taylorSValue d f

omit [Fintype I] [DecidableEq I] in
lemma taylorS_eval (d : I → ℕ) (f : S d) (t : ℚ) :
    (taylorS d f).eval (algebraMap ℚ (S d) t) = translationS d t f := by
  apply Subtype.ext
  have h := congrArg (fun p : Polynomial (MvPolynomial (Σi,Fin (d i)) ℚ) =>
    p.eval (C t)) (map_taylorS d f)
  rw [taylor_eval] at h
  change (symmetricSpace d).val ((taylorS d f).eval (algebraMap ℚ (S d) t)) =
    translation t f.val
  calc
    _ = (Polynomial.map (symmetricSpace d).val.toRingHom (taylorS d f)).eval (C t) := by
      rw [Polynomial.eval_map]
      exact (Polynomial.eval₂_at_apply (symmetricSpace d).val.toRingHom (algebraMap ℚ (S d) t)).symm
    _ = translation t f.val := h

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.CommonTranslation
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma taylorS_coeff_destabilizing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) {f : S d} (hf : f ∈ destabilizingSpace a μ d) (n : ℕ) :
    (taylorS d f).coeff n ∈ destabilizingSpace a μ d := by
  apply polynomial_coeff_mem (destabilizingSpace a μ d) (taylorS d f)
  intro t
  rw [taylorS_eval]
  exact translation_destabilizing a μ d t hf

noncomputable def taylorB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    B a μ d →ₐ[ℚ] Polynomial (B a μ d) :=
  Ideal.Quotient.liftₐ (destabilizingIdeal a μ d)
    ((Polynomial.mapAlgHom (quotientAlg a μ d)).comp (taylorS d)) (by
      intro f hf
      apply Polynomial.ext
      intro n
      change (Polynomial.map (quotientAlg a μ d).toRingHom (taylorS d f)).coeff n = (0 : Polynomial (B a μ d)).coeff n
      rw [Polynomial.coeff_map,Polynomial.coeff_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (taylorS_coeff_destabilizing a μ d hf n))

@[simp] lemma taylorB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (f : S d) :
    taylorB a μ d (quotientAlg a μ d f) = Polynomial.map (quotientAlg a μ d).toRingHom (taylorS d f) := rfl

noncomputable def relativeTaylor (d e : I → ℕ) :
    S d ⊗[ℚ] S e →ₐ[ℚ] Polynomial (S d ⊗[ℚ] S e) :=
  let L : S d →ₐ[ℚ] Polynomial (S d ⊗[ℚ] S e) :=
    (Polynomial.mapAlgHom (Algebra.TensorProduct.includeLeft : S d →ₐ[ℚ] S d ⊗[ℚ] S e)).comp (taylorS d)
  let R : S e →ₐ[ℚ] Polynomial (S d ⊗[ℚ] S e) :=
    Polynomial.CAlgHom.comp (Algebra.TensorProduct.includeRight : S e →ₐ[ℚ] S d ⊗[ℚ] S e)
  Algebra.TensorProduct.lift (S:=ℚ) L R (fun x y => (mul_comm (L x) (R y)))

omit [Fintype I] [DecidableEq I] in
@[simp] lemma relativeTaylor_tmul (d e : I → ℕ) (f : S d) (g : S e) :
    relativeTaylor d e (f ⊗ₜ[ℚ] g) =
      Polynomial.map (Algebra.TensorProduct.includeLeft : S d →ₐ[ℚ] S d ⊗[ℚ] S e).toRingHom (taylorS d f) *
      Polynomial.C ((1 : S d) ⊗ₜ[ℚ] g) := by
  simp only [relativeTaylor]
  rfl

noncomputable def quotientTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    S d ⊗[ℚ] S e →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e :=
  Algebra.TensorProduct.map (quotientAlg a μ d) (quotientAlg a μ e)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CrossDifference
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open ElementaryPositivity.CommonTranslation
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def crossDifference (d e : I → ℕ) :
    MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ :=
  ∏ i, ∏ x : Fin (d i), ∏ y : Fin (e i),
    (X (Sum.inl ⟨i,x⟩) - X (Sum.inr ⟨i,y⟩))

lemma prod_sub_perm {α β R : Type*} [Fintype α] [Fintype β] [CommRing R]
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) (l : α → R) (r : β → R) :
    (∏ x : α, (∏ y : β, (l (σ x) - r (τ y)))) = ∏ x : α, (∏ y : β, (l x - r y)) := by
  calc
    _ = ∏ x : α, (∏ y : β, (l (σ x) - r y)) := by
      apply Finset.prod_congr rfl
      intro x hx
      exact Equiv.prod_comp τ (fun y => l (σ x) - r y)
    _ = _ := Equiv.prod_comp σ (fun x => ∏ y : β, (l x - r y))

omit [DecidableEq I] in
lemma rename_crossDifference (d e : I → ℕ)
    (h : ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) → ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i)))) :
    rename h (crossDifference d e) =
      ∏ i,∏ x : Fin (d i),∏ y : Fin (e i), (X (h (Sum.inl ⟨i,x⟩))-X (h (Sum.inr ⟨i,y⟩))) := by
  simp only [crossDifference,map_prod,map_sub,rename_X]

omit [DecidableEq I] in
lemma crossDifference_symmetric (d e : I → ℕ) (σ : (∀ i,Equiv.Perm (Fin (d i))) ×
    (∀ i,Equiv.Perm (Fin (e i)))) :
    rename (sumAction (packAction (fun i=>Fin (d i))) (packAction (fun i=>Fin (e i))) σ)
      (crossDifference d e) = crossDifference d e := by
  refine (rename_crossDifference d e _).trans ?_
  exact Finset.prod_congr rfl (fun i hi =>
    prod_sub_perm (R := MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ)
      (σ.1 i) (σ.2 i) (fun x => X (Sum.inl ⟨i,x⟩)) (fun y => X (Sum.inr ⟨i,y⟩)))

noncomputable def crossTensor (d e : I → ℕ) : S d ⊗[ℚ] S e :=
  separateTensor d e (crossDifference d e)

@[simp] lemma tensorValue_crossTensor (d e : I → ℕ) :
    tensorValue d e (crossTensor d e) = crossDifference d e :=
  tensorValue_separateTensor d e _ (crossDifference_symmetric d e)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ShuffleTensorLinear
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.tensorValue_crossTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def shuffleTensorLinear (a : I → I → ℕ) (d e : I → ℕ) :
    S d ⊗[ℚ] S e →ₗ[ℚ] S (d+e) := TensorProduct.lift (shuffleLinear a d e)

@[simp] lemma shuffleTensorLinear_tmul (a : I → I → ℕ) (d e : I → ℕ) (f : S d) (g : S e) :
    shuffleTensorLinear a d e (f ⊗ₜ[ℚ] g) = shufflePolynomial a f g := rfl

noncomputable def twoTargetTransfer (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂) →ₗ[ℚ]
      S (d₁+e₁) ⊗[ℚ] S (d₂+e₂) :=
  TensorProduct.map (shuffleTensorLinear a d₁ e₁) (shuffleTensorLinear a d₂ e₂)

@[simp] lemma twoTargetTransfer_tmul (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f₁ : S d₁) (g₁ : S e₁) (f₂ : S d₂) (g₂ : S e₂) :
    twoTargetTransfer a d₁ e₁ d₂ e₂ ((f₁ ⊗ₜ[ℚ] g₁) ⊗ₜ[ℚ] (f₂ ⊗ₜ[ℚ] g₂)) =
      shufflePolynomial a f₁ g₁ ⊗ₜ[ℚ] shufflePolynomial a f₂ g₂ := by
  simp [twoTargetTransfer]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CellVars
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.tensorValue_crossTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*}

abbrev CellVars (d e : I → ℕ) := (Σi,Fin (d i)) ⊕ (Σi,Fin (e i))
abbrev CellGroup (d e : I → ℕ) :=
  (∀ i,Equiv.Perm (Fin (d i))) × (∀ i,Equiv.Perm (Fin (e i)))

noncomputable def fourValue (d₁ e₁ d₂ e₂ : I → ℕ) :
    (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂) →ₗ[ℚ]
      MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ :=
  (tensorEquivSum ℚ _ _ ℚ).toLinearMap ∘ₗ
    TensorProduct.map (tensorValue d₁ e₁) (tensorValue d₂ e₂)

@[simp] lemma fourValue_tmul (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S d₁ ⊗[ℚ] S e₁) (g : S d₂ ⊗[ℚ] S e₂) :
    fourValue d₁ e₁ d₂ e₂ (f ⊗ₜ[ℚ] g) =
      rename Sum.inl (tensorValue d₁ e₁ f) * rename Sum.inr (tensorValue d₂ e₂ g) :=
  tensorEquivSum_tmul _ _

variable [Fintype I] [DecidableEq I]

noncomputable def separateFour (d₁ e₁ d₂ e₂ : I → ℕ) :
    MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ →ₗ[ℚ]
      (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂) :=
  TensorProduct.map (separateTensor d₁ e₁) (separateTensor d₂ e₂) ∘ₗ
    (tensorEquivSum ℚ _ _ ℚ).symm.toLinearMap

@[simp] lemma separateFour_product (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : MvPolynomial (CellVars d₁ e₁) ℚ) (g : MvPolynomial (CellVars d₂ e₂) ℚ) :
    separateFour d₁ e₁ d₂ e₂ (rename Sum.inl f * rename Sum.inr g) =
      separateTensor d₁ e₁ f ⊗ₜ[ℚ] separateTensor d₂ e₂ g := by
  rw [← tensorEquivSum_tmul]
  simp [separateFour]

@[simp] lemma separateFour_fourValue (d₁ e₁ d₂ e₂ : I → ℕ)
    (p : (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂)) :
    separateFour d₁ e₁ d₂ e₂ (fourValue d₁ e₁ d₂ e₂ p) = p := by
  induction p using OAI.tensorInductionOn with
  | tmul f g => simp only [fourValue_tmul,separateFour_product,separateTensor_tensorValue]
  | add f g hf hg => simp only [map_add,hf,hg]

noncomputable def cellTransfer (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ →ₗ[ℚ]
      S (d₁+e₁) ⊗[ℚ] S (d₂+e₂) :=
  twoTargetTransfer a d₁ e₁ d₂ e₂ ∘ₗ separateFour d₁ e₁ d₂ e₂

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def renameInjFraction {α β : Type*} (f : α → β) (hf : Function.Injective f) :
    FractionRing (MvPolynomial α ℚ) →+* FractionRing (MvPolynomial β ℚ) :=
  IsFractionRing.lift (g := (algebraMap (MvPolynomial β ℚ)
    (FractionRing (MvPolynomial β ℚ))).comp (rename f).toRingHom)
    ((IsFractionRing.injective (MvPolynomial β ℚ) _).comp (MvPolynomial.rename_injective f hf))

@[simp] lemma renameInjFraction_algebraMap {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (p : MvPolynomial α ℚ) :
    renameInjFraction f hf (algebraMap _ (FractionRing (MvPolynomial α ℚ)) p) =
      algebraMap _ (FractionRing (MvPolynomial β ℚ)) (rename f p) := by
  exact IsFractionRing.lift_algebraMap (g := (algebraMap (MvPolynomial β ℚ)
    (FractionRing (MvPolynomial β ℚ))).comp (rename f).toRingHom) _ _

noncomputable def localizeTensor (d e : I → ℕ) :
    S d ⊗[ℚ] S e →ₗ[ℚ] FractionRing (MvPolynomial (CellVars d e) ℚ) where
  toFun f := algebraMap _ _ (tensorValue d e f)
  map_add' := by intro f g; rw [map_add,map_add]
  map_smul' := by
    intro r f
    rw [map_smul]
    exact map_rat_smul (algebraMap (MvPolynomial (CellVars d e) ℚ)
      (FractionRing (MvPolynomial (CellVars d e) ℚ))) r _

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Split
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.ShuffleConvolution
variable {A R : Type*} [Fintype A] [DecidableEq A] [CommSemiring R]

def Split (s : Finset A) := {p : Finset A × Finset A // Disjoint p.1 p.2 ∧ p.1 ∪ p.2 = s}
instance instFintypeSplit (s : Finset A) : Fintype (Split s) := by unfold Split; infer_instance

omit [Fintype A] in
lemma Split.left_subset {s : Finset A} (p : Split s) : p.val.1 ⊆ s := by
  intro a ha
  have hm := Finset.mem_union_left p.val.2 ha
  simpa only [p.property.2] using hm
omit [Fintype A] in
lemma Split.right_subset {s : Finset A} (p : Split s) : p.val.2 ⊆ s := by
  intro a ha
  have hm := Finset.mem_union_right p.val.1 ha
  simpa only [p.property.2] using hm

abbrev LeftIndex (s : Finset A) := Σ p : Split s, Split p.val.1
abbrev RightIndex (s : Finset A) := Σ p : Split s, Split p.val.2

def rebracket (s : Finset A) : LeftIndex s ≃ RightIndex s where
  toFun z := by
    let a := z.2.val.1
    let b := z.2.val.2
    let c := z.1.val.2
    have hab : Disjoint a b := z.2.property.1
    have hac : Disjoint a c := z.1.property.1.mono_left z.2.left_subset
    have hbc : Disjoint b c := z.1.property.1.mono_left z.2.right_subset
    have hu : a ∪ (b ∪ c) = s := by
      rw [← Finset.union_assoc, z.2.property.2, z.1.property.2]
    exact ⟨⟨(a,b∪c),⟨Finset.disjoint_union_right.mpr ⟨hab,hac⟩,hu⟩⟩,
      ⟨(b,c),⟨hbc,rfl⟩⟩⟩
  invFun z := by
    let a := z.1.val.1
    let b := z.2.val.1
    let c := z.2.val.2
    have hab : Disjoint a b := z.1.property.1.mono_right z.2.left_subset
    have hac : Disjoint a c := z.1.property.1.mono_right z.2.right_subset
    have hbc : Disjoint b c := z.2.property.1
    have hu : (a∪b)∪c = s := by
      rw [Finset.union_assoc, z.2.property.2, z.1.property.2]
    exact ⟨⟨(a∪b,c),⟨Finset.disjoint_union_left.mpr ⟨hac,hbc⟩,hu⟩⟩,
      ⟨(a,b),⟨hab,rfl⟩⟩⟩
  left_inv z := by
    rcases z with ⟨⟨⟨ab,c⟩,hac,hu⟩,⟨⟨a,b⟩,hab,habu⟩⟩
    dsimp at habu
    subst ab
    rfl
  right_inv z := by
    rcases z with ⟨⟨⟨a,bc⟩,hac,hu⟩,⟨⟨b,c⟩,hbc,hbcu⟩⟩
    dsimp at hbcu
    subst bc
    rfl

end ElementaryPositivity.ShuffleConvolution

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_Pack
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.PackConvolution
open ElementaryPositivity.ShuffleConvolution
variable {I : Type*} [Fintype I] {A : I → Type*}
variable [∀ i,DecidableEq (A i)]
variable {R : Type*} [CommSemiring R]

abbrev Pack := ∀ i, Finset (A i)
abbrev Cut (s : Pack (A := A)) := ∀ i, Split (s i)

def left {s : Pack (A := A)} (p : Cut s) : Pack (A := A) := fun i => (p i).val.1
def right {s : Pack (A := A)} (p : Cut s) : Pack (A := A) := fun i => (p i).val.2

def kernel (w : (Σi,A i) → (Σi,A i) → R) (s t : Pack (A := A)) : R :=
  ∏ i, ∏ x ∈ s i, ∏ j, ∏ y ∈ t j, w ⟨i,x⟩ ⟨j,y⟩

lemma kernel_union_left (w : (Σi,A i) → (Σi,A i) → R) (s t u : Pack (A := A))
    (h : ∀ i,Disjoint (s i) (t i)) :
    kernel w (fun i => s i ∪ t i) u = kernel w s u * kernel w t u := by
  simp only [kernel, Finset.prod_union (h _), Finset.prod_mul_distrib]
lemma kernel_union_right (w : (Σi,A i) → (Σi,A i) → R) (s t u : Pack (A := A))
    (h : ∀ i,Disjoint (t i) (u i)) :
    kernel w s (fun i => t i ∪ u i) = kernel w s t * kernel w s u := by
  simp only [kernel, Finset.prod_union (h _), Finset.prod_mul_distrib]

variable [DecidableEq I] [∀ i,Fintype (A i)]

abbrev LeftIndex (s : Pack (A := A)) := Σ p : Cut s, Cut (left p)
abbrev RightIndex (s : Pack (A := A)) := Σ p : Cut s, Cut (right p)

def distribute {J : Type*} {B : J → Type*} {C : ∀ j, B j → Type*} :
    (Σ f : ∀ j,B j, ∀ j,C j (f j)) ≃ (∀ j,Σ b : B j,C j b) where
  toFun z j := ⟨z.1 j,z.2 j⟩
  invFun z := ⟨fun j => (z j).1,fun j => (z j).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def rebracket (s : Pack (A := A)) : LeftIndex s ≃ RightIndex s :=
  distribute.trans ((Equiv.piCongrRight fun i => ShuffleConvolution.rebracket (s i)).trans
    distribute.symm)

def shuffle (w : (Σi,A i) → (Σi,A i) → R)
    (f g : Pack (A := A) → R) (s : Pack (A := A)) : R :=
  ∑ p : Cut s, f (left p) * g (right p) * kernel w (left p) (right p)

lemma shuffle_assoc (w : (Σi,A i) → (Σi,A i) → R)
    (f g h : Pack (A := A) → R) :
    shuffle w (shuffle w f g) h = shuffle w f (shuffle w g h) := by
  funext s
  have lhs : shuffle w (shuffle w f g) h s =
      ∑ z : LeftIndex s, (f (left z.2) * g (right z.2) * kernel w (left z.2) (right z.2)) *
        h (right z.1) * kernel w (left z.1) (right z.1) := by
    simp only [shuffle, Fintype.sum_sigma, Finset.sum_mul]
  have rhs : shuffle w f (shuffle w g h) s =
      ∑ z : RightIndex s, f (left z.1) *
        (g (left z.2) * h (right z.2) * kernel w (left z.2) (right z.2)) *
          kernel w (left z.1) (right z.1) := by
    simp only [shuffle, Fintype.sum_sigma, Finset.mul_sum, Finset.sum_mul]
  rw [lhs,rhs,← (rebracket s).sum_comp]
  apply Finset.sum_congr rfl
  intro z hz
  change (f (left z.2) * g (right z.2) * kernel w (left z.2) (right z.2)) *
      h (right z.1) * kernel w (left z.1) (right z.1) =
    f (left z.2) * (g (right z.2) * h (right z.1) * kernel w (right z.2) (right z.1)) *
      kernel w (left z.2) (fun i => right z.2 i ∪ right z.1 i)
  have hu : left z.1 = fun i => left z.2 i ∪ right z.2 i := by
    funext i; exact (z.2 i).property.2.symm
  have hk := congrArg (fun t => kernel w t (right z.1)) hu
  rw [hk, kernel_union_left w (left z.2) (right z.2) (right z.1) (fun i => (z.2 i).property.1),
    kernel_union_right w (left z.2) (right z.2) (right z.1) (fun i =>
      (z.1 i).property.1.mono_left (z.2 i).right_subset)]
  ac_rfl

end ElementaryPositivity.PackConvolution

namespace ElementaryPositivity.PackEnumeration
variable {A : Type*} [DecidableEq A]

abbrev Split (s : Finset A) :=
  {p : Finset A × Finset A // Disjoint p.1 p.2 ∧ p.1 ∪ p.2 = s}

def embedding {n : ℕ} {s : Finset A} (r : Fin n ≃ s) : Fin n ↪ A :=
  r.toEmbedding.trans (Function.Embedding.subtype _)

omit [DecidableEq A] in
lemma map_univ {n : ℕ} {s : Finset A} (r : Fin n ≃ s) :
    Finset.univ.map (embedding r) = s := by
  ext x
  simp only [Finset.mem_map, Finset.mem_univ, true_and, embedding,
    Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨y,rfl⟩; exact (r y).property
  · intro hx
    exact ⟨r.symm ⟨x,hx⟩,congrArg Subtype.val (r.apply_symm_apply ⟨x,hx⟩)⟩

def split {n : ℕ} {s : Finset A} (r : Fin n ≃ s) (t : Finset (Fin n)) : Split s :=
  ⟨(t.map (embedding r),tᶜ.map (embedding r)),
    (Finset.disjoint_map _).mpr (disjoint_compl_right), by
      rw [← Finset.map_union, Finset.union_compl, map_univ]⟩

lemma split_injective {n : ℕ} {s : Finset A} (r : Fin n ≃ s) : Function.Injective (split r) := by
  intro a b hab
  apply Finset.map_injective (embedding r)
  exact congrArg (fun p => p.val.1) hab

lemma split_right_unique {s : Finset A} (p q : Split s) (h : p.val.1 = q.val.1) : p = q := by
  apply Subtype.ext
  apply Prod.ext h
  have hp := p.property
  have hq := q.property
  apply Finset.ext
  intro x
  have hh : x ∈ p.val.2 ↔ x ∈ s ∧ x ∉ p.val.1 := by
    have hu : x ∈ s ↔ x ∈ p.val.1 ∨ x ∈ p.val.2 := by
      simpa only [Finset.mem_union] using (congrArg (fun t => x ∈ t) hp.2.symm).to_iff
    have hd : ¬(x ∈ p.val.1 ∧ x ∈ p.val.2) := by
      intro hmem
      exact Finset.disjoint_left.mp hp.1 hmem.1 hmem.2
    tauto
  have hh' : x ∈ q.val.2 ↔ x ∈ s ∧ x ∉ q.val.1 := by
    have hu : x ∈ s ↔ x ∈ q.val.1 ∨ x ∈ q.val.2 := by
      simpa only [Finset.mem_union] using (congrArg (fun t => x ∈ t) hq.2.symm).to_iff
    have hd : ¬(x ∈ q.val.1 ∧ x ∈ q.val.2) := by
      intro hmem
      exact Finset.disjoint_left.mp hq.1 hmem.1 hmem.2
    tauto
  rw [hh,hh',h]

lemma split_surjective {n : ℕ} {s : Finset A} (r : Fin n ≃ s) : Function.Surjective (split r) := by
  intro p
  let t := Finset.univ.filter fun j => ↑(r j) ∈ p.val.1
  refine ⟨t,split_right_unique _ _ ?_⟩
  change t.map (embedding r) = p.val.1
  ext x
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact (Finset.mem_filter.mp hj).2
  · intro hx
    have hs : x ∈ s := p.property.2 ▸ Finset.mem_union_left p.val.2 hx
    refine ⟨r.symm ⟨x,hs⟩,?_,?_⟩
    · simp [t,hx]
    · exact congrArg Subtype.val (r.apply_symm_apply ⟨x,hs⟩)

noncomputable def splitEquiv {n : ℕ} {s : Finset A} (r : Fin n ≃ s) : Finset (Fin n) ≃ Split s :=
  Equiv.ofBijective (split r) ⟨split_injective r,split_surjective r⟩

@[simp] lemma splitEquiv_left {n : ℕ} {s : Finset A} (r : Fin n ≃ s) (t : Finset (Fin n)) :
    (splitEquiv r t).val.1 = t.map (embedding r) := rfl
@[simp] lemma splitEquiv_right {n : ℕ} {s : Finset A} (r : Fin n ≃ s) (t : Finset (Fin n)) :
    (splitEquiv r t).val.2 = tᶜ.map (embedding r) := rfl

noncomputable def sizedSplitEquiv {n : ℕ} {s : Finset A} (r : Fin n ≃ s) (k : ℕ) :
    {t : Finset (Fin n) // t.card = k} ≃ {p : Split s // p.val.1.card = k} :=
  (splitEquiv r).subtypeEquiv (by intro t; simp)

noncomputable def mapEquiv {B : Type*} (f : B ↪ A) (t : Finset B) : ↥t ≃ ↥(t.map f) :=
  Equiv.ofBijective (fun x => ⟨f x.val,Finset.mem_map.mpr ⟨x.val,x.property,rfl⟩⟩)
    ⟨by
      intro x y h
      apply Subtype.ext
      exact f.injective (congrArg Subtype.val h), by
      intro y
      obtain ⟨x,hx,hxy⟩ := Finset.mem_map.mp y.property
      exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩⟩

omit [DecidableEq A] in
@[simp] lemma mapEquiv_apply {B : Type*} (f : B ↪ A) (t : Finset B) (x : t) :
    ↑(mapEquiv f t x) = f x.val := rfl

end ElementaryPositivity.PackEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Realization
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

abbrev Realization (d : I → ℕ) (s : ∀ i,Finset (A i)) := ∀ i,Fin (d i) ≃ s i

def realizationMap {d : I → ℕ} {s : ∀ i,Finset (A i)} (r : Realization d s) :
    (Σi,Fin (d i)) → (Σi,A i) := fun x => ⟨x.1,r x.1 x.2⟩

omit [Fintype I] [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma realizationMap_injective {d : I → ℕ} {s : ∀ i,Finset (A i)} (r : Realization d s) :
    Function.Injective (realizationMap r) := by
  exact (Function.Embedding.sigmaMap (Function.Embedding.refl I)
    (fun i => (r i).toEmbedding.trans (Function.Embedding.subtype _))).injective

noncomputable def valueAt {d : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization d s) (f : S d) : FractionRing (MvPolynomial (Σi,A i) ℚ) :=
  algebraMap _ _ (rename (realizationMap r) f.val)

noncomputable def defaultRealization {d : I → ℕ} {s : ∀ i,Finset (A i)}
    (h : ∀ i,(s i).card = d i) : Realization d s := fun i =>
  Fintype.equivOfCardEq (by simp [h i])

noncomputable def labeledValue {d : I → ℕ} (f : S d) (s : ∀ i,Finset (A i)) :
    FractionRing (MvPolynomial (Σi,A i) ℚ) :=
  if h : ∀ i,(s i).card = d i then valueAt (defaultRealization h) f else 0

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

abbrev SizedCut (d : I → ℕ) (s : ∀ i,Finset (A i)) :=
  {p : PackConvolution.Cut s // ∀ i,(PackConvolution.left p i).card = d i}

noncomputable def cutRealizationEquiv {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) : Cut d e ≃ SizedCut d s :=
  (Equiv.piCongrRight fun i => PackEnumeration.sizedSplitEquiv (r i) (d i)).trans
    Equiv.subtypePiEquivPi.symm

omit [Fintype I] [DecidableEq I] in
@[simp] lemma cutRealizationEquiv_left {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) (t : Cut d e) (i : I) :
    PackConvolution.left (cutRealizationEquiv r t).val i =
      (t i).val.map (PackEnumeration.embedding (r i)) := rfl
omit [Fintype I] [DecidableEq I] in
@[simp] lemma cutRealizationEquiv_right {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) (t : Cut d e) (i : I) :
    PackConvolution.right (cutRealizationEquiv r t).val i =
      (t i).valᶜ.map (PackEnumeration.embedding (r i)) := rfl

noncomputable def pairKernel (a : I → I → ℕ) (x y : Σi,A i) :
    FractionRing (MvPolynomial (Σi,A i) ℚ) :=
  let v := algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (diagonal x y)
  v^(a x.1 y.1) / if x.1 = y.1 then v else 1

omit [∀ i,DecidableEq (A i)] in
lemma kernel_formula (a : I → I → ℕ) (s t : ∀ i,Finset (A i)) :
    PackConvolution.kernel (pairKernel a) s t =
      (∏ i,∏ j,∏ x ∈ s i,∏ y ∈ t j,
        (algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (diagonal (⟨i,x⟩ : Σi,A i) ⟨j,y⟩))^(a i j)) /
      (∏ i,∏ x ∈ s i,∏ y ∈ t i,
        algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (diagonal (⟨i,x⟩ : Σi,A i) ⟨i,y⟩)) := by
  simp only [PackConvolution.kernel,pairKernel,Finset.prod_div_distrib]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact Finset.prod_comm
  · apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro x hx
    rw [Finset.prod_eq_single i]
    · simp
    · intro j hj hji
      simp only [ite_eq_right (Ne.symm hji),Finset.prod_const_one]
    · simp

variable [∀ i,Fintype (A i)]

def castS {d e : I → ℕ} (h : d=e) (f : S d) : S e := h ▸ f

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_RestrictSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.ShuffleConvolution
variable {A : Type*} [Fintype A] [DecidableEq A]

def restrictSplit {s t : Finset A} (ht : t ⊆ s) (q : Split s) : Split t :=
  ⟨(q.val.1 ∩ t,q.val.2 ∩ t),q.property.1.mono Finset.inter_subset_left Finset.inter_subset_left,by
    change (q.val.1 ∩ t) ∪ (q.val.2 ∩ t) = t
    rw [← Finset.union_inter_distrib_right,q.property.2]
    exact Finset.inter_eq_right.mpr ht⟩

def grid {s : Finset A} (p : Split s) : Split s ≃ Split p.val.1 × Split p.val.2 where
  toFun q := (restrictSplit p.left_subset q,restrictSplit p.right_subset q)
  invFun q := ⟨(q.1.val.1 ∪ q.2.val.1,q.1.val.2 ∪ q.2.val.2),by
    constructor
    · apply Finset.disjoint_union_left.mpr
      constructor
      · apply Finset.disjoint_union_right.mpr
        exact ⟨q.1.property.1,p.property.1.mono q.1.left_subset q.2.right_subset⟩
      · apply Finset.disjoint_union_right.mpr
        exact ⟨p.property.1.symm.mono q.2.left_subset q.1.right_subset,q.2.property.1⟩
    · calc
        (q.1.val.1 ∪ q.2.val.1) ∪ (q.1.val.2 ∪ q.2.val.2) =
            (q.1.val.1 ∪ q.1.val.2) ∪ (q.2.val.1 ∪ q.2.val.2) := by ac_rfl
        _ = s := by rw [q.1.property.2,q.2.property.2,p.property.2]⟩
  left_inv q := by
    apply Subtype.ext
    dsimp [restrictSplit]
    congr 1
    · rw [← Finset.inter_union_distrib_left,p.property.2]
      exact Finset.inter_eq_left.mpr q.left_subset
    · rw [← Finset.inter_union_distrib_left,p.property.2]
      exact Finset.inter_eq_left.mpr q.right_subset
  right_inv q := by
    apply Prod.ext <;> apply Subtype.ext
    · dsimp [restrictSplit]
      have h1 := p.property.1.symm.mono_left q.2.left_subset
      have h2 := p.property.1.symm.mono_left q.2.right_subset
      rw [Finset.union_inter_distrib_right,Finset.union_inter_distrib_right,
        Finset.inter_eq_left.mpr q.1.left_subset,Finset.inter_eq_left.mpr q.1.right_subset,
        Finset.disjoint_iff_inter_eq_empty.mp h1,Finset.disjoint_iff_inter_eq_empty.mp h2]
      simp
    · dsimp [restrictSplit]
      have h1 := p.property.1.mono_left q.1.left_subset
      have h2 := p.property.1.mono_left q.1.right_subset
      rw [Finset.union_inter_distrib_right,Finset.union_inter_distrib_right,
        Finset.inter_eq_left.mpr q.2.left_subset,Finset.inter_eq_left.mpr q.2.right_subset,
        Finset.disjoint_iff_inter_eq_empty.mp h1,Finset.disjoint_iff_inter_eq_empty.mp h2]
      simp

end ElementaryPositivity.ShuffleConvolution

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_Grid
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.PackConvolution
open ElementaryPositivity.ShuffleConvolution
variable {I : Type*} {A : I → Type*}
variable [∀ i,DecidableEq (A i)]
variable {R : Type*} [CommSemiring R]

def grid {s : Pack (A:=A)} (p : Cut s) : Cut s ≃ Cut (left p) × Cut (right p) :=
  (Equiv.piCongrRight fun i => ShuffleConvolution.grid (p i)).trans
    { toFun := fun q => (fun i => (q i).1, fun i => (q i).2)
      invFun := fun q i => (q.1 i,q.2 i)
      left_inv := by intro q; rfl
      right_inv := by intro q; rfl }

lemma grid_inverse_left {s : Pack (A:=A)} (p : Cut s) (q : Cut (left p)) (r : Cut (right p)) :
    left ((grid p).symm (q,r)) = fun i => left q i ∪ left r i := rfl
lemma grid_inverse_right {s : Pack (A:=A)} (p : Cut s) (q : Cut (left p)) (r : Cut (right p)) :
    right ((grid p).symm (q,r)) = fun i => right q i ∪ right r i := rfl

variable [Fintype I]

lemma grid_kernel (w : (Σi,A i) → (Σi,A i) → R)
    {s : Pack (A:=A)} (p : Cut s) (q : Cut (left p)) (r : Cut (right p)) :
    kernel w (left ((grid p).symm (q,r))) (right ((grid p).symm (q,r))) =
      kernel w (left q) (right q) * kernel w (left r) (right r) *
        kernel w (left q) (right r) * kernel w (left r) (right q) := by
  have hl : ∀ i,Disjoint (left q i) (left r i) := fun i =>
    (p i).property.1.mono (q i).left_subset (r i).left_subset
  have hr : ∀ i,Disjoint (right q i) (right r i) := fun i =>
    (p i).property.1.mono (q i).right_subset (r i).right_subset
  rw [grid_inverse_left,grid_inverse_right,
    kernel_union_left w (left q) (left r) (fun i => right q i ∪ right r i) hl,
    kernel_union_right w (left q) (right q) (right r) hr,
    kernel_union_right w (left r) (right q) (right r) hr]
  ac_rfl

variable [DecidableEq I] [∀ i,Fintype (A i)]

theorem shuffle_grid (w : (Σi,A i) → (Σi,A i) → R)
    (f g : Pack (A:=A) → R) {s : Pack (A:=A)} (p : Cut s) :
    shuffle w f g s = ∑ q : Cut (left p), ∑ r : Cut (right p),
      f (fun i => left q i ∪ left r i) * g (fun i => right q i ∪ right r i) *
        (kernel w (left q) (right q) * kernel w (left r) (right r) *
          kernel w (left q) (right r) * kernel w (left r) (right q)) := by
  rw [shuffle,← (grid p).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  rw [grid_kernel,grid_inverse_left,grid_inverse_right]

end ElementaryPositivity.PackConvolution

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SameDen
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
open ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

noncomputable def sameDen (s t : Pack (A:=A)) : MvPolynomial (Σi,A i) ℚ :=
  ∏ i,∏ x ∈ s i,∏ y ∈ t i,diagonal (⟨i,x⟩ : Σi,A i) ⟨i,y⟩

noncomputable def arrowNum (a : I → I → ℕ) (s t : Pack (A:=A)) : MvPolynomial (Σi,A i) ℚ :=
  ∏ i,∏ j,∏ x ∈ s i,∏ y ∈ t j,diagonal (⟨i,x⟩ : Σi,A i) ⟨j,y⟩ ^ a i j

omit [DecidableEq I] in
lemma sameDen_union_left (s t r : Pack (A:=A)) (h : ∀ i,Disjoint (s i) (t i)) :
    sameDen (fun i=>s i ∪ t i) r = sameDen s r * sameDen t r := by
  simp only [sameDen,Finset.prod_union (h _),Finset.prod_mul_distrib]

omit [DecidableEq I] in
lemma sameDen_union_right (s t r : Pack (A:=A)) (h : ∀ i,Disjoint (t i) (r i)) :
    sameDen s (fun i=>t i ∪ r i) = sameDen s t * sameDen s r := by
  simp only [sameDen,Finset.prod_union (h _),Finset.prod_mul_distrib]

omit [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma sameDen_ne_zero (s t : Pack (A:=A)) (h : ∀ i,Disjoint (s i) (t i)) :
    sameDen s t ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Finset.prod_ne_zero_iff.mpr
  intro x hx
  apply Finset.prod_ne_zero_iff.mpr
  intro y hy
  apply diagonal_ne_zero
  intro heq
  have hxy : x=y := eq_of_heq (Sigma.mk.inj_iff.mp heq).2
  exact Finset.disjoint_left.mp (h i) hx (hxy.symm ▸ hy)

omit [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma sameDen_reverse_dvd (s t : Pack (A:=A)) : sameDen s t ∣ sameDen t s := by
  unfold sameDen
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  rw [Finset.prod_comm]
  apply Finset.prod_dvd_prod_of_dvd
  intro x hx
  apply Finset.prod_dvd_prod_of_dvd
  intro y hy
  refine ⟨-1,?_⟩
  simp only [diagonal]
  ring

noncomputable def crossDen (q₁ q₂ r₁ r₂ : Pack (A:=A)) : MvPolynomial (Σi,A i) ℚ :=
  sameDen q₁ r₂ * sameDen r₁ q₂

omit [DecidableEq I] in
lemma crossDen_dvd {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (q : PackConvolution.Cut (left p)) (r : PackConvolution.Cut (right p)) :
    crossDen (left q) (right q) (left r) (right r) ∣ sameDen (left p) (right p) := by
  have hq : (fun i=>left q i ∪ right q i) = left p := funext fun i=>(q i).property.2
  have hr : (fun i=>left r i ∪ right r i) = right p := funext fun i=>(r i).property.2
  conv_rhs => rw [← hq,← hr]
  rw [sameDen_union_left (left q) (right q) (fun i=>left r i ∪ right r i) (fun i=>(q i).property.1),
    sameDen_union_right (left q) (left r) (right r) (fun i=>(r i).property.1),
    sameDen_union_right (right q) (left r) (right r) (fun i=>(r i).property.1)]
  apply dvd_trans (mul_dvd_mul_left (sameDen (left q) (right r))
    (sameDen_reverse_dvd (left r) (right q)))
  refine ⟨sameDen (left q) (left r) * sameDen (right q) (right r),?_⟩
  ac_rfl

omit [DecidableEq I] in
lemma crossDen_ne_zero {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (q : PackConvolution.Cut (left p)) (r : PackConvolution.Cut (right p)) :
    crossDen (left q) (right q) (left r) (right r) ≠ 0 := by
  apply mul_ne_zero
  · exact sameDen_ne_zero _ _ (fun i=>(p i).property.1.mono (q i).left_subset (r i).right_subset)
  · exact sameDen_ne_zero _ _ (fun i=>(p i).property.1.symm.mono (r i).left_subset (q i).right_subset)

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

abbrev CutShape (s : Pack (A:=A)) := ∀ i, Fin ((s i).card + 1)

def cutShape {s : Pack (A:=A)} (q : PackConvolution.Cut s) : CutShape s := fun i =>
  ⟨(left q i).card, Nat.lt_succ_of_le (Finset.card_le_card (q i).left_subset)⟩

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
lemma cutShape_eq_iff {s : Pack (A:=A)} (q : PackConvolution.Cut s) (d : CutShape s) :
    cutShape q = d ↔ ∀ i,(left q i).card = (d i).val := by
  constructor
  · intro h i
    exact congrArg Fin.val (congrFun h i)
  · intro h
    exact funext fun i=>Fin.ext (h i)

noncomputable def cutByShape (s : Pack (A:=A)) :
    PackConvolution.Cut s ≃ Σ d : CutShape s,SizedCut (fun i=>(d i).val) s :=
  (Equiv.sigmaFiberEquiv (cutShape (s:=s))).symm.trans
    (Equiv.sigmaCongrRight fun d=>Equiv.subtypeEquivRight fun q=>cutShape_eq_iff q d)

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
@[simp] lemma cutByShape_snd (s : Pack (A:=A)) (q : PackConvolution.Cut s) :
    (cutByShape s q).2.val = q := rfl

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
@[simp] lemma cutByShape_symm {s : Pack (A:=A)}
    (d : CutShape s) (q : SizedCut (fun i=>(d i).val) s) :
    (cutByShape s).symm ⟨d,q⟩ = q.val := rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_LabeledPolynomial
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.tensorValue_crossTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

noncomputable def labeledPolynomial {d : I → ℕ} (f : S d) (s : Pack (A:=A)) :
    MvPolynomial (Σi,A i) ℚ :=
  if h : ∀ i,(s i).card = d i then rename (realizationMap (defaultRealization h)) f.val else 0

omit [DecidableEq I] [∀ i,DecidableEq (A i)] in
@[simp] lemma labeledPolynomial_algebraMap {d : I → ℕ} (f : S d) (s : Pack (A:=A)) :
    algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (labeledPolynomial f s) =
      labeledValue f s := by
  unfold labeledPolynomial labeledValue
  split_ifs <;> simp [valueAt]

def mapPack (σ : ∀ i,Equiv.Perm (A i)) (s : Pack (A:=A)) : Pack (A:=A) :=
  fun i=>(s i).map (σ i).toEmbedding

noncomputable def mapPackCut (σ : ∀ i,Equiv.Perm (A i)) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) : PackConvolution.Cut (mapPack σ s) := fun i=>
  ⟨((left p i).map (σ i).toEmbedding,(right p i).map (σ i).toEmbedding),
    (Finset.disjoint_map _).mpr (p i).property.1,by
      rw [← Finset.map_union]
      change Finset.map (σ i).toEmbedding ((p i).val.1 ∪ (p i).val.2) = _
      rw [(p i).property.2]
      rfl⟩

omit [Fintype I] [DecidableEq I] in
@[simp] lemma mapPackCut_left (σ : ∀ i,Equiv.Perm (A i)) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) : left (mapPackCut σ p) = mapPack σ (left p) := rfl
omit [Fintype I] [DecidableEq I] in
@[simp] lemma mapPackCut_right (σ : ∀ i,Equiv.Perm (A i)) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) : right (mapPackCut σ p) = mapPack σ (right p) := rfl

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A B : I → Type*} [∀ i,DecidableEq (A i)] [∀ i,DecidableEq (B i)]

def embedPack (φ : ∀ i,A i ↪ B i) (s : Pack (A:=A)) : Pack (A:=B) :=
  fun i=>(s i).map (φ i)

noncomputable def embedPackCut (φ : ∀ i,A i ↪ B i) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) : PackConvolution.Cut (embedPack φ s) := fun i=>
  ⟨((left p i).map (φ i),(right p i).map (φ i)),
    (Finset.disjoint_map _).mpr (p i).property.1,by
      rw [← Finset.map_union]
      change Finset.map (φ i) ((p i).val.1 ∪ (p i).val.2) = _
      rw [(p i).property.2]
      rfl⟩

omit [Fintype I] [DecidableEq I] in
@[simp] lemma embedPackCut_left (φ : ∀ i,A i ↪ B i) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) : left (embedPackCut φ p) = embedPack φ (left p) := rfl
omit [Fintype I] [DecidableEq I] in
@[simp] lemma embedPackCut_right (φ : ∀ i,A i ↪ B i) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) : right (embedPackCut φ p) = embedPack φ (right p) := rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SumPackCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open ElementaryPositivity.SeparatedSymmetry
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A B : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
  [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)]

noncomputable def sumPackCut (A B : I → Type*) [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
    [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)] :
    PackConvolution.Cut (fun i=>(Finset.univ : Finset (A i ⊕ B i))) := fun i=>
  ⟨((Finset.univ.map Function.Embedding.inl),(Finset.univ.map Function.Embedding.inr)),by
    constructor
    · apply Finset.disjoint_left.mpr
      intro x hx hy
      simp only [Finset.mem_map,Finset.mem_univ,true_and] at hx hy
      obtain ⟨x,rfl⟩ := hx
      obtain ⟨y,h⟩ := hy
      change Sum.inr y = Sum.inl x at h
      cases h
    · ext x
      cases x <;> simp⟩

abbrev FourPacks (d₁ e₁ d₂ e₂ : I → ℕ) (i : I) :=
  (Fin (d₁ i) ⊕ Fin (e₁ i)) ⊕ (Fin (d₂ i) ⊕ Fin (e₂ i))

noncomputable def canonicalGridCut (d₁ e₁ d₂ e₂ : I → ℕ) :=
  sumPackCut (fun i=>Fin (d₁ i) ⊕ Fin (e₁ i)) (fun i=>Fin (d₂ i) ⊕ Fin (e₂ i))

noncomputable def canonicalLeftCut (d₁ e₁ d₂ e₂ : I → ℕ) :
    PackConvolution.Cut (left (canonicalGridCut d₁ e₁ d₂ e₂)) :=
  embedPackCut (fun _=>Function.Embedding.inl)
    (sumPackCut (fun i=>Fin (d₁ i)) (fun i=>Fin (e₁ i)))

noncomputable def canonicalRightCut (d₁ e₁ d₂ e₂ : I → ℕ) :
    PackConvolution.Cut (right (canonicalGridCut d₁ e₁ d₂ e₂)) :=
  embedPackCut (fun _=>Function.Embedding.inr)
    (sumPackCut (fun i=>Fin (d₂ i)) (fun i=>Fin (e₂ i)))

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TargetEmbedding
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.tensorValue_crossTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

noncomputable def targetEmbedding {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p)) :
    CellVars d e ↪ (Σi,A i) where
  toFun := Sum.elim (realizationMap R) (realizationMap T)
  inj' := by
    rintro (x|x) (y|y) h
    · exact congrArg Sum.inl (realizationMap_injective R h)
    · rcases x with ⟨i,x⟩
      rcases y with ⟨j,y⟩
      have hij := congrArg Sigma.fst h
      change i=j at hij
      subst j
      have hxy : (R i x).val = (T i y).val := eq_of_heq (Sigma.mk.inj_iff.mp h).2
      exact (Finset.disjoint_left.mp (p i).property.1 (R i x).property
        (hxy.symm ▸ (T i y).property)).elim
    · rcases x with ⟨i,x⟩
      rcases y with ⟨j,y⟩
      have hij := congrArg Sigma.fst h
      change i=j at hij
      subst j
      have hxy : (T i x).val = (R i y).val := eq_of_heq (Sigma.mk.inj_iff.mp h).2
      exact (Finset.disjoint_left.mp (p i).property.1 (R i y).property
        (hxy ▸ (T i x).property)).elim
    · exact congrArg Sum.inr (realizationMap_injective T h)

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

noncomputable def castTensor {d e d' e' : I → ℕ} (h : d=d') (k : e=e') :
    S d ⊗[ℚ] S e →ₗ[ℚ] S d' ⊗[ℚ] S e' := by
  subst d'
  subst e'
  exact LinearMap.id

noncomputable def targetValueAt {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p)) :
    S d ⊗[ℚ] S e →+ FractionRing (MvPolynomial (Σi,A i) ℚ) where
  toFun t := renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
    (localizeTensor d e t)
  map_zero' := by rw [map_zero,map_zero]
  map_add' := by intro f g; rw [map_add,map_add]

omit [Fintype I] [DecidableEq I] in
@[simp] lemma targetValueAt_apply {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p))
    (f : S d ⊗[ℚ] S e) :
    targetValueAt p R T f = renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
      (localizeTensor d e f) := rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GridShapeTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma realization_card {d : I → ℕ} {s : Pack (A:=A)} (R : Realization d s) :
    (fun i=>(s i).card) = d := by
  funext i
  simpa using (Fintype.card_congr (R i)).symm

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_Mass
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]

def mass (c : I → ℝ) (d : I → ℕ) : ℝ := ∑ i,(d i : ℝ) * c i

noncomputable def slope (c η : I → ℝ) (d : I → ℕ) : ℝ := mass η d / mass c d

lemma mass_add (c : I → ℝ) (d e : I → ℕ) : mass c (d+e) = mass c d + mass c e := by
  simp [mass,Nat.cast_add,add_mul,Finset.sum_add_distrib]

@[simp] lemma mass_zero (c : I → ℝ) : mass c 0 = 0 := by simp [mass]

end ElementaryPositivity.SlopeArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CanonicalCard
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

noncomputable def crossSign (d e : I → ℕ) : ℚ :=
  ∏ i, ∏ _ : Fin (d i), ∏ _ : Fin (e i), (-1:ℚ)

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def relativeTaylorB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    B a μ d ⊗[ℚ] B a μ e →ₐ[ℚ] Polynomial (B a μ d ⊗[ℚ] B a μ e) :=
  let L : B a μ d →ₐ[ℚ] Polynomial (B a μ d ⊗[ℚ] B a μ e) :=
    (Polynomial.mapAlgHom (Algebra.TensorProduct.includeLeft : B a μ d →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e)).comp (taylorB a μ d)
  let R : B a μ e →ₐ[ℚ] Polynomial (B a μ d ⊗[ℚ] B a μ e) :=
    Polynomial.CAlgHom.comp (Algebra.TensorProduct.includeRight : B a μ e →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e)
  Algebra.TensorProduct.lift (S:=ℚ) L R (fun x y => mul_comm (L x) (R y))

@[simp] lemma relativeTaylorB_tmul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (f : B a μ d) (g : B a μ e) :
    relativeTaylorB a μ d e (f ⊗ₜ[ℚ] g) =
      Polynomial.map (Algebra.TensorProduct.includeLeft : B a μ d →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e).toRingHom (taylorB a μ d f) *
      Polynomial.C ((1 : B a μ d) ⊗ₜ[ℚ] g) := by
  simp only [relativeTaylorB]
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_DimensionGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
variable {I : Type*}

abbrev DimensionSplit (d : I → ℕ) := ∀ i, Fin (d i + 1)

namespace DimensionSplit

def left {d : I → ℕ} (s : DimensionSplit d) : I → ℕ := fun i => (s i).val
def right {d : I → ℕ} (s : DimensionSplit d) : I → ℕ := fun i => d i - (s i).val

@[simp] lemma left_add_right {d : I → ℕ} (s : DimensionSplit d) : left s + right s = d := by
  funext i
  have hi := (s i).isLt
  simp only [Pi.add_apply, left, right]
  omega

@[ext] lemma ext {d : I → ℕ} {s t : DimensionSplit d} (h : left s = left t) : s = t := by
  funext i
  exact Fin.ext (congrFun h i)

def ofPair (a b : I → ℕ) {d : I → ℕ} (h : a+b=d) : DimensionSplit d :=
  fun i => ⟨a i, by have hi := congrFun h i; simp only [Pi.add_apply] at hi; omega⟩

@[simp] lemma left_ofPair (a b : I → ℕ) {d : I → ℕ} (h : a+b=d) :
    left (ofPair a b h) = a := rfl

@[simp] lemma right_ofPair (a b : I → ℕ) {d : I → ℕ} (h : a+b=d) :
    right (ofPair a b h) = b := by
  funext i
  have hi := congrFun h i
  simp only [Pi.add_apply] at hi
  simp only [right, ofPair]
  omega

@[simp] lemma ofPair_left_right {d : I → ℕ} (s : DimensionSplit d) :
    ofPair (left s) (right s) (left_add_right s) = s := by
  apply ext
  rfl

end DimensionSplit

open DimensionSplit

abbrev RowDimensionGrid (d e α β : I → ℕ) :=
  {s : DimensionSplit α × DimensionSplit β //
    left s.1 + left s.2 = d ∧ right s.1 + right s.2 = e}

abbrev ColumnDimensionGrid (d e α β : I → ℕ) :=
  {s : DimensionSplit d × DimensionSplit e //
    left s.1 + left s.2 = α ∧ right s.1 + right s.2 = β}

attribute [local instance] Classical.propDecidable

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_EulerForm
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.cutRealizationEquiv_left _root_.OAI.ElementaryPositivity.RawShuffle.cutRealizationEquiv_right _root_.OAI.ElementaryPositivity.RawShuffle.cutSplit_inl _root_.OAI.ElementaryPositivity.RawShuffle.cutSplit_inr _root_.OAI.ElementaryPositivity.RawShuffle.fourValue_tmul _root_.OAI.ElementaryPositivity.RawShuffle.labeledPolynomial_algebraMap _root_.OAI.ElementaryPositivity.RawShuffle.localizeS_apply _root_.OAI.ElementaryPositivity.RawShuffle.map_taylorS _root_.OAI.ElementaryPositivity.RawShuffle.map_taylorSValue _root_.OAI.ElementaryPositivity.RawShuffle.mem_destabilizingIdeal _root_.OAI.ElementaryPositivity.RawShuffle.packSplit_inl _root_.OAI.ElementaryPositivity.RawShuffle.packSplit_inr _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlg_apply _root_.OAI.ElementaryPositivity.RawShuffle.relativeTaylorB_tmul _root_.OAI.ElementaryPositivity.RawShuffle.relativeTaylor_tmul _root_.OAI.ElementaryPositivity.RawShuffle.reynoldsS_val _root_.OAI.ElementaryPositivity.RawShuffle.separateFour_fourValue _root_.OAI.ElementaryPositivity.RawShuffle.separateFour_product _root_.OAI.ElementaryPositivity.RawShuffle.separateTensor_product _root_.OAI.ElementaryPositivity.RawShuffle.separateTensor_tensorValue _root_.OAI.ElementaryPositivity.RawShuffle.shuffleTensorLinear_tmul _root_.OAI.ElementaryPositivity.RawShuffle.targetValueAt_apply _root_.OAI.ElementaryPositivity.RawShuffle.taylorB_mk _root_.OAI.ElementaryPositivity.RawShuffle.tensorValueAlg_apply _root_.OAI.ElementaryPositivity.RawShuffle.tensorValue_crossTensor _root_.OAI.ElementaryPositivity.RawShuffle.tensorValue_restrictTensor _root_.OAI.ElementaryPositivity.RawShuffle.tensorValue_tmul _root_.OAI.ElementaryPositivity.RawShuffle.twoTargetTransfer_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.Homogeneity
variable {I : Type*} [Fintype I] [DecidableEq I]

def eulerForm (a : I → I → ℕ) (d e : I → ℕ) : ℤ :=
  (∑ i,(d i:ℤ)*e i) - ∑ i, ∑ j,(a i j:ℤ)*d i*e j

lemma diagonal_homogeneous {σ : Type*} (i j : σ) :
    (diagonal i j : MvPolynomial σ ℚ).IsWeightedHomogeneous (fun _=>(1:ℤ)) 1 :=
  (isWeightedHomogeneous_X ℚ (fun _=>(1:ℤ)) j).sub
    (isWeightedHomogeneous_X ℚ (fun _=>(1:ℤ)) i)

omit [Fintype I] [DecidableEq I] in
lemma cutFactor_homogeneous {d e : I → ℕ} (A : Cut d e) (i j : I) (k : ℕ) :
    (cutFactor A i j k).IsWeightedHomogeneous (fun _=>(1:ℤ)) ((d i:ℤ)*e j*k) := by
  classical
  unfold cutFactor
  have h := IsWeightedHomogeneous.prod (A i).val _ _ (fun x _=>
    IsWeightedHomogeneous.prod (A j).valᶜ _ _
      (fun y _=> (diagonal_homogeneous (⟨i,x⟩ : Σi,Fin (d i+e i)) ⟨j,y⟩).pow k))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,(A i).property,right_card]
  ring

omit [DecidableEq I] in
lemma cutDenominator_homogeneous {d e : I → ℕ} (A : Cut d e) :
    (cutDenominator A).IsWeightedHomogeneous (fun _=>(1:ℤ)) (∑ i,(d i:ℤ)*e i) := by
  unfold cutDenominator
  simpa only [Nat.cast_one,mul_one] using IsWeightedHomogeneous.prod Finset.univ _ _
    (fun i _=> cutFactor_homogeneous A i i 1)

omit [DecidableEq I] in
lemma cutNumerator_homogeneous (a : I → I → ℕ) {d e : I → ℕ} (A : Cut d e)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ)
    {m n : ℤ} (hf : f.IsWeightedHomogeneous (fun _=>(1:ℤ)) m)
    (hg : g.IsWeightedHomogeneous (fun _=>(1:ℤ)) n) :
    (cutNumerator a A f g).IsWeightedHomogeneous (fun _=>(1:ℤ))
      (m+n+ ∑ i, ∑ j,(a i j:ℤ)*d i*e j) := by
  unfold cutNumerator
  have h := (constantWeight_rename (leftInput A) f hf).mul
    (constantWeight_rename (rightInput A) g hg)
  have hk := IsWeightedHomogeneous.prod Finset.univ _ _ (fun i _=>
    IsWeightedHomogeneous.prod Finset.univ _ _
      (fun j _=> cutFactor_homogeneous A i j (a i j)))
  have heq : (∑ i, ∑ j,(d i:ℤ)*e j*a i j) =
      ∑ i, ∑ j,(a i j:ℤ)*d i*e j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq] at hk
  exact h.mul hk

omit [DecidableEq I] in
lemma naturalVandermonde_homogeneous (d : I → ℕ) :
    (naturalVandermonde d (fun _=>True)).IsWeightedHomogeneous (fun _=>(1:ℤ))
      (naturalPairs d (fun _=>True)).card := by
  classical
  rw [naturalVandermonde_product]
  simpa using IsWeightedHomogeneous.prod (naturalPairs d (fun _=>True)) _ _
    (fun p _=> diagonal_homogeneous (finPackPair d p).1 (finPackPair d p).2)

theorem shufflePolynomial_homogeneous (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g : S e) {m n : ℤ}
    (hf : f.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) m)
    (hg : g.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) n) :
    (shufflePolynomial a f g).val.IsWeightedHomogeneous (fun _=>(1:ℤ))
      (m+n-eulerForm a d e) := by
  classical
  let V := naturalVandermonde (d+e) (fun _=>True)
  let v : ℤ := (naturalPairs (d+e) (fun _=>True)).card
  have hV : V.IsWeightedHomogeneous (fun _=>(1:ℤ)) v := naturalVandermonde_homogeneous _
  have hV0 : V≠0 := naturalVandermonde_ne_zero _ _
  have hb : ∀ A : Cut d e, ∃ b, V = cutDenominator A * b := fun A=> cutDenominator_dvd A
  choose b hb using hb
  have hbhome (A : Cut d e) : (b A).IsWeightedHomogeneous (fun _=>(1:ℤ))
      (v- ∑ i,(d i:ℤ)*e i) :=
    Homogeneity.of_mul (cutDenominator A) (b A) (cutDenominator_homogeneous A)
      (cutDenominator_ne_zero A) (by rw [← hb]; exact hV)
  have hclear : V*(shufflePolynomial a f g).val = ∑ A : Cut d e,b A*cutNumerator a A f.val g.val := by
    apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
    rw [map_mul,shufflePolynomial_eq,rawShuffle,Finset.mul_sum,map_sum]
    apply Finset.sum_congr rfl
    intro A hA
    rw [hb A,map_mul,map_mul]
    have hden : algebraMap _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
        (cutDenominator A) ≠ 0 :=
      by
        intro hz
        apply cutDenominator_ne_zero A
        exact (IsFractionRing.injective (MvPolynomial (Σi,Fin (d i+e i)) ℚ)
          (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))) (by simpa only [map_zero] using hz)
    let φ := algebraMap (MvPolynomial (Σi,Fin (d i+e i)) ℚ)
      (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
    change (φ (cutDenominator A) * φ (b A)) *
      (φ (cutNumerator a A f.val g.val) / φ (cutDenominator A)) =
      φ (b A) * φ (cutNumerator a A f.val g.val)
    change φ (cutDenominator A) ≠ 0 at hden
    field_simp
  have hhom : (V*(shufflePolynomial a f g).val).IsWeightedHomogeneous
      (fun _=>(1:ℤ)) (v+(m+n-eulerForm a d e)) := by
    rw [hclear]
    apply IsWeightedHomogeneous.sum
    intro A hA
    convert (hbhome A).mul (cutNumerator_homogeneous a A f.val g.val hf hg) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [eulerForm]
    ring
  have hh := Homogeneity.of_mul V (shufflePolynomial a f g).val hV hV0 hhom
  simpa only [add_sub_cancel_left] using hh

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def componentS (d : I → ℕ) (k : ℤ) : S d →ₗ[ℚ] S d where
  toFun f := ⟨weightedHomogeneousComponent (fun _=>(1:ℤ)) k f.val, by
    intro σ
    rw [constantWeight_component_rename,f.property σ]⟩
  map_add' f g := Subtype.ext (map_add _ _ _)
  map_smul' r f := Subtype.ext (map_smul _ _ _)

omit [Fintype I] [DecidableEq I] in
@[simp] lemma componentS_val (d : I → ℕ) (k : ℤ) (f : S d) :
    (componentS d k f).val = weightedHomogeneousComponent (fun _=>(1:ℤ)) k f.val := rfl

omit [Fintype I] [DecidableEq I] in
lemma componentS_homogeneous (d : I → ℕ) (k : ℤ) (f : S d) :
    (componentS d k f).val.IsWeightedHomogeneous (fun _=>(1:ℤ)) k :=
  weightedHomogeneousComponent_isWeightedHomogeneous _ _

omit [Fintype I] [DecidableEq I] in
lemma sum_componentS (d : I → ℕ) (f : S d) :
    ∑ k ∈ degreeSet f.val,componentS d k f = f := by
  apply Subtype.ext
  change (symmetricSpace d).val (∑ k ∈ degreeSet f.val,componentS d k f) = f.val
  rw [map_sum]
  exact sum_components f.val

omit [Fintype I] [DecidableEq I] in
lemma componentS_of_homogeneous (d : I → ℕ) (f : S d) {m : ℤ}
    (hf : f.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) m) (k : ℤ) :
    componentS d k f = if k=m then f else 0 := by
  classical
  apply Subtype.ext
  change weightedHomogeneousComponent (fun _=>(1:ℤ)) k f.val = _
  rw [weightedHomogeneousComponent_of_mem hf]
  split_ifs <;> rfl

omit [Fintype I] [DecidableEq I] in
lemma homogeneous_dimensionCast {d e : I → ℕ} (h : d=e) (f : S d) {k : ℤ}
    (hf : f.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) k) :
    (dimensionCast h f).val.IsWeightedHomogeneous (fun _=>(1:ℤ)) k := by
  subst e
  exact hf

lemma shuffleLinear_apply (a : I → I → ℕ) (d e : I → ℕ) (f : S d) (g : S e) :
    shuffleLinear a d e f g = shufflePolynomial a f g := rfl

lemma shuffle_sum_components (a : I → I → ℕ) {d e : I → ℕ} (f : S d) (g : S e) :
    shufflePolynomial a f g =
    ∑ k ∈ degreeSet f.val, ∑ l ∈ degreeSet g.val,
      shufflePolynomial a (componentS d k f) (componentS e l g) := by
  change shuffleLinear a d e f g = _
  conv_lhs => rw [← sum_componentS d f,← sum_componentS e g]
  simp only [map_sum,LinearMap.sum_apply,shuffleLinear_apply]
  rw [Finset.sum_comm]

theorem componentS_destabilizing_mem (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k : ℤ) (f : S d) (hf : f ∈ destabilizingSpace a μ d) :
    componentS d k f ∈ destabilizingSpace a μ d := by
  classical
  apply Submodule.span_induction (p:=fun x _=> componentS d k x ∈ destabilizingSpace a μ d)
    ?_ ?_ ?_ ?_ hf
  · intro F hF
    obtain ⟨u,v,h,f,g,hu,hv,hμ,rfl⟩ := hF
    rw [shuffle_sum_components a f g,map_sum,map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [map_sum,map_sum]
    apply Submodule.sum_mem
    intro j hj
    have hhom := homogeneous_dimensionCast h
      (shufflePolynomial a (componentS u i f) (componentS v j g))
      (shufflePolynomial_homogeneous a _ _ (componentS_homogeneous u i f)
        (componentS_homogeneous v j g))
    rw [componentS_of_homogeneous _ _ hhom]
    split_ifs
    · apply Submodule.subset_span
      exact ⟨u,v,h,componentS u i f,componentS v j g,hu,hv,hμ,rfl⟩
    · exact Submodule.zero_mem _
  · simp
  · intro x y hx hy hxc hyc
    simpa only [map_add] using (destabilizingSpace a μ d).add_mem hxc hyc
  · intro r x hx hxc
    simpa only [map_smul] using (destabilizingSpace a μ d).smul_mem r hxc

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalTensorDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
universe u v w i j
variable {K : Type u} [Field K]
variable {M : Type v} [AddCommGroup M] [Module K M]
variable {N : Type w} [AddCommGroup N] [Module K N]

noncomputable def additiveTensorFiltration (F : ℤ → Submodule K M)
    (G : ℤ → Submodule K N) (W : ℤ) : Submodule K (M ⊗[K] N) :=
  Submodule.span K {z | ∃ u v x y, W≤u+v ∧ x∈F u ∧ y∈G v ∧ z=x⊗ₜ[K]y}

end ElementaryPositivity.LinearDetection

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentPolynomialAction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R]

noncomputable def polynomialLinear : Polynomial R →ₗ[ℚ] LaurentSeries R where
  toFun := polynomial
  map_add' := polynomial.map_add
  map_smul' q p := by
    change polynomial (q • p)=q • polynomial p
    induction p using Polynomial.induction_on' with
    | add p r hp hr => simp only [smul_add,map_add,hp,hr]
    | monomial n r =>
      simp only [Polynomial.smul_monomial,polynomial_monomial]
      exact (single.linearMap (R:=ℚ) (-(n:ℤ))).map_smul q r

noncomputable def mulPolynomial (k : LaurentSeries R) : Polynomial R →ₗ[ℚ] LaurentSeries R :=
  (LinearMap.mulLeft ℚ k).comp polynomialLinear
@[simp] lemma mulPolynomial_apply (k : LaurentSeries R) (p : Polynomial R) :
    mulPolynomial k p=k*polynomial p := rfl
noncomputable def mulPolynomialCoeff (k : LaurentSeries R) (j : ℤ) : Polynomial R →ₗ[ℚ] R :=
  (coeff.linearMap (R:=ℚ) (-j)).comp (mulPolynomial k)
@[simp] lemma mulPolynomialCoeff_apply (k : LaurentSeries R) (j : ℤ) (p : Polynomial R) :
    mulPolynomialCoeff k j p=(k*polynomial p).coeff (-j) := rfl
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_InputOrderedEnergy
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open WeightedTorusSeries
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ)

def crossDiagonal (d : I → ℕ) : ℤ := ∑i,(1-(a i i:ℤ))*(d i:ℤ)^2

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_OrderedRootReordering
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open RawShuffle SlopeArithmetic WeightedTorusSeries WallUnits UnitSelections PowerSeries
noncomputable section
variable {M J : Type*} [AddCommGroup M] [Fintype J]
variable (Ω : M→+M→+ℤ) (C : (J→ℤ)→+M) (L h : M→+ℝ) (V : AddSubmonoid M)

def orderedPlaneProducts : Set (PowerSeries (Torus LaurentRay.vUnit Ω)) :=
  {F | ∃l : List (WallUnitDatum M),
    (∀u∈l,u.Allowed C (fun p=>p∈V ∧ 0<L p)) ∧
    l.Pairwise (fun u v=>0≤Ω u.root v.root) ∧ F=(l.map (WallUnitDatum.value Ω)).prod}

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end


