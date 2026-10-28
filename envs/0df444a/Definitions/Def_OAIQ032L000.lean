-- Prove2me | Definitions.Def_OAIQ032L000
-- name    : OAIQ032L000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:42:10.835246+00:00
-- url     : https://prove2.me/theorems/f78c55fb-728f-4cdf-a10d-b26dc64d6772
-- title:
--   Definitions bundle OAIQ032L000 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 103 declarations of OpenAI's Lean: 52 definitions, 2 inductive types or structures, 1 instance and 48 theorems. The definitions and types are `OAI.Lech.ActualCech.Allowed`, `OAI.Lech.ActualCech.Cochains`, `OAI.Lech.ActualCech.Row`, `OAI.Lech.ActualCech.allowedSet`, `OAI.Lech.ActualCech.chosen`, `OAI.Lech.ActualCech.contraction`, `OAI.Lech.ActualCech.d`, `OAI.Lech.ActualCech.delta`, `OAI.Lech.ActualCech.exponentEquiv`, `OAI.Lech.ActualCech.extra`, `OAI.Lech.ActualCech.homogeneous`, `OAI.Lech.ActualCech.homogeneousD`, `OAI.Lech.ActualCech.intersection`, `OAI.Lech.ActualCech.laurentCochains`, `OAI.Lech.ActualCech.laurentD`, `OAI.Lech.ActualCech.laurentEquiv`, `OAI.Lech.ActualCech.supportedTranspose`, `OAI.Lech.ActualCech.transpose`, `OAI.Lech.AdicFlat.contract`, `OAI.Lech.AllModuleLength`, `OAI.Lech.AllModuleLength.torsionLength`, `OAI.Lech.AlternatingCech.Alt`, `OAI.Lech.AlternatingCech.basis`, `OAI.Lech.AlternatingCech.cochains`, `OAI.Lech.AlternatingCech.delete`, `OAI.Lech.AlternatingCech.epsilon`, `OAI.Lech.AlternatingCech.evaluation`, `OAI.Lech.AlternatingCech.sorted`, `OAI.Lech.AlternatingCech.sortedCoordinates`, `OAI.Lech.AlternatingCech.sortedDelta`, `OAI.Lech.AlternatingCech.unaugmentedAugmentation`, `OAI.Lech.AlternatingCech.unaugmentedEquiv`, `OAI.Lech.AlternatingCech.unaugmentedInclusion`, `OAI.Lech.AlternatingCech.zeroAugmentation`, `OAI.Lech.BinaryChange.Binary`, `OAI.Lech.FiniteCoverCech.Row`, `OAI.Lech.FiniteCoverCech.cochains`, `OAI.Lech.FiniteCoverCech.intersection`, `OAI.Lech.PartialLaurent.Laurent`, `OAI.Lech.PartialLaurent.Poly` and 14 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_ActualCechTranspose`, `Multiplicity_AdicDense`, `Multiplicity_AdicFlatCriterion`, `Multiplicity_AlternatingCechAlt`, `Multiplicity_AlternatingCechUnaugmentedComplex`, `Multiplicity_FilteredFractionReesDenominatorTheory`, `Multiplicity_FiniteComplexTopInclusion`, `Multiplicity_LechConnectingIso`, `Multiplicity_LechTorsionOf`, `Multiplicity_PartialLaurentTotalDegree`, `Multiplicity_PowerSeriesFinDimension`, `Multiplicity_PrimitiveChartFaithfullyFlat`, `Multiplicity_ProductSourceCoverFaceSlice`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L010`, `OAIQ032L011`, `OAIQ032L012`, `OAIQ032L013`, `OAIQ032L014`, `OAIQ032L015`, `OAIQ032L016`, `OAIQ032L017` and `OAIQ032L018`; the statements `OAI.Lech.CharP.dutta_limit_from_perfection`, `OAI.Lech.CharP.normalized_perfection_module_finite` and `OAI.Lech.CharP.perfection_complex_value`; the proofs of `OAI.Lech.FrobeniusIntermediate.exists_positive_module_rank_transfer`, `OAI.Lech.TensorGenerator.length_le`, `OAI.Lech.TensorGenerator.scalar_cokernel_le`, `OAI.Lech.exists_frobenius_tensor_transfer` and `OAI.Lech.frobeniusModule_finiteLength`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ032_LECH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
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
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteComplexTopInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech

section

section
universe u
variable {R : Type u} [CommRing R]

 
def powerTorsion (I : Ideal R) : ObjectProperty (ModuleCat.{u} R) :=
  fun M => ∃ n : ℕ, I ^ n ≤ Module.annihilator R M


structure TorsionLength (I : Ideal R) where
  value : ModuleCat.{u} R → ℝ≥0∞
  zero : ∀ {M}, IsZero M → value M = 0
  additive : ∀ {S : ShortComplex (ModuleCat.{u} R)}, S.ShortExact →
    powerTorsion I S.X₂ → value S.X₂ = value S.X₁ + value S.X₃

end


universe u v
end


universe u
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechTorsionOf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory

attribute [local instance] Classical.propDecidable
namespace Lech
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal DirectSum
universe u
 

structure AllModuleLength (C : Type u) [CommRing C] where
  value : ModuleCat.{u} C → ℝ≥0∞
  zero : ∀ {M}, IsZero M → value M = 0
  additive : ∀ {S : ShortComplex (ModuleCat.{u} C)}, S.ShortExact →
    value S.X₂ = value S.X₁ + value S.X₃
  directSum_zero : ∀ {ι : Type u} (G : ι → Type u) [∀ i, AddCommGroup (G i)]
    [∀ i, Module C (G i)],
    (∀ i, value (ModuleCat.of C (G i)) = 0) → value (ModuleCat.of C (⨁ i, G i)) = 0
  iSup_zero : ∀ {ι M : Type u} [AddCommGroup M] [Module C M]
    (U : ι → Submodule C M),
    (∀ i, value (ModuleCat.of C (U i)) = 0) →
      value (ModuleCat.of C (⨆ i, U i : Submodule C M)) = 0
  directLimit_zero : ∀ {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (G : ι → Type u) [∀ i, AddCommGroup (G i)] [∀ i, Module C (G i)]
    (g : ∀ i j, i ≤ j → G i →ₗ[C] G j),
    (∀ i, value (ModuleCat.of C (G i)) = 0) →
      value (ModuleCat.of C (Module.DirectLimit G g)) = 0

namespace AllModuleLength
variable {C : Type u} [CommRing C] (ell : AllModuleLength C)
 
def torsionLength (I : Ideal C) : TorsionLength I where
  value := ell.value
  zero := ell.zero
  additive h _ := ell.additive h

end AllModuleLength
end Lech


namespace Lech.PartialLaurent
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))
 
def exponents : AddSubmonoid (Fin h → ℤ) where
  carrier := {e | ∀ i, i ∉ s → 0 ≤ e i}
  zero_mem' := by simp
  add_mem' := by
    intro e f he hf i hi
    exact add_nonneg (he i hi) (hf i hi)
abbrev Poly := AddMonoidAlgebra R (Fin h → ℕ)
abbrev Laurent := AddMonoidAlgebra R (exponents s)
def fromNat : (Fin h → ℕ) →+ exponents s where
  toFun a := ⟨fun i => (a i : ℤ),fun _ _ => Int.natCast_nonneg _⟩
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp
def toLaurent : Poly R (h := h) →+* Laurent R s :=
  mapDomainRingHom R (fromNat s)
instance instAlgebraPolyLaurent : Algebra (Poly R (h := h)) (Laurent R s) := (toLaurent R s).toAlgebra
@[simp] lemma algebraMap_single (a : Fin h → ℕ) (r : R) :
    algebraMap (Poly R (h := h)) (Laurent R s) (single a r) = single (fromNat s a) r := by
  exact mapDomain_single

def exponentInclusion {s t : Finset (Fin h)} (hst : s ⊆ t) : exponents s →+ exponents t where
  toFun e := ⟨e.val,fun i hi => e.property i (fun his => hi (hst his))⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def restrict {s t : Finset (Fin h)} (hst : s ⊆ t) : Laurent R s →+* Laurent R t :=
  mapDomainRingHom R (exponentInclusion hst)
@[simp] lemma restrict_single {s t : Finset (Fin h)} (hst : s ⊆ t)
    (e : exponents s) (a : R) :
    restrict R hst (single e a) = single (exponentInclusion hst e) a := mapDomain_single

def degree (e : exponents s) : ℤ := ∑ i, e.val i
 
def homogeneous (t : ℤ) : Submodule R (Laurent R s) :=
  (Finsupp.supported R R {e : exponents s | degree s e = t}).comap
    (coeffLinearEquiv R).toLinearMap

def homogeneousCoefficients (t : ℤ) :
    homogeneous R s t ≃ₗ[R] Finsupp.supported R R {e : exponents s | degree s e = t} where
  toFun a := ⟨(coeffLinearEquiv R) a.val,a.property⟩
  invFun a := ⟨(coeffLinearEquiv R).symm a.val,by
    unfold homogeneous
    apply Submodule.mem_comap.mpr
    simpa only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using a.property⟩
  left_inv a := Subtype.ext (LinearEquiv.symm_apply_apply (coeffLinearEquiv R) a.val)
  right_inv a := Subtype.ext (LinearEquiv.apply_symm_apply (coeffLinearEquiv R) a.val)
  map_add' a b := Subtype.ext (map_add (coeffLinearEquiv R) a.val b.val)
  map_smul' r a := Subtype.ext (map_smul (coeffLinearEquiv R) r a.val)
 

def homogeneousEquiv (t : ℤ) : homogeneous R s t ≃ₗ[R]
    ({e : exponents s // degree s e = t} →₀ R) :=
  (homogeneousCoefficients R s t).trans (Finsupp.supportedEquivFinsupp _)
end Lech.PartialLaurent

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PartialLaurentTotalDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
namespace Lech.PartialLaurent
open AddMonoidAlgebra HomogeneousLocalization
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))
def totalDegreeInt : exponents s →+ ℤ where
  toFun := degree s
  map_zero' := by simp [degree]
  map_add' a b := by simp [degree,Finset.sum_add_distrib]
abbrev laurentGrade := gradeBy R (totalDegreeInt s)
end Lech.PartialLaurent


namespace Lech.PartialLaurent
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] {h : ℕ}
lemma restrict_homogeneous {s t : Finset (Fin h)} (hst : s ⊆ t)
    {d : ℤ} {a : Laurent R s} (ha : a ∈ laurentGrade R s d) :
    restrict R hst a ∈ laurentGrade R t d := by
  classical
  intro e he
  change e ∈ (Finsupp.mapDomain (exponentInclusion hst) a.coeff).support at he
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support he)
  exact ha v hv

end Lech.PartialLaurent


namespace Lech.PartialLaurent
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] {h : ℕ}

def coefficientChartRestrict {s v : Finset (Fin h)} (hsv : s ⊆ v) (d : ℤ) :
    homogeneous R s d →ₗ[R] homogeneous R v d where
  toFun a := ⟨restrict R hsv a.val, restrict_homogeneous R hsv a.property⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' c a := by
    apply Subtype.ext
    apply coeff_injective
    exact Finsupp.mapDomain_smul c a.val.coeff



end Lech.PartialLaurent


namespace Lech.ActualCech
open scoped BigOperators
universe u v
variable (A : Type u) [CommRing A] {ι : Type v}
abbrev Row (n : ℕ) := (Fin n → ι) → A
 

def delta (n : ℕ) : Row A (ι := ι) n →ₗ[A] Row A (ι := ι) (n+1) where
  toFun f a := ∑ i : Fin (n+1), (-1 : A)^i.val * f (a ∘ i.succAbove)
  map_add' f g := by ext a; simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    ext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
 
def extra (j : ι) (n : ℕ) : Row A (ι := ι) (n+1) →ₗ[A] Row A (ι := ι) n where
  toFun f a := f (Fin.cons j a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma delete_insert_zero {n : ℕ} (j : ι) (a : Fin n → ι) :
    Fin.cons j a ∘ (0 : Fin (n+1)).succAbove = a := by
  funext i
  simp
lemma delete_insert_succ {n : ℕ} (j : ι) (a : Fin (n+1) → ι) (i : Fin (n+1)) :
    Fin.cons j a ∘ i.succ.succAbove = Fin.cons j (a ∘ i.succAbove) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · simp [Fin.succ_succAbove_succ]

 
lemma extra_delta (j : ι) (n : ℕ) (f : Row A (ι := ι) (n+1)) :
    extra A j (n+1) (delta A (n+1) f) + delta A n (extra A j n f) = f := by
  ext a
  change (∑ i : Fin (n+2), (-1 : A)^i.val * f (Fin.cons j a ∘ i.succAbove)) +
      (∑ i : Fin (n+1), (-1 : A)^i.val * f (Fin.cons j (a ∘ i.succAbove))) = f a
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_mul,delete_insert_zero,Fin.val_succ,
    pow_succ,delete_insert_succ,mul_neg_one,neg_mul,Finset.sum_neg_distrib]
  abel



lemma delta_square (n : ℕ) (f : Row A (ι := ι) n) :
    delta A (n+1) (delta A n f) = 0 := by
  induction n with
  | zero =>
    ext a
    have hf (b : Fin 0 → ι) : f b = f Fin.elim0 := congrArg f (Subsingleton.elim _ _)
    simp [delta,Fin.sum_univ_two,hf]
  | succ n ih =>
    have hh (j : ι) : extra A j (n+2) (delta A (n+2) (delta A (n+1) f))=0 := by
      have h₁ := extra_delta A j (n+1) (delta A (n+1) f)
      have h₂ := congrArg (delta A (n+1)) (extra_delta A j n f)
      rw [map_add, ih, add_zero] at h₂
      rw [h₂] at h₁
      exact add_right_cancel (h₁.trans (zero_add _).symm)
    ext a
    have he := congrFun (hh (a 0)) (fun i => a i.succ)
    change delta A (n+2) (delta A (n+1) f) (Fin.cons (a 0) (Fin.tail a))=0 at he
    rw [Fin.cons_self_tail] at he
    exact he

 

abbrev Cochains (h n : ℕ) := (Fin h → ℤ) →₀ Row A (ι := Fin h) n

def d (h n : ℕ) : Cochains A h n →ₗ[A] Cochains A h (n+1) :=
  Finsupp.mapRange.linearMap (delta A n)
@[simp] lemma d_apply (h n : ℕ) (f : Cochains A h n) (e : Fin h → ℤ) :
    d A h n f e = delta A n (f e) := rfl

 

def Allowed {h n : ℕ} (e : Fin h → ℤ) (a : Fin n → Fin h) : Prop :=
  ∀ i, e i < 0 → i ∈ Set.range a

def homogeneous (h n : ℕ) (t : ℤ) : Submodule A (Cochains A h n) where
  carrier := {f | ∀ e a, (∑ i, e i) ≠ t ∨ ¬ Allowed e a → f e a=0}
  zero_mem' := by intro e a he; rfl
  add_mem' := by intro f g hf hg e a he; change f e a + g e a=0; rw [hf e a he,hg e a he,add_zero]
  smul_mem' := by intro r f hf e a he; change r * f e a = 0; rw [hf e a he,mul_zero]

lemma d_mem {h n : ℕ} {t : ℤ} {f : Cochains A h n} (hf : f ∈ homogeneous A h n t) :
    d A h n f ∈ homogeneous A h (n+1) t := by
  intro e a he
  change (∑ i : Fin (n+1), (-1 : A)^i.val * f e (a ∘ i.succAbove))=0
  apply Finset.sum_eq_zero
  intro i _
  rw [hf e (a ∘ i.succAbove) ?_, mul_zero]
  rcases he with he | he
  · exact Or.inl he
  · right
    intro hg
    apply he
    intro j hj
    obtain ⟨k,hk⟩ := hg j hj
    exact ⟨i.succAbove k,hk⟩

lemma exists_nonneg {h : ℕ} (hh : 0<h) {e : Fin h → ℤ} (he : 0 ≤ ∑ i,e i) :
    ∃ j, 0 ≤ e j := by
  by_contra hn
  have hneg : ∀ j, e j < 0 := fun j => lt_of_not_ge (fun hj => hn ⟨j,hj⟩)
  have : (∑ j,e j) < 0 := Finset.sum_neg (fun j _ => hneg j)
    ⟨⟨0,hh⟩,Finset.mem_univ _⟩
  omega

 

def chosen {h : ℕ} (hh : 0<h) (e : Fin h → ℤ) : Fin h :=
  if he : 0≤∑ i,e i then (exists_nonneg hh he).choose else ⟨0,hh⟩

def contraction {h : ℕ} (hh : 0<h) (n : ℕ) :
    Cochains A h (n+1) →ₗ[A] Cochains A h n :=
  Finsupp.lsum A (fun e => (Finsupp.lsingle e).comp (extra A (chosen hh e) n))
@[simp] lemma contraction_apply {h : ℕ} (hh : 0<h) (n : ℕ)
    (f : Cochains A h (n+1)) (e : Fin h → ℤ) :
    contraction A hh n f e = extra A (chosen hh e) n (f e) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha,hb]
  | single k r =>
    simp only [contraction,Finsupp.lsum_single,LinearMap.comp_apply,Finsupp.lsingle_apply]
    by_cases hk : k=e
    · subst k; simp
    · simp [hk]

end Lech.ActualCech
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ActualCechTranspose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
namespace Lech.ActualCech

section
open scoped BigOperators
universe u
variable (A : Type u) [CommRing A]


def transpose (h n : ℕ) : Cochains A h n ≃ₗ[A]
    ((Fin n → Fin h) → ((Fin h → ℤ) →₀ A)) :=
  (Finsupp.mapRange.linearEquiv
    (Finsupp.linearEquivFunOnFinite A A (Fin n → Fin h)).symm).trans <|
  (Finsupp.curryLinearEquiv A).symm.trans <|
  (Finsupp.domLCongr (Equiv.prodComm _ _)).trans <|
  (Finsupp.curryLinearEquiv A).trans <|
  Finsupp.linearEquivFunOnFinite A ((Fin h → ℤ) →₀ A) (Fin n → Fin h)

@[simp] lemma transpose_apply (h n : ℕ) (f : Cochains A h n)
    (a : Fin n → Fin h) (e : Fin h → ℤ) : transpose A h n f a e = f e a := by
  simp [transpose, Finsupp.domLCongr_apply]

@[simp] lemma transpose_symm_apply (h n : ℕ)
    (f : (Fin n → Fin h) → ((Fin h → ℤ) →₀ A)) (e : Fin h → ℤ) (a : Fin n → Fin h) :
    (transpose A h n).symm f e a = f a e := by
  have he := congrArg (fun g => g a e) ((transpose A h n).apply_symm_apply f)
  simpa only [transpose_apply] using he

def allowedSet {h n : ℕ} (a : Fin n → Fin h) (t : ℤ) : Set (Fin h → ℤ) :=
  {e | (∑ i,e i) = t ∧ Allowed e a}


def supportedTranspose (h n : ℕ) (t : ℤ) : homogeneous A h n t ≃ₗ[A]
    ((a : Fin n → Fin h) → Finsupp.supported A A (allowedSet a t)) where
  toFun f a := ⟨transpose A h n f.val a, by
    rw [Finsupp.mem_supported']
    intro e he
    rw [transpose_apply]
    apply f.property e a
    simpa only [allowedSet,Set.mem_ofPred_eq,not_and_or] using he⟩
  invFun f := ⟨(transpose A h n).symm (fun a => (f a).val), by
    intro e a he
    rw [transpose_symm_apply]
    apply (Finsupp.mem_supported' A (f a).val).mp (f a).property e
    simpa only [allowedSet,Set.mem_ofPred_eq,not_and_or] using he⟩
  left_inv f := by apply Subtype.ext; exact (transpose A h n).symm_apply_apply f.val
  right_inv f := by
    funext a
    apply Subtype.ext
    exact congrFun ((transpose A h n).apply_symm_apply (fun a => (f a).val)) a
  map_add' f g := by funext a; apply Subtype.ext; exact congrFun (map_add (transpose A h n) f.val g.val) a
  map_smul' r f := by funext a; apply Subtype.ext; exact congrFun (map_smul (transpose A h n) r f.val) a

 
def intersection {h n : ℕ} (a : Fin n → Fin h) : Finset (Fin h) :=
  Finset.univ.image a
@[simp] lemma mem_intersection {h n : ℕ} (a : Fin n → Fin h) (i : Fin h) :
    i ∈ intersection a ↔ i ∈ Set.range a := by simp [intersection]

lemma mem_exponents_intersection {h n : ℕ} (a : Fin n → Fin h) (e : Fin h → ℤ) :
    e ∈ PartialLaurent.exponents (intersection a) ↔ Allowed e a := by
  change (∀ i, i ∉ intersection a → 0 ≤ e i) ↔ (∀ i, e i < 0 → i ∈ Set.range a)
  simp only [mem_intersection]
  constructor
  · intro he i hi
    by_contra hn
    exact (not_lt_of_ge (he i hn)) hi
  · intro he i hi
    exact le_of_not_gt (fun hn => hi (he i hn))


def exponentEquiv {h n : ℕ} (a : Fin n → Fin h) (t : ℤ) :
    allowedSet a t ≃ {e : PartialLaurent.exponents (intersection a) //
      PartialLaurent.degree (intersection a) e = t} where
  toFun e := ⟨⟨e.val,(mem_exponents_intersection a e.val).mpr e.property.2⟩,e.property.1⟩
  invFun e := ⟨e.val.val, e.property,(mem_exponents_intersection a e.val.val).mp e.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl


abbrev laurentCochains (h n : ℕ) (t : ℤ) :=
  (a : Fin n → Fin h) → PartialLaurent.homogeneous A (intersection a) t
 

def laurentEquiv (h n : ℕ) (t : ℤ) : homogeneous A h n t ≃ₗ[A]
    laurentCochains A h n t :=
  (supportedTranspose A h n t).trans <|
  LinearEquiv.piCongrRight (fun a =>
    (Finsupp.supportedEquivFinsupp (allowedSet a t)).trans <|
    (Finsupp.domLCongr (exponentEquiv a t)).trans <|
    (PartialLaurent.homogeneousEquiv A (intersection a) t).symm)
@[simp] lemma homogeneousEquiv_apply {h : ℕ} (s : Finset (Fin h)) (t : ℤ)
    (f : PartialLaurent.homogeneous A s t)
    (e : {e : PartialLaurent.exponents s // PartialLaurent.degree s e = t}) :
    PartialLaurent.homogeneousEquiv A s t f e = f.val.coeff e.val := rfl

@[simp] lemma laurentEquiv_homogeneousEquiv (h n : ℕ) (t : ℤ)
    (f : homogeneous A h n t) (a : Fin n → Fin h)
    (e : {e : PartialLaurent.exponents (intersection a) //
      PartialLaurent.degree (intersection a) e=t}) :
    PartialLaurent.homogeneousEquiv A (intersection a) t (laurentEquiv A h n t f a) e =
      f.val e.val.val a := by
  change PartialLaurent.homogeneousEquiv A (intersection a) t
    ((PartialLaurent.homogeneousEquiv A (intersection a) t).symm
      (Finsupp.domLCongr (R := A) (M := A) (exponentEquiv a t)
      (Finsupp.supportedEquivFinsupp (R := A) (allowedSet a t)
      (supportedTranspose A h n t f a)))) e = _
  rw [LinearEquiv.apply_symm_apply]
  rw [Finsupp.domLCongr_apply]
  change transpose A h n f.val a ((exponentEquiv a t).symm e).val = _
  exact transpose_apply A h n f.val a e.val.val

lemma laurentEquiv_coeff (h n : ℕ) (t : ℤ)
    (f : homogeneous A h n t) (a : Fin n → Fin h)
    (e : PartialLaurent.exponents (intersection a)) :
    (laurentEquiv A h n t f a).val.coeff e = f.val e.val a := by
  by_cases he : PartialLaurent.degree (intersection a) e=t
  · exact laurentEquiv_homogeneousEquiv A h n t f a ⟨e,he⟩
  · have hleft : (laurentEquiv A h n t f a).val.coeff e = 0 := by
      exact (Finsupp.mem_supported' A _).mp (laurentEquiv A h n t f a).property e he
    rw [hleft, f.property e.val a (Or.inl he)]

lemma intersection_delete {h n : ℕ} (a : Fin (n+1) → Fin h) (i : Fin (n+1)) :
    intersection (a ∘ i.succAbove) ⊆ intersection a := by
  intro j hj
  rw [mem_intersection] at hj ⊢
  obtain ⟨k,hk⟩ := hj
  exact ⟨i.succAbove k,hk⟩

 
def laurentD (h n : ℕ) (t : ℤ) :
    laurentCochains A h n t →ₗ[A] laurentCochains A h (n+1) t where
  toFun f a := ∑ i : Fin (n+1), (-1 : A)^i.val •
    PartialLaurent.coefficientChartRestrict A (intersection_delete a i) t (f (a ∘ i.succAbove))
  map_add' f g := by
    funext a
    simp only [Pi.add_apply,map_add,smul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    funext a
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _

lemma restrict_coeff_image {h : ℕ} {s v : Finset (Fin h)} (hsv : s ⊆ v)
    (f : PartialLaurent.Laurent A s) (e : PartialLaurent.exponents s) :
    (PartialLaurent.restrict A hsv f).coeff (PartialLaurent.exponentInclusion hsv e) =
      f.coeff e := by
  change Finsupp.mapDomain (PartialLaurent.exponentInclusion hsv) f.coeff
    (PartialLaurent.exponentInclusion hsv e) = _
  apply Finsupp.mapDomain_apply
  intro a b hab
  exact Subtype.ext (congrArg (fun e : PartialLaurent.exponents v => e.val) hab)

lemma restrict_coeff_zero {h : ℕ} {s v : Finset (Fin h)} (hsv : s ⊆ v)
    (f : PartialLaurent.Laurent A s) (e : PartialLaurent.exponents v)
    (he : e.val ∉ PartialLaurent.exponents s) :
    (PartialLaurent.restrict A hsv f).coeff e = 0 := by
  change Finsupp.mapDomain (PartialLaurent.exponentInclusion hsv) f.coeff e = _
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨a,ha⟩
  exact he ((congrArg Subtype.val ha) ▸ a.property)

lemma laurentEquiv_restrict_coeff (h n : ℕ) (t : ℤ)
    (f : homogeneous A h n t) (a : Fin (n+1) → Fin h) (i : Fin (n+1))
    (e : PartialLaurent.exponents (intersection a)) :
    (PartialLaurent.coefficientChartRestrict A (intersection_delete a i) t
      (laurentEquiv A h n t f (a ∘ i.succAbove))).val.coeff e =
      f.val e.val (a ∘ i.succAbove) := by
  by_cases he : e.val ∈ PartialLaurent.exponents (intersection (a ∘ i.succAbove))
  · let es : PartialLaurent.exponents (intersection (a ∘ i.succAbove)) := ⟨e.val,he⟩
    have hes : PartialLaurent.exponentInclusion (intersection_delete a i) es = e := rfl
    change (PartialLaurent.restrict A (intersection_delete a i)
      (laurentEquiv A h n t f (a ∘ i.succAbove)).val).coeff e = _
    rw [← hes, restrict_coeff_image, laurentEquiv_coeff]
    rfl
  · change (PartialLaurent.restrict A (intersection_delete a i)
      (laurentEquiv A h n t f (a ∘ i.succAbove)).val).coeff e = _
    rw [restrict_coeff_zero A _ _ e he]
    exact (f.property e.val (a ∘ i.succAbove)
      (Or.inr (fun ha => he ((mem_exponents_intersection _ _).mpr ha)))).symm

def homogeneousD (h n : ℕ) (t : ℤ) :
    homogeneous A h n t →ₗ[A] homogeneous A h (n+1) t where
  toFun f := ⟨d A h n f.val,d_mem A f.property⟩
  map_add' f g := Subtype.ext (map_add (d A h n) f.val g.val)
  map_smul' r f := Subtype.ext (map_smul (d A h n) r f.val)


lemma laurentD_equiv (h n : ℕ) (t : ℤ) (f : homogeneous A h n t) :
    laurentD A h n t (laurentEquiv A h n t f) =
      laurentEquiv A h (n+1) t (homogeneousD A h n t f) := by
  funext a
  apply Subtype.ext
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro e
  rw [laurentEquiv_coeff]
  change (∑ i : Fin (n+1), (-1 : A)^i.val •
    PartialLaurent.coefficientChartRestrict A (intersection_delete a i) t
      (laurentEquiv A h n t f (a ∘ i.succAbove))).val.coeff e =
        (∑ i : Fin (n+1), (-1 : A)^i.val * f.val e.val (a ∘ i.succAbove))
  simp only [Submodule.coe_sum, Submodule.coe_smul, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    laurentEquiv_restrict_coeff, smul_eq_mul]


end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (A : Type u) [CommRing A]

lemma homogeneousD_square (h n : ℕ) (t : ℤ) (f : homogeneous A h n t) :
    homogeneousD A h (n+1) t (homogeneousD A h n t f)=0 := by
  apply Subtype.ext
  apply Finsupp.ext
  intro e
  exact delta_square A n (f.val e)

lemma laurentD_square (h n : ℕ) (t : ℤ) (f : laurentCochains A h n t) :
    laurentD A h (n+1) t (laurentD A h n t f)=0 := by
  obtain ⟨x,rfl⟩ := (laurentEquiv A h n t).surjective f
  rw [laurentD_equiv,laurentD_equiv,homogeneousD_square,map_zero]


end Lech.ActualCech

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AdicDense
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.AdicFlat
variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]

lemma map_pow_smul_top {M : Type*} [AddCommGroup M] [Module R M] [Module T M]
    [IsScalarTower R T M] (I : Ideal R) (J : Ideal T)
    (hJ : I.map (algebraMap R T)=J) (n : ℕ) :
    (J^n • (⊤ : Submodule T M)).restrictScalars R=I^n • (⊤ : Submodule R M) := by
  simpa only [Ideal.map_pow,hJ,Submodule.restrictScalars_top] using
    Submodule.restrictScalars_map_smul_eq (I^n) (⊤ : Submodule T M)

lemma completion_dense (I : Ideal R) (J : Ideal T) (hJ : I.map (algebraMap R T)=J)
    (hfg : J.FG) (n : ℕ) (s : AdicCompletion J T) :
    ∃ t : T,s-algebraMap T (AdicCompletion J T) t ∈
      I^n • (⊤ : Submodule R (AdicCompletion J T)) := by
  obtain ⟨t,ht⟩ := (J^n • (⊤ : Submodule T T)).mkQ_surjective
    (AdicCompletion.eval J T n s)
  refine ⟨t,?_⟩
  rw [← map_pow_smul_top I J hJ]
  change s-AdicCompletion.of J T t ∈ J^n • (⊤ : Submodule T (AdicCompletion J T))
  rw [AdicCompletion.pow_smul_top_eq_ker_eval hfg,LinearMap.mem_ker,map_sub,
    AdicCompletion.eval_of,ht,sub_self]

lemma completion_contract (I : Ideal R) (J : Ideal T) (hJ : I.map (algebraMap R T)=J)
    (hfg : J.FG) (n : ℕ) (t : T)
    (ht : algebraMap T (AdicCompletion J T) t ∈
      I^n • (⊤ : Submodule R (AdicCompletion J T))) :
    t ∈ I^n • (⊤ : Submodule R T) := by
  rw [← map_pow_smul_top I J hJ] at ht ⊢
  change AdicCompletion.of J T t ∈ J^n • (⊤ : Submodule T (AdicCompletion J T)) at ht
  rw [AdicCompletion.pow_smul_top_eq_ker_eval hfg,LinearMap.mem_ker,
    AdicCompletion.eval_of,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero] at ht
  exact ht
end Lech.AdicFlat

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AdicFlatCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open TensorProduct
namespace Lech.AdicFlat
variable {R : Type*} [CommRing R]

def contract (S : Type*) [CommRing S] [Algebra R S] (J : Ideal R) : S ⊗[R] J →ₗ[S] S :=
  (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp
    (AlgebraTensorModule.lTensor S S J.subtype)

@[simp] lemma contract_tmul (S : Type*) [CommRing S] [Algebra R S]
    (J : Ideal R) (s : S) (j : J) : contract S J (s ⊗ₜ[R] j)=(j:R) • s := rfl

lemma coord_contract {T ι : Type*} [CommRing T] [Algebra R T] [DecidableEq ι]
    (b : Module.Basis ι R T) (J : Ideal R) (y : T ⊗[R] J) (i : ι) :
    b.coord i (contract T J y)=((TensorProduct.equivFinsuppOfBasisLeft b y i : J):R) := by
  classical
  induction y using OAI.tensorInductionOn with
  | tmul t j =>
    simp [mul_comm]
  | add y z hy hz => simp only [map_add,Finsupp.add_apply,Submodule.coe_add,hy,hz]

lemma contract_mem_power {T ι : Type*} [CommRing T] [Algebra R T]
    (b : Module.Basis ι R T) (I J : Ideal R) (c : ℕ)
    (hc : ∀ n ≥ c,I^n ⊓ J ≤ I^(n-c)*J)
    (n : ℕ) (y : T ⊗[R] J)
    (hy : contract T J y ∈ I^(n+c) • (⊤ : Submodule R T)) :
    y ∈ I^n • (⊤ : Submodule R (T ⊗[R] J)) := by
  classical
  let a := TensorProduct.equivFinsuppOfBasisLeft b y
  have ha : ∀ i,a i ∈ I^n • (⊤ : Submodule R J) := by
    intro i
    apply (Submodule.mem_smul_top_iff (I^n) J (a i)).mpr
    have hh := Submodule.smul_top_le_comap_smul_top (I^(n+c)) (b.coord i) hy
    have hcoord : (a i : R) ∈ I^(n+c) := by
      simpa only [Submodule.mem_comap,smul_eq_mul,Ideal.mul_top,coord_contract] using hh
    have hr := hc (n+c) (Nat.le_add_left c n) ⟨hcoord,(a i).2⟩
    simpa only [Nat.add_sub_cancel,smul_eq_mul] using hr
  have he : a.sum (fun i j => b i ⊗ₜ[R] j)=y := by
    simpa only [TensorProduct.equivFinsuppOfBasisLeft_symm_apply] using
      (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply y
  rw [← he]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_top_le_comap_smul_top (I^n) (TensorProduct.mk R T J (b i)) (ha i)

lemma artin_rees_ideal [IsNoetherianRing R] (I J : Ideal R) :
    ∃ c : ℕ,∀ n ≥ c,I^n ⊓ J ≤ I^(n-c)*J := by
  obtain ⟨c,hc⟩ := I.exists_pow_inf_eq_pow_smul J
  refine ⟨c,fun n hn => ?_⟩
  have he := hc n hn
  simp only [smul_eq_mul,Ideal.mul_top] at he
  rw [he]
  exact Ideal.mul_mono_right inf_le_right

 
lemma tensor_dense {T S M : Type*} [CommRing T] [Algebra R T]
    [CommRing S] [Algebra R S] [Algebra T S] [IsScalarTower R T S]
    [AddCommGroup M] [Module R M] (I : Ideal R) (n : ℕ)
    (hd : ∀ s : S,∃ t : T,s-algebraMap T S t ∈ I^n • (⊤ : Submodule R S))
    (x : S ⊗[R] M) :
    ∃ y : T ⊗[R] M,x-(LinearMap.rTensor M (IsScalarTower.toAlgHom R T S).toLinearMap) y ∈
      I^n • (⊤ : Submodule R (S ⊗[R] M)) := by
  induction x using OAI.tensorInductionOn with
  | tmul s m =>
    obtain ⟨t,ht⟩ := hd s
    refine ⟨t ⊗ₜ[R] m,?_⟩
    have hh := Submodule.smul_top_le_comap_smul_top (I^n)
      ((TensorProduct.mk R S M).flip m) ht
    simpa only [Submodule.mem_comap,LinearMap.flip_apply,sub_tmul,LinearMap.rTensor_tmul,
      IsScalarTower.toAlgHom_apply,AlgHom.toLinearMap_apply,TensorProduct.mk_apply,sub_tmul] using hh
  | add x z hx hz =>
    obtain ⟨a,ha⟩ := hx
    obtain ⟨b,hb⟩ := hz
    refine ⟨a+b,?_⟩
    simpa only [map_add,add_sub_add_comm] using Submodule.add_mem _ ha hb

end Lech.AdicFlat

namespace Lech.AdicFlat
variable {R T S : Type*} [CommRing R] [CommRing T] [CommRing S]
  [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S]

lemma contract_natural (J : Ideal R) (y : T ⊗[R] J) :
    contract S J ((LinearMap.rTensor J (IsScalarTower.toAlgHom R T S).toLinearMap) y)=
      algebraMap T S (contract T J y) := by
  induction y using OAI.tensorInductionOn with
  | tmul t j =>
    simp only [LinearMap.rTensor_tmul,AlgHom.toLinearMap_apply,IsScalarTower.toAlgHom_apply,contract_tmul]
    exact ((IsScalarTower.toAlgHom R T S).toLinearMap.map_smul (j:R) t).symm
  | add a b ha hb => simp [ha,hb]

 

lemma flat_of_free_dense [IsNoetherianRing R] [Module.Free R T] (I : Ideal R)
    (hd : ∀ n (s : S),∃ t : T,s-algebraMap T S t ∈ I^n • (⊤ : Submodule R S))
    (hp : ∀ n (t : T),algebraMap T S t ∈ I^n • (⊤ : Submodule R S) →
      t ∈ I^n • (⊤ : Submodule R T))
    (hs : ∀ J : Ideal R,IsHausdorff I (S ⊗[R] J)) : Module.Flat R S := by
  let b := Module.Free.chooseBasis R T
  apply Module.Flat.iff_lTensor_injective'.mpr
  intro J
  have hinj : Function.Injective (contract S J) := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    change x=0
    have hx0 : contract S J x=0 := hx
    let : IsHausdorff I (S ⊗[R] J) := hs J
    apply (IsHausdorff.eq_iff_smodEq (I:=I)).mpr
    intro n
    rw [SModEq.sub_mem,sub_zero]
    obtain ⟨c,hc⟩ := artin_rees_ideal I J
    obtain ⟨y,hy⟩ := tensor_dense I (n+c) (hd (n+c)) x
    let g := LinearMap.rTensor J (IsScalarTower.toAlgHom R T S).toLinearMap
    have hy' : contract T J y ∈ I^(n+c) • (⊤ : Submodule R T) := by
      apply hp (n+c)
      have hh := Submodule.smul_top_le_comap_smul_top (I^(n+c))
        ((contract S J).restrictScalars R) hy
      change contract S J (x-g y) ∈ I^(n+c) • (⊤ : Submodule R S) at hh
      rw [map_sub,hx0,contract_natural,zero_sub] at hh
      exact neg_mem_iff.mp hh
    have hyy := contract_mem_power b I J c hc n y hy'
    have hmap : g y ∈ I^n • (⊤ : Submodule R (S ⊗[R] J)) :=
      Submodule.smul_top_le_comap_smul_top (I^n) g hyy
    have hie : I^(n+c) • (⊤ : Submodule R (S ⊗[R] J)) ≤ I^n • ⊤ :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right n c))
    have hadd := Submodule.add_mem _ (hie hy) hmap
    simpa [g] using hadd
  intro x y hxy
  apply hinj
  exact congrArg (TensorProduct.AlgebraTensorModule.rid R S S) hxy
end Lech.AdicFlat

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominatorTheory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian

open scoped BigOperators


namespace Lech.FiniteCoverCech
open scoped BigOperators
universe u v w
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
variable {ι : Type w}
abbrev Row (n : ℕ) := (Fin n → ι) → M

variable [Fintype ι] [DecidableEq ι]
def intersection {n : ℕ} (a : Fin n → ι) : Finset ι := Finset.univ.image a
omit [Fintype ι] in
lemma intersection_delete {n : ℕ} (a : Fin (n+1) → ι) (i : Fin (n+1)) :
    intersection (a ∘ i.succAbove) ⊆ intersection a := by
  intro j hj
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_image.mpr ⟨i.succAbove k,Finset.mem_univ _,rfl⟩
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
def cochains (n : ℕ) : Submodule R (Row M (ι := ι) n) where
  carrier := {f | ∀ a,f a∈F (intersection a)}
  zero_mem' _ := (F _).zero_mem
  add_mem' hf hg a := (F _).add_mem (hf a) (hg a)
  smul_mem' r _ hf a := (F _).smul_mem r (hf a)
end Lech.FiniteCoverCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AlternatingCechAlt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
namespace Lech.AlternatingCech
open scoped BigOperators
universe u v w
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
abbrev Alt (n : ℕ) := (ι → R) [⋀^Fin n]→ₗ[R] M
abbrev basis : Module.Basis ι R (ι → R) := Pi.basisFun R ι
def evaluation (n : ℕ) : Alt R M (ι := ι) n →ₗ[R] FiniteCoverCech.Row M (ι := ι) n where
  toFun f a := f (fun i => basis R (a i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def epsilon : (ι → R) →ₗ[R] R := ∑ i : ι,LinearMap.proj i
lemma epsilon_basis (i : ι) : epsilon R (basis R i)=1 := by
  simp [epsilon,basis,Pi.basisFun_apply]

variable (F : Finset ι → Submodule R M) (hF : Monotone F)
def cochains (n : ℕ) : Submodule R (Alt R M (ι := ι) n) :=
  (FiniteCoverCech.cochains R M F n).comap (evaluation R M n)
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open scoped BigOperators
open Set
universe u v w
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
variable {ι : Type w} [Fintype ι] [LinearOrder ι]
 
def sortedCoordinates (n : ℕ) : Alt R M (ι := ι) n ≃ₗ[R] (powersetCard ι n → M) :=
  exteriorPower.alternatingMapLinearEquiv.trans
    (((basis R (ι := ι)).exteriorPower n).constr R).symm
lemma sortedCoordinates_apply (n : ℕ) (f : Alt R M (ι := ι) n) (s : powersetCard ι n) :
    sortedCoordinates R M n f s = f (fun i => basis R (s.val.orderEmbOfFin s.property i)) := by
  change exteriorPower.alternatingMapLinearEquiv f ((basis R).exteriorPower n s)=_
  rw [exteriorPower.basis_apply,exteriorPower.ιMulti_family,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl
end Lech.AlternatingCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverFaceSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.AlternatingCech
open scoped BigOperators
open Set
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [LinearOrder ι]
local instance faceSliceSortedDecEq_r74ecb7_1 : DecidableEq ι := Classical.decEq ι
def delete {n : ℕ} (s : powersetCard ι (n+1)) (i : Fin (n+1)) : powersetCard ι n :=
  powersetCard.ofFinEmbEquiv ((Fin.succAboveOrderEmb i).trans
    (powersetCard.ofFinEmbEquiv.symm s))
omit [Fintype ι] in
lemma delete_sorted {n : ℕ} (s : powersetCard ι (n+1)) (i : Fin (n+1)) :
    powersetCard.ofFinEmbEquiv.symm (delete s i)=
      (Fin.succAboveOrderEmb i).trans (powersetCard.ofFinEmbEquiv.symm s) :=
  powersetCard.ofFinEmbEquiv.symm_apply_apply _
omit [Fintype ι] in
lemma delete_subset {n : ℕ} (s : powersetCard ι (n+1)) (i : Fin (n+1)) :
    (delete s i).val ⊆ s.val := by
  intro j hj
  have hj' : j∈Set.range (powersetCard.ofFinEmbEquiv.symm (delete s i)) :=
    (powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ _).mpr hj
  rw [delete_sorted] at hj'
  obtain ⟨k,rfl⟩ := hj'
  exact (powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨i.succAbove k,rfl⟩
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
abbrev sorted (n : ℕ) := ∀ s : powersetCard ι n,F s.val
 
def sortedDelta (n : ℕ) : sorted R M F n →ₗ[R] sorted R M F (n+1) where
  toFun f s := ∑ i : Fin (n+1),(-1:ℤ)^i.val •
    Submodule.inclusion (hF (delete_subset s i)) (f (delete s i))
  map_add' f g := by ext s;simp [Finset.sum_add_distrib,smul_add]
  map_smul' r f := by
    funext s
    simp only [Pi.smul_apply,map_smul,Finset.smul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
end Lech.AlternatingCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechConnectingIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.AlternatingCech
universe u v
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type v} [DecidableEq ι]
 

def zeroAugmentation (F : Finset ι → Submodule R M) (s : Finset ι) : Submodule R M :=
  if s=∅ then ⊥ else F s
end Lech.AlternatingCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AlternatingCechUnaugmentedComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.AlternatingCech
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [LinearOrder ι]
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
def unaugmentedInclusion (p : ℕ) : sorted R M (zeroAugmentation R M F) p →ₗ[R] sorted R M F p where
  toFun f s := ⟨f s,by
    have h := (f s).property
    by_cases hs : s.val=∅
    · have hz : (f s:M)=0 := by simpa only [zeroAugmentation,ite_eq_left hs,Submodule.mem_bot] using h
      rw [hz];exact (F s.val).zero_mem
    · simpa only [zeroAugmentation,ite_eq_right hs] using h⟩
  map_add' f g := rfl
  map_smul' r f := rfl
omit [Fintype ι] in
lemma unaugmentedInclusion_injective (p : ℕ) : Function.Injective (unaugmentedInclusion R M F p) := by
  intro f g h
  ext s
  exact congrArg (fun f : sorted R M F p => (f s:M)) h
omit [Fintype ι] in
lemma unaugmentedInclusion_surjective (p : ℕ) (hp : 0<p) : Function.Surjective (unaugmentedInclusion R M F p) := by
  intro f
  refine ⟨(fun s => ⟨f s,?_⟩),rfl⟩
  have hs : s.val≠∅ := (Finset.card_pos.mp (s.property.symm ▸ hp)).ne_empty
  simpa only [zeroAugmentation,ite_eq_right hs] using (f s).property
def unaugmentedEquiv (p : ℕ) (hp : 0<p) : sorted R M (zeroAugmentation R M F) p ≃ₗ[R] sorted R M F p :=
  LinearEquiv.ofBijective (unaugmentedInclusion R M F p)
    ⟨unaugmentedInclusion_injective R M F p,unaugmentedInclusion_surjective R M F p hp⟩
variable [Nonempty ι]

def unaugmentedAugmentation : sorted R M F 0 →ₗ[R] sorted R M (zeroAugmentation R M F) 1 :=
  (unaugmentedEquiv R M F 1 (by omega)).symm.toLinearMap.comp (sortedDelta R M F hF 0)
end Lech.AlternatingCech


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrimitiveChartFaithfullyFlat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.BinaryChange
open Polynomial
universe u
variable {B : Type u} [CommRing B]
abbrev Binary := MvPolynomial (Fin 2) B

end Lech.BinaryChange


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PowerSeriesFinDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory


namespace Lech.AdicNakayama
variable {R : Type*} [CommRing R] (I : Ideal R) (ι : Type*) [Fintype ι]

lemma mem_smul_top_pi (v : ι → R) :
    v ∈ I • (⊤ : Submodule R (ι → R)) ↔ ∀ i, v i ∈ I := by
  classical
  constructor
  · intro hv i
    have hh := Submodule.smul_top_le_comap_smul_top I (LinearMap.proj i) hv
    simpa only [Submodule.mem_comap,LinearMap.proj_apply,smul_eq_mul,Ideal.mul_top] using hh
  · intro hv
    have he : v = ∑ i, v i • Pi.single i (1 : R) := by
      ext j
      simp [Pi.single_apply]
    rw [he]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem_smul (hv i) (Submodule.mem_top))

lemma precomplete_pi [IsPrecomplete I R] : IsPrecomplete I (ι → R) := by
  constructor
  intro f hf
  have hc i : ∀ {m n : ℕ}, m ≤ n → f m i ≡ f n i [SMOD (I^m • (⊤ : Submodule R R))] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    simpa only [Pi.sub_apply,smul_eq_mul,Ideal.mul_top] using
      (mem_smul_top_pi (I^m) ι _).mp (SModEq.sub_mem.mp (hf hmn)) i
  choose L hL using (fun i => IsPrecomplete.prec (I := I) (M := R) inferInstance (hc i))
  refine ⟨L,fun n => ?_⟩
  rw [SModEq.sub_mem,mem_smul_top_pi]
  intro i
  simpa only [Pi.sub_apply,smul_eq_mul,Ideal.mul_top] using SModEq.sub_mem.mp (hL i n)

variable {M : Type*} [AddCommGroup M] [Module R M]

 

theorem finite_of_quotient [IsPrecomplete I R] [IsHausdorff I M]
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] : Module.Finite R M := by
  obtain ⟨n,g,hg⟩ := Module.Finite.exists_fin' R (M ⧸ (I • (⊤ : Submodule R M)))
  let := precomplete_pi I (Fin n)
  obtain ⟨f,hf⟩ := Module.projective_lifting_property (I • (⊤ : Submodule R M)).mkQ g
    (I • (⊤ : Submodule R M)).mkQ_surjective
  apply Module.Finite.of_surjective f
  apply surjective_of_mkQ_comp_surjective (I := I)
  rw [hf]
  exact hg

end Lech.AdicNakayama


end

end OAI
end


