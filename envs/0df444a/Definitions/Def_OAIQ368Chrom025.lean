-- Prove2me | Definitions.Def_OAIQ368Chrom025
-- name    : OAIQ368Chrom025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:08:26.248025+00:00
-- url     : https://prove2.me/theorems/a62a04a6-745f-42e0-86b4-f847a38bd204
-- title:
--   Definitions bundle OAIQ368Chrom025 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 17 definitions and 10 theorems. The definitions and types are `OAI.ElementaryPositivity.BiTruncation.Through`, `OAI.ElementaryPositivity.QuantumTorus.biRegrade`, `OAI.ElementaryPositivity.QuantumTorus.biRegradeAddCommMonoid`, `OAI.ElementaryPositivity.QuantumTorus.biRegradeAddGroup`, `OAI.ElementaryPositivity.QuantumTorus.biRegradeHom`, `OAI.ElementaryPositivity.QuantumTorus.biRegradeRing`, `OAI.ElementaryPositivity.QuantumTorus.biRegradeTopology`, `OAI.ElementaryPositivity.QuantumTorus.biThroughRing`, `OAI.ElementaryPositivity.QuantumTorus.laurentCompletionAddCommMonoid`, `OAI.ElementaryPositivity.QuantumTorus.oldLaurent`, `OAI.ElementaryPositivity.QuantumTorus.oldLaurentHom`, `OAI.ElementaryPositivity.RationalFiber.instAddCommMonoidTorus_1`, `OAI.ElementaryPositivity.RationalFiber.instRingTorus_3`, `OAI.ElementaryPositivity.RationalFiber.instRingTorus_6`, `OAI.ElementaryPositivity.RationalFiber.laurentExpansionRing`, `OAI.ElementaryPositivity.RationalFiber.oldUnitExpand`, `OAI.ElementaryPositivity.RationalFiber.rationalLaurentFaithfulRing`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_GradedAlgebra_BiRegrade`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/BiRegrade.lean), [`Chromatic_GradedAlgebra_LaurentPureAction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/LaurentPureAction.lean), [`Chromatic_GradedAlgebra_PureComparisonIdentification`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/PureComparisonIdentification.lean), [`Chromatic_GradedAlgebra_RationalLaurentFaithful`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/RationalLaurentFaithful.lean), [`Chromatic_Walls_CompletedPureComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/CompletedPureComparison.lean), [`Chromatic_Walls_LaurentCompletion`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/LaurentCompletion.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom005` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.ElementaryPositivity.RationalFiber.finite_refinement_import`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom005

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalLaurentFaithful
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
local instance rationalLaurentFaithfulRing : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.biSupportedRing
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.biSupportedAddCommMonoid
local instance biSupportedAddGroup_rcfad1a_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma BiSupported.bi_vanish {f : PowerSeries (Torus v Ω)} (hf : BiSupported v Ω δ κ f)
    (d e n : ℕ) (hne : n≠d+e) : coeff e (coeff d (biHomogenize v Ω δ κ (coeff n f)))=0 := by
  ext m
  rw [biHomogenize_coeff]
  split_ifs with hh
  · by_contra hz
    obtain ⟨hd,hk,he⟩:=hf n m hz
    have hD : δ m=(d:ℤ):=by rw [hh.1,Int.toNat_of_nonneg hd]
    have hK : κ m=(e:ℤ):=by rw [hh.2,Int.toNat_of_nonneg hk]
    apply hne
    omega
  · rfl
lemma BiSupported.bi_product_vanish {f g : PowerSeries (Torus v Ω)}
    (hf : BiSupported v Ω δ κ f) (hg : BiSupported v Ω δ κ g)
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
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_BiRegrade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
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
local instance biRegradeRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance biRegradeAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance biRegradeAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def biRegrade (f : PowerSeries (Torus v Ω)) : PowerSeries (PowerSeries (Torus v Ω)) :=
  PowerSeries.mk fun d=>PowerSeries.mk fun e=>coeff e (coeff d (biHomogenize v Ω δ κ (coeff (d+e) f)))
lemma biRegrade_coeff (f : PowerSeries (Torus v Ω)) (d e : ℕ) :
    coeff e (coeff d (biRegrade v Ω δ κ f))=
      coeff e (coeff d (biHomogenize v Ω δ κ (coeff (d+e) f))) := by simp [biRegrade]

section Topology
local instance biRegradeTopology : TopologicalSpace (Torus v Ω) := ⊥
local instance biRegradeDiscreteTopology : DiscreteTopology (Torus v Ω) := ⟨rfl⟩
open scoped PowerSeries.WithPiTopology
lemma biRegrade_hasSum {f : PowerSeries (Torus v Ω)} (hf : BiSupported v Ω δ κ f) :
    HasSum (fun n=>biHomogenize v Ω δ κ (coeff n f)) (biRegrade v Ω δ κ f) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro e
  rw [biRegrade_coeff]
  have H : HasSum (fun n=>coeff e (coeff d (biHomogenize v Ω δ κ (coeff n f))))
      (∑n∈({d+e}:Finset ℕ),coeff e (coeff d (biHomogenize v Ω δ κ (coeff n f)))) :=
    hasSum_sum_of_ne_finset_zero (s:={d+e})
    (f:=fun n=>coeff e (coeff d (biHomogenize v Ω δ κ (coeff n f))))
    (fun n hn=>hf.bi_vanish v Ω δ κ d e n (by simpa using hn))
  simpa using H
lemma biRegrade_product_summable {f g : PowerSeries (Torus v Ω)}
    (hf : BiSupported v Ω δ κ f) (hg : BiSupported v Ω δ κ g) :
    Summable (fun ab : ℕ×ℕ=>biHomogenize v Ω δ κ (coeff ab.1 f)*
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
lemma biRegrade_mul {f g : PowerSeries (Torus v Ω)}
    (hf : BiSupported v Ω δ κ f) (hg : BiSupported v Ω δ κ g) :
    biRegrade v Ω δ κ (f*g)=biRegrade v Ω δ κ f*biRegrade v Ω δ κ g := by
  rw [←(biRegrade_hasSum v Ω δ κ hf).tsum_eq,←(biRegrade_hasSum v Ω δ κ hg).tsum_eq,
    (biRegrade_hasSum v Ω δ κ hf).summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
      (biRegrade_hasSum v Ω δ κ hg).summable (biRegrade_product_summable v Ω δ κ hf hg),
    ←(biRegrade_hasSum v Ω δ κ (hf.mul v Ω δ κ hg)).tsum_eq]
  apply tsum_congr
  intro n
  rw [coeff_mul,_root_.map_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  exact biHomogenize_mul v Ω δ κ _ _ (fun m hm=>⟨(hf ab.1 m hm).1,(hf ab.1 m hm).2.1⟩)
    (fun m hm=>⟨(hg ab.2 m hm).1,(hg ab.2 m hm).2.1⟩)
end Topology
lemma biRegrade_add (f g : PowerSeries (Torus v Ω)) :
    biRegrade v Ω δ κ (f+g)=biRegrade v Ω δ κ f+biRegrade v Ω δ κ g := by
  apply PowerSeries.ext
  intro d
  apply PowerSeries.ext
  intro e
  simp only [biRegrade_coeff,_root_.map_add]
  rw [_root_.map_add,_root_.map_add,_root_.map_add]
lemma biRegrade_one : biRegrade v Ω δ κ 1=1 := by
  apply PowerSeries.ext
  intro d
  apply PowerSeries.ext
  intro e
  rw [biRegrade_coeff,coeff_one]
  by_cases hd : d=0
  · subst d
    by_cases he : e=0
    · subst e
      simp [biHomogenize_one]
    · simp [he]
  · have hde : d+e≠0:=by omega
    simp [hd]
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
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.laurentCompletionRing
local instance laurentCompletionAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance laurentCompletionAddGroup_rcfad1a_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
local instance laurentCompletionNonUnitalSemiring_rcfad1a_1 : NonUnitalSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalSemiring
local instance laurentCompletionNonUnitalNonAssocSemiring_rcfad1a_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma biRegrade_zero : biRegrade v Ω δ κ 0=0 := by
  apply PowerSeries.ext
  intro d
  apply PowerSeries.ext
  intro e
  simp only [biRegrade_coeff, _root_.map_zero]
def biRegradeHom : biSupportedSubring v Ω δ κ →+* PowerSeries (PowerSeries (Torus v Ω)) where
  toFun f:=biRegrade v Ω δ κ f.val
  map_zero':=biRegrade_zero v Ω δ κ
  map_one':=biRegrade_one v Ω δ κ
  map_add' f g:=biRegrade_add v Ω δ κ f.val g.val
  map_mul' f g:=biRegrade_mul v Ω δ κ f.property g.property

def oldLaurent (f : PowerSeries (Torus v Ω)) : PowerSeries (HahnSeries ℤ (Torus v Ω)) :=
  PowerSeries.map (HahnSeries.ofPowerSeries ℤ (Torus v Ω)) (biRegrade v Ω δ κ f)
def oldLaurentHom : biSupportedSubring v Ω δ κ →+* PowerSeries (HahnSeries ℤ (Torus v Ω)) :=
  (PowerSeries.map (HahnSeries.ofPowerSeries ℤ (Torus v Ω))).comp (biRegradeHom v Ω δ κ)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
local instance laurentExpansionRing : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentPureAction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ κ : M →+ ℤ) (p : M) (hδ : δ p=0) (hκ : κ p=1)
local instance instRingTorus_3 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance instAddCommMonoidTorus_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedPureComparison
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_5
local instance instAddCommMonoidTorus_2_rcfad1a_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_2_rcfad1a_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_5_rcfad1a_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_5_rcfad1a_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
def oldUnitExpand (u : (biSupportedSubring v Ω δ k)ˣ) :
    (PowerSeries (HahnSeries ℤ (Torus v Ω)))ˣ :=
  Units.map (oldLaurentHom v Ω δ k) u

end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (hδ : δ p=0) (B : ℕ)
local instance instRingTorus_6 : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_PureComparisonIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.BiTruncation
open PowerSeries
variable {R : Type*} [Semiring R]
def Through (N : ℕ) (f g : PowerSeries (PowerSeries R)) : Prop :=
  ∀d e,d+e≤N → coeff e (coeff d f)=coeff e (coeff d g)
end ElementaryPositivity.BiTruncation

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries BiTruncation
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ)
local instance biThroughRing : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end


