-- Prove2me | Definitions.Def_OAIQ124K005
-- name    : OAIQ124K005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:44:59.955951+00:00
-- url     : https://prove2.me/theorems/c34798d5-6ad9-47b3-9fb9-1c5bdcb6a900
-- title:
--   Definitions bundle OAIQ124K005 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 53 declarations of OpenAI's Lean: 19 definitions, 2 inductive types or structures, 2 instances and 30 theorems. The definitions and types are `OAI.KLInvariance.BruhatGraph.bmpRecInterval`, `OAI.KLInvariance.BruhatGraph.finiteEdges`, `OAI.KLInvariance.CoordinateProjection.restrict`, `OAI.KLInvariance.FiniteCharacterLocalization.stabilizer`, `OAI.KLInvariance.Graded.ModuleData.pairEdge`, `OAI.KLInvariance.Graded.ModuleData.pairEdgePiece`, `OAI.KLInvariance.Graded.ModuleData.pairLower`, `OAI.KLInvariance.Graded.ModuleData.pairUpper`, `OAI.KLInvariance.Graded.basisPiece`, `OAI.KLInvariance.HeckeQ.barBasis`, `OAI.KLInvariance.HeckeQ.barLinear`, `OAI.KLInvariance.HeckeQ.leftInv`, `OAI.KLInvariance.HeckeQ.positiveWord`, `OAI.KLInvariance.HeckeQ.standardUnit`, `OAI.KLInvariance.HeckeQ.unit`, `OAI.KLInvariance.HeckeQ.wordUnit`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Iso`, `OAI.KLInvariance.MomentGraph.Sheaf.Iso`, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.assignments`, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.sections`, `OAI.KLInvariance.TitsSpace.BruhatUpper`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: `KazhdanLusztig_BalancedPairings`, `KazhdanLusztig_BottSamelson`, `KazhdanLusztig_Bruhat`, `KazhdanLusztig_CharacterReciprocity`, `KazhdanLusztig_DyerPaths`, `KazhdanLusztig_Frobenius`, `KazhdanLusztig_GradedSheaves`, `KazhdanLusztig_Hecke`, `KazhdanLusztig_IntegralPairings`, `KazhdanLusztig_MinimalExtensions`, `KazhdanLusztig_SheafMorphisms`, `KazhdanLusztig_Sheaves`, `KazhdanLusztig_Support`.
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K000` and `OAIQ124K001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K008`, `OAIQ124K009`, `OAIQ124K010` and `OAIQ124K011`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K000
import Definitions.Def_OAIQ124K001

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Bruhat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Strong Bruhat order, subwords, length, finite lower ideals and arbitrary finite intervals; the selected R family.
-/

section


namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}


/-! Exchange consequences required for the source's finite-rank reduction
and for consistency of the equal-parameter Hecke recursion. -/

theorem lowerSimple_step_mono (cs : CoxeterSystem M W) (i : B) {x y : W}
    (hxy : BruhatStep cs x y) :
    BruhatLE cs (lowerSimple cs i x) (lowerSimple cs i y) := by
  classical
  by_cases heq : y = cs.simple i * x
  · rw [heq, lowerSimple_mul]
    exact .refl
  · have hs := bruhatStep_simple_mul cs hxy i heq
    by_cases hx : cs.length (cs.simple i * x) < cs.length x
    · by_cases hy : cs.length (cs.simple i * y) < cs.length y
      · simp only [lowerSimple, ite_eq_left hx, ite_eq_left hy]
        exact .single hs
      · simp only [lowerSimple, ite_eq_left hx, ite_eq_right hy]
        have hlow := lowerSimple_le cs i x
        simp only [lowerSimple, ite_eq_left hx] at hlow
        exact hlow.trans (.single hxy)
    · by_cases hy : cs.length (cs.simple i * y) < cs.length y
      · simp only [lowerSimple, ite_eq_right hx, ite_eq_left hy]
        have hupp := le_upperSimple cs i x
        simp only [upperSimple, ite_eq_right hx] at hupp
        exact hupp.trans (.single hs)
      · simp only [lowerSimple, ite_eq_right hx, ite_eq_right hy]
        exact .single hxy

theorem lowerSimple_mono (cs : CoxeterSystem M W) (i : B) {x y : W}
    (hxy : BruhatLE cs x y) :
    BruhatLE cs (lowerSimple cs i x) (lowerSimple cs i y) := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head hstep _ ih => exact (lowerSimple_step_mono cs i hstep).trans ih


end KLInvariance
end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Hecke
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hecke and Laurent actions, braid independence, bar involution, triangular support and inverse coefficients.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}


namespace HeckeQ

open Hecke (Space basis end_ext)
variable {C : Type*} [CommRing C]

theorem left_quadratic (cs : CoxeterSystem M W) (q : C) (i : B) :
    left cs q i * left cs q i = q • 1 + (q - 1) • left cs q i := by
  apply end_ext
  intro w
  simp only [Module.End.mul_apply, left_basis, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  rcases cs.length_simple_mul w i with h | h
  · have hasc : ¬cs.length (cs.simple i * w) < cs.length w := by omega
    have hdesc : cs.length w < cs.length (cs.simple i * w) := by omega
    simp [hasc, hdesc]
  · have hdesc : cs.length (cs.simple i * w) < cs.length w := by omega
    have hasc : ¬cs.length w < cs.length (cs.simple i * w) := by omega
    simp [hasc, hdesc, smul_add, smul_smul]

noncomputable def leftInv (cs : CoxeterSystem M W) (q : Cˣ) (i : B) :
    Module.End C (Space W C) := (↑q⁻¹ : C) • (left cs (q : C) i - ((q : C) - 1) • 1)

theorem leftInv_apply (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (v : Space W C) :
    leftInv cs q i v = (↑q⁻¹ : C) • (left cs (q : C) i v - ((q : C) - 1) • v) := rfl

theorem left_mul_leftInv (cs : CoxeterSystem M W) (q : Cˣ) (i : B) :
    left cs (q : C) i * leftInv cs q i = 1 := by
  apply end_ext
  intro w
  have h := congrArg (fun f : Module.End C (Space W C) => f (basis w))
    (left_quadratic cs (q:C) i)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h
  simp only [Module.End.mul_apply, leftInv_apply, Module.End.one_apply,
    map_smul, map_sub]
  rw [h]
  simp [smul_smul]

theorem leftInv_mul_left (cs : CoxeterSystem M W) (q : Cˣ) (i : B) :
    leftInv cs q i * left cs (q : C) i = 1 := by
  apply end_ext
  intro w
  have h := congrArg (fun f : Module.End C (Space W C) => f (basis w))
    (left_quadratic cs (q:C) i)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h
  simp only [Module.End.mul_apply, leftInv_apply, Module.End.one_apply]
  rw [h]
  simp [smul_smul]


noncomputable def unit (cs : CoxeterSystem M W) (q : Cˣ) (i : B) :
    (Module.End C (Space W C))ˣ where
  val := left cs (q : C) i
  inv := leftInv cs q i
  val_inv := left_mul_leftInv cs q i
  inv_val := leftInv_mul_left cs q i

noncomputable def wordUnit (cs : CoxeterSystem M W) (q : Cˣ) (ω : List B) :
    (Module.End C (Space W C))ˣ := (ω.map (unit cs q)).prod

@[simp] theorem wordUnit_val (cs : CoxeterSystem M W) (q : Cˣ) (ω : List B) :
    (wordUnit cs q ω).val = leftWord cs (q : C) ω := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    change (unit cs q i).val * (wordUnit cs q ω).val = left cs (q : C) i * leftWord cs (q : C) ω
    rw [ih]
    rfl

/-- The genuine normalized standard-basis action, a unit in the regular
endomorphism algebra. No presentation relations are assumed. -/
noncomputable def standardUnit (cs : CoxeterSystem M W) (q : Cˣ) (w : W) :
    (Module.End C (Space W C))ˣ :=
  wordUnit cs q (Classical.choose (cs.exists_isReduced w))

/-- The bar image of an actual standard basis vector; inverse units give
expression independence before any polynomial coefficients are extracted. -/
noncomputable def barBasis (cs : CoxeterSystem M W) (q : Cˣ) (w : W) : Space W C :=
  ((standardUnit cs q w⁻¹)⁻¹).val (basis 1)

noncomputable def barLinear (cs : CoxeterSystem M W) (q : Cˣ) : Module.End C (Space W C) :=
  Finsupp.linearCombination C (barBasis cs q)

@[simp] theorem barLinear_basis (cs : CoxeterSystem M W) (q : Cˣ) (w : W) :
    barLinear cs q (basis w) = barBasis cs q w := by
  simp [barLinear, basis, Finsupp.linearCombination_single]

@[simp] theorem leftInv_basis (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (w : W) :
    leftInv cs q i (basis w) =
      if cs.length (cs.simple i * w) < cs.length w then basis (cs.simple i * w)
      else (↑q⁻¹ : C) • basis (cs.simple i * w) + ((↑q⁻¹ : C) - 1) • basis w := by
  rw [leftInv_apply, left_basis]
  split_ifs
  · simp [smul_smul]
  · rw [smul_sub, smul_smul]
    have hscalar : (↑q⁻¹ : C) * ((q : C) - 1) = 1 - (↑q⁻¹ : C) := by
      rw [mul_sub, q.inv_mul, mul_one]
    rw [hscalar, sub_smul, one_smul]
    module

end HeckeQ


end KLInvariance
end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Sheaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Ordered moment graphs, sheaves, flabbiness, sections and boundary images.
-/

section


/-! The finite-section extension argument required by source §4.3. No BMP
character theorem is postulated. These definitions are ordinary module-valued
sheaves on a directed ordered graph; labels enter later through which edge
modules vanish after localization. -/

namespace KLInvariance.MomentGraph

universe u v w z

variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V] {E : Type w}

namespace Sheaf
variable {G : OrderedGraph V E} (B : Sheaf (R := R) G)

theorem compatible_mono {Ω Ω' : Set V} {f : B.Assignment}
    (hf : B.CompatibleOn Ω f) (h : Ω' ⊆ Ω) : B.CompatibleOn Ω' f :=
  fun e hs ht => hf e (h hs) (h ht)

end Sheaf
end KLInvariance.MomentGraph

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_GradedSheaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded moment-graph sheaves, boundary sections, graded covers and morphisms.
-/


section


namespace KLInvariance.MomentGraph.Sheaf
universe u v w z z'
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}

structure Iso (B : Sheaf.{u,v,w,z} (R := R) G) (C : Sheaf.{u,v,w,z'} (R := R) G) where
  vertex : ∀ x, B.vertex x ≃ₗ[R] C.vertex x
  edge : ∀ e, B.edge e ≃ₗ[R] C.edge e
  lower : ∀ e v, edge e (B.lower e v) = C.lower e (vertex (G.source e) v)
  upper : ∀ e v, edge e (B.upper e v) = C.upper e (vertex (G.target e) v)

namespace Iso
variable {B : Sheaf.{u,v,w,z} (R := R) G} {C : Sheaf.{u,v,w,z'} (R := R) G}
  (j : Iso B C)

noncomputable def assignments : B.Assignment ≃ₗ[R] C.Assignment :=
  LinearEquiv.piCongrRight j.vertex

theorem compatible_iff (Ω : Set V) (f : B.Assignment) :
    C.CompatibleOn Ω (j.assignments f) ↔ B.CompatibleOn Ω f := by
  constructor <;> intro h e hs ht
  · apply (j.edge e).injective
    rw [j.lower,j.upper]
    exact h e hs ht
  · change C.lower e (j.vertex _ (f _)) = C.upper e (j.vertex _ (f _))
    rw [← j.lower,← j.upper,h e hs ht]

theorem map_sections (Ω : Set V) :
    (B.sections Ω).map j.assignments.toLinearMap = C.sections Ω := by
  ext g
  constructor
  · rintro ⟨f,hf,rfl⟩
    exact (j.compatible_iff Ω f).mpr hf
  · intro hg
    refine ⟨j.assignments.symm g,?_,j.assignments.apply_symm_apply g⟩
    apply (j.compatible_iff Ω _).mp
    change C.CompatibleOn Ω g at hg
    simpa using hg

noncomputable def sections (Ω : Set V) : B.sections Ω ≃ₗ[R] C.sections Ω :=
  j.assignments.ofSubmodules _ _ (j.map_sections Ω)

end Iso

end KLInvariance.MomentGraph.Sheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_MinimalExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Minimal-boundary extension sheaves, graded splittings and sheaf decomposition.
-/


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}

structure Iso (B C : GradedSheaf (𝓐 := 𝓐) G) extends Sheaf.Iso B.forget C.forget where
  vertex_graded : ∀ x n v, v ∈ (B.vertex x).piece n → vertex x v ∈ (C.vertex x).piece n
  edge_graded : ∀ e n v, v ∈ (B.edge e).piece n → edge e v ∈ (C.edge e).piece n

end KLInvariance.MomentGraph.GradedSheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SheafMorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded sheaf morphisms, exact section constructions and character sums.
-/


section

/-! A homogeneous idempotent with image in the positive-ideal multiple of a
bounded-below graded module is zero. This is the minimal-cover rigidity needed
to identify the indecomposable in the BMP construction. -/
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} (M : ModuleData.{uk,ua,um} 𝓐)

 theorem idempotent_eq_zero (f : Hom M M)
    (hi : ∀ v, f.map (f.map v) = f.map v)
    (hm : LinearMap.range f.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A M)) :
    f.map = 0 := by
  have hker : LinearMap.ker f.map = ⊤ :=
    eq_top_of_positive_smul_sup 𝓐 M.piece 0 M.nonneg (LinearMap.ker f.map)
      (by
        intro n m h
        change f.map (component M.piece n m) = 0
        rw [← f.component, LinearMap.mem_ker.mp h, map_zero])
      (by
        apply top_unique
        intro m _
        apply Submodule.mem_sup.mpr
        refine ⟨m-f.map m,?_,f.map m,hm ⟨m,rfl⟩,sub_add_cancel _ _⟩
        change f.map (m-f.map m) = 0
        rw [map_sub,hi,sub_self])
  exact LinearMap.ker_eq_top.mp hker

end KLInvariance.Graded.ModuleData

end


section

/-! The actual minimal boundary sheaf is indecomposable: it has no nontrivial
homogeneous idempotent. No KL character or costalk freeness is used here. -/

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)

 theorem unit_idempotent_trivial [IsDomain A]
    (f : Hom (unit.{uk,ua,um} hneg) (unit.{uk,ua,um} hneg))
    (hi : ∀ v, f.map (f.map v) = f.map v) :
    f.map = 0 ∨ f.map = LinearMap.id := by
  let e : unit.{uk,ua,um} hneg := fun _ => 1
  let c : A := f.map e PUnit.unit
  have expand (v : unit.{uk,ua,um} hneg) : v = v PUnit.unit • e := by
    funext i
    cases i
    exact (mul_one _).symm
  have hf (v : unit.{uk,ua,um} hneg) (i : PUnit.{max ua um + 1}) :
      f.map v i = v PUnit.unit * c := by
    calc
      f.map v i = f.map (v PUnit.unit • e) i := congrArg (fun v => f.map v i) (expand v)
      _ = v PUnit.unit * c := by rw [map_smul]; cases i; rfl
  have hc : c*c=c := by
    have h := congrFun (hi e) PUnit.unit
    rw [hf (f.map e) PUnit.unit] at h
    exact h
  have hz : c*(c-1)=0 := by rw [mul_sub,mul_one,hc,sub_self]
  rcases mul_eq_zero.mp hz with hc | hc
  · left
    apply LinearMap.ext
    intro v
    funext i
    rw [hf,hc,mul_zero]
    rfl
  · right
    have hc : c=1 := sub_eq_zero.mp hc
    apply LinearMap.ext
    intro v
    funext i
    rw [hf,hc,mul_one]
    cases i
    rfl

end KLInvariance.Graded.ModuleData

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Frobenius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coxeter Frobenius extensions, tensor duality and translation across reflection pairs.
-/


section

/-! Tensor induction of integral self-dual bimodules across a Frobenius
extension. All pairings refer to actual integral modules. -/
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
noncomputable section

attribute [instance] PairedModule.add PairedModule.module PairedModule.free PairedModule.finite

end
end KLInvariance.FrobeniusDuality

end


section

namespace KLInvariance.Graded
universe uk us
variable {k : Type uk} [Field k] {σ : Type us}

 theorem algHom_polynomialGrading (f : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (hX : ∀ i, f (MvPolynomial.X i) ∈ polynomialGrading k σ 1)
    {n : ℤ} {p : MvPolynomial σ k} (hp : p ∈ polynomialGrading k σ n) :
    f p ∈ polynomialGrading k σ n := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (polynomialGrading k σ n).zero_mem
  | add p q _ _ hp hq => simpa only [map_add] using (polynomialGrading k σ n).add_mem hp hq
  | monomial d c hd =>
    rw [MvPolynomial.monomial_eq,map_mul]
    have hc : f (MvPolynomial.C c)=MvPolynomial.C c := f.commutes c
    rw [hc]
    apply MvPolynomial.IsWeightedHomogeneous.C_mul
    simp only [Finsupp.prod,map_prod,map_pow]
    have hh := SetLike.prod_pow_mem_graded (polynomialGrading k σ)
      (fun _ : σ => (1:ℤ)) (fun i => f (MvPolynomial.X i)) d (F := d.support)
      (fun i _ => hX i)
    simpa only [Finsupp.weight_apply,Finsupp.sum] using hd ▸ hh

end KLInvariance.Graded

namespace KLInvariance.ReflectionFrobenius
open Module KLInvariance.Graded
universe uk uv us
variable {k : Type uk} [Field k] [CharZero k]
  {V : Type uv} [AddCommGroup V] [Module k V]
  {σ : Type us} [Fintype σ] (basis : Basis σ k V)
noncomputable section

omit [CharZero k] in
 theorem polynomialLinear_homogeneous (v : V) :
    polynomialLinear basis v ∈ polynomialGrading k σ 1 := by
  classical
  unfold polynomialLinear
  rw [← basis.sum_repr v]
  simp only [map_sum,map_smul,SymmetricAlgebra.equivMvPolynomial_ι_apply]
  apply Submodule.sum_mem
  intro i _
  exact (polynomialGrading k σ 1).smul_mem _
    (MvPolynomial.isWeightedHomogeneous_X k (fun _ : σ => (1:ℤ)) i)

omit [CharZero k] in
 theorem polynomialAction_homogeneous (e : V ≃ₗ[k] V) {n : ℤ}
    {p : MvPolynomial σ k} (hp : p ∈ polynomialGrading k σ n) :
    polynomialAction basis e p ∈ polynomialGrading k σ n := by
  apply algHom_polynomialGrading (polynomialAction basis e).toAlgHom _ hp
  intro i
  change polynomialAction basis e (MvPolynomial.X i) ∈ _
  have hx : MvPolynomial.X i = polynomialLinear basis (basis i) := by
    simp [polynomialLinear]
  rw [hx,polynomialAction_linear]
  exact polynomialLinear_homogeneous basis _

end
end KLInvariance.ReflectionFrobenius

end


section

/-! A grading defined by an actual homogeneous free basis, with an explicit
coefficient test. Used to put the genuine grading on tensor Bott--Samelsons. -/
namespace KLInvariance.Graded
open Module
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐]
  [SetLike.GradedMonoid 𝓐]
  {N : Type um} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  {ι : Type ui} [Fintype ι] (b : Basis ι A N) (d : ι → ℤ)
noncomputable section

 def basisPiece (n : ℤ) : Submodule k N :=
  (shiftedPiece 𝓐 d n).comap (b.equivFun.restrictScalars k).toLinearMap

 instance basisPiece_decomposition : DirectSum.Decomposition (basisPiece 𝓐 b d) := by
  let _ : DirectSum.Decomposition (shiftedPiece 𝓐 d) := (shifted_isInternal 𝓐 d).chooseDecomposition
  apply DirectSum.IsInternal.chooseDecomposition
  have he : basisPiece 𝓐 b d = fun n => (shiftedPiece 𝓐 d n).map
      (b.equivFun.restrictScalars k).symm.toLinearMap := by
    funext n
    exact Submodule.comap_equiv_eq_map_symm _ _
  rw [he]
  apply image_isInternal (shiftedPiece 𝓐 d)
    (b.equivFun.restrictScalars k).symm.toLinearMap
    (b.equivFun.restrictScalars k).symm.surjective
  intro n m hm
  have hz : m=0 := (b.equivFun.restrictScalars k).symm.injective (by simpa using hm)
  subst m
  simp

 instance basisPiece_graded : SetLike.GradedSMul 𝓐 (basisPiece 𝓐 b d) where
  smul_mem := by
    intro n m a x ha hx i
    change b.repr (a • x) i ∈ 𝓐 ((n+m)-d i)
    rw [map_smul,Finsupp.smul_apply,smul_eq_mul]
    change ∀ i, b.repr x i ∈ 𝓐 (m-d i) at hx
    have h := SetLike.GradedMul.mul_mem ha (hx i)
    simpa only [add_sub_assoc] using h

end
end KLInvariance.Graded

end


section

/-! Localization coordinates for tensor induction over a reflection wall.
This is an integral injectivity argument, not character normalization. -/
namespace KLInvariance.ReflectionFrobenius
open scoped Matrix
universe ua ui
variable {A : Type ua} [CommRing A] [IsDomain A] [CharZero A]
  {ι : Type ui} [Fintype ι] (τ : A ≃+* A) (α : A)
noncomputable section

 theorem wallCoordinate_injective (hα : α ≠ 0) (E : Matrix ι ι A)
    (hE : Function.Injective (Matrix.mulVec E)) : Function.Injective (wallCoordinate τ α E) := by
  intro v w hv
  have h₀ : (fun j => v (0,j)+α*v (1,j)) = (fun j => w (0,j)+α*w (1,j)) := by
    apply hE
    funext j
    simpa only [wallCoordinate,ite_eq_left rfl,ite_true, if_true] using congrFun hv (0,j)
  have h₁ : (fun j => v (0,j)-α*v (1,j)) = (fun j => w (0,j)-α*w (1,j)) := by
    apply matrixTwist_injective τ E hE
    funext j
    simpa only [wallCoordinate,show (1:Fin 2) ≠ 0 by decide,ite_false, if_false] using congrFun hv (1,j)
  funext ⟨ε,j⟩
  have h0 := congrFun h₀ j
  have h1 := congrFun h₁ j
  have hi1 : v (1,j)=w (1,j) := by
    have hh : (2:A)*α*(v (1,j)-w (1,j))=0 := by linear_combination h0-h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (mul_ne_zero two_ne_zero hα))
  have hi0 : v (0,j)=w (0,j) := by simpa only [hi1,add_left_inj] using h0
  fin_cases ε
  · exact hi0
  · exact hi1

end
end KLInvariance.ReflectionFrobenius

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BottSamelson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bott-Samelson tensor ranges, actual sections, grading and right kernels.
-/


section

/-! Intermediate standard-filtration predicates on the genuine tensor word.
These are proved by word induction; they are not main-theorem assumptions. -/
namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem simple_represents (i : I) : Represents M cs (cs.simple i) (root i) := by
  refine ⟨1,i,?_,?_⟩
  · simp
  · simp

end
end KLInvariance.TitsSpace

end


section

/-! Pair-projection edges of actual finite graded modules. The hypotheses say
only that the two actual weight projections are homogeneous and surjective. -/
namespace KLInvariance.Graded.ModuleData
open PairProjection
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {M X Y : ModuleData.{uk,ua,um} 𝓐}
  (f : Hom M X) (g : Hom M Y)
noncomputable section

 theorem pairLower_kernel_homogeneous (n : ℤ) (z : X)
    (hz : lower f.map g.map z=0) :
    lower f.map g.map (component X.piece n z)=0 := by
  obtain ⟨m,hm,hy⟩ := (kernel_lower f.map g.map z).mp hz
  apply (kernel_lower f.map g.map _).mpr
  refine ⟨component M.piece n m,?_,?_⟩
  · rw [← f.component,hm]
  · rw [← g.component,hy,map_zero]

 def pairEdgePiece (n : ℤ) : Submodule k (Edge f.map g.map) :=
  (X.piece n).map ((lower f.map g.map).restrictScalars k)

 def pairEdge (hg : Function.Surjective g.map) : ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A (Edge f.map g.map)
  kModule := inferInstance
  tower := inferInstance
  piece := pairEdgePiece f g
  decomposition := (image_isInternal X.piece ((lower f.map g.map).restrictScalars k)
    (lower_surjective f.map g.map hg) (pairLower_kernel_homogeneous f g)).chooseDecomposition
  graded := ⟨by
    rintro i j a z ha ⟨w,hw,rfl⟩
    exact ⟨a • w,SetLike.GradedSMul.smul_mem ha hw,map_smul (lower f.map g.map) a w⟩⟩
  nonneg := by
    intro n hn
    unfold pairEdgePiece
    rw [X.nonneg n hn,Submodule.map_bot]
  finite := Module.Finite.of_surjective (lower f.map g.map) (lower_surjective f.map g.map hg)

 def pairLower (hg : Function.Surjective g.map) : Hom X (pairEdge f g hg) where
  map := lower f.map g.map
  graded := fun _ z hz => ⟨z,hz,rfl⟩

 theorem Hom.homogeneous_lift (hg : Function.Surjective g.map) (n : ℤ)
    (y : Y) (hy : y ∈ Y.piece n) : ∃ m : M, m ∈ M.piece n ∧ g.map m=y := by
  obtain ⟨m,hm⟩ := hg y
  refine ⟨Graded.component M.piece n m,(DirectSum.decompose M.piece m n).property,?_⟩
  rw [← g.component,hm]
  exact DirectSum.decompose_of_mem_same Y.piece hy

 def pairUpper (hg : Function.Surjective g.map) : Hom Y (pairEdge f g hg) where
  map := upper f.map g.map
  graded := by
    intro n y hy
    obtain ⟨m,hm,rfl⟩ := g.homogeneous_lift hg n y hy
    exact ⟨f.map m,f.graded n m hm,compatible f.map g.map m⟩

end
end KLInvariance.Graded.ModuleData

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_IntegralPairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert recurrences, projective section ranges, integral lattices and graded perfect adjoints.
-/


section

/-! The honest unnormalized Hecke word (T_s+1)...(T_t+1), including exact
coefficient recurrence over a general commutative ring, without invertibility
of q or any KL/BMP character assertion. -/
namespace KLInvariance.HeckeQ
open Hecke (Space basis)
variable {I W C : Type*} [Group W] {M : CoxeterMatrix I} [CommRing C]
noncomputable section

 def positiveWord (cs : CoxeterSystem M W) (q : C) : List I → Space W C
  | [] => basis 1
  | i::l => positiveWord cs q l+left cs q i (positiveWord cs q l)

 @[simp] theorem positiveWord_nil (cs : CoxeterSystem M W) (q : C) :
    positiveWord cs q []=basis 1 := rfl

end
end KLInvariance.HeckeQ

end


section

/-! Range-valued projections to sets of coordinates and their natural
surjective restriction maps. -/
namespace KLInvariance.CoordinateProjection
universe ur un uv ux
variable {R : Type ur} [CommRing R] {N : Type un} [AddCommGroup N] [Module R N]
  {V : Type uv} {X : V → Type ux} [∀ x, AddCommGroup (X x)] [∀ x, Module R (X x)]
  (f : ∀ x, N →ₗ[R] X x)
noncomputable section

 @[simp] theorem project_apply (U : Set V) (n : N) (x : U) : (project f U n).val x=f x.val n := rfl

 def restrict {U K : Set V} (h : U⊆K) : image f K →ₗ[R] image f U where
  toFun z := ⟨fun x => z.val ⟨x.val,h x.property⟩,by
    obtain ⟨n,hn⟩ := z.property
    refine ⟨n,?_⟩
    funext x
    exact congrFun hn ⟨x.val,h x.property⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 @[simp] theorem restrict_project {U K : Set V} (h : U⊆K) (n : N) :
    restrict f h (project f K n)=project f U n := rfl

end
end KLInvariance.CoordinateProjection

end


section

/-! Upper sets and actual finite-word projection predicates. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection
universe u v
variable {I : Type u} [klPreservedInstance11 : Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def BruhatUpper (U : Set W) : Prop :=
  ∀ {x y}, BruhatLE cs x y → x∈U → y∈U

end
end KLInvariance.TitsSpace

end


section

/-! Integral local projectors for finite character lattices. This lemma does
not assert any BMP character theorem or identify a chosen summand with BMP. -/
namespace KLInvariance.FiniteCharacterLocalization
universe u v w
variable {R : Type u} [CommRing R] {X : Type v}
  {E : X → Type w} [∀ x, AddCommGroup (E x)] [∀ x, Module R (E x)]
noncomputable section

 def stabilizer (L : Submodule R (∀ x, E x)) : Subalgebra R (X → R) where
  carrier := {f | ∀ m ∈ L, diagonal f m ∈ L}
  mul_mem' := by
    intro f g hf hg m hm
    have h := hf _ (hg m hm)
    simpa only [diagonal,LinearMap.coe_mk,AddHom.coe_mk,Pi.mul_apply,mul_smul] using h
  one_mem' := by intro m hm; simpa [diagonal] using hm
  add_mem' := by
    intro f g hf hg m hm
    have he : diagonal (f+g) m = diagonal f m+diagonal g m := by
      funext x
      exact add_smul _ _ _
    rw [he]
    exact L.add_mem (hf m hm) (hg m hm)
  zero_mem' := by
    intro m _
    have he : diagonal (0 : X → R) m=0 := by
      funext x
      exact zero_smul _ _
    rw [he]
    exact L.zero_mem
  algebraMap_mem' := by
    intro r m hm
    exact L.smul_mem r hm

/-- A polynomial in stable diagonal weights which kills the complement of
`C` and is a common scalar on `C`. Its scalar is a product, not a quotient. -/
 theorem uniform_projector (L : Submodule R (∀ x, E x)) (C : Finset X)
    (f : X → R) (hf : f ∈ stabilizer L) (hz : ∀ x ∉ C, f x=0) :
    ∃ g ∈ stabilizer L,
      (∀ x ∈ C, g x=∏ y ∈ C, f y) ∧ (∀ x ∉ C, g x=0) := by
  classical
  let d : R := ∏ y ∈ C, f y
  let h : X → R := ∏ y ∈ C, (algebraMap R (X → R) (f y)-f)
  have hh : h ∈ stabilizer L := by
    exact (stabilizer L).prod_mem fun y _ =>
      (stabilizer L).sub_mem ((stabilizer L).algebraMap_mem (f y)) hf
  refine ⟨algebraMap R (X → R) d-h,
    (stabilizer L).sub_mem ((stabilizer L).algebraMap_mem d) hh,?_,?_⟩
  · intro x hx
    change d-h x=d
    suffices h x=0 by rw [this,sub_zero]
    dsimp [h]
    rw [Finset.prod_apply]
    apply Finset.prod_eq_zero hx
    simp
  · intro x hx
    change d-h x=0
    suffices h x=d by rw [this,sub_self]
    dsimp [h,d]
    rw [Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro y _
    simp [hz x hx]

end
end KLInvariance.FiniteCharacterLocalization

end


section


namespace KLInvariance.ProjectiveLattice
variable {R : Type*} [CommRing R] [klPreservedInstance15 : IsDomain R] [klPreservedInstance16 : UniqueFactorizationMonoid R]

 omit [IsDomain R] [UniqueFactorizationMonoid R] in
 theorem finsupp_divide {ι : Type*} (r : R) (f : ι →₀ R)
    (h : ∀ i, r ∣ f i) : ∃ g : ι →₀ R, r • g = f := by
  classical
  let g : ι →₀ R := ∑ i ∈ f.support, Finsupp.single i (Classical.choose (h i))
  refine ⟨g, ?_⟩
  dsimp [g]
  rw [Finset.smul_sum]
  have heq : (∑ i ∈ f.support, r • Finsupp.single i (Classical.choose (h i))) =
      ∑ i ∈ f.support, Finsupp.single i (f i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finsupp.smul_single, smul_eq_mul, ← Classical.choose_spec (h i)]
  rw [heq]
  exact Finsupp.sum_single f

include klPreservedInstance15 klPreservedInstance16 in
 theorem prime_divide_of_relation {P : Type*} [AddCommGroup P] [Module R P]
    [Module.Projective R P] (p a c : R) (hp : Prime p) (ha : ¬p ∣ a)
    (m n : P) (h : a • m=(p*c) • n) : ∃ z : P, p • z=m := by
  have _ := klPreservedInstance15
  have _ := klPreservedInstance16
  obtain ⟨s,hs⟩ := Module.Projective.out (R := R) (P := P)
  have hdvd : ∀ i, p ∣ s m i := by
    intro i
    have he := congrArg (fun z : P => s z i) h
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at he
    have hm : p ∣ a*s m i := by
      rw [he]
      exact dvd_mul_of_dvd_left (dvd_mul_right p c) _
    exact (hp.dvd_mul.mp hm).resolve_left ha
  obtain ⟨z,hz⟩ := finsupp_divide p (s m) hdvd
  refine ⟨Finsupp.linearCombination R id z,?_⟩
  rw [← map_smul,hz,hs]

 theorem mem_of_prime_local_membership
    {E : Type*} [AddCommGroup E] [Module R E] [Module.IsTorsionFree R E]
    (M : Submodule R E) [Module.Projective R M] (x : E)
    (hgeneric : ∃ c : R, c ≠ 0 ∧ c • x ∈ M)
    (hlocal : ∀ p : R, Prime p → ∃ a : R, ¬p ∣ a ∧ a • x ∈ M) : x ∈ M := by
  obtain ⟨c,hcz,hcx⟩ := hgeneric
  suffices ∀ c : R, c≠0 → c • x ∈ M → x ∈ M from this c hcz hcx
  intro c
  induction c using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp
  | h₂ c hc =>
    intro _ hcx
    obtain ⟨u,rfl⟩ := hc
    simpa using M.smul_mem (↑u⁻¹ : R) hcx
  | h₃ c p hcz hp ih =>
    intro _ hpcx
    obtain ⟨a,hpa,hax⟩ := hlocal p hp
    let m : M := ⟨(p*c) • x,hpcx⟩
    let n : M := ⟨a • x,hax⟩
    have he : a • m=(p*c) • n := by
      apply Subtype.ext
      exact smul_comm a (p*c) x
    obtain ⟨z,hz⟩ := prime_divide_of_relation p a c hp hpa m n he
    have hcx : c • x=(z : E) := by
      apply smul_right_injective E hp.ne_zero
      have hv := congrArg Subtype.val hz
      change p • (z : E)=(p*c) • x at hv
      simpa only [mul_smul] using hv.symm
    exact ih hcz (hcx ▸ z.property)

end KLInvariance.ProjectiveLattice

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BalancedPairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded stalk duality, integral perfect balanced all-sections pairings, recognition and top grading.
-/


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {M N : ModuleData.{uk,ua,um} 𝓐}
 theorem Hom.eq_of_map_eq (f g : Hom M N) (h : f.map=g.map) : f=g := by
  cases f
  cases g
  cases h
  rfl
end KLInvariance.Graded.ModuleData

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded unit splittings, integral support and balanced cuts, and boundary-sheaf support and recognition.
-/


section

/-! The actual minimal-boundary sheaf is a summand of the reduced word.
No splitting or word-recognition axiom is supplied as a premise. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem symmetricLabel_represents (u b : W) (e : Edge cs u b) :
    Represents M cs (label cs u b e) (BruhatGraph.root cs u b e).val :=
  positiveRoot_represents M cs ⟨label cs u b e,label_isReflection cs u b e⟩

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CharacterReciprocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Conditional boundary-sheaf duality and stalk-character propositions, free sheaves, actual R-reciprocity and lower convolution. StalkCharacterObligation remains a Prop, not an unconditional character theorem or a premise of the R-first route.
-/


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

local instance finiteEdges : Fintype (Edge cs 1 b) := Fintype.ofFinite _

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DyerPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite character cancellation, reflection-ratio orders and adapted Dyer decreasing paths.
-/


section

/-! R-reciprocity for the ACTUAL minimal-boundary BMP character, obtained
by simultaneous word stalk/costalk decomposition and unipotent cancellation.
This is not a character identification: strict halfdegree remains separate. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance instDecidable_solutions_5_r4494c2_1 (p : Prop) : Decidable p := Classical.propDecidable p
local instance bmpRecInterval (b : W) : Fintype (Interval cs 1 b) := by
  let := interval_finite cs 1 b
  exact Fintype.ofFinite _

end
end KLInvariance.BruhatGraph

end


end OAI
end


