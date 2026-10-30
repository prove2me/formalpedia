-- Prove2me | Definitions.Def_OAIQ124K014
-- name    : OAIQ124K014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:57:42.127883+00:00
-- url     : https://prove2.me/theorems/accf1101-066d-404d-b90b-6d56a519dc3c
-- title:
--   Definitions bundle OAIQ124K014 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 52 declarations of OpenAI's Lean: 17 definitions and 35 theorems. The definitions and types are `OAI.KLInvariance.Graded.ModuleData.descendedEdge`, `OAI.KLInvariance.MomentGraph.BoundarySheaf.homIsoOfIso`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.aboveIso`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.assignmentMap`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.image`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageInclusion`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageProjection`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageSplit`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.isoOfBijective`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.sectionMap`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Iso.hom`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Iso.invHom`, `OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.downEnd`, `OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.liftEnd`, `OAI.KLInvariance.TitsSpace.bottHeadPatch`, `OAI.KLInvariance.TitsSpace.bottVertexProjection`, `OAI.KLInvariance.TitsSpace.bottWeightSupported`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_BalancedPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BalancedPairings.lean), [`KazhdanLusztig_EdgeLocalization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/EdgeLocalization.lean), [`KazhdanLusztig_Frobenius`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Frobenius.lean), [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean), [`KazhdanLusztig_Support`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Support.lean).
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K008`, `OAIQ124K009` and `OAIQ124K010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K016`, `OAIQ124K017` and `OAIQ124K018`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K008
import Definitions.Def_OAIQ124K009
import Definitions.Def_OAIQ124K010

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Frobenius
attribute [-instance] _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_graded _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_graded
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

/-! Genuine tensor-defined Bott--Samelson bimodules for the extended real
Coxeter realization. The perfect pairing is integral and balanced. This
construction alone does not identify indecomposable BMP summands or prove
the Elias--Williamson character theorem. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottSamelson_balanced (l : List I) (a : SymmetricCoefficient (M := M))
    (m n : BottSamelsonModule cs l) :
    bottSamelsonDuality cs l (bottSamelsonRight cs l a m) n =
      bottSamelsonDuality cs l m (bottSamelsonRight cs l a n) :=
  (bottSamelson cs l).balanced a m n

end
end KLInvariance.TitsSpace

end


section

/-! The actual tensor-defined Bott--Samelson module has the word grading and
its integral duality lowers degree by word length (degree-one roots).
This does not identify an indecomposable summand with the BMP sheaf. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
open _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottBasis_pairing_homogeneous (l : List I) (e f : BottIndex l) :
    bottSamelsonDuality cs l (bottBasis cs l e) (bottBasis cs l f) ∈
      symmetricGrading basis (bottDegree l e+bottDegree l f-l.length) := by
  induction l with
  | nil =>
    change PUnit at e f
    change (Basis.singleton PUnit (SymmetricCoefficient (M := M)) e) *
      (Basis.singleton PUnit (SymmetricCoefficient (M := M)) f) ∈ symmetricGrading basis 0
    simp only [Basis.singleton_apply, one_mul]
    exact SetLike.one_mem_graded _
  | cons i l ih =>
    change (Fin 2 × BottIndex l) at e f
    rcases e with ⟨ei, ej⟩
    rcases f with ⟨fi, fj⟩
    let : Module.Free (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
      simpleFixed_free cs i
    let : Module.Finite (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
      simpleFixed_finite cs i
    have h := inducedPairing_basis_homogeneous
      (coefficientAction cs (cs.simple i)) (simpleRootPolynomial i)
      (simple_involutive cs i) (simpleRootPolynomial_ne_zero i)
      (simple_anti cs i) (simple_divisible cs i) (bottSamelson cs l).obj
      (bottBasis cs l) (symmetricGrading basis) (simpleRoot_homogeneous basis i)
      (coefficientAction_homogeneous cs basis (cs.simple i))
      (bottDegree l) l.length ih ei fi ej fj
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,bottDegree]
    convert h using 1; rfl

 theorem bottDuality_homogeneous (l : List I) {n m : ℤ}
    {x y : BottSamelsonModule cs l} (hx : x ∈ bottPiece cs basis l n)
    (hy : y ∈ bottPiece cs basis l m) :
    bottSamelsonDuality cs l x y ∈ symmetricGrading basis (n+m-l.length) := by
  exact pairing_homogeneous (symmetricGrading basis) (bottBasis cs l) (bottDegree l)
    (bottSamelsonDuality cs l).toLinearMap l.length
    (bottBasis_pairing_homogeneous cs basis l) hx hy

end
end KLInvariance.TitsSpace

end


section

/-! Integral weight support and orthogonality for the actual tensor module.
These are the vertex support statements behind the section pairing, not an
identification of the minimal BMP sheaf or its character. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 local instance instDecidableEqBottIndex_r6fc1a1_1 (l : List I) : DecidableEq (BottIndex l) := Classical.decEq _
def bottWeightSupported (l : List I) (x : W) : Submodule (SymmetricCoefficient (M := M))
    (BottSamelsonModule cs l) where
  carrier := {m | ∀ e, bottWeight cs l e ≠ x → bottEvaluation cs l e m = 0}
  zero_mem' := by intro e _; exact map_zero _
  add_mem' := by intro m n hm hn e he; rw [map_add,hm e he,hn e he,zero_add]
  smul_mem' := by intro a m hm e he; rw [map_smul,hm e he,smul_zero]

end
end KLInvariance.TitsSpace

end


section

/-! Exact Bruhat support of the actual tensor word's subexpression weights.
The ambient Coxeter system is not assumed crystallographic. -/
namespace KLInvariance.TitsSpace
universe u v
variable {I : Type u} {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottWeight_bruhat (l : List I) (hl : cs.IsReduced l) (e : BottIndex l) :
    BruhatLE cs (bottWeight cs l e) (cs.wordProd l) := by
  rw [← bottSubword_wordProd]
  exact bruhat_of_subword cs (bottSubword_sublist l e) hl

end
end KLInvariance.TitsSpace

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

/-! Genuine first/reflected-tail maps on projected upper-set images. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius ReflectionPairTranslation
open CoordinateProjection ProjectiveRange
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 theorem bottStalkProjection_zero_of_eq (l : List I) {x y : W} (h : x=y)
    (m : BottSamelsonModule cs l) (hm : bottStalkProjection cs l x m=0) :
    bottStalkProjection cs l y m=0 := by
  subst y
  exact hm

 theorem bottTensorEnd_first (i : I) (l : List I)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (m : BottSamelsonModule cs (i::l)) :
    bottHeadTail cs i l (bottTensorEnd cs i l e m)=e (bottHeadTail cs i l m) :=
  tensorFirst_map e m

 theorem bottTensorEnd_second (i : I) (l : List I)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (m : BottSamelsonModule cs (i::l)) :
    bottHeadReflectedTail cs i l (bottTensorEnd cs i l e m)=
      twistMap (coefficientAction cs (cs.simple i)).toRingEquiv e (bottHeadReflectedTail cs i l m) :=
  tensorSecond_map (coefficientAction cs (cs.simple i)).toRingEquiv (fun c => c.property) e m

end
end KLInvariance.TitsSpace

end


section

/-! Honest head/tail gluing. An exclusive-part crossing can only be the
simple head edge; alpha-divisibility handles precisely that crossing. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
open FrobeniusDuality ReflectionFrobenius
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 theorem bottHead_difference (i : I) (l : List I) (m : BottSamelsonModule cs (i::l)) :
    ∃ n : BottSamelsonModule cs l,
      bottHeadTail cs i l m-(bottHeadReflectedTail cs i l m).val=simpleRootPolynomial (M := M) i • n :=
  tensor_difference (coefficientAction cs (cs.simple i)).toRingEquiv (fun c => c.property)
    (simpleRootPolynomial (M := M) i) (simple_divisible cs i) m

 def bottHeadPatch (i : I) (l : List I) (U : Set W) (m : BottSamelsonModule cs (i::l)) :
    ∀ x : simpleUnion cs i U, bottStalk cs l x.val := by
  classical
  exact fun x => if x.val∈U then bottStalkProjection cs l x.val (bottHeadTail cs i l m)
    else bottStalkProjection cs l x.val (bottHeadReflectedTail cs i l m).val

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace
open Module TensorProduct CoordinateProjection ReflectionPairTranslation
open FrobeniusDuality ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 theorem bottSeed_first (i : I) (l : List I) (n : BottSamelsonModule cs l) :
    bottHeadTail cs i l (bottSeed cs i l n)=n := bottHeadTail_seed cs i l n

 theorem bottSeed_second (i : I) (l : List I) (n : BottSamelsonModule cs l) :
    bottHeadReflectedTail cs i l (bottSeed cs i l n)=Twist.mk n := bottHeadReflectedTail_seed cs i l n

end
end KLInvariance.TitsSpace

end


section

/-! Exact root-prime character classes of the actual Coxeter polynomial
coefficient action. These are the two-vertex blocks needed in integral
section realization; they are not BMP or KL-character assumptions. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem reflection_character_congruence_iff {t : W} {a : I → ℝ}
    (ha : Represents M cs t a) (x y : W) :
    (∀ p : SymmetricCoefficient (M := M),
      SymmetricAlgebra.ι ℝ (Extended M) (embed M a) ∣
        coefficientAction cs x p-coefficientAction cs y p) ↔
      x=y ∨ y=t*x := by
  constructor
  · intro hp
    let w := y*x⁻¹
    have hline (v : Extended M) :
        extendedAction M cs w v-v ∈ Submodule.span ℝ {embed M a} := by
      let p := (coefficientAction cs x).symm (SymmetricAlgebra.ι ℝ (Extended M) v)
      have hx : coefficientAction cs x p=SymmetricAlgebra.ι ℝ (Extended M) v :=
        AlgEquiv.apply_symm_apply _ _
      have hy : coefficientAction cs y p =
          coefficientAction cs w (SymmetricAlgebra.ι ℝ (Extended M) v) := by
        have h := coefficientAction_mul cs w x p
        rw [show w*x=y by dsimp [w]; group,hx] at h
        exact h
      have h := hp p
      rw [hx,hy,coefficientAction_ι,← map_sub] at h
      have hs := (EdgeAlgebra.symmetric_ι_dvd_iff (embed M a)
        (v-extendedAction M cs w v)).mp h
      simpa only [neg_sub,EdgeAlgebra.rootLine] using (EdgeAlgebra.rootLine (k := ℝ) (embed M a)).neg_mem hs
    have hnorm : extendedForm M (embed M a) (embed M a)=2 := by
      rw [(extendedForm_spec M).2.2]
      exact ha.isRoot.norm
    rcases Realization.orthogonal_eq_id_or_rootReflection
      (extendedForm M) (embed M a) hnorm (extendedAction M cs w)
      (extendedAction_preserves M cs w) hline with hid | href
    · left
      have hw : w=1 := by
        apply extendedAction_injective M cs
        apply LinearEquiv.ext
        intro v
        change extendedAction M cs w v=extendedAction M cs 1 v
        rw [map_one]
        change extendedAction M cs w v=v
        exact LinearMap.congr_fun hid v
      exact (mul_inv_eq_one.mp hw).symm
    · right
      have hw : w=t := by
        apply extendedAction_injective M cs
        apply LinearEquiv.ext
        intro v
        rw [ha.extendedAction_eq]
        exact href v
      exact mul_inv_eq_iff_eq_mul.mp hw
  · rintro (rfl | rfl)
    · intro p
      rw [sub_self]
      exact dvd_zero _
    · intro p
      rw [coefficientAction_mul]
      exact reflectionCoefficient_divisible cs ha (coefficientAction cs x p)

end
end KLInvariance.TitsSpace

end


section

/-! Flabbiness of the genuine interval word sheaf; the extension outside the
finite support is zero, not an extra assumption on the source interval. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottStalk_subsingleton_of_not_bruhat (l : List I) (hl : cs.IsReduced l)
    (x : W) (hx : ¬BruhatLE cs x (cs.wordProd l)) : Subsingleton (bottStalk cs l x) := by
  constructor
  intro p q
  apply Subtype.ext
  funext e
  exact (hx (e.property ▸ bottWeight_bruhat cs l hl e.val)).elim

end
end KLInvariance.TitsSpace

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

/-! Integral realization of tensor words as ALL sections of their actual
pair-projection sheaf. This assertion alone is not a BMP summand theorem,
flabbiness/standard-filtration theorem, or EW character theorem. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph FiniteCharacterLocalization
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottVertexProjection (l : List I) (u b : W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)]
    (∀ x : Interval cs u b, bottStalk cs l x.val) :=
  LinearMap.pi (fun x => bottStalkProjection cs l x.val)

end
end KLInvariance.TitsSpace

end


section

/-! Section maps for the actual graded sheaf morphisms. A sheaf splitting
really gives an integral graded section splitting; it is not replaced by a
generic-fibre splitting. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 def Hom.assignmentMap (h : Hom B C) : B.forget.Assignment →ₗ[A] C.forget.Assignment where
  toFun f x := (h.vertex x).map (f x)
  map_add' f g := by funext x; exact map_add (h.vertex x).map (f x) (g x)
  map_smul' r f := by funext x; exact map_smul (h.vertex x).map r (f x)

 theorem Hom.assignmentMap_compatible (h : Hom B C) (Ω : Set V)
    (f : B.forget.Assignment) (hf : B.forget.CompatibleOn Ω f) :
    C.forget.CompatibleOn Ω (h.assignmentMap f) := by
  intro e hs ht
  change (C.lower e).map ((h.vertex _).map (f _)) =
    (C.upper e).map ((h.vertex _).map (f _))
  exact (h.lower e (f (G.source e))).symm.trans
    ((congrArg (h.edge e).map (hf e hs ht)).trans (h.upper e (f (G.target e))))

 def Hom.sectionMap (h : Hom B C) (Ω : Set V) :
    B.forget.sections Ω →ₗ[A] C.forget.sections Ω :=
  (h.assignmentMap.domRestrict (B.forget.sections Ω)).codRestrict (C.forget.sections Ω)
    (fun f => h.assignmentMap_compatible Ω f.val f.property)

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.Graded.ModuleData
open PairProjection LinearDescent
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {M X Y : ModuleData.{uk,ua,um} 𝓐}
  (e : Hom M M) (f : Hom M X) (g : Hom M Y)
  (hf : Function.Surjective f.map) (hg : Function.Surjective g.map)
  (hef : ∀ m, f.map m=0 → f.map (e.map m)=0)
  (heg : ∀ m, g.map m=0 → g.map (e.map m)=0)
noncomputable section

 def descendedEdge : Hom (pairEdge f g hg) (pairEdge f g hg) where
  map := descend (lower f.map g.map) (lower_surjective f.map g.map hg)
    (descended e f hf hef).map (lower_kernel_preserved e f g hf hef heg)
  graded := by
    intro n z hz
    obtain ⟨x,hx,rfl⟩ := hz
    refine ⟨(descended e f hf hef).map x,(descended e f hf hef).graded n x hx,?_⟩
    exact (descend_apply (lower f.map g.map) (lower_surjective f.map g.map hg)
      (descended e f hf hef).map (lower_kernel_preserved e f g hf hef heg) x).symm

 theorem descendedEdge_lower (x : X) :
    (descendedEdge e f g hf hg hef heg).map (lower f.map g.map x)=
      lower f.map g.map ((descended e f hf hef).map x) :=
  descend_apply _ _ _ _ x

 theorem descendedEdge_upper (y : Y) :
    (descendedEdge e f g hf hg hef heg).map (upper f.map g.map y)=
      upper f.map g.map ((descended e g hg heg).map y) := by
  obtain ⟨m,rfl⟩ := hg y
  rw [← compatible f.map g.map m,descendedEdge_lower]
  change lower f.map g.map (descend f.map hf e.map hef (f.map m)) =
    upper f.map g.map (descend g.map hg e.map heg (g.map m))
  rw [descend_apply,descend_apply]
  exact compatible f.map g.map (e.map m)

end
end KLInvariance.Graded.ModuleData

end


section

/-! The literal integral image sheaf of a graded projector, with its actual
splitting. Used for word-adjoint projectors; no BMP summand is assumed. -/

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 def Hom.image (h : Hom B B) : GradedSheaf (𝓐 := 𝓐) G where
  vertex x := ModuleData.range (h.vertex x)
  edge e := ModuleData.range (h.edge e)
  lower e := ModuleData.rangeMap (h.vertex (G.source e)) (h.edge e) (B.lower e) (h.lower e)
  upper e := ModuleData.rangeMap (h.vertex (G.target e)) (h.edge e) (B.upper e) (h.upper e)

 def Hom.imageInclusion (h : Hom B B) : Hom h.image B where
  vertex x := ModuleData.rangeInclusion (h.vertex x)
  edge e := ModuleData.rangeInclusion (h.edge e)
  lower _ _ := rfl
  upper _ _ := rfl

 def Hom.imageProjection (h : Hom B B) : Hom B h.image where
  vertex x := ModuleData.rangeProjection (h.vertex x)
  edge e := ModuleData.rangeProjection (h.edge e)
  lower e v := Subtype.ext (h.lower e v)
  upper e v := Subtype.ext (h.upper e v)

 def Hom.imageSplit (h : Hom B B)
    (hv : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (he : ∀ e v, (h.edge e).map ((h.edge e).map v)=(h.edge e).map v) : SplitIn h.image B where
  inclusion := h.imageInclusion
  projection := h.imageProjection
  vertex_split x v := by
    obtain ⟨m,hm⟩ := v.property
    apply Subtype.ext
    change (h.vertex x).map v.val=v.val
    rw [← hm,hv]
  edge_split e v := by
    obtain ⟨m,hm⟩ := v.property
    apply Subtype.ext
    change (h.edge e).map v.val=v.val
    rw [← hm,he]

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G}

 theorem Hom.eq_of_vertex (f g : Hom B C)
    (hs : ∀ e, Function.Surjective (B.lower e).map)
    (hv : ∀ x v, (f.vertex x).map v=(g.vertex x).map v) : f=g := by
  apply f.eq_of_maps g hv
  intro e v
  obtain ⟨w,rfl⟩ := hs e v
  rw [f.lower,g.lower,hv]

end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! The endomorphism-corner formulation of a primitive graded sheaf
projector. This is a criterion, not an assertion of a BMP splitting. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G}

 theorem Hom.primitive_of_antiInvolution
    (a : Hom B B → Hom B B)
    (ha : Function.Involutive a)
    (hac : ∀ f g, a (f.comp g)=(a g).comp (a f))
    (haz : a Hom.zero=Hom.zero)
    (p : Hom B B) (hp : p.PrimitiveProjector) :
    (a p).PrimitiveProjector := by
  constructor
  · exact (hac p p).symm.trans (congrArg a hp.1)
  · intro f hf hfp hpf
    have hi : (a f).comp (a f)=a f := (hac f f).symm.trans (congrArg a hf)
    have hleft : (a f).comp p=a f := by
      have hh := congrArg a hpf
      rw [hac,ha] at hh
      exact hh
    have hright : p.comp (a f)=a f := by
      have hh := congrArg a hfp
      rw [hac,ha] at hh
      exact hh
    rcases hp.2 (a f) hi hleft hright with hz | he
    · left
      have hh := congrArg a hz
      rw [ha,haz] at hh
      exact hh
    · right
      exact (ha f).symm.trans (congrArg a he)

end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Primitive-corner recognition for genuine graded sheaf splittings.
This supplies the algebraic recognition step for a prospective BMP summand;
it neither postulates the splitting nor the word/BMP character. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 def SplitIn.liftEnd (s : SplitIn B C) (f : Hom B B) : Hom C C :=
  s.inclusion.comp (f.comp s.projection)

 theorem SplitIn.liftEnd_injective (s : SplitIn B C) : Function.Injective s.liftEnd := by
  intro f g h
  apply Hom.eq_of_maps
  · intro x v
    have hh := congrArg (fun q : Hom C C => (s.projection.vertex x).map
      ((q.vertex x).map ((s.inclusion.vertex x).map v))) h
    change (s.projection.vertex x).map ((s.inclusion.vertex x).map
      ((f.vertex x).map ((s.projection.vertex x).map ((s.inclusion.vertex x).map v))))=
      (s.projection.vertex x).map ((s.inclusion.vertex x).map
      ((g.vertex x).map ((s.projection.vertex x).map ((s.inclusion.vertex x).map v)))) at hh
    simpa only [s.vertex_split] using hh
  · intro e v
    have hh := congrArg (fun q : Hom C C => (s.projection.edge e).map
      ((q.edge e).map ((s.inclusion.edge e).map v))) h
    change (s.projection.edge e).map ((s.inclusion.edge e).map
      ((f.edge e).map ((s.projection.edge e).map ((s.inclusion.edge e).map v))))=
      (s.projection.edge e).map ((s.inclusion.edge e).map
      ((g.edge e).map ((s.projection.edge e).map ((s.inclusion.edge e).map v)))) at hh
    simpa only [s.edge_split] using hh

 theorem SplitIn.liftEnd_comp (s : SplitIn B C) (f g : Hom B B) :
    s.liftEnd (f.comp g)=(s.liftEnd f).comp (s.liftEnd g) := by
  apply Hom.eq_of_maps
  · intro x v
    change (s.inclusion.vertex x).map ((f.vertex x).map ((g.vertex x).map
      ((s.projection.vertex x).map v)))=
      (s.inclusion.vertex x).map ((f.vertex x).map ((s.projection.vertex x).map
      ((s.inclusion.vertex x).map ((g.vertex x).map ((s.projection.vertex x).map v)))))
    rw [s.vertex_split]
  · intro e v
    change (s.inclusion.edge e).map ((f.edge e).map ((g.edge e).map
      ((s.projection.edge e).map v)))=
      (s.inclusion.edge e).map ((f.edge e).map ((s.projection.edge e).map
      ((s.inclusion.edge e).map ((g.edge e).map ((s.projection.edge e).map v)))))
    rw [s.edge_split]

 theorem SplitIn.liftEnd_zero (s : SplitIn B C) : s.liftEnd Hom.zero=Hom.zero := by
  apply Hom.eq_of_maps
  · intro x v
    change (s.inclusion.vertex x).map 0=0
    exact map_zero _
  · intro e v
    change (s.inclusion.edge e).map 0=0
    exact map_zero _

 theorem SplitIn.primitive_id_of_projector (s : SplitIn B C)
    (h : s.projector.PrimitiveProjector) : (Hom.id B).PrimitiveProjector := by
  constructor
  · apply Hom.eq_of_maps <;> intros <;> rfl
  · intro f hf _ _
    have hc : (s.liftEnd f).comp (s.liftEnd f)=s.liftEnd f :=
      (s.liftEnd_comp f f).symm.trans (congrArg s.liftEnd hf)
    have hi : s.liftEnd (Hom.id B)=s.projector := by
      apply Hom.eq_of_maps <;> intros <;> rfl
    have hleft : (s.liftEnd f).comp s.projector=s.liftEnd f := by
      rw [← hi,← s.liftEnd_comp]
      congr 1
    have hright : s.projector.comp (s.liftEnd f)=s.liftEnd f := by
      rw [← hi,← s.liftEnd_comp]
      congr 1
    rcases h.2 (s.liftEnd f) hc hleft hright with hz | he
    · exact Or.inl (s.liftEnd_injective (hz.trans s.liftEnd_zero.symm))
    · exact Or.inr (s.liftEnd_injective (he.trans hi.symm))

 variable [IsNoetherianRing A]

 theorem Hom.primitive_image (p : Hom B B) (hp : p.PrimitiveProjector) :
    (Hom.id p.image).PrimitiveProjector := by
  have hv : ∀ x v, (p.vertex x).map ((p.vertex x).map v)=(p.vertex x).map v := by
    intro x v
    exact congrArg (fun q : Hom B B => (q.vertex x).map v) hp.1
  have he : ∀ e v, (p.edge e).map ((p.edge e).map v)=(p.edge e).map v := by
    intro e v
    exact congrArg (fun q : Hom B B => (q.edge e).map v) hp.1
  let s := p.imageSplit hv he
  have hs : s.projector=p := by
    apply Hom.eq_of_maps <;> intros <;> rfl
  apply s.primitive_id_of_projector
  rw [hs]
  exact hp

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! A normalized minimal boundary sheaf is primitive, and that property
passes to its projector in every ACTUAL graded splitting. No word splitting
is asserted here. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 def SplitIn.downEnd (s : SplitIn B C) (f : Hom C C) : Hom B B :=
  s.projection.comp (f.comp s.inclusion)

 theorem SplitIn.lift_down (s : SplitIn B C) (f : Hom C C)
    (hf : f.comp s.projector=f) (hf' : s.projector.comp f=f) :
    s.liftEnd (s.downEnd f)=f := by
  have heq : s.liftEnd (s.downEnd f)=s.projector.comp (f.comp s.projector) := by
    apply Hom.eq_of_maps <;> intros <;> rfl
  rw [heq,hf,hf']

 theorem SplitIn.downEnd_idempotent (s : SplitIn B C) (f : Hom C C)
    (hf : f.comp f=f) (hf' : s.projector.comp f=f) :
    (s.downEnd f).comp (s.downEnd f)=s.downEnd f := by
  have heq : (s.downEnd f).comp (s.downEnd f)=s.downEnd (f.comp (s.projector.comp f)) := by
    apply Hom.eq_of_maps <;> intros <;> rfl
  rw [heq,hf',hf]

 theorem SplitIn.primitive_projector_of_id (s : SplitIn B C)
    (h : (Hom.id B).PrimitiveProjector) : s.projector.PrimitiveProjector := by
  constructor
  · apply Hom.eq_of_maps
    · exact s.projector_vertex
    · exact s.projector_edge
  · intro f hf hfp hpf
    have hg := s.downEnd_idempotent f hf hpf
    have hl : (s.downEnd f).comp (Hom.id B)=s.downEnd f := by
      apply Hom.eq_of_maps <;> intros <;> rfl
    have hr : (Hom.id B).comp (s.downEnd f)=s.downEnd f := by
      apply Hom.eq_of_maps <;> intros <;> rfl
    rcases h.2 (s.downEnd f) hg hl hr with hz | he
    · left
      exact (s.lift_down f hfp hpf).symm.trans ((congrArg s.liftEnd hz).trans s.liftEnd_zero)
    · right
      have hi : s.liftEnd (Hom.id B)=s.projector := by
        apply Hom.eq_of_maps <;> intros <;> rfl
      exact (s.lift_down f hfp hpf).symm.trans ((congrArg s.liftEnd he).trans hi)

end
end KLInvariance.MomentGraph.GradedSheaf

namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {hneg : ∀ n < 0, 𝓐 n=⊥} {V E : Type um} [PartialOrder V] [Finite V]
  {G : OrderedGraph V E} {α : E → A} {b : V} [IsDomain A]
  (B : BoundarySheaf hneg G α b)

 theorem split_projector_primitive
    {C : GradedSheaf (𝓐 := 𝓐) G} (s : GradedSheaf.SplitIn B.sheaf C) :
    s.projector.PrimitiveProjector :=
  s.primitive_projector_of_id B.primitive_identity

end KLInvariance.MomentGraph.BoundarySheaf

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

/-! The actual BMP axioms inherited by a graded sheaf retract. These are
implications, not claims that the word sheaf already satisfies the axioms. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 theorem SplitIn.flabby (s : SplitIn B C) (hC : C.forget.Flabby) : B.forget.Flabby := by
  intro Ω hΩ f hf
  obtain ⟨g,hg,hgf⟩ := hC Ω hΩ (s.inclusion.assignmentMap f)
    (s.inclusion.assignmentMap_compatible Ω f hf)
  refine ⟨s.projection.assignmentMap g,
    s.projection.assignmentMap_compatible Set.univ g hg,?_⟩
  intro x hx
  change (s.projection.vertex x).map (g x)=f x
  rw [hgf x hx]
  exact s.vertex_split x (f x)

 theorem SplitIn.generated (s : SplitIn B C) (hC : C.forget.Generated) : B.forget.Generated := by
  intro x v
  obtain ⟨f,hf,hfx⟩ := hC x ((s.inclusion.vertex x).map v)
  refine ⟨s.projection.assignmentMap f,
    s.projection.assignmentMap_compatible Set.univ f hf,?_⟩
  change (s.projection.vertex x).map (f x)=v
  rw [hfx]
  exact s.vertex_split x v

 theorem SplitIn.upperQuotient (s : SplitIn B C) {α : E → A}
    (hC : C.UpperQuotient α) : B.UpperQuotient α := by
  intro e
  constructor
  · intro v
    obtain ⟨c,hc⟩ := (hC e).1 ((s.inclusion.edge e).map v)
    refine ⟨(s.projection.vertex (G.target e)).map c,?_⟩
    rw [← s.projection.upper,hc]
    exact s.edge_split e v
  · intro v
    constructor
    · intro hv
      have hz : (C.upper e).map ((s.inclusion.vertex _).map v)=0 := by
        rw [← s.inclusion.upper,hv]
        exact map_zero _
      obtain ⟨c,hc⟩ := (hC e).2 _ |>.mp hz
      refine ⟨(s.projection.vertex _).map c,?_⟩
      have h := congrArg (s.projection.vertex _).map hc
      rw [s.vertex_split,map_smul] at h
      exact h
    · rintro ⟨w,rfl⟩
      have hz := ((hC e).2 (α e • (s.inclusion.vertex _).map w)).mpr
        ⟨(s.inclusion.vertex _).map w,rfl⟩
      have he : (s.inclusion.edge e).map ((B.upper e).map (α e • w))=0 := by
        rw [s.inclusion.upper,map_smul]
        exact hz
      have h := congrArg (s.projection.edge e).map he
      rw [s.edge_split,map_zero] at h
      exact h

 theorem SplitIn.vertex_projective (s : SplitIn B C) (x : V)
    [Module.Projective A (C.vertex x)] : Module.Projective A (B.vertex x) := by
  apply Module.Projective.of_split (s.inclusion.vertex x).map (s.projection.vertex x).map
  apply LinearMap.ext
  exact s.vertex_split x

 theorem SplitIn.vertex_free
    [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
    [IsDomain A] [IsNoetherianRing A]
    (hneg : ∀ n < 0, 𝓐 n=⊥)
    (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c=a)
    (s : SplitIn B C) (x : V) [Module.Projective A (C.vertex x)] :
    Module.Free A (B.vertex x) := by
  let D := B.vertex x
  let : Module.Projective A D := s.vertex_projective x
  obtain ⟨ι,_,bs,_⟩ := exists_homogeneous_basis_connected 𝓐 D.piece hneg hzero 0 D.nonneg
  exact Module.Free.of_basis bs

end
end KLInvariance.MomentGraph.GradedSheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_EdgeLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bruhat sheaf localization, graded transport, local edge-image bounds and support.
-/


section

namespace KLInvariance.MomentGraph.Sheaf.AboveIso
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  [Fintype E] [IsNoetherianRing A] [IsDomain A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {B C : GradedSheaf (𝓐 := 𝓐) G} {x : V}
  (j : AboveIso B.forget C.forget x)

include hneg hzero in
 theorem stalk_hom_bijective
    (hj : ∀ e (h : x < G.target e) n v, v ∈ (B.edge e).piece n →
      j.edge e h v ∈ (C.edge e).piece n)
    (hBfree : Module.Free A (B.vertex x)) (hCfree : Module.Free A (C.vertex x))
    (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
    (hBmin : B.KernelMinimal x) (hCmin : C.KernelMinimal x)
    (f₀ : ModuleData.Hom (B.vertex x) (C.vertex x))
    (hf₀ : ∀ v, j.boundary (B.forget.stalkMap x v) =
      C.forget.stalkMap x (f₀.map v)) : Function.Bijective f₀.map := by
  let T := ModuleData.range (C.stalkHom x)
  let f : ModuleData.Hom (B.vertex x) T :=
    { map := LinearMap.codRestrict (LinearMap.range (C.forget.stalkMap x))
        (j.boundary.toLinearMap.comp (B.forget.stalkMap x)) (by
          intro v
          rw [← j.map_stalk_image hBf hBg hCf hCg]
          exact ⟨B.forget.stalkMap x v,⟨v,rfl⟩,rfl⟩)
      graded := by
        intro n v hv e _
        exact hj e.val _ n _ ((B.stalkHom x).graded n v hv e (Set.mem_univ e)) }
  let g : ModuleData.Hom (C.vertex x) T :=
    { map := (C.forget.stalkMap x).rangeRestrict
      graded := fun n v hv => (C.stalkHom x).graded n v hv }
  have hfs : Function.Surjective f.map := by
    intro v
    have hv : v.val ∈ (LinearMap.range (B.forget.stalkMap x)).map j.boundary.toLinearMap := by
      rw [j.map_stalk_image hBf hBg hCf hCg]
      exact v.property
    obtain ⟨w,⟨z,rfl⟩,hz⟩ := hv
    exact ⟨z,Subtype.ext hz⟩
  have hgs : Function.Surjective g.map := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w,Subtype.ext hw⟩
  have hfm : LinearMap.ker f.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A (B.vertex x)) := by
    intro v hv
    apply (B.kernelMinimal_iff x).mp hBmin
    apply LinearMap.mem_ker.mpr
    apply j.boundary.injective
    rw [map_zero]
    have hh : f.map v = 0 := LinearMap.mem_ker.mp hv
    exact congrArg (fun z : T => z.val) hh
  have hgm : LinearMap.ker g.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A (C.vertex x)) := by
    intro v hv
    apply (C.kernelMinimal_iff x).mp hCmin
    have hh : g.map v = 0 := LinearMap.mem_ker.mp hv
    exact congrArg (fun z : T => z.val) hh
  let F : ModuleData.MinimalCover T := ⟨B.vertex x,hBfree,f,hfs,hfm⟩
  let D : ModuleData.MinimalCover T := ⟨C.vertex x,hCfree,g,hgs,hgm⟩
  apply F.hom_bijective hneg hzero D f₀
  apply LinearMap.ext
  intro v
  exact Subtype.ext (hf₀ v).symm

end KLInvariance.MomentGraph.Sheaf.AboveIso

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 theorem Hom.edge_bijective_of_vertex (f : Hom B C) (α : E → A)
    (hB : B.UpperQuotient α) (hC : C.UpperQuotient α) (e : E)
    (hv : Function.Bijective (f.vertex (G.target e)).map) :
    Function.Bijective (f.edge e).map := by
  let v := LinearEquiv.ofBijective (f.vertex (G.target e)).map hv
  let j := QuotientEdge.iso (B.upper e).map (C.upper e).map
    (hB e).1 (hC e).1 v (QuotientEdge.map_kernel_scalar _ _ (α e) (hB e).2 (hC e).2 v)
  have he : (f.edge e).map=j.toLinearMap := by
    apply LinearMap.ext
    intro m
    obtain ⟨m,rfl⟩ := (hB e).1 m
    rw [f.upper]
    exact (QuotientEdge.iso_apply (B.upper e).map (C.upper e).map
      (hB e).1 (hC e).1 v
      (QuotientEdge.map_kernel_scalar _ _ (α e) (hB e).2 (hC e).2 v) m).symm
  rw [he]
  exact j.bijective

 def Hom.isoOfBijective (f : Hom B C)
    (hv : ∀ x, Function.Bijective (f.vertex x).map)
    (he : ∀ e, Function.Bijective (f.edge e).map) : Iso B C where
  vertex x := LinearEquiv.ofBijective (f.vertex x).map (hv x)
  edge e := LinearEquiv.ofBijective (f.edge e).map (he e)
  lower := f.lower
  upper := f.upper
  vertex_graded x := (f.vertex x).graded
  edge_graded e := (f.edge e).graded

 def Hom.aboveIso (f : Hom B C) (x : V)
    (hv : ∀ y, x<y → Function.Bijective (f.vertex y).map)
    (he : ∀ e, x<G.target e → Function.Bijective (f.edge e).map) :
    Sheaf.AboveIso B.forget C.forget x where
  vertex y hy := LinearEquiv.ofBijective (f.vertex y).map (hv y hy)
  edge e he' := LinearEquiv.ofBijective (f.edge e).map (he e he')
  lower e _ := f.lower e
  upper e _ := f.upper e

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Invertibility detected at the top of the actual normalized minimal-boundary
sheaf. This is stronger than uniqueness of its isomorphism class. -/
namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (B C : BoundarySheaf hneg G α b)
noncomputable section

 include hzero in
 theorem hom_vertex_bijective (f : GradedSheaf.Hom B.sheaf C.sheaf)
    (hb : Function.Bijective (f.vertex b).map) (x : V) :
    Function.Bijective (f.vertex x).map := by
  classical
  refine wellFounded_gt.induction (C := fun y => Function.Bijective (f.vertex y).map) x ?_
  intro x ih
  by_cases hx : x=b
  · subst x
    exact hb
  have he : ∀ e, x<G.target e → Function.Bijective (f.edge e).map :=
    fun e h => f.edge_bijective_of_vertex α B.quotient C.quotient e (ih _ h)
  let j := f.aboveIso x ih he
  apply j.stalk_hom_bijective hneg hzero
    (fun e h n v hv => (f.edge e).graded n v hv)
    (B.free x) (C.free x) B.flabby.flabby B.generated C.flabby.flabby C.generated
    (B.minimal x hx) (C.minimal x hx) (f.vertex x)
  intro v
  funext e
  change (f.edge e.val).map (B.sheaf.forget.stalkMap x v e)=
    C.sheaf.forget.stalkMap x ((f.vertex x).map v) e
  rcases e with ⟨e,he⟩
  subst x
  exact f.lower e v

end
end KLInvariance.MomentGraph.BoundarySheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 def Iso.hom (j : Iso B C) : Hom B C where
  vertex x := ⟨(j.vertex x).toLinearMap,j.vertex_graded x⟩
  edge e := ⟨(j.edge e).toLinearMap,j.edge_graded e⟩
  lower := j.lower
  upper := j.upper

 def Iso.invHom (j : Iso B C) : Hom C B where
  vertex x := ⟨(j.vertex x).symm.toLinearMap,fun n v hv =>
    (j.hom.vertex x).mem_of_map_mem (j.vertex x).injective n _
      (by change j.vertex x ((j.vertex x).symm v) ∈ _
          exact ((j.vertex x).apply_symm_apply v).symm ▸ hv)⟩
  edge e := ⟨(j.edge e).symm.toLinearMap,fun n v hv =>
    (j.hom.edge e).mem_of_map_mem (j.edge e).injective n _
      (by change j.edge e ((j.edge e).symm v) ∈ _
          exact ((j.edge e).apply_symm_apply v).symm ▸ hv)⟩
  lower e v := by
    apply (j.edge e).injective
    exact ((j.edge e).apply_symm_apply _).trans
      ((j.lower e ((j.vertex (G.source e)).symm v)).trans
        (congrArg (C.forget.lower e) ((j.vertex (G.source e)).apply_symm_apply v))).symm
  upper e v := by
    apply (j.edge e).injective
    exact ((j.edge e).apply_symm_apply _).trans
      ((j.upper e ((j.vertex (G.target e)).symm v)).trans
        (congrArg (C.forget.upper e) ((j.vertex (G.target e)).apply_symm_apply v))).symm

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (B : BoundarySheaf hneg G α b) {C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 include hzero in
 theorem hom_vertex_bijective_of_iso (j : GradedSheaf.Iso B.sheaf C)
    (f : GradedSheaf.Hom B.sheaf C) (hb : Function.Bijective (f.vertex b).map)
    (x : V) : Function.Bijective (f.vertex x).map := by
  let g := j.invHom.comp f
  have hgb : Function.Bijective (g.vertex b).map := (j.vertex b).symm.bijective.comp hb
  have hg := hom_vertex_bijective hzero B B g hgb x
  constructor
  · intro v w h
    apply hg.1
    exact congrArg (j.vertex x).symm h
  · intro w
    obtain ⟨v,hv⟩ := hg.2 ((j.vertex x).symm w)
    exact ⟨v,(j.vertex x).symm.injective hv⟩

 def homIsoOfIso (j : GradedSheaf.Iso B.sheaf C) (hq : C.UpperQuotient α)
    (f : GradedSheaf.Hom B.sheaf C) (hb : Function.Bijective (f.vertex b).map) :
    GradedSheaf.Iso B.sheaf C :=
  f.isoOfBijective (hom_vertex_bijective_of_iso hzero B j f hb)
    (fun e => f.edge_bijective_of_vertex α B.quotient hq e
      (hom_vertex_bijective_of_iso hzero B j f hb _))

end
end KLInvariance.MomentGraph.BoundarySheaf

end


end OAI
end


