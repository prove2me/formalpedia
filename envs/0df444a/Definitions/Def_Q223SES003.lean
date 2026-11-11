-- Prove2me | Definitions.Def_Q223SES003
-- name    : Q223SES003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:44:41.431642+00:00
-- url     : https://prove2.me/theorems/06c81eb6-9035-4bbd-9632-c649b528b417
-- title:
--   Definitions bundle Q223SES003 of the split of OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 27 definitions, 11 instances and 10 theorems. The definitions and types are `OAI.MaximalSeshadri.PointCoordinates.affineCenter`, `OAI.MaximalSeshadri.Projective.gradedPolynomialEval`, `OAI.MaximalSeshadri.Projective.instDecidableEq_solutions`, `OAI.MaximalSeshadri.Projective.principalGlobalIdeal`, `OAI.MaximalSeshadri.Projective.projectiveCoordinateCover`, `OAI.MaximalSeshadri.Projective.shiftCoefficients`, `OAI.MaximalSeshadri.Projective.shiftedVariable`, `OAI.MaximalSeshadri.ProjectiveGeometry.genericPoint`, `OAI.MaximalSeshadri.QuadraticJets.exponent02`, `OAI.MaximalSeshadri.QuadraticJets.exponent11`, `OAI.MaximalSeshadri.QuadraticJets.exponent20`, `OAI.MaximalSeshadri.RationalPoint`, `OAI.MaximalSeshadri.SchemeConfiguration`, `OAI.MaximalSeshadri.collisionLocus`, `OAI.MaximalSeshadri.fieldPoint`, `OAI.MaximalSeshadri.nodeQuadrilateral`, `OAI.MaximalSeshadri.nonemptyAffineCover`, `OAI.MaximalSeshadri.overLeftIso`, `OAI.MaximalSeshadri.overPowerZeroIso`, `OAI.MaximalSeshadri.pairDiagonal`, `OAI.MaximalSeshadri.pairProjection`, `OAI.MaximalSeshadri.powerSuccIso`, `OAI.MaximalSeshadri.rationalImage`, `OAI.MaximalSeshadri.rationalTupleImage`, `OAI.MaximalSeshadri.tensorSpecialize`, `OAI.circleMeasurableSpace`, `OAI.starSubalgebraCommCStarAlgebra`.
--
--   **Sources.** They come from these modules of lean/OAI/AlgebraicGeometry, in whole or in part: [`Seshadri_Bertini_Derivations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Bertini/Derivations.lean), [`Seshadri_Blowup_BlowupIntegral`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupIntegral.lean), [`Seshadri_Configurations_AffineCenter`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Configurations/AffineCenter.lean), [`Seshadri_Configurations_Configurations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Configurations/Configurations.lean), [`Seshadri_Configurations_SmoothRationalPoints`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Configurations/SmoothRationalPoints.lean), [`Seshadri_Divisors_CenteredSections`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/CenteredSections.lean), [`Seshadri_Divisors_PrincipalSectionIdeal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/PrincipalSectionIdeal.lean), [`Seshadri_Jets_QuadraticJets`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Jets/QuadraticJets.lean), [`Seshadri_Lattice_NodePolygon`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Lattice/NodePolygon.lean), [`Seshadri_Projective_ClosedEmbedding`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/ClosedEmbedding.lean), [`Seshadri_Projective_ProjectiveTranslate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/ProjectiveTranslate.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `Q223SES006`; the statements `OAI_MaximalSeshadri_Geometry_Surface_exists_all_section_quadrilateral_etale` and `OAI.MaximalSeshadri.Geometry.Surface.exists_all_section_quadrilateral_etale_s01`; the proofs of `OAI_MaximalSeshadri_BertiniIntegral_etale_generic_hyperplane_section` and `OAI.MaximalSeshadri.BertiniIntegral.etale_generic_hyperplane_section_s01`.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/AlgebraicGeometry at commit adc7f12

import Mathlib

section
-- module Solutions.Q223_SES.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_Derivations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MaximalSeshadri
noncomputable section
open scoped TensorProduct

variable {F A B : Type} [Field F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]

def tensorSpecialize (φ : A →ₐ[F] F) : A ⊗[F] B →ₐ[F] B :=
  (Algebra.TensorProduct.lid F B).toAlgHom.comp
    (Algebra.TensorProduct.map φ (AlgHom.id F B))

end
end MaximalSeshadri


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.ProjectiveGeometry
noncomputable section
open AlgebraicGeometry
universe u v
variable {A : Type u} {σ : Type v} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

def genericPoint [IsDomain A] [Nonempty (Proj 𝒜)] : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := ⊥
  isPrime := Ideal.isPrime_bot
  not_irrelevant_le h := by
    obtain ⟨x⟩ := ‹Nonempty (Proj 𝒜)›
    exact x.not_irrelevant_le (h.trans bot_le)

end
end MaximalSeshadri.ProjectiveGeometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Configurations_AffineCenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.PointCoordinates
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
variable {K : Type} [Field K] {X : Scheme} [IsAffine X]

def affineCenter (p : Γ(X, ⊤) →+* K) : X :=
  X.isoSpec.inv ⟨RingHom.ker p, RingHom.ker_isPrime p⟩

end
end MaximalSeshadri.PointCoordinates
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Configurations_SmoothRationalPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

def fieldPoint (F : Type) [Field F] : Spec (CommRingCat.of F) :=
  ⟨⊥, Ideal.isPrime_bot⟩

end
end MaximalSeshadri
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Configurations_Configurations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open scoped TensorProduct

variable {F : Type} [Field F] [IsAlgClosed F] [Uncountable F]

def nonemptyAffineCover (X : Scheme) : X.OpenCover where
  I₀ := { U : X.Opens // IsAffineOpen U ∧ Nonempty U }
  X i := Spec Γ(X, i.1)
  f i := i.2.1.fromSpec
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.Opens) from trivial)
    let i : { U : X.Opens // IsAffineOpen U ∧ Nonempty U } :=
      ⟨U, hU, ⟨⟨x, hxU⟩⟩⟩
    refine ⟨i, ?_⟩
    rw [hU.range_fromSpec]
    exact hxU

instance nonemptyAffineCover_nonempty (X : Scheme) (i : (nonemptyAffineCover X).I₀) :
    Nonempty ((nonemptyAffineCover X).X i) := by
  let : Nonempty i.1 := i.2.2
  exact Nonempty.map i.2.1.isoSpec.hom inferInstance

instance nonemptyAffineCover_integral (X : Scheme) [IsIntegral X]
    (i : (nonemptyAffineCover X).I₀) : IsIntegral ((nonemptyAffineCover X).X i) :=
  isIntegral_of_isOpenImmersion ((nonemptyAffineCover X).f i)

end
end MaximalSeshadri

namespace MaximalSeshadri
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

def powerSuccIso {C : Type*} [Category C] [HasFiniteProducts C] (X : C) (n : ℕ) :
    (∏ᶜ (fun _ : Fin (n + 1) => X)) ≅ X ⨯ (∏ᶜ (fun _ : Fin n => X)) where
  hom := prod.lift (Pi.π _ 0) (Pi.lift fun i => Pi.π _ i.succ)
  inv := Pi.lift (Fin.cases prod.fst (fun i => prod.snd ≫ Pi.π _ i))
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
      exact prod.lift_fst _ _
    · simp
      rw [← Category.assoc, prod.lift_snd]
      simp
  inv_hom_id := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst]
      simp
    · apply Pi.hom_ext
      intro i
      simp
      rw [← Category.assoc, prod.lift_snd]
      simp

def overPowerZeroIso {C : Type*} [Category C] [HasFiniteLimits C] {B : C}
    (X : Over B) : (∏ᶜ (fun _ : Fin 0 => X)) ≅ Over.mk (𝟙 B) where
  hom := Over.homMk (∏ᶜ (fun _ : Fin 0 => X)).hom
  inv := Pi.lift (fun i => i.elim0)
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    exact i.elim0
  inv_hom_id := Over.mkIdTerminal.hom_ext _ _

def overLeftIso {C : Type*} [Category C] {B : C} {X Y : Over B} (e : X ≅ Y) :
    X.left ≅ Y.left where
  hom := e.hom.left
  inv := e.inv.left
  hom_inv_id := by simp [← Over.comp_left]
  inv_hom_id := by simp [← Over.comp_left]

end
end MaximalSeshadri

namespace MaximalSeshadri
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable {F : Type} [Field F]

abbrev RationalPoint (X : Over (Spec (CommRingCat.of F))) :=
  Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ X

def rationalImage {X : Over (Spec (CommRingCat.of F))} (p : RationalPoint X) : X.left :=
  p.left (fieldPoint F)

def rationalTupleImage (X : Over (Spec (CommRingCat.of F))) (r : ℕ)
    (p : Fin r → RationalPoint X) : (∏ᶜ (fun _ : Fin r => X)).left :=
  (Pi.lift p).left (fieldPoint F)

def pairProjection (X : Over (Spec (CommRingCat.of F))) (r : ℕ) (i j : Fin r) :
    (∏ᶜ (fun _ : Fin r => X)).left ⟶ pullback X.hom X.hom :=
  pullback.lift (Pi.π (fun _ : Fin r => X) i).left
    (Pi.π (fun _ : Fin r => X) j).left ((Over.w _).trans (Over.w _).symm)

def pairDiagonal (X : Over (Spec (CommRingCat.of F))) (r : ℕ) (i j : Fin r) :
    Set (∏ᶜ (fun _ : Fin r => X)).left :=
  pairProjection X r i j ⁻¹' Set.range (pullback.diagonal X.hom)

def collisionLocus (X : Over (Spec (CommRingCat.of F))) (r : ℕ) :
    Set (∏ᶜ (fun _ : Fin r => X)).left :=
  ⋃ ij : {ij : Fin r × Fin r // ij.1 ≠ ij.2}, pairDiagonal X r ij.val.1 ij.val.2

def SchemeConfiguration (X : Over (Spec (CommRingCat.of F))) (r : ℕ) :=
  {p : Fin r → RationalPoint X // Function.Injective (fun i => rationalImage (p i))}

instance schemeConfigurationTopology (X : Over (Spec (CommRingCat.of F))) (r : ℕ) :
    TopologicalSpace (SchemeConfiguration X r) :=
  TopologicalSpace.induced (fun p => rationalTupleImage X r p.val) inferInstance

end
end MaximalSeshadri

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_ClosedEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry
open MvPolynomial HomogeneousLocalization
variable {K σ R : Type u} [CommRing K] [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma polynomial_irrelevant_le :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X (R := K) : σ → MvPolynomial σ K)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ idealOfVars σ K
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff]
  intro d hd
  change 1 ≤ d.sum fun _ v => v
  rw [Finsupp.sum, ← hp.degree_eq_sum_deg_support hd]
  exact hn

lemma projective_coordinate_cover :
    (⨆ i : σ, Proj.basicOpen (homogeneousSubmodule σ K) (X i)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _ polynomial_irrelevant_le

def projectiveCoordinateCover : (Proj (homogeneousSubmodule σ K)).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan _ (X (R := K))
    (m := fun _ => 1) (fun i => isHomogeneous_X K i) (fun _ => by decide)
    polynomial_irrelevant_le

end
end MaximalSeshadri.Projective


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_ProjectiveTranslate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                             
section

namespace MaximalSeshadri.Projective
noncomputable section
open MvPolynomial
variable {R A σ : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

lemma aeval_mem_grade (x : σ → A) (hx : ∀ i, x i ∈ 𝒜 1)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) :
    aeval x p ∈ 𝒜 d := by
  classical
  rw [p.as_sum]
  simp only [map_sum, aeval_monomial]
  apply sum_mem
  intro m hm
  have h := SetLike.prod_pow_mem_graded 𝒜 (fun _ : σ => (1 : ℕ)) x
    (F := m.support) m (fun i _ => hx i)
  simp only [smul_eq_mul, mul_one] at h
  rw [← hp.degree_eq_sum_deg_support hm] at h
  simpa only [Algebra.smul_def, Finsupp.prod] using (𝒜 d).smul_mem (p.coeff m) h

attribute [local instance] MvPolynomial.gradedAlgebra

def gradedPolynomialEval (x : σ → A) (hx : ∀ i, x i ∈ 𝒜 1) :
    homogeneousSubmodule σ R →+*ᵍ 𝒜 where
  toRingHom := (aeval x).toRingHom
  map_mem := fun hp => aeval_mem_grade 𝒜 x hx hp

end

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousIdeal MvPolynomial
universe u
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

def shiftedVariable (c : σ → K) : Option σ → MvPolynomial (Option σ) K
  | none => X none
  | some i => X (some i) + C (c i) * X none

end
end MaximalSeshadri.Projective

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_CenteredSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] [Fintype σ] {X : Scheme}
local instance instDecidableEq_solutions : DecidableEq σ := Classical.decEq σ

def shiftCoefficients (c : σ → K) : Option σ → (Option σ → K)
  | none => Pi.single none 1
  | some i => Pi.single (some i) 1 + Pi.single none (c i)

end
end MaximalSeshadri.Projective

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_PrincipalSectionIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                               
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

def principalGlobalIdeal (a : Γ(X, ⊤)) : X.IdealSheafData where
  ideal U := Ideal.span {X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op a}
  map_ideal_basicOpen U r := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    change (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op ≫
      X.presheaf.map (homOfLE (X.basicOpen_le r)).op) a = _
    rw [← CategoryTheory.Functor.map_comp]
    rfl

@[simp] lemma principalGlobalIdeal_top [IsAffine X] (a : Γ(X, ⊤)) :
    (principalGlobalIdeal a).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {a} := by
  change Ideal.span {X.presheaf.map (𝟙 _) a} = _
  rw [CategoryTheory.Functor.map_id]
  rfl

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_QuadraticJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.QuadraticJets
noncomputable section
open MvPolynomial MaximalSeshadri.Projective

variable {K A σ : Type} [Field K] [CommRing A] [Algebra K A] [Fintype σ]

def exponent20 : Fin 2 →₀ ℕ := Finsupp.single 0 2
def exponent11 : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1
def exponent02 : Fin 2 →₀ ℕ := Finsupp.single 1 2

lemma degree20 : exponent20.degree < 3 := by simp [exponent20]
lemma degree11 : exponent11.degree < 3 := by simp [exponent11]
lemma degree02 : exponent02.degree < 3 := by simp [exponent02]

end
end MaximalSeshadri.QuadraticJets

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Lattice_NodePolygon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri
noncomputable section
open scoped BigOperators

def nodeQuadrilateral (a b c : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {(0, 0), (a, 0), (c, c), (0, b)}

end
end MaximalSeshadri

end


end OAI
end


