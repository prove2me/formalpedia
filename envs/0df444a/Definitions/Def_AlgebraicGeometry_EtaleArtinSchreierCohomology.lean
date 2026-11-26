-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleArtinSchreierCohomology
-- name    : AlgebraicGeometry_EtaleArtinSchreierCohomology
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T11:14:42.087845+00:00
-- url     : https://prove2.me/theorems/1812d6ac-3f92-5c1b-8170-58224cf99d74
-- title:
--   Cohomology of the Artin–Schreier sequence
-- statement:
--   Surjectivity of the Artin–Schreier difference on additive cohomology identifies constant cohomology with the kernel, compatibly with comparisons.
-- source:
--   Stacks Project, Lemma 59.63.6, https://stacks.math.columbia.edu/tag/0A3P.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Definitions.Def_AlgebraicGeometry_EtaleOpenCoefficientComparison
import Definitions.Def_AlgebraicGeometry_FrobeniusFixedBaseChange
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

noncomputable section

section

section

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace PhilipponArtinSchreierCohomology

universe u v w w'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

private theorem injective_cohomology_of_surjective_previous
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact) (q : ℕ)
    (h : ∀ n, Function.Surjective (Sheaf.H.map S.g n)) :
    Function.Injective (Sheaf.H.map S.f q) := by
  let Z := (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))
  cases q with
  | zero =>
    haveI := hS.mono_f
    exact Ext.postcomp_mk₀_injective_of_mono Z S.f
  | succ n =>
    rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
    intro x hx
    change Sheaf.H.map S.f (n + 1) x = 0 at hx
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Z hS x hx (n₀ := n) rfl
    obtain ⟨z, hz⟩ := h n y
    rw [← hy, ← hz]
    simp only [Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero,
      ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

private theorem map_sub_id {B : Sheaf J AddCommGrpCat.{w}} (F : B ⟶ B) (q : ℕ) (x : B.H q) :
    Sheaf.H.map (F - 𝟙 B) q x = Sheaf.H.map F q x - x := by
  apply eq_sub_of_add_eq
  calc
    Sheaf.H.map (F - 𝟙 B) q x + x =
        Sheaf.H.map (F - 𝟙 B) q x + Sheaf.H.map (𝟙 B) q x := by rw [Sheaf.H.map_id_apply]
    _ = Sheaf.H.map F q x := by rw [← Sheaf.H.map_add_apply, sub_add_cancel]

/-- If the last map in a short exact sequence is surjective on cohomology,
the cohomology of the first sheaf is the kernel at the middle sheaf. -/
noncomputable def equivKernel_of_surjective
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact)
    (h : ∀ n, Function.Surjective (Sheaf.H.map S.g n)) (q : ℕ) :
    S.X₁.H q ≃+ (Sheaf.H.map S.g q).ker := by
  let f := Sheaf.H.map S.f q
  let g := Sheaf.H.map S.g q
  let f' := f.codRestrict g.ker (fun x => by
    change Sheaf.H.map S.g q (Sheaf.H.map S.f q x) = 0
    rw [← Sheaf.H.map_comp_apply, S.zero]
    simp [Sheaf.H.map_apply])
  refine AddEquiv.ofBijective f' ⟨?_, ?_⟩
  · intro x y hxy
    exact injective_cohomology_of_surjective_previous S hS q h (congrArg Subtype.val hxy)
  · intro y
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₂ _ hS y.val y.property
    exact ⟨x, Subtype.ext hx⟩

/-- The kernel of the Artin–Schreier map on cohomology consists of the
Frobenius-fixed classes. -/
theorem mem_artinSchreierKernel_iff {B : Sheaf J AddCommGrpCat.{w}}
    (F : B ⟶ B) (q : ℕ) (x : B.H q) :
    x ∈ (Sheaf.H.map (F - 𝟙 B) q).ker ↔ Sheaf.H.map F q x = x := by
  change Sheaf.H.map (F - 𝟙 B) q x = 0 ↔ _
  rw [map_sub_id, sub_eq_zero]

/-- The Artin–Schreier map is surjective on finite-dimensional coherent
cohomology over a separably closed field. -/
theorem artinSchreier_surjective {K : Type*} [Field K] [IsSepClosed K]
    {p : ℕ} [CharP K p] {B : Sheaf J AddCommGrpCat.{w}} (F : B ⟶ B) (q : ℕ)
    [Module K (B.H q)] [Module.Finite K (B.H q)]
    (hF : ∀ (a : K) (x : B.H q), Sheaf.H.map F q (a • x) = a ^ p • Sheaf.H.map F q x) :
    Function.Surjective (Sheaf.H.map (F - 𝟙 B) q) := by
  simpa only [Function.Surjective, map_sub_id] using
    (PhilipponArtinSchreierLinear.surjective_sub_id (K := K) (p := p) (Sheaf.H.map F q) hF)

/-- The short exact Artin–Schreier sequence gives an injection on cohomology
into the fixed vectors whenever the higher cohomology of the additive sheaf
is finite-dimensional and its Frobenius satisfies the scalar rule. -/
theorem finite_of_shortExact
    {K : Type*} [Field K] [IsSepClosed K] {p : ℕ} [CharP K p]
    {A B : Sheaf J AddCommGrpCat.{w}} (f : A ⟶ B) (F : B ⟶ B)
    (hz : f ≫ (F - 𝟙 B) = 0)
    (hS : (ShortComplex.mk f (F - 𝟙 B) hz).ShortExact)
    (M : ∀ n : ℕ, Module K (B.H n))
    (hM : ∀ n : ℕ, @Module.Finite K (B.H n) _ _ (M n))
    (hF : ∀ (n : ℕ) (a : K) (x : B.H n),
      Sheaf.H.map F n ((M n).smul a x) = (M n).smul (a ^ p) (Sheaf.H.map F n x))
    (q : ℕ) : Finite (A.H q) := by
  have hsurj (n : ℕ) : Function.Surjective (Sheaf.H.map (F - 𝟙 B) n) := by
    letI := M n
    letI := hM n
    exact artinSchreier_surjective F n (hF n)
  have hinj : Function.Injective (Sheaf.H.map f q) :=
    injective_cohomology_of_surjective_previous _ hS q hsurj
  letI := M q
  letI := hM q
  letI := PhilipponArtinSchreierLinear.finite_fixed (K := K) (p := p) (Sheaf.H.map F q) (hF q)
  let lift (x : A.H q) : {b : B.H q // Sheaf.H.map F q b = b} :=
    ⟨Sheaf.H.map f q x, by
      apply sub_eq_zero.mp
      rw [← map_sub_id, ← Sheaf.H.map_comp_apply, hz]
      simp [Sheaf.H.map_apply]⟩
  exact Finite.of_injective lift (fun x y h => hinj (congrArg Subtype.val h))

end PhilipponArtinSchreierCohomology

end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtalePrimeTorsionComparison (restrict)
open PhilipponEtaleSmallSite (pullbackSheaves)
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PhilipponArtinSchreierBaseChange
universe u
private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
/-- When both last maps are surjective on cohomology, comparison for the
first coefficient sheaf follows from comparison on the cohomology kernels. -/
theorem restrict_bijective_of_kernel_comparison {X Y : Scheme.{u}} (a : Y ⟶ X)
    (S : ShortComplex (Ab X)) (T : ShortComplex (Ab Y))
    (hS : S.ShortExact) (hT : T.ShortExact)
    (m : S.map (pullbackSheaves a) ⟶ T) [IsIso m.τ₁]
    (h₁ : ∀ n, Function.Surjective (Sheaf.H.map S.g n))
    (h₂ : ∀ n, Function.Surjective (Sheaf.H.map T.g n)) (q : ℕ)
    (h : Set.BijOn (fun x => Sheaf.H.map m.τ₂ q (restrict a S.X₂ q x))
      ((Sheaf.H.map S.g q).ker : Set (S.X₂.H q))
      ((Sheaf.H.map T.g q).ker : Set (T.X₂.H q))) :
    Function.Bijective (restrict a S.X₁ q) := by
  let eS := PhilipponArtinSchreierCohomology.equivKernel_of_surjective S hS h₁ q
  let eT := PhilipponArtinSchreierCohomology.equivKernel_of_surjective T hT h₂ q
  let k := Equiv.ofBijective _ h.bijective
  let e := eS.toEquiv.trans (k.trans eT.toEquiv.symm)
  let i := (Sheaf.functorH Y.smallEtaleTopology q).mapIso (asIso m.τ₁)
  have eq : (fun x => i.hom (restrict a S.X₁ q x)) = e := by
    funext x
    apply eT.injective
    have he : eT (e x) = k (eS x) := eT.toEquiv.apply_symm_apply _
    rw [he]
    apply Subtype.ext
    change Sheaf.H.map T.f q (Sheaf.H.map m.τ₁ q (restrict a S.X₁ q x)) =
      Sheaf.H.map m.τ₂ q (restrict a S.X₂ q (Sheaf.H.map S.f q x))
    have naturality : restrict a S.X₂ q (Sheaf.H.map S.f q x) =
        Sheaf.H.map ((pullbackSheaves a).map S.f) q (restrict a S.X₁ q x) :=
      PhilipponExtComparison.comparison_post (pullbackSheaves a) _ S.f q x
    rw [naturality]
    let R := S.map (pullbackSheaves a)
    let y : R.X₁.H q := restrict a S.X₁ q x
    change Sheaf.H.map T.f q (Sheaf.H.map m.τ₁ q y) =
      Sheaf.H.map m.τ₂ q (Sheaf.H.map R.f q y)
    exact (Sheaf.H.map_comp_apply m.τ₁ T.f y).symm.trans
      ((congrArg (fun f => Sheaf.H.map f q y) m.comm₁₂).trans
        (Sheaf.H.map_comp_apply R.f m.τ₂ y))
  apply (ConcreteCategory.bijective_of_isIso i.hom).of_comp_iff' _ |>.mp
  change Function.Bijective (fun x => i.hom (restrict a S.X₁ q x))
  rw [eq]
  exact e.bijective

end PhilipponArtinSchreierBaseChange

end

end


