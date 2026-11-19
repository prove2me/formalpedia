-- Prove2me | Definitions.Def_RPLib_S4_CDPack52
-- name    : RPLib_S4_CDPack52
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:32:51.602496+00:00
-- url     : https://prove2.me/theorems/0df87f3f-2fcb-4a2e-9ba6-2e78dbc06ace
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 52 of 71
-- statement:
--   Part 52 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_IsogDegA_Count`: S4-IsogDegA, file Count: a closed fibre of the right size (G2, part 2)
--   * `Def_RP_IsogDegA`: S4-IsogDegA: isogeny degree of an abelian variety (lemmas L24-L26 of S4_COREB_ROUTE.md §3)
--   * `Def_RP_IsogDegB_SepFF`: S4-IsogDegB, file SepFF: an injective differential makes the isogeny separable (Sep-4b)
--   * `Def_RP_IsogDegB_DomA`: S4-IsogDegB, file DomA: locally quasi-finite endomorphisms are dominant (O4, part 1)
--   * `Def_RP_IsogDegB_DomB`: S4-IsogDegB, file DomB: finite kernel ⇔ dominant ⇔ deg ≠ 0 (O4, part 2)
--   * `Def_RP_IsogDegB_Frob`: S4-IsogDegB, Frobenius-type endomorphisms (lemma L28 of S4_COREB_ROUTE.md §3)
--   * `Def_RP_JacSymB_Ker2`: S4-JacSymB, file E1: functions vanishing to high order along the fibre lie in `M^2`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack47
import Definitions.Def_RPLib_S4_CDPack25

/-!
# Curve-duality library package, part 52 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_IsogDegA_Count`: S4-IsogDegA, file Count: a closed fibre of the right size (G2, part 2)
* `Def_RP_IsogDegA`: S4-IsogDegA: isogeny degree of an abelian variety (lemmas L24-L26 of S4_COREB_ROUTE.md §3)
* `Def_RP_IsogDegB_SepFF`: S4-IsogDegB, file SepFF: an injective differential makes the isogeny separable (Sep-4b)
* `Def_RP_IsogDegB_DomA`: S4-IsogDegB, file DomA: locally quasi-finite endomorphisms are dominant (O4, part 1)
* `Def_RP_IsogDegB_DomB`: S4-IsogDegB, file DomB: finite kernel ⇔ dominant ⇔ deg ≠ 0 (O4, part 2)
* `Def_RP_IsogDegB_Frob`: S4-IsogDegB, Frobenius-type endomorphisms (lemma L28 of S4_COREB_ROUTE.md §3)
* `Def_RP_JacSymB_Ker2`: S4-JacSymB, file E1: functions vanishing to high order along the fibre lie in `M^2`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_IsogDegA_Count =====
section

/-!
# S4-IsogDegA, file Count: a closed fibre of the right size (G2, part 2)

For a dominant endomorphism `φ` of a proper integral group variety `A` over an algebraically
closed field, some closed point `y` has exactly `[K(A) : φ^* K(A)]_s` points in its fibre.
Proof: an affine open `V` (through the generic point) and `U = φ⁻¹ V` give a finite extension
`Γ(V) → Γ(U)` of domains with fraction field `K(A)` on both sides; O1 (prime form) gives `a ≠ 0`;
a closed point of the nonempty open `D(a)` (Jacobson) has the right number of primes over it,
and those are the fibre points (SpecFib).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Topology

namespace RamanujanPetersson.IsogDegA

/-- `f^*` on sections over `V` and on function fields agree. -/
theorem germ_ffMap_of_mem {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] (V : Y.Opens) (hη : genericPoint Y ∈ V)
    (hη' : genericPoint X ∈ f ⁻¹ᵁ V) :
    Y.presheaf.germ V (genericPoint Y) hη ≫ ffMap f =
      f.app V ≫ X.presheaf.germ (f ⁻¹ᵁ V) (genericPoint X) hη' := by
  rw [ffMap, ← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes, Scheme.Hom.germ_stalkMap]

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] (φ : A ⟶ A) [IsMonHom φ]
  [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left]

/-- **G2.** Some closed fibre of a dominant endomorphism has `sepdeg` points. -/
theorem exists_closed_card_fiber [IsDominant φ.left] :
    ∃ y : A.left, IsClosed ({y} : Set A.left) ∧ Finite (φ.left ⁻¹' {y}) ∧
      Nat.card (φ.left ⁻¹' {y}) = @Field.finSepDegree _ _ _ _ (ffAlgebra φ.left) := by
  have hfin : IsFinite φ.left := isFinite_left A φ
  obtain ⟨V, hV, hηV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := genericPoint A.left) (U := ⊤) trivial
  have hηU : genericPoint A.left ∈ φ.left ⁻¹ᵁ V := by
    show φ.left (genericPoint A.left) ∈ V
    rw [map_genericPoint]
    exact hηV
  haveI : Nonempty V := ⟨⟨_, hηV⟩⟩
  haveI : Nonempty (φ.left ⁻¹ᵁ V) := ⟨⟨_, hηU⟩⟩
  have hU : IsAffineOpen (φ.left ⁻¹ᵁ V) := hV.preimage φ.left
  letI : Algebra Γ(A.left, V) Γ(A.left, φ.left ⁻¹ᵁ V) := (φ.left.app V).hom.toAlgebra
  haveI : Module.Finite Γ(A.left, V) Γ(A.left, φ.left ⁻¹ᵁ V) := φ.left.finite_app V hV
  haveI := functionField_isFractionRing_of_isAffineOpen A.left V hV
  haveI := functionField_isFractionRing_of_isAffineOpen A.left _ hU
  have e : V ≤ A.hom ⁻¹ᵁ ⊤ := by simp
  letI : Algebra k Γ(A.left, V) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appLE ⊤ V e).hom.toAlgebra
  haveI : Algebra.FiniteType k Γ(A.left, V) := by
    change RingHom.FiniteType ((A.hom.appLE ⊤ V e).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    refine RingHom.FiniteType.comp ?_ (RingHom.FiniteType.of_surjective _
      fun x ↦ ⟨(Scheme.ΓSpecIso (.of k)).hom x, by simp⟩)
    exact HasRingHomProperty.appLE @LocallyOfFiniteType (f := A.hom) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ e
  obtain ⟨a, ha, hcount⟩ := card_primesOver_self (R := Γ(A.left, V))
    (B := Γ(A.left, φ.left ⁻¹ᵁ V)) (K := A.left.functionField) (ffAlgebra φ.left)
    (fun r ↦ congrArg (fun g ↦ g.hom r) (germ_ffMap_of_mem φ.left V hηV hηU)) k
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have hne : ((A.left.basicOpen a : A.left.Opens) : Set A.left).Nonempty :=
    (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 fun h0 ↦ ha ((basicOpen_eq_bot_iff a).1 h0)
  obtain ⟨y, hyO, hy⟩ := nonempty_inter_closedPoints hne (A.left.basicOpen a).isOpen.isLocallyClosed
  have hyV : y ∈ V := A.left.basicOpen_le a hyO
  have hm := hV.primeIdealOf_isMaximal_of_isClosed ⟨y, hyV⟩ hy
  have ham : a ∉ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal := by
    have h1 : hV.primeIdealOf ⟨y, hyV⟩ ∈ hV.fromSpec ⁻¹ᵁ A.left.basicOpen a := by
      show hV.fromSpec (hV.primeIdealOf ⟨y, hyV⟩) ∈ A.left.basicOpen a
      rw [hV.fromSpec_primeIdealOf]
      exact hyO
    rw [hV.fromSpec_preimage_basicOpen] at h1
    exact (PrimeSpectrum.mem_basicOpen _ _).1 h1
  obtain ⟨hF, hC⟩ := hcount _ hm ham
  let eq := fiberPrimesEquiv φ.left hV hU rfl y hyV
  exact ⟨y, hy, Finite.of_equiv _ eq.symm, (Nat.card_congr eq).trans hC⟩

end RamanujanPetersson.IsogDegA

end

-- ===== S4.Def_RP_IsogDegA =====
section

/-!
# S4-IsogDegA: isogeny degree of an abelian variety (lemmas L24-L26 of S4_COREB_ROUTE.md §3)

`A : Over (Spec k)` a proper integral group scheme over an algebraically closed field `k`
(an abelian variety), `φ : A ⟶ A` a homomorphism.
* L24: `degree φ = [K(A) : φ^* K(A)]` if `φ` is dominant, `0` otherwise; it is multiplicative;
  a dominant `φ` is finite and surjective.
* L25: `degree φ = sepdeg * insepdeg`, `insepdeg` a power of the exponential characteristic.
* L26: `sepdeg = #Ker φ (k)`, where `Ker φ (k) = {c : 𝟙_ ⟶ A // c ≫ φ = 1}`; every fibre over a
  closed point has `#Ker φ (k)` points (translations).
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Topology MonObj CartesianMonoidalCategory

namespace RamanujanPetersson.IsogDegA

/-- Over a closed point, the points of a locally quasi-finite morphism's fibre are closed. -/
theorem isClosed_of_mem_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (y : Y)
    (hy : IsClosed ({y} : Set Y)) (x : X) (hx : f x = y) : IsClosed ({x} : Set X) := by
  have hsub : closure ({x} : Set X) ⊆ f ⁻¹' {y} :=
    (hy.preimage f.continuous).closure_subset_iff.2 (by simpa using hx)
  refine closure_subset_iff_isClosed.1 fun z hz ↦ ?_
  exact ((f.isDiscrete_preimage_singleton y).eq_of_specializes
    (specializes_iff_mem_closure.2 hz) hx (hsub hz)).symm

section Variety

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- Translation by `a` on the points of `A`. -/
noncomputable def translEquiv (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : A.left ≃ A.left where
  toFun := (transl A a).left
  invFun := (transl A a⁻¹).left
  left_inv z := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, transl_comp_transl, _root_.mul_inv_cancel, transl_one]
    rfl
  right_inv z := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, transl_comp_transl, _root_.inv_mul_cancel, transl_one]
    rfl

variable (φ : A ⟶ A) [IsMonHom φ]

/-- The `k`-points of the kernel. -/
abbrev kerPts : Type u := {c : 𝟙_ (Over (Spec (.of k))) ⟶ A // c ≫ φ = 1}

variable [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left]

/-- `Ker φ (k)` is the fibre over the origin. -/
noncomputable def kerEquivFiber [IsDominant φ.left] : kerPts A φ ≃ (φ.left ⁻¹' {pt A 1}) := by
  have := isFinite_left A φ
  refine Equiv.ofBijective (fun c ↦ ⟨pt A c.1, by simp [← pt_comp, c.2]⟩) ⟨fun c₁ c₂ h ↦ ?_, ?_⟩
  · exact Subtype.ext (pt_injective A (congrArg Subtype.val h))
  · rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := exists_pt_eq A x (isClosed_of_mem_fiber φ.left _ (isClosed_pt A 1) x hx)
    refine ⟨⟨c, pt_injective A ?_⟩, rfl⟩
    rw [pt_comp]
    exact hx

/-- Translations identify all fibres over closed points. -/
noncomputable def fiberEquivFiber [IsDominant φ.left] (y : A.left) (hy : IsClosed ({y} : Set A.left)) :
    (φ.left ⁻¹' {pt A 1}) ≃ (φ.left ⁻¹' {y}) := by
  have := isFinite_left A φ
  have := surjective_of_isDominant A φ
  have hc := Classical.choose_spec (φ.left.surjective y)
  set x₀ := Classical.choose (φ.left.surjective y)
  have hc₀ := Classical.choose_spec (exists_pt_eq A x₀ (isClosed_of_mem_fiber φ.left y hy x₀ hc))
  set c₀ := Classical.choose (exists_pt_eq A x₀ (isClosed_of_mem_fiber φ.left y hy x₀ hc))
  have hcomm : ∀ z, φ.left (translEquiv A c₀ z) = translEquiv A (c₀ ≫ φ) (φ.left z) := fun z ↦ by
    show φ.left ((transl A c₀).left z) = (transl A (c₀ ≫ φ)).left (φ.left z)
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, transl_comp_hom, Over.comp_left,
      Scheme.Hom.comp_apply]
  have hy' : translEquiv A (c₀ ≫ φ) (pt A 1) = y := by
    change (transl A (c₀ ≫ φ)).left (pt A 1) = y
    rw [transl_pt, _root_.one_mul, pt_comp, hc₀, hc]
  refine Equiv.subtypeEquiv (translEquiv A c₀) fun z ↦ ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff, hcomm, ← hy']
  exact (translEquiv A (c₀ ≫ φ)).injective.eq_iff.symm

/-- **L26.** `#Ker φ (k) = [K(A) : φ^* K(A)]_s`, and every closed fibre has `#Ker φ (k)` points. -/
theorem card_kerPts [IsDominant φ.left] :
    Finite (kerPts A φ) ∧
      Nat.card (kerPts A φ) = @Field.finSepDegree _ _ _ _ (ffAlgebra φ.left) ∧
      ∀ y : A.left, IsClosed ({y} : Set A.left) →
        Nat.card (φ.left ⁻¹' {y}) = Nat.card (kerPts A φ) := by
  obtain ⟨y, hy, hF, hC⟩ := exists_closed_card_fiber A φ
  let e := (kerEquivFiber A φ).trans (fiberEquivFiber A φ y hy)
  exact ⟨Finite.of_equiv _ e.symm, (Nat.card_congr e).trans hC, fun y' hy' ↦
    (Nat.card_congr ((kerEquivFiber A φ).trans (fiberEquivFiber A φ y' hy'))).symm⟩

/-- **L24.** For dominant `φ`: `degree φ = [K(A) : φ^* K(A)]`, and `φ` is finite and surjective. -/
theorem isogDeg_L24 [IsDominant φ.left] :
    degree φ.left = @Module.finrank _ _ _ _ (ffAlgebra φ.left).toModule ∧
      IsFinite φ.left ∧ Function.Surjective φ.left := by
  have := surjective_of_isDominant A φ
  exact ⟨degree_of_isDominant _, isFinite_left A φ, φ.left.surjective⟩

omit [GrpObj A] [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom] in
/-- **L24** (convention): a non-dominant `φ` has degree `0`. -/
theorem isogDeg_L24_zero (h : ¬ IsDominant φ.left) : degree φ.left = 0 :=
  degree_of_not_isDominant _ h

/-- **L24** (multiplicativity, D1). -/
theorem isogDeg_L24_mul (ψ : A ⟶ A) [IsMonHom ψ] :
    degree (ψ ≫ φ).left = degree φ.left * degree ψ.left :=
  degree_comp_left' A ψ φ

omit [GrpObj A] [IsMonHom φ] [IsAlgClosed k] in
/-- **L25.** `degree φ = sepdeg * insepdeg`, `insepdeg` a power of the exponential characteristic. -/
theorem isogDeg_L25 [IsDominant φ.left] :
    degree φ.left = @Field.finSepDegree _ _ _ _ (ffAlgebra φ.left) *
        @Field.finInsepDegree _ _ _ _ (ffAlgebra φ.left) ∧
      ∃ n, @Field.finInsepDegree _ _ _ _ (ffAlgebra φ.left) = ringExpChar k ^ n := by
  have : ExpChar A.left.functionField (ringExpChar k) :=
    expChar_of_injective_ringHom (kMap A).injective _
  exact ⟨(degree_of_isDominant _).trans (degDom_eq_sep_mul_insep _),
    finInsepDegree_ffAlgebra_eq_pow φ.left (ringExpChar k) (ffMap_finite A φ)⟩

end Variety

end RamanujanPetersson.IsogDegA

end

-- ===== S4.Def_RP_IsogDegB_SepFF =====
section

/-!
# S4-IsogDegB, file SepFF: an injective differential makes the isogeny separable (Sep-4b)

`φ♯ : 𝒪_{A,φ e} → 𝒪_{A,e}` is formally unramified (file Sep). Composing with the localization
`𝒪_{A,e} → K(A)` and restricting scalars to `φ^* K(A)` makes `K(A) / φ^* K(A)` formally unramified,
hence separable. So `deg φ = [K(A) : φ^* K(A)]_s = #Ker φ(k)` (IsogDegA, L24 + L26).
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory IsLocalRing

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA

universe u

/-- The stalk-to-function-field maps intertwine `f.stalkMap x` and the function-field map. -/
theorem stalkSpec_ffMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X] [IrreducibleSpace Y]
    [IsDominant f] (x : X) :
    Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes (Set.mem_univ (f x))) ≫
        ffMap f =
      f.stalkMap x ≫ X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ x)) := by
  rw [ffMap, ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp,
    ← Scheme.Hom.stalkSpecializes_stalkMap]

section Abstract

variable {S R K L : Type*} [CommRing S] [CommRing R] [Field K] [Field L]
  [Algebra S R] [Algebra R L] [IsFractionRing R L] [hKL : Algebra K L]

/-- A formally unramified local map, localized at the generic point, gives a separable extension. -/
theorem isSeparable_of_square [Algebra.FormallyUnramified S R] [hfin : Module.Finite K L]
    (a : S →+* K) (hsq : (algebraMap R L).comp (algebraMap S R) = (algebraMap K L).comp a) :
    Algebra.IsSeparable K L := by
  let _ : Algebra S L := ((algebraMap K L).comp a).toAlgebra
  let _ : Algebra S K := a.toAlgebra
  have : IsScalarTower S K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower S R L :=
    IsScalarTower.of_algebraMap_eq fun s ↦ (RingHom.congr_fun hsq s).symm
  have : Algebra.FormallyUnramified R L :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors R)
  have : Algebra.FormallyUnramified S L := Algebra.FormallyUnramified.comp S R L
  have : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_restrictScalars S K L
  exact (Algebra.FormallyUnramified.iff_isSeparable K L).1 this

end Abstract

section Variety

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

/-- An injective differential makes `φ♯` formally unramified. -/
theorem formallyUnramified_of_injective (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    (hinj : Function.Injective (dφ φ)) :
    @Algebra.FormallyUnramified (A.left.presheaf.stalk (φ.left (pt A 1)))
      (A.left.presheaf.stalk (pt A 1)) _ _ (φ.left.stalkMap (pt A 1)).hom.toAlgebra := by
  let _ : Algebra (A.left.presheaf.stalk (φ.left (pt A 1))) (A.left.presheaf.stalk (pt A 1)) :=
    (φ.left.stalkMap (pt A 1)).hom.toAlgebra
  have : IsLocalHom (algebraMap (A.left.presheaf.stalk (φ.left (pt A 1)))
      (A.left.presheaf.stalk (pt A 1))) :=
    inferInstanceAs (IsLocalHom (φ.left.stalkMap (pt A 1)).hom)
  have : Algebra.EssFiniteType (A.left.presheaf.stalk (φ.left (pt A 1)))
      (A.left.presheaf.stalk (pt A 1)) := LocallyOfFiniteType.stalkMap φ.left (pt A 1)
  exact formallyUnramified_of_le (fun r ↦ exists_res_stalk φ r) (cotangent_le_of_injective φ hinj)

/-- **Sep-4b.** An injective differential makes `K(A) / φ^* K(A)` separable. -/
theorem isSeparable_of_injective (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    [IsIntegral A.left] [IsDominant φ.left] (hinj : Function.Injective (dφ φ)) :
    @Algebra.IsSeparable A.left.functionField A.left.functionField _ _ (ffAlgebra φ.left) := by
  let _ : Algebra (A.left.presheaf.stalk (φ.left (pt A 1))) (A.left.presheaf.stalk (pt A 1)) :=
    (φ.left.stalkMap (pt A 1)).hom.toAlgebra
  have := formallyUnramified_of_injective φ hinj
  exact isSeparable_of_square (hKL := ffAlgebra φ.left) (hfin := ffMap_finite A φ)
    (A.left.presheaf.stalkSpecializes
      ((genericPoint_spec A.left).specializes (Set.mem_univ (φ.left (pt A 1))))).hom
    (congrArg CommRingCat.Hom.hom (stalkSpec_ffMap φ.left (pt A 1))).symm

/-- An injective differential gives `deg φ = #Ker φ(k)`. -/
theorem degree_eq_card_of_injective (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    [IsIntegral A.left] [IsDominant φ.left] (hinj : Function.Injective (dφ φ)) :
    degree φ.left = Nat.card (kerPts A φ) := by
  have hsep := isSeparable_of_injective φ hinj
  letI := ffAlgebra φ.left
  rw [(isogDeg_L24 A φ).1, (card_kerPts A φ).2.1]
  exact (Field.finSepDegree_eq_finrank_of_isSeparable (F := A.left.functionField)
    (E := A.left.functionField)).symm

end Variety

end RamanujanPetersson.IsogDegB

end

-- ===== S4.Def_RP_IsogDegB_DomA =====
section

/-!
# S4-IsogDegB, file DomA: locally quasi-finite endomorphisms are dominant (O4, part 1)

For an endomorphism `f` of an irreducible scheme with Noetherian underlying space, the closures of
`f^n η` form a descending chain, so `f^n η = f^(n+1) η` for some `n`. Then `η ⤳ f η` lie in one
fibre of `f^n`; if `f` is locally quasi-finite that fibre is discrete, so `f η = η`.
Consequences: an injective differential gives a dominant, separable isogeny with `deg = #Ker`.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory
  TopologicalSpace

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA

universe u

section Iterate

variable {X : Scheme.{u}} (f : X ⟶ X)

/-- `f^n` as a morphism (`f^(n+1) = f ≫ f^n`). -/
noncomputable def iter : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => f ≫ iter n

theorem iter_succ_apply (n : ℕ) (x : X) : iter f (n + 1) x = iter f n (f x) :=
  Scheme.Hom.comp_apply f (iter f n) x

theorem lqf_iter [LocallyQuasiFinite f] : ∀ n, LocallyQuasiFinite (iter f n)
  | 0 => by show LocallyQuasiFinite (𝟙 X); infer_instance
  | n + 1 => by
    have := lqf_iter n
    show LocallyQuasiFinite (f ≫ iter f n); infer_instance

/-- **Dom-1.** A locally quasi-finite endomorphism of an irreducible scheme with Noetherian
underlying space is dominant. -/
theorem isDominant_of_lqf [IrreducibleSpace X] [NoetherianSpace X] [LocallyQuasiFinite f] :
    IsDominant f := by
  have hη : genericPoint X ⤳ f (genericPoint X) :=
    (genericPoint_spec X).specializes (Set.mem_univ _)
  have hx : ∀ n, iter f n (genericPoint X) ⤳ iter f (n + 1) (genericPoint X) := fun n ↦ by
    rw [iter_succ_apply]; exact hη.map (iter f n).continuous
  let U : ℕ →o Opens X :=
    ⟨fun n ↦ ⟨(closure {iter f n (genericPoint X)})ᶜ, isClosed_closure.isOpen_compl⟩,
      monotone_nat_of_le_succ fun n ↦ by
        show (closure {iter f n (genericPoint X)})ᶜ ⊆ (closure {iter f (n + 1) (genericPoint X)})ᶜ
        exact Set.compl_subset_compl.2 (specializes_iff_closure_subset.1 (hx n))⟩
  obtain ⟨n, hn⟩ := wellFoundedGT_iff_monotone_chain_condition.1 inferInstance U
  have hc : closure {iter f n (genericPoint X)} = closure {iter f (n + 1) (genericPoint X)} :=
    compl_injective (congrArg (fun V : Opens X ↦ (V : Set X)) (hn (n + 1) (Nat.le_succ n)))
  have he : iter f (n + 1) (genericPoint X) = iter f n (genericPoint X) :=
    ((specializes_iff_closure_subset.2 hc.le).antisymm (hx n)).eq
  rw [iter_succ_apply] at he
  have := lqf_iter f n
  exact isDominant_of_map_genericPoint f
    (((iter f n).isDiscrete_preimage_singleton (iter f n (genericPoint X))).eq_of_specializes
      hη rfl he).symm

end Iterate

section Variety

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

omit [GrpObj A] in
theorem noetherianSpace_left [IsProper A.hom] : NoetherianSpace A.left := by
  have := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsNoetherian A.left := { }
  infer_instance

/-- An isogeny quasi-finite at one point is dominant. -/
theorem isDominant_of_quasiFiniteAt (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    [IsIntegral A.left] (x₀ : A.left) (h₀ : φ.left.QuasiFiniteAt x₀) : IsDominant φ.left := by
  have := locallyQuasiFinite_of_quasiFiniteAt A φ x₀ h₀
  have := noetherianSpace_left (A := A)
  exact isDominant_of_lqf φ.left

/-- **L27 (separability criterion).** An injective differential makes `φ` a dominant isogeny
with `K(A) / φ^* K(A)` separable and `deg φ = #Ker φ(k)`. -/
theorem separable_of_injective (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    [IsIntegral A.left] (hinj : Function.Injective (dφ φ)) :
    ∃ _ : IsDominant φ.left,
      @Algebra.IsSeparable A.left.functionField A.left.functionField _ _ (ffAlgebra φ.left) ∧
      degree φ.left = Nat.card (kerPts A φ) := by
  have := isDominant_of_quasiFiniteAt φ (pt A 1) (quasiFiniteAt_of_injective φ hinj)
  exact ⟨this, isSeparable_of_injective φ hinj, degree_eq_card_of_injective φ hinj⟩

end Variety

end RamanujanPetersson.IsogDegB

end

-- ===== S4.Def_RP_IsogDegB_DomB =====
section

/-!
# S4-IsogDegB, file DomB: finite kernel ⇔ dominant ⇔ deg ≠ 0 (O4, part 2)

`Ker φ(k)` finite ⇒ the fibre `φ⁻¹{e}` is finite (it is closed, and in the Jacobson space `A` its
closed points, which are the kernel points, are dense) ⇒ `φ` is quasi-finite at `e`
(the fibre scheme is finite, hence discrete) ⇒ `φ` is dominant (DomA).
Conversely a dominant `φ` has a finite kernel (IsogDegA, L26), and `deg φ = 0` iff `φ` is not dominant.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory
  TopologicalSpace

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA

universe u

set_option backward.isDefEq.respectTransparency.types false in
/-- A finite fibre makes a morphism locally of finite type quasi-finite there (cf. Stacks 02UP). -/
theorem quasiFiniteAt_of_finite_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (hx : (f ⁻¹' {f x}).Finite) : f.QuasiFiniteAt x := by
  have : Finite (f ⁻¹' {f x}) := hx.to_subtype
  have : Finite (f.fiber (f x)) := (f.fiberHomeo (f x)).finite_iff.mpr ‹_›
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

/-- A closed set of a Jacobson space with finitely many closed points is finite. -/
theorem finite_of_closedPoints {X : Type*} [TopologicalSpace X] [JacobsonSpace X] {Z : Set X}
    (hZ : IsClosed Z) (h : (Z ∩ closedPoints X).Finite) : Z.Finite := by
  have hcl : IsClosed (Z ∩ closedPoints X) := by
    rw [← Set.biUnion_of_singleton (Z ∩ closedPoints X)]
    exact h.isClosed_biUnion fun x hx ↦ hx.2
  rw [← closure_inter_closedPoints hZ, hcl.closure_eq]
  exact h

theorem finrank_ne_zero_of_finite {K L : Type*} [Field K] [Field L] [hKL : Algebra K L]
    [hfin : Module.Finite K L] : Module.finrank K L ≠ 0 :=
  Module.finrank_pos.ne'

section Variety

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

/-- Finitely many kernel points ⇒ finite fibre over `e`. -/
theorem finite_fiber_of_finite_ker (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    (h : Finite (kerPts A φ)) : (φ.left ⁻¹' {pt A 1}).Finite := by
  have := LocallyOfFiniteType.jacobsonSpace A.hom
  refine finite_of_closedPoints (IsClosed.preimage φ.left.continuous (isClosed_pt A 1)) ?_
  refine (Set.finite_range (fun c : kerPts A φ ↦ pt A c.1)).subset ?_
  rintro z ⟨hz, hzc⟩
  obtain ⟨c, rfl⟩ := exists_pt_eq A z hzc
  refine ⟨⟨c, pt_injective A ?_⟩, rfl⟩
  rw [pt_comp]
  exact hz

/-- Finitely many kernel points ⇒ `φ` dominant. -/
theorem isDominant_of_finite_ker (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    [IsIntegral A.left] (h : Finite (kerPts A φ)) : IsDominant φ.left := by
  refine isDominant_of_quasiFiniteAt φ (pt A 1) (quasiFiniteAt_of_finite_fiber φ.left (pt A 1) ?_)
  rw [left_pt_one φ]
  exact finite_fiber_of_finite_ker φ h

/-- **Finite kernel ⇔ dominant.** -/
theorem isDominant_iff_finite_ker (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    [IsIntegral A.left] : IsDominant φ.left ↔ Finite (kerPts A φ) :=
  ⟨fun _ ↦ (card_kerPts A φ).1, isDominant_of_finite_ker φ⟩

/-- **deg φ = 0 ⇔ Ker φ(k) infinite** (the `deg_eq_zero_iff` field of `DegreeData`). -/
theorem degree_eq_zero_iff (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    [IsIntegral A.left] : degree φ.left = 0 ↔ Infinite (kerPts A φ) := by
  rw [← not_finite_iff_infinite, ← isDominant_iff_finite_ker φ]
  constructor
  · intro h0 hd
    rw [(isogDeg_L24 A φ).1] at h0
    exact finrank_ne_zero_of_finite (hKL := ffAlgebra φ.left) (hfin := ffMap_finite A φ) h0
  · exact isogDeg_L24_zero A φ

end Variety

end RamanujanPetersson.IsogDegB

end

-- ===== S4.Def_RP_IsogDegB_Frob =====
section

/-!
# S4-IsogDegB, Frobenius-type endomorphisms (lemma L28 of S4_COREB_ROUTE.md §3)

* If `π♯ : 𝒪_{A,e} → 𝒪_{A,e}` lands in the subring generated by `k` and the `p`-th powers
  (`CharP k p`), then `dπ = 1` (`dφ_eq_one_of_frob`): tangent vectors are pointed derivations, and
  these kill constants and `p`-th powers.
* For a commutative `A`, `polyEnd π F = F(π) = ∏ (π^∘n)^{F_n}` in the Hom-group; it is a
  homomorphism, `F ↦ F(π)` is additive, and `t ≫ π = 1` gives `t ≫ F(π) = t ^ F(0)`.
* Hence `dπ = 1` gives `d F(π) = F(0)`, and for `p ∤ F(0)` the map `F(π)` is a dominant separable
  isogeny with `deg F(π) = #Ker F(π)(k)` (`polyEnd_separable`).
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory IsLocalRing

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA Polynomial

universe u

section Kill

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

theorem kS_tvec (t : Tan A) :
    kS A ≫ tvec t = CommRingCat.ofHom (algebraMap k (DualNumber k)) := by
  apply Spec.map_injective
  rw [Spec.map_comp, ← fromSpecStalk_comp_hom, ← Category.assoc, tvec_spec, Over.w]
  rfl

/-- Tangent vectors vanish on the subring generated by `k` and the `p`-th powers. -/
theorem coeff_eq_zero_of_mem (p : ℕ) [CharP k p] (t : Tan A) {r : A.left.presheaf.stalk (pt A 1)}
    (hr : r ∈ Subring.closure (Set.range (kS A).hom ∪ Set.range (fun x ↦ x ^ p))) :
    coeff t r = 0 := by
  let P : Subring (A.left.presheaf.stalk (pt A 1)) :=
    { carrier := {x | coeff t x = 0}
      mul_mem' := fun {a b} (ha : ((tvec t).hom a).snd = 0) (hb : ((tvec t).hom b).snd = 0) ↦ by
        show ((tvec t).hom (a * b)).snd = 0
        rw [map_mul, TrivSqZeroExt.snd_mul, ha, hb, smul_zero, smul_zero, add_zero]
      one_mem' := by
        show ((tvec t).hom 1).snd = 0
        rw [map_one, TrivSqZeroExt.snd_one]
      add_mem' := fun {a b} (ha : ((tvec t).hom a).snd = 0) (hb : ((tvec t).hom b).snd = 0) ↦ by
        show ((tvec t).hom (a + b)).snd = 0
        rw [map_add, TrivSqZeroExt.snd_add, ha, hb, add_zero]
      zero_mem' := by
        show ((tvec t).hom 0).snd = 0
        rw [map_zero, TrivSqZeroExt.snd_zero]
      neg_mem' := fun {a} (ha : ((tvec t).hom a).snd = 0) ↦ by
        show ((tvec t).hom (-a)).snd = 0
        rw [map_neg, TrivSqZeroExt.snd_neg, ha, neg_zero] }
  refine (Subring.closure_le.2 ?_ : _ ≤ P) hr
  rintro _ (⟨c, rfl⟩ | ⟨x, rfl⟩)
  · show ((kS A ≫ tvec t).hom c).snd = 0
    rw [kS_tvec]
    exact TrivSqZeroExt.snd_inl _ _
  · show ((tvec t).hom (x ^ p)).snd = 0
    rw [map_pow, TrivSqZeroExt.snd_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

/-- **L28 (Frobenius kill).** If `π♯` maps `𝒪_{A,e}` into the subring generated by `k` and the
`p`-th powers, then `dπ = 1`. -/
theorem dφ_eq_one_of_frob (π : A ⟶ A) [IsMonHom π] (p : ℕ) [CharP k p]
    (hF : ∀ r, (sharp π).hom r ∈
      Subring.closure (Set.range (kS A).hom ∪ Set.range (fun x ↦ x ^ p))) :
    dφ π = 1 := by
  refine MonoidHom.ext fun t ↦ ?_
  rw [MonoidHom.one_apply, tan_eq_one_iff]
  intro r
  rw [coeff_dφ]
  exact coeff_eq_zero_of_mem p t (hF r)

/-- `π^∘n`. -/
noncomputable def piter (π : A ⟶ A) : ℕ → (A ⟶ A)
  | 0 => 𝟙 A
  | n + 1 => π ≫ piter π n

theorem isMonHom_piter (π : A ⟶ A) [IsMonHom π] (n : ℕ) : IsMonHom (piter π n) := by
  induction n with
  | zero => show IsMonHom (𝟙 A); infer_instance
  | succ n ih => show IsMonHom (π ≫ piter π n); infer_instance

instance (π : A ⟶ A) [IsMonHom π] (n : ℕ) : IsMonHom (piter π n) := isMonHom_piter π n

theorem comp_piter {X : Over (Spec (.of k))} (π : A ⟶ A) [IsMonHom π] (t : X ⟶ A)
    (ht : t ≫ π = 1) (n : ℕ) : t ≫ piter π (n + 1) = 1 := by
  show t ≫ π ≫ piter π n = 1
  rw [← Category.assoc, ht, MonObj.one_comp]

end Kill

section Poly

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]

theorem isMonHom_one : IsMonHom (1 : A ⟶ A) := by
  rw [Hom.one_def]; infer_instance

instance isMonHom_mul (φ ψ : A ⟶ A) [IsMonHom φ] [IsMonHom ψ] : IsMonHom (φ * ψ) := by
  rw [Hom.mul_def]; infer_instance

theorem isMonHom_zpow (φ : A ⟶ A) [IsMonHom φ] (n : ℤ) : IsMonHom (φ ^ n) := by
  have hpow : ∀ m : ℕ, IsMonHom (φ ^ m) := by
    intro m
    induction m with
    | zero => rw [pow_zero]; exact isMonHom_one
    | succ m ih => rw [pow_succ]; infer_instance
  cases n with
  | ofNat m => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact hpow m
  | negSucc m => rw [zpow_negSucc]; have := hpow (m + 1); infer_instance

/-- `F(π) = ∏ₙ (π^∘n)^{Fₙ}` in the commutative Hom-group (`+` on `End A` is `*` here). -/
noncomputable def polyEnd (π : A ⟶ A) (F : ℤ[X]) : A ⟶ A :=
  F.toFinsupp.coeff.prod fun n c ↦ piter π n ^ c

theorem isMonHom_polyEnd (π : A ⟶ A) [IsMonHom π] (F : ℤ[X]) : IsMonHom (polyEnd π F) := by
  unfold polyEnd Finsupp.prod
  refine Finset.prod_induction _ (fun f ↦ IsMonHom f) (fun a b ha hb ↦ ?_) isMonHom_one
    (fun n _ ↦ isMonHom_zpow _ _)
  have := ha; have := hb; infer_instance

instance (π : A ⟶ A) [IsMonHom π] (F : ℤ[X]) : IsMonHom (polyEnd π F) := isMonHom_polyEnd π F

theorem polyEnd_add (π : A ⟶ A) (F G : ℤ[X]) :
    polyEnd π (F + G) = polyEnd π F * polyEnd π G := by
  unfold polyEnd
  rw [Polynomial.toFinsupp_add, AddMonoidAlgebra.coeff_add]
  exact Finsupp.prod_add_index' (fun n ↦ zpow_zero _) (fun n a b ↦ zpow_add _ a b)

theorem polyEnd_monomial (π : A ⟶ A) (n : ℕ) (c : ℤ) :
    polyEnd π (monomial n c) = piter π n ^ c := by
  unfold polyEnd
  rw [Polynomial.toFinsupp_monomial, AddMonoidAlgebra.coeff_single]
  exact Finsupp.prod_single_index (zpow_zero _)

/-- `t ≫ π = 1` gives `t ≫ F(π) = t ^ F(0)`. -/
theorem comp_polyEnd {X : Over (Spec (.of k))} (π : A ⟶ A) [IsMonHom π] (t : X ⟶ A)
    (ht : t ≫ π = 1) (F : ℤ[X]) : t ≫ polyEnd π F = t ^ F.coeff 0 := by
  let P : (A ⟶ A) →* (X ⟶ A) := MonoidHom.mk' (fun g ↦ t ≫ g) (MonObj.comp_mul t)
  have e : t ≫ polyEnd π F = P (polyEnd π F) := rfl
  rw [e]
  unfold polyEnd Finsupp.prod
  rw [map_prod, Finset.prod_eq_single 0]
  · show t ≫ piter π 0 ^ F.toFinsupp.coeff 0 = _
    rw [GrpObj.comp_zpow, Polynomial.toFinsupp_apply]
    rfl
  · intro n _ hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
    show t ≫ piter π (m + 1) ^ F.toFinsupp.coeff (m + 1) = 1
    rw [GrpObj.comp_zpow, comp_piter π t ht, one_zpow]
  · intro h0
    rw [Finsupp.notMem_support_iff.1 h0]
    exact (congrArg P (zpow_zero (piter π 0))).trans (map_one P)

/-- **L28.** If `dπ = 1` then `d F(π) = F(0)`. -/
theorem dφ_polyEnd (π : A ⟶ A) [IsMonHom π] (hπ : dφ π = 1) (F : ℤ[X]) (t : Tan A) :
    dφ (polyEnd π F) t = t ^ F.coeff 0 := by
  apply Subtype.ext
  rw [dφ_val, SubgroupClass.coe_zpow]
  apply comp_polyEnd π t.1
  have h := congrArg Subtype.val (DFunLike.congr_fun hπ t)
  rwa [dφ_val, MonoidHom.one_apply, OneMemClass.coe_one] at h

theorem coeff_dφ_polyEnd (π : A ⟶ A) [IsMonHom π] (hπ : dφ π = 1) (F : ℤ[X]) (t : Tan A)
    (r : A.left.presheaf.stalk (pt A 1)) :
    coeff (dφ (polyEnd π F) t) r = (F.coeff 0 : k) * coeff t r := by
  rw [dφ_polyEnd π hπ, coeff_zpow]

theorem dφ_polyEnd_injective (π : A ⟶ A) [IsMonHom π] (hπ : dφ π = 1) (p : ℕ) [CharP k p]
    (F : ℤ[X]) (hp : ¬ (p : ℤ) ∣ F.coeff 0) : Function.Injective (dφ (polyEnd π F)) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  rw [tan_eq_one_iff] at ht ⊢
  intro r
  have h := ht r
  rw [coeff_dφ_polyEnd π hπ] at h
  have hc : (F.coeff 0 : k) ≠ 0 := fun h0 ↦ hp ((CharP.intCast_eq_zero_iff k p _).1 h0)
  exact (mul_eq_zero.1 h).resolve_left hc

/-- **L28.** If `dπ = 1` and `p ∤ F(0)`, then `F(π)` is dominant and separable with
`deg F(π) = #Ker F(π)(k)`. -/
theorem polyEnd_separable (π : A ⟶ A) [IsMonHom π] (hπ : dφ π = 1) (p : ℕ) [CharP k p]
    [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left] (F : ℤ[X])
    (hp : ¬ (p : ℤ) ∣ F.coeff 0) :
    ∃ _ : IsDominant (polyEnd π F).left,
      @Algebra.IsSeparable A.left.functionField A.left.functionField _ _
        (ffAlgebra (polyEnd π F).left) ∧
      degree (polyEnd π F).left = Nat.card (kerPts A (polyEnd π F)) :=
  separable_of_injective _ (dφ_polyEnd_injective π hπ p F hp)

theorem degree_polyEnd (π : A ⟶ A) [IsMonHom π] (hπ : dφ π = 1) (p : ℕ) [CharP k p]
    [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left] (F : ℤ[X])
    (hp : ¬ (p : ℤ) ∣ F.coeff 0) :
    degree (polyEnd π F).left = Nat.card (kerPts A (polyEnd π F)) := by
  obtain ⟨_, _, h⟩ := polyEnd_separable π hπ p F hp
  exact h

end Poly

end RamanujanPetersson.IsogDegB

end

-- ===== S4.Def_RP_JacSymB_Ker2 =====
section

/-!
# S4-JacSymB, file E1: functions vanishing to high order along the fibre lie in `M^2`

For a `k`-point `symPt a` of `Sym^g X` with maximal ideal `M`, and `K_n = ⋂_{ψ ∈ a} (ker ψ)^n`, the kernel of
`Sym^g B → Sym^g (B / K_n)` lies in `M^2` for `n` large (radical + Artin-Rees for the finite module `X^g`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section Ker2

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.FiniteType k B] {g : ℕ}

omit [IsDomain B] in
open scoped Classical in
/-- The coordinate copies of the ideal of the support lie in the radical of `M · X^g`. -/
theorem span_inc_le_radical (a : Fin g → (B →ₐ[k] k)) :
    Ideal.span (⋃ l : Fin g, inc l '' ((⨅ ψ ∈ Finset.univ.image a, RingHom.ker ψ : Ideal B) : Set B)) ≤
      (Ideal.map (algebraMap (SymRing k B g) (XPow k B g)) (RingHom.ker (symPt a))).radical := by
  classical
  rw [Ideal.radical_eq_sInf, le_sInf_iff]
  rintro Q ⟨hQ, hQp⟩
  have hc : Q.comap (algebraMap (SymRing k B g) (XPow k B g)) = RingHom.ker (symPt a) :=
    ((ker_isMaximal (symPt a)).eq_of_le (Ideal.comap_ne_top _ hQp.ne_top)
      (Ideal.map_le_iff_le_comap.1 hQ)).symm
  have hQm : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap Q (hc ▸ ker_isMaximal _)
  obtain ⟨ψ, hψ⟩ := exists_algHom_ker_eq (k := k) Q
  let b : Fin g → (B →ₐ[k] k) := fun l => ψ.comp (inc l)
  have hψb : ψ = ptOf b := algHom_ext_inc (fun l => (ptOf_inc b l).symm)
  have hsym : symPt b = symPt a := by
    apply algHom_eq_of_ker_eq
    rw [← hc]
    ext s
    rw [RingHom.mem_ker, Ideal.mem_comap, ← hψ, RingHom.mem_ker, hψb]
    rfl
  have hm := mset_eq_of_symPt_eq b a hsym
  rw [Ideal.span_le]
  intro t ht
  rw [Set.mem_iUnion] at ht
  obtain ⟨l, j, hj, rfl⟩ := ht
  have hbl : b l ∈ Finset.univ.image a := by
    have hmem : b l ∈ (mset b : Multiset (B →ₐ[k] k)) := by simp [mset_coe]
    rw [hm, mset_coe] at hmem
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  have hj' : j ∈ RingHom.ker (b l) := Submodule.mem_iInf _ |>.1 (Submodule.mem_iInf _ |>.1 hj (b l)) hbl
  rw [SetLike.mem_coe, ← hψ, RingHom.mem_ker]
  exact (RingHom.mem_ker).1 hj'

omit [IsAlgClosed k] [IsDomain B] in
/-- Artin-Rees for the finite `Sym^g`-module `X^g`: `Sym^g ∩ M^(c+2) X^g ⊆ M^2`. -/
theorem exists_artinRees (M : Ideal (SymRing k B g)) :
    ∃ c : ℕ, ∀ s : SymRing k B g,
      (s : XPow k B g) ∈ Ideal.map (algebraMap (SymRing k B g) (XPow k B g)) (M ^ (c + 2)) → s ∈ M ^ 2 := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul M
    (LinearMap.range (Algebra.linearMap (SymRing k B g) (XPow k B g)))
  refine ⟨c, fun s hs => ?_⟩
  have h1 : (s : XPow k B g) ∈ M ^ (c + 2) • (⊤ : Submodule (SymRing k B g) (XPow k B g)) ⊓
      LinearMap.range (Algebra.linearMap (SymRing k B g) (XPow k B g)) := by
    refine ⟨?_, ⟨s, rfl⟩⟩
    rw [Ideal.smul_top_eq_map]
    exact hs
  rw [hc (c + 2) (by omega), show c + 2 - c = 2 by omega] at h1
  have key : ∀ t ∈ M ^ 2 • (M ^ c • (⊤ : Submodule (SymRing k B g) (XPow k B g)) ⊓
      LinearMap.range (Algebra.linearMap (SymRing k B g) (XPow k B g))),
      ∃ s' ∈ M ^ 2, (s' : XPow k B g) = t := by
    intro t ht
    refine Submodule.smul_induction_on (p := fun t => ∃ s' ∈ M ^ 2, (s' : XPow k B g) = t) ht ?_ ?_
    · intro r hr n hn
      obtain ⟨s0, rfl⟩ := hn.2
      exact ⟨r * s0, Ideal.mul_mem_right _ _ hr, by simp [Algebra.smul_def]⟩
    · rintro x y ⟨s1, h1, rfl⟩ ⟨s2, h2, rfl⟩
      exact ⟨s1 + s2, add_mem h1 h2, by simp⟩
  obtain ⟨s', hs', he⟩ := key _ h1
  rwa [Subtype.val_injective he] at hs'

omit [IsDomain B] in
open scoped Classical in
/-- **Step (i).** Functions on `Sym^g X` vanishing on the `n`-th fibre neighbourhood lie in `M^2`, `n` large. -/
theorem exists_ker_symMap_le_sq (a : Fin g → (B →ₐ[k] k)) :
    ∃ n : ℕ, RingHom.ker (symMap (g := g)
      (Ideal.Quotient.mkₐ k (⨅ ψ ∈ Finset.univ.image a, RingHom.ker ψ ^ n))) ≤ RingHom.ker (symPt a) ^ 2 := by
  classical
  obtain ⟨r, hr⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (span_inc_le_radical a)
    (IsNoetherian.noetherian _)
  obtain ⟨c, hc⟩ := exists_artinRees (RingHom.ker (symPt a))
  refine ⟨r * (c + 2), fun s hs => hc s ?_⟩
  set K : Ideal B := ⨅ ψ ∈ Finset.univ.image a, RingHom.ker ψ ^ (r * (c + 2))
  have h1 : (s : XPow k B g) ∈ RingHom.ker (xMap (g := g) (Ideal.Quotient.mkₐ k K)) := by
    rw [RingHom.mem_ker] at hs ⊢
    exact congrArg Subtype.val hs
  have h2 := ker_xMap_le _ (Ideal.Quotient.mkₐ_surjective k K) h1
  have hK : RingHom.ker (Ideal.Quotient.mkₐ k K) = K := by
    ext x
    rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  rw [hK] at h2
  refine (?_ : Ideal.span (⋃ l : Fin g, inc l '' (K : Set B)) ≤ _) h2
  rw [Ideal.span_le]
  intro t ht
  rw [Set.mem_iUnion] at ht
  obtain ⟨l, j, hj, rfl⟩ := ht
  have hjJ := iInf_pow_le_pow_iInf (k := k) (Finset.univ.image a) (r * (c + 2)) hj
  have hmap : Ideal.map (inc (k := k) l) ((⨅ ψ ∈ Finset.univ.image a, RingHom.ker ψ) ^ (r * (c + 2))) ≤
      Ideal.span (⋃ l : Fin g, inc l '' ((⨅ ψ ∈ Finset.univ.image a, RingHom.ker ψ : Ideal B) : Set B)) ^
        (r * (c + 2)) := by
    rw [Ideal.map_pow]
    apply Ideal.pow_right_mono
    rw [Ideal.map_le_iff_le_comap]
    intro j' hj'
    exact Ideal.subset_span (Set.mem_iUnion.2 ⟨l, j', hj', rfl⟩)
  have h3 := hmap (Ideal.mem_map_of_mem _ hjJ)
  rw [pow_mul] at h3
  rw [SetLike.mem_coe, Ideal.map_pow]
  exact Ideal.pow_right_mono hr _ h3

end Ker2

end RamanujanPetersson.JacSym

end


