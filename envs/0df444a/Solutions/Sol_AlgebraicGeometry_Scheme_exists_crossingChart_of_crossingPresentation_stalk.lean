-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_crossingChart_of_crossingPresentation_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/80960c1f-3b04-5744-84ce-78b605b1c9bb

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Theorems.Thm_Algebra_IsUnramifiedAt_isEtaleAt_of_ringKrullDim_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_crossingChart_of_crossingPresentation_stalk

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TopologicalSpace

universe u

noncomputable section

namespace BGeom

variable {O : Type u} [CommRing O] {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of O))

def toΓ : O →+* Γ(X, ⊤) := πX.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom

def toΓU (U : X.Opens) : O →+* Γ(X, U) := (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp (toΓ πX)

theorem toΓU_apply (U : X.Opens) (o : O) :
    toΓU πX U o = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o)) := rfl

theorem germ_toΓU (U : X.Opens) (x : X) (hxU : x ∈ U) (o : O) :
    X.presheaf.germ U x hxU (toΓU πX U o) =
      X.presheaf.germ ⊤ x trivial (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o)) := by
  rw [toΓU_apply, TopCat.Presheaf.germ_res_apply]

theorem map_toΓU {U V : X.Opens} (i : V ≤ U) (o : O) :
    X.presheaf.map (homOfLE i).op (toΓU πX U o) = toΓU πX V o := by
  rw [toΓU_apply, toΓU_apply, ← CommRingCat.comp_apply, ← X.presheaf.map_comp]; rfl

theorem exists_representatives (x : X) (s : O) (g h : X.presheaf.stalk x)
    (hrel : g * h = X.presheaf.germ ⊤ x trivial (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv s))) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (gU hU : Γ(X, U)),
      X.presheaf.germ U x hxU gU = g ∧ X.presheaf.germ U x hxU hU = h ∧ gU * hU = toΓU πX U s := by
  obtain ⟨U₁, hx₁, g₁, hg₁⟩ := X.presheaf.germ_exist (x := x) g
  obtain ⟨U₂, hx₂, h₂, hh₂⟩ := X.presheaf.germ_exist (x := x) h
  let U₀ : X.Opens := U₁ ⊓ U₂
  have hx₀ : x ∈ U₀ := ⟨hx₁, hx₂⟩
  let g₀ : Γ(X, U₀) := X.presheaf.map (homOfLE (inf_le_left : U₀ ≤ U₁)).op g₁
  let h₀ : Γ(X, U₀) := X.presheaf.map (homOfLE (inf_le_right : U₀ ≤ U₂)).op h₂
  have hg₀ : X.presheaf.germ U₀ x hx₀ g₀ = g := by rw [TopCat.Presheaf.germ_res_apply]; exact hg₁
  have hh₀ : X.presheaf.germ U₀ x hx₀ h₀ = h := by rw [TopCat.Presheaf.germ_res_apply]; exact hh₂
  have hgerm : X.presheaf.germ U₀ x hx₀ (g₀ * h₀) = X.presheaf.germ U₀ x hx₀ (toΓU πX U₀ s) := by
    rw [map_mul, hg₀, hh₀, germ_toΓU, hrel]
  obtain ⟨W, hxW, iU, iV, hW⟩ := X.presheaf.germ_eq x hx₀ hx₀ _ _ hgerm
  have hWU : W ≤ U₀ := iU.le
  obtain rfl : iU = homOfLE hWU := Subsingleton.elim _ _
  obtain rfl : iV = homOfLE hWU := Subsingleton.elim _ _
  refine ⟨W, hxW, X.presheaf.map (homOfLE hWU).op g₀, X.presheaf.map (homOfLE hWU).op h₀, ?_, ?_, ?_⟩
  · rw [TopCat.Presheaf.germ_res_apply]; exact hg₀
  · rw [TopCat.Presheaf.germ_res_apply]; exact hh₀
  · simp only [map_mul] at hW
    rw [hW, map_toΓU]

section chart

variable (U : X.Opens) (s : O) (a b : Γ(X, U)) (hab : a * b = toΓU πX U s)

def chartRingHom : CrossingQuotient O s →+* Γ(X, U) :=
  letI : Algebra O Γ(X, U) := (toΓU πX U).toAlgebra
  (CrossingQuotient.lift s a b (by rw [hab]; rfl)).toRingHom

include hab in
theorem chartRingHom_U : chartRingHom πX U s a b hab (CrossingQuotient.U s) = a := by
  letI : Algebra O Γ(X, U) := (toΓU πX U).toAlgebra
  change (CrossingQuotient.lift s a b _) (CrossingQuotient.U s) = a
  exact CrossingQuotient.lift_U s a b _

include hab in
theorem chartRingHom_V : chartRingHom πX U s a b hab (CrossingQuotient.V s) = b := by
  letI : Algebra O Γ(X, U) := (toΓU πX U).toAlgebra
  change (CrossingQuotient.lift s a b _) (CrossingQuotient.V s) = b
  exact CrossingQuotient.lift_V s a b _

include hab in
theorem chartRingHom_algebraMap (o : O) : chartRingHom πX U s a b hab (algebraMap O _ o) = toΓU πX U o := by
  letI : Algebra O Γ(X, U) := (toΓU πX U).toAlgebra
  change (CrossingQuotient.lift s a b _) (algebraMap O _ o) = algebraMap O Γ(X, U) o
  exact AlgHom.commutes _ o

def chartHomTop : CommRingCat.of (CrossingQuotient O s) ⟶ Γ((U : Scheme.{u}), ⊤) :=
  CommRingCat.ofHom (chartRingHom πX U s a b hab) ≫ U.topIso.inv

def chart : (U : Scheme.{u}) ⟶ CrossingQuotient.crossingScheme s :=
  (U : Scheme.{u}).toSpecΓ ≫ Spec.map (chartHomTop πX U s a b hab)

theorem topIso_inv_map_le_top (t : Γ(X, ⊤)) :
    U.topIso.inv (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t) = U.ι.appTop t := by
  rw [Scheme.Opens.topIso, Scheme.Opens.ι_appTop]
  change (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ (X.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).inv) t = _
  rw [Functor.mapIso_inv, ← Functor.map_comp]
  congr 2

theorem chart_over : chart πX U s a b hab ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O s))) = U.ι ≫ πX := by
  have hq : U.ι ≫ πX = (U : Scheme.{u}).toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ (U.ι ≫ πX).appTop) := by
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, ← SpecMap_ΓSpecIso_hom,
      ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  rw [hq, chart, Category.assoc, ← Spec.map_comp]
  congr 2
  ext o
  change U.topIso.inv (chartRingHom πX U s a b hab (algebraMap O _ o)) = (U.ι ≫ πX).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o)
  rw [chartRingHom_algebraMap, toΓU_apply, topIso_inv_map_le_top, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

theorem mem_asIdeal_chart_iff (c : CrossingQuotient O s) (y : ↥(U : Scheme.{u})) :
    c ∈ ((chart πX U s a b hab).base y).asIdeal ↔ U.ι.base y ∉ X.basicOpen (chartRingHom πX U s a b hab c) := by
  have h1 : c ∈ ((chart πX U s a b hab).base y).asIdeal ↔
      chartHomTop πX U s a b hab c ∈ (((U : Scheme.{u}).toSpecΓ).base y).asIdeal := Iff.rfl
  rw [h1]
  have h2 : chartHomTop πX U s a b hab c ∈ (((U : Scheme.{u}).toSpecΓ).base y).asIdeal ↔
      y ∉ (U : Scheme.{u}).toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (chartHomTop πX U s a b hab c) := by
    change _ ↔ ¬ (chartHomTop πX U s a b hab c ∉ (((U : Scheme.{u}).toSpecΓ).base y).asIdeal)
    rw [not_not]
  rw [h2, Scheme.toSpecΓ_preimage_basicOpen]
  have h3 : X.basicOpen (chartRingHom πX U s a b hab c) = U.ι ''ᵁ (U : Scheme.{u}).basicOpen (chartHomTop πX U s a b hab c) := by
    rw [chartHomTop, CommRingCat.comp_apply, Scheme.Opens.ι_image_basicOpen_topIso_inv]; rfl
  rw [h3]
  constructor
  · rintro hy ⟨y', hy', hyy'⟩
    exact hy (U.ι.isOpenEmbedding.injective hyy' ▸ hy')
  · intro hy hy'
    exact hy ⟨y, hy', rfl⟩

theorem U_mem_asIdeal_chart_iff (y : ↥(U : Scheme.{u})) :
    CrossingQuotient.U s ∈ ((chart πX U s a b hab).base y).asIdeal ↔ U.ι.base y ∉ X.basicOpen a := by
  rw [mem_asIdeal_chart_iff, chartRingHom_U]

theorem V_mem_asIdeal_chart_iff (y : ↥(U : Scheme.{u})) :
    CrossingQuotient.V s ∈ ((chart πX U s a b hab).base y).asIdeal ↔ U.ι.base y ∉ X.basicOpen b := by
  rw [mem_asIdeal_chart_iff, chartRingHom_V]

end chart

section isolate

theorem exists_notMem_and_forall_eq_of_map_eq_maximalIdeal {A : Type*} [CommRing A] [IsNoetherianRing A]
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalRing S] (𝔭 : Ideal A) [𝔭.IsMaximal] [IsLocalization.AtPrime S 𝔭]
    (I : Ideal A) (hloc : I.map (algebraMap A S) = IsLocalRing.maximalIdeal S) :
    ∃ f : A, f ∉ 𝔭 ∧ ∀ 𝔮 : Ideal A, 𝔮.IsPrime → I ≤ 𝔮 → f ∉ 𝔮 → 𝔮 = 𝔭 := by

  have key : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ 𝔭 → 𝔮 = 𝔭 := by
    intro 𝔮 h𝔮 hI𝔮 h𝔮𝔭
    have hdisj : Disjoint (𝔭.primeCompl : Set A) (𝔮 : Set A) := by
      rw [Set.disjoint_left]; intro a ha ha'; exact ha (h𝔮𝔭 ha')
    have hprime : (𝔮.map (algebraMap A S)).IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔭.primeCompl S 𝔮 h𝔮 hdisj
    have hle : IsLocalRing.maximalIdeal S ≤ 𝔮.map (algebraMap A S) := hloc ▸ Ideal.map_mono hI𝔮
    have heq : 𝔮.map (algebraMap A S) = IsLocalRing.maximalIdeal S :=
      ((IsLocalRing.maximalIdeal.isMaximal S).eq_of_le hprime.ne_top hle).symm
    have h1 : 𝔮 = (𝔮.map (algebraMap A S)).under A :=
      (IsLocalization.under_map_of_isPrime_disjoint 𝔭.primeCompl S h𝔮 hdisj).symm
    rw [h1, heq, IsLocalization.AtPrime.under_maximalIdeal S 𝔭]

  have hfin : (I.minimalPrimes).Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing A I
  have hpick : ∀ P ∈ hfin.toFinset.filter (· ≠ 𝔭), ∃ a : A, a ∈ P ∧ a ∉ 𝔭 := by
    intro P hP
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hP
    by_contra hall
    push Not at hall
    exact hP.2 (key P hP.1.1.1 hP.1.1.2 hall)
  classical
  choose! a ha using hpick
  refine ⟨∏ P ∈ hfin.toFinset.filter (· ≠ 𝔭), a P, ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨P, hP, haP⟩
    exact (ha P hP).2 haP
  · intro 𝔮 h𝔮 hI𝔮 hf
    obtain ⟨P, hPmin, hP𝔮⟩ := Ideal.exists_minimalPrimes_le hI𝔮
    by_cases hP : P = 𝔭
    · subst hP
      exact (Ideal.IsMaximal.eq_of_le inferInstance h𝔮.ne_top hP𝔮).symm
    · exfalso
      apply hf
      have hmem : P ∈ hfin.toFinset.filter (· ≠ 𝔭) := by
        rw [Finset.mem_filter, Set.Finite.mem_toFinset]; exact ⟨hPmin, hP⟩
      exact Ideal.IsPrime.prod_mem_iff.mpr ⟨P, hmem, hP𝔮 (ha P hmem).1⟩

variable {πX}

theorem mem_primeIdealOf_asIdeal_iff {U : X.Opens} (hU : IsAffineOpen U) (x : U) (f : Γ(X, U)) :
    f ∈ (hU.primeIdealOf x).asIdeal ↔ (x : X) ∉ X.basicOpen f := by
  rw [hU.primeIdealOf_eq_map_closedPoint]
  change f ∈ Ideal.comap (X.presheaf.germ U x x.2).hom (IsLocalRing.closedPoint (X.presheaf.stalk x)).asIdeal ↔ _
  rw [Ideal.mem_comap]
  change X.presheaf.germ U x x.2 f ∈ IsLocalRing.maximalIdeal _ ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, X.mem_basicOpen f x x.2]

theorem exists_open_forall_eq_of_maximalIdeal_eq_span [IsLocallyNoetherian X] {U : X.Opens} {x : X} (hxU : x ∈ U)
    (hx : IsClosed ({x} : Set X)) (t₁ t₂ t₃ : Γ(X, U))
    (hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
      Ideal.span {X.presheaf.germ U x hxU t₁, X.presheaf.germ U x hxU t₂, X.presheaf.germ U x hxU t₃}) :
    ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧
      ∀ y : X, y ∈ V → y ∉ X.basicOpen t₁ → y ∉ X.basicOpen t₂ → y ∉ X.basicOpen t₃ → y = x := by

  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU'⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
  have hWU : W ≤ U := hWU'
  haveI : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let 𝔭 := hW.primeIdealOf ⟨x, hxW⟩
  haveI h𝔭max : 𝔭.asIdeal.IsMaximal := hW.primeIdealOf_isMaximal_of_isClosed ⟨x, hxW⟩ hx
  letI := X.presheaf.algebra_section_stalk (⟨x, hxW⟩ : W)
  haveI := hW.isLocalization_stalk ⟨x, hxW⟩
  let r : Γ(X, U) →+* Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom
  let I : Ideal Γ(X, W) := Ideal.span {r t₁, r t₂, r t₃}
  have halg : ∀ a : Γ(X, W), algebraMap Γ(X, W) (X.presheaf.stalk ((⟨x, hxW⟩ : W) : X)) a = X.presheaf.germ W x hxW a :=
    fun a => rfl
  have hloc : I.map (algebraMap Γ(X, W) (X.presheaf.stalk ((⟨x, hxW⟩ : W) : X))) = IsLocalRing.maximalIdeal _ := by
    rw [Ideal.map_span]
    change Ideal.span (_ '' {r t₁, r t₂, r t₃}) = IsLocalRing.maximalIdeal (X.presheaf.stalk x)
    rw [hmax, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, halg, halg, halg]
    change Ideal.span {X.presheaf.germ W x hxW (X.presheaf.map (homOfLE hWU).op t₁),
      X.presheaf.germ W x hxW (X.presheaf.map (homOfLE hWU).op t₂),
      X.presheaf.germ W x hxW (X.presheaf.map (homOfLE hWU).op t₃)} = _
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  obtain ⟨f, hf𝔭, hf⟩ := exists_notMem_and_forall_eq_of_map_eq_maximalIdeal (X.presheaf.stalk ((⟨x, hxW⟩ : W) : X))
    𝔭.asIdeal I hloc
  refine ⟨X.basicOpen f, ?_, (X.basicOpen_le f).trans hWU, ?_⟩
  · have := (mem_primeIdealOf_asIdeal_iff hW ⟨x, hxW⟩ f).not.mp hf𝔭
    simpa using this
  · intro y hyV hy₁ hy₂ hy₃
    have hyW : y ∈ W := X.basicOpen_le f hyV
    let 𝔮 := hW.primeIdealOf ⟨y, hyW⟩
    have hI𝔮 : I ≤ 𝔮.asIdeal := by
      rw [Ideal.span_le]
      have key : ∀ t : Γ(X, U), y ∉ X.basicOpen t → r t ∈ (𝔮.asIdeal : Set Γ(X, W)) := fun t ht => by
        rw [SetLike.mem_coe, mem_primeIdealOf_asIdeal_iff]
        change y ∉ X.basicOpen (X.presheaf.map (homOfLE hWU).op t)
        rw [Scheme.basicOpen_res]
        exact fun h => ht h.2
      rintro a (rfl | rfl | rfl)
      · exact key t₁ hy₁
      · exact key t₂ hy₂
      · exact key t₃ hy₃
    have hf𝔮 : f ∉ 𝔮.asIdeal := by
      rw [mem_primeIdealOf_asIdeal_iff]; exact not_not.mpr hyV
    have h𝔮𝔭 : 𝔮.asIdeal = 𝔭.asIdeal := hf 𝔮.asIdeal 𝔮.isPrime hI𝔮 hf𝔮
    have : 𝔮 = 𝔭 := PrimeSpectrum.ext h𝔮𝔭
    have hy := hW.fromSpec_primeIdealOf ⟨y, hyW⟩
    have hx' := hW.fromSpec_primeIdealOf ⟨x, hxW⟩
    change hW.fromSpec 𝔮 = y at hy
    change hW.fromSpec 𝔭 = x at hx'
    rw [← hy, ← hx', this]

end isolate

section atpoint

variable (U : X.Opens) (s : O) (a b : Γ(X, U)) (hab : a * b = toΓU πX U s)

theorem topIso_inv_eq : (U.topIso.inv : Γ(X, U) ⟶ Γ((U : Scheme.{u}), ⊤)) =
    X.presheaf.map (homOfLE (U.ι_image_top).le).op := by
  rw [Scheme.Opens.topIso, Functor.mapIso_inv]
  congr 1

theorem stalkIso_hom_germ_topIso_inv (y : ↥(U : Scheme.{u})) (t : Γ(X, U)) :
    (U.stalkIso y).hom ((U : Scheme.{u}).presheaf.germ ⊤ y trivial (U.topIso.inv t)) = X.presheaf.germ U y.1 y.2 t := by
  rw [← CommRingCat.comp_apply, Scheme.Opens.germ_stalkIso_hom, topIso_inv_eq]
  exact TopCat.Presheaf.germ_res_apply X.presheaf _ _ _ _

theorem chart_appTop (c : CrossingQuotient O s) :
    (chart πX U s a b hab).appTop ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O s))).inv c) =
      chartHomTop πX U s a b hab c := by
  rw [chart, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply _ ((Spec.map _).appTop),
    ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply, Scheme.toSpecΓ_appTop, ← CommRingCat.comp_apply,
    Iso.inv_hom_id]
  rfl

theorem stalkMap_chart_germ (y : ↥(U : Scheme.{u})) (c : CrossingQuotient O s) :
    (chart πX U s a b hab).stalkMap y
        ((CrossingQuotient.crossingScheme s).presheaf.germ ⊤ ((chart πX U s a b hab).base y) trivial
          ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O s))).inv c)) =
      (U : Scheme.{u}).presheaf.germ ⊤ y trivial (chartHomTop πX U s a b hab c) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  change (U : Scheme.{u}).presheaf.germ ⊤ y trivial ((chart πX U s a b hab).appTop _) = _
  rw [chart_appTop]

theorem stalkIso_stalkMap_chart_germ (y : ↥(U : Scheme.{u})) (c : CrossingQuotient O s) :
    (U.stalkIso y).hom ((chart πX U s a b hab).stalkMap y
        ((CrossingQuotient.crossingScheme s).presheaf.germ ⊤ ((chart πX U s a b hab).base y) trivial
          ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O s))).inv c))) =
      X.presheaf.germ U y.1 y.2 (chartRingHom πX U s a b hab c) := by
  rw [stalkMap_chart_germ, chartHomTop, CommRingCat.comp_apply, stalkIso_hom_germ_topIso_inv]; rfl

end atpoint

section atpoint2

variable (U : X.Opens) (s : O) (a b : Γ(X, U)) (hab : a * b = toΓU πX U s)

omit πX in

theorem map_maximalIdeal_of_iso {A B : CommRingCat.{u}} [IsLocalRing A] [IsLocalRing B] (e : A ≅ B) :
    (IsLocalRing.maximalIdeal A).map e.hom.hom = IsLocalRing.maximalIdeal B := by
  let e' : A ≃+* B := e.commRingCatIsoToRingEquiv
  have he : ∀ a, e.hom.hom a = e' a := fun a => rfl
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro z hz
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, he, MulEquiv.isUnit_map]
    exact hz
  · intro w hw
    have : w = e.hom.hom (e'.symm w) := by rw [he, RingEquiv.apply_symm_apply]
    rw [this]
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← MulEquiv.isUnit_map e', RingEquiv.apply_symm_apply]
    exact hw

theorem map_stalkMap_chart_maximalIdeal (ϖ : O) (y : ↥(U : Scheme.{u}))
    (hgen : IsLocalRing.maximalIdeal (X.presheaf.stalk y.1) =
      Ideal.span {X.presheaf.germ U y.1 y.2 (toΓU πX U ϖ), X.presheaf.germ U y.1 y.2 a, X.presheaf.germ U y.1 y.2 b}) :
    Ideal.map ((chart πX U s a b hab).stalkMap y).hom
        (IsLocalRing.maximalIdeal ((CrossingQuotient.crossingScheme s).presheaf.stalk ((chart πX U s a b hab).base y))) =
      IsLocalRing.maximalIdeal ((U : Scheme.{u}).presheaf.stalk y) := by
  set f := chart πX U s a b hab
  set p := f.base y
  letI : Algebra (CommRingCat.of (CrossingQuotient O s)) ((CrossingQuotient.crossingScheme s).presheaf.stalk p) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of (CrossingQuotient O s)) p
  haveI : IsLocalization.AtPrime ((CrossingQuotient.crossingScheme s).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (CrossingQuotient O s)) p
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal ((CrossingQuotient.crossingScheme s).presheaf.stalk p),
    Ideal.map_map]

  have hinj : Function.Injective (Ideal.map (U.stalkIso y).hom.hom) := by
    intro I J hIJ
    have := congrArg (Ideal.comap (U.stalkIso y).hom.hom) hIJ
    rwa [Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso (U.stalkIso y).hom),
      Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso (U.stalkIso y).hom)] at this
  apply hinj
  rw [map_maximalIdeal_of_iso, Ideal.map_map, hgen]

  have hcomp : ((U.stalkIso y).hom.hom.comp ((f.stalkMap y).hom.comp
      (algebraMap (CommRingCat.of (CrossingQuotient O s)) ((CrossingQuotient.crossingScheme s).presheaf.stalk p)))) =
      (X.presheaf.germ U y.1 y.2).hom.comp (chartRingHom πX U s a b hab) :=
    RingHom.ext fun c => stalkIso_stalkMap_chart_germ πX U s a b hab y c
  rw [hcomp, ← Ideal.map_map]

  have hmem : ∀ c : CrossingQuotient O s, c ∈ p.asIdeal ↔
      X.presheaf.germ U y.1 y.2 (chartRingHom πX U s a b hab c) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y.1) := by
    intro c
    rw [mem_asIdeal_chart_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    change y.1 ∉ X.basicOpen _ ↔ _
    rw [X.mem_basicOpen _ y.1 y.2]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, Ideal.mem_comap, ← hgen]
    exact (hmem c).mp hc
  · rw [Ideal.span_le]
    have h3 : ∀ c : CrossingQuotient O s, X.presheaf.germ U y.1 y.2 (chartRingHom πX U s a b hab c) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk y.1) →
        X.presheaf.germ U y.1 y.2 (chartRingHom πX U s a b hab c) ∈
          (((p.asIdeal.map (chartRingHom πX U s a b hab)).map (X.presheaf.germ U y.1 y.2).hom : Ideal _) : Set _) :=
      fun c hc => Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ((hmem c).mpr hc))
    rintro z (rfl | rfl | rfl)
    · have h := h3 (algebraMap O _ ϖ) (by rw [chartRingHom_algebraMap, hgen]; exact Ideal.subset_span (Or.inl rfl))
      rwa [chartRingHom_algebraMap] at h
    · have h := h3 (CrossingQuotient.U s) (by rw [chartRingHom_U, hgen]; exact Ideal.subset_span (Or.inr (Or.inl rfl)))
      rwa [chartRingHom_U] at h
    · have h := h3 (CrossingQuotient.V s) (by rw [chartRingHom_V, hgen]; exact Ideal.subset_span (Or.inr (Or.inr rfl)))
      rwa [chartRingHom_V] at h

end atpoint2

section atpoint3

variable (U : X.Opens) (s : O) (a b : Γ(X, U)) (hab : a * b = toΓU πX U s)

theorem isIso_residueFieldMap_chart (y : ↥(U : Scheme.{u}))
    (hsurj : Function.Surjective fun o : O =>
      IsLocalRing.residue (X.presheaf.stalk y.1) (X.presheaf.germ U y.1 y.2 (toΓU πX U o))) :
    IsIso ((chart πX U s a b hab).residueFieldMap y) := by
  set f := chart πX U s a b hab
  set p := f.base y

  have hsurjF : Function.Surjective (f.residueFieldMap y).hom := by
    intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨o, ho⟩ := hsurj (IsLocalRing.residue _ ((U.stalkIso y).hom w))

    let q : (U : Scheme.{u}).presheaf.stalk y := f.stalkMap y
      ((CrossingQuotient.crossingScheme s).presheaf.germ ⊤ p trivial
        ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O s))).inv (algebraMap O _ o)))
    have hq : (U.stalkIso y).hom q = X.presheaf.germ U y.1 y.2 (toΓU πX U o) := by
      rw [stalkIso_stalkMap_chart_germ, chartRingHom_algebraMap]
    have hwq : w - q ∈ IsLocalRing.maximalIdeal ((U : Scheme.{u}).presheaf.stalk y) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        ← MulEquiv.isUnit_map (U.stalkIso y).commRingCatIsoToRingEquiv]
      change ¬ IsUnit ((U.stalkIso y).hom (w - q))
      rw [map_sub, hq, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← Ideal.Quotient.eq]
      exact ho.symm
    refine ⟨IsLocalRing.residue _ ((CrossingQuotient.crossingScheme s).presheaf.germ ⊤ p trivial
        ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O s))).inv (algebraMap O _ o))), ?_⟩
    change (((CrossingQuotient.crossingScheme s).residue p ≫ f.residueFieldMap y) _) = _
    rw [Scheme.residue_residueFieldMap, CommRingCat.comp_apply]
    change IsLocalRing.residue _ q = Ideal.Quotient.mk _ w
    rw [eq_comm]
    exact (Ideal.Quotient.eq).mpr hwq
  have hbij : Function.Bijective (f.residueFieldMap y).hom := ⟨(f.residueFieldMap y).hom.injective, hsurjF⟩
  haveI : IsIso ((forget CommRingCat).map (f.residueFieldMap y)) := (isIso_iff_bijective _).mpr hbij
  exact isIso_of_reflects_iso _ (forget CommRingCat)

end atpoint3

private theorem _root_.Algebra.IsUnramifiedAt.isEtaleAt_of_ringKrullDim_le'
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] [Algebra.IsUnramifiedAt R q]
    (hdim : ringKrullDim (Localization.AtPrime (q.under R)) ≤ ringKrullDim (Localization.AtPrime q)) :
    Algebra.IsEtaleAt R q ∧ Module.Flat R (Localization.AtPrime q) :=
  Algebra.IsUnramifiedAt.isEtaleAt_of_ringKrullDim_le R S q hdim

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_exists_crossingChart_of_crossingPresentation_stalk.Algebra.IsUnramifiedAt.isEtaleAt_of_ringKrullDim_le'" "Algebra.IsUnramifiedAt.isEtaleAt_of_ringKrullDim_le'"
section flat

variable (U : X.Opens) (s : O) (a b : Γ(X, U)) (hab : a * b = toΓU πX U s)

theorem map_map_asIdeal_chart_eq_maximalIdeal (ϖ : O) (y : ↥(U : Scheme.{u}))
    (hgen : IsLocalRing.maximalIdeal (X.presheaf.stalk y.1) =
      Ideal.span {X.presheaf.germ U y.1 y.2 (toΓU πX U ϖ), X.presheaf.germ U y.1 y.2 a, X.presheaf.germ U y.1 y.2 b}) :
    (((chart πX U s a b hab).base y).asIdeal.map (chartRingHom πX U s a b hab)).map (X.presheaf.germ U y.1 y.2).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk y.1) := by
  set p := (chart πX U s a b hab).base y
  have hmem : ∀ c : CrossingQuotient O s, c ∈ p.asIdeal ↔
      X.presheaf.germ U y.1 y.2 (chartRingHom πX U s a b hab c) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y.1) := by
    intro c
    rw [mem_asIdeal_chart_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    change y.1 ∉ X.basicOpen _ ↔ _
    rw [X.mem_basicOpen _ y.1 y.2]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, Ideal.mem_comap]
    exact (hmem c).mp hc
  · rw [hgen, Ideal.span_le]
    have h3 : ∀ c : CrossingQuotient O s, X.presheaf.germ U y.1 y.2 (chartRingHom πX U s a b hab c) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk y.1) →
        X.presheaf.germ U y.1 y.2 (chartRingHom πX U s a b hab c) ∈
          (((p.asIdeal.map (chartRingHom πX U s a b hab)).map (X.presheaf.germ U y.1 y.2).hom : Ideal _) : Set _) :=
      fun c hc => Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ((hmem c).mpr hc))
    rintro z (rfl | rfl | rfl)
    · have h := h3 (algebraMap O _ ϖ) (by rw [chartRingHom_algebraMap, hgen]; exact Ideal.subset_span (Or.inl rfl))
      rwa [chartRingHom_algebraMap] at h
    · have h := h3 (CrossingQuotient.U s) (by rw [chartRingHom_U, hgen]; exact Ideal.subset_span (Or.inr (Or.inl rfl)))
      rwa [chartRingHom_U] at h
    · have h := h3 (CrossingQuotient.V s) (by rw [chartRingHom_V, hgen]; exact Ideal.subset_span (Or.inr (Or.inr rfl)))
      rwa [chartRingHom_V] at h

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3200000 in

theorem flat_stalkMap_chart [IsNoetherianRing O] [IsDomain (CrossingQuotient O s)] [IsIntegrallyClosed (CrossingQuotient O s)]
    [LocallyOfFiniteType πX] (hU : IsAffineOpen U) (ϖ : O) (y : ↥(U : Scheme.{u}))
    (hgen : IsLocalRing.maximalIdeal (X.presheaf.stalk y.1) =
      Ideal.span {X.presheaf.germ U y.1 y.2 (toΓU πX U ϖ), X.presheaf.germ U y.1 y.2 a, X.presheaf.germ U y.1 y.2 b})
    (hsurj : Function.Surjective fun o : O =>
      IsLocalRing.residue (X.presheaf.stalk y.1) (X.presheaf.germ U y.1 y.2 (toΓU πX U o)))
    (hdim : ringKrullDim (CrossingQuotient O s) ≤ ringKrullDim (X.presheaf.stalk y.1)) :
    ((chart πX U s a b hab).stalkMap y).hom.Flat := by
  set f := chart πX U s a b hab
  set p := f.base y
  let φ : CrossingQuotient O s →+* Γ(X, U) := chartRingHom πX U s a b hab

  let y' : U := ⟨y.1, y.2⟩
  let q : Ideal Γ(X, U) := (hU.primeIdealOf y').asIdeal

  letI algCA : Algebra (CrossingQuotient O s) Γ(X, U) := φ.toAlgebra
  letI := X.presheaf.algebra_section_stalk y'
  haveI : IsLocalization.AtPrime (X.presheaf.stalk y.1) q := hU.isLocalization_stalk y'
  letI algCS : Algebra (CrossingQuotient O s) (X.presheaf.stalk y.1) := ((X.presheaf.germ U y.1 y.2).hom.comp φ).toAlgebra
  haveI : IsScalarTower (CrossingQuotient O s) Γ(X, U) (X.presheaf.stalk y.1) :=
    IsScalarTower.of_algebraMap_eq (R := CrossingQuotient O s) (S := Γ(X, U)) (A := X.presheaf.stalk y.1) fun c => rfl

  have hP : q.under (CrossingQuotient O s) = p.asIdeal := by
    ext c
    rw [Ideal.under_def, Ideal.mem_comap, mem_asIdeal_chart_iff]
    change φ c ∈ (hU.primeIdealOf y').asIdeal ↔ _
    rw [mem_primeIdealOf_asIdeal_iff]
    rfl

  haveI : Algebra.FiniteType (CrossingQuotient O s) Γ(X, U) := by
    letI algO : Algebra O Γ(X, U) := (toΓU πX U).toAlgebra
    haveI : IsScalarTower O (CrossingQuotient O s) Γ(X, U) :=
      IsScalarTower.of_algebraMap_eq (R := O) (S := CrossingQuotient O s) (A := Γ(X, U))
        fun o => (chartRingHom_algebraMap πX U s a b hab o).symm
    have hft : (toΓU πX U).FiniteType := by
      have h1 : (πX.appLE ⊤ U le_top).hom.FiniteType :=
        HasRingHomProperty.appLE @LocallyOfFiniteType πX inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
      have h2 : toΓU πX U = (πX.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom := rfl
      rw [h2]
      exact h1.comp (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
    haveI : Algebra.FiniteType O Γ(X, U) := hft
    exact Algebra.FiniteType.of_restrictScalars_finiteType O (CrossingQuotient O s) Γ(X, U)

  let L := Localization.AtPrime q
  let e : L ≃ₐ[Γ(X, U)] X.presheaf.stalk y.1 := IsLocalization.algEquiv q.primeCompl L (X.presheaf.stalk y.1)
  let eh : L →+* X.presheaf.stalk y.1 := e.toRingEquiv.toRingHom
  have ehbij : Function.Bijective eh := e.bijective
  have he : ∀ z : Γ(X, U), eh (algebraMap Γ(X, U) L z) = X.presheaf.germ U y.1 y.2 z := fun z => e.commutes z
  haveI : IsScalarTower (CrossingQuotient O s) Γ(X, U) L := inferInstance
  have heC : ∀ c : CrossingQuotient O s, eh (algebraMap (CrossingQuotient O s) L c) =
      X.presheaf.germ U y.1 y.2 (φ c) := fun c => by
    rw [IsScalarTower.algebraMap_apply (CrossingQuotient O s) Γ(X, U) L, he]; rfl

  have hmapL : (q.under (CrossingQuotient O s)).map (algebraMap (CrossingQuotient O s) L) = IsLocalRing.maximalIdeal L := by
    have hinj : Function.Injective (Ideal.map eh) := by
      intro I J hIJ
      have := congrArg (Ideal.comap eh) hIJ
      rwa [Ideal.comap_map_of_bijective eh ehbij, Ideal.comap_map_of_bijective eh ehbij] at this
    apply hinj
    rw [Ideal.map_map, hP]
    have h1 : (eh.comp (algebraMap (CrossingQuotient O s) L)) = (X.presheaf.germ U y.1 y.2).hom.comp φ := RingHom.ext heC
    rw [h1, ← Ideal.map_map, map_map_asIdeal_chart_eq_maximalIdeal πX U s a b hab ϖ y hgen]

    exact (map_maximalIdeal_of_iso (e.toRingEquiv.toCommRingCatIso)).symm

  set P : Ideal (CrossingQuotient O s) := q.under (CrossingQuotient O s) with hPdef
  haveI : q.LiesOver P := ⟨hPdef⟩
  letI := Localization.AtPrime.algebraOfLiesOver P q
  haveI hsep : Algebra.IsSeparable P.ResidueField q.ResidueField := by
    have hsurjL : Function.Surjective (algebraMap P.ResidueField q.ResidueField) := by
      intro z
      obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨o, ho⟩ := hsurj (IsLocalRing.residue _ (eh l))
      have hl : l - algebraMap (CrossingQuotient O s) L (algebraMap O _ o) ∈ IsLocalRing.maximalIdeal L := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← MulEquiv.isUnit_map e.toRingEquiv]
        change ¬ IsUnit (eh (l - _))
        rw [map_sub, heC, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← Ideal.Quotient.eq]
        change IsLocalRing.residue _ (eh l) = IsLocalRing.residue _ (X.presheaf.germ U y.1 y.2 (φ (algebraMap O _ o)))
        rw [← ho]
        change IsLocalRing.residue _ (X.presheaf.germ U y.1 y.2 (toΓU πX U o)) =
          IsLocalRing.residue _ (X.presheaf.germ U y.1 y.2 (chartRingHom πX U s a b hab (algebraMap O _ o)))
        rw [chartRingHom_algebraMap]
      refine ⟨algebraMap (CrossingQuotient O s) _ (algebraMap O _ o), ?_⟩
      rw [show algebraMap P.ResidueField q.ResidueField (algebraMap (CrossingQuotient O s) P.ResidueField (algebraMap O _ o)) =
          algebraMap Γ(X, U) q.ResidueField (φ (algebraMap O _ o)) from
        Ideal.ResidueField.map_algebraMap P q (algebraMap (CrossingQuotient O s) Γ(X, U)) Ideal.LiesOver.over _]
      change Ideal.Quotient.mk _ (algebraMap Γ(X, U) L (φ (algebraMap O _ o))) = Ideal.Quotient.mk _ l
      rw [eq_comm, Ideal.Quotient.eq]
      have e1 : (algebraMap Γ(X, U) L) (φ (algebraMap O _ o)) = algebraMap (CrossingQuotient O s) L (algebraMap O _ o) :=
        (IsScalarTower.algebraMap_apply (CrossingQuotient O s) Γ(X, U) L _).symm
      rw [e1]
      exact hl
    exact ⟨fun z => by obtain ⟨k, rfl⟩ := hsurjL z; exact isSeparable_algebraMap k⟩
  haveI : Algebra.IsUnramifiedAt (CrossingQuotient O s) q :=
    (Algebra.isUnramifiedAt_iff_map_eq (CrossingQuotient O s) P q).mpr ⟨hsep, hmapL⟩

  have hdim' : ringKrullDim (Localization.AtPrime P) ≤ ringKrullDim (Localization.AtPrime q) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P),
      show ringKrullDim (Localization.AtPrime q) = ringKrullDim L from rfl, ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
    exact (Ideal.height_le_ringKrullDim_of_isPrime).trans hdim

  obtain ⟨-, hflatL⟩ := Algebra.IsUnramifiedAt.isEtaleAt_of_ringKrullDim_le' (CrossingQuotient O s) Γ(X, U) q hdim'
  have hflatS : Module.Flat (CrossingQuotient O s) (X.presheaf.stalk y.1) :=
    (Module.Flat.equiv_iff (e.toLinearEquiv.restrictScalars (CrossingQuotient O s))).mp hflatL
  have hflat1 : ((X.presheaf.germ U y.1 y.2).hom.comp φ).Flat := hflatS

  let t : CrossingQuotient O s →+* (CrossingQuotient.crossingScheme s).presheaf.stalk p :=
    ((CrossingQuotient.crossingScheme s).presheaf.germ ⊤ p trivial).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O s))).inv.hom
  let g : (CrossingQuotient.crossingScheme s).presheaf.stalk p →+* (U : Scheme.{u}).presheaf.stalk y := (f.stalkMap y).hom
  have hgt : g.comp t = (U.stalkIso y).inv.hom.comp ((X.presheaf.germ U y.1 y.2).hom.comp φ) := by
    refine RingHom.ext fun c => ?_
    have h := stalkIso_stalkMap_chart_germ πX U s a b hab y c
    have h' := congrArg (U.stalkIso y).inv h
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at h'
    exact h'
  have hflat2 : (g.comp t).Flat := by
    rw [hgt]
    exact RingHom.Flat.comp hflat1 (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (U.stalkIso y).inv))

  letI algt : Algebra (CommRingCat.of (CrossingQuotient O s)) ((CrossingQuotient.crossingScheme s).presheaf.stalk p) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of (CrossingQuotient O s)) p
  haveI : IsLocalization.AtPrime ((CrossingQuotient.crossingScheme s).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (CrossingQuotient O s)) p
  letI algg : Algebra ((CrossingQuotient.crossingScheme s).presheaf.stalk p) ((U : Scheme.{u}).presheaf.stalk y) := g.toAlgebra
  letI alggt : Algebra (CommRingCat.of (CrossingQuotient O s)) ((U : Scheme.{u}).presheaf.stalk y) := (g.comp t).toAlgebra
  haveI : IsScalarTower (CommRingCat.of (CrossingQuotient O s)) ((CrossingQuotient.crossingScheme s).presheaf.stalk p)
      ((U : Scheme.{u}).presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq (R := CommRingCat.of (CrossingQuotient O s))
      (S := (CrossingQuotient.crossingScheme s).presheaf.stalk p) (A := (U : Scheme.{u}).presheaf.stalk y) fun c => rfl
  have hflat3 : Module.Flat (CommRingCat.of (CrossingQuotient O s)) ((U : Scheme.{u}).presheaf.stalk y) := hflat2
  have hflat4 : Module.Flat ((CrossingQuotient.crossingScheme s).presheaf.stalk p) ((U : Scheme.{u}).presheaf.stalk y) :=
    (Module.flat_iff_of_isLocalization (S := (CrossingQuotient.crossingScheme s).presheaf.stalk p)
      (p := p.asIdeal.primeCompl) ((U : Scheme.{u}).presheaf.stalk y)).mpr hflat3
  exact hflat4

end flat

end BGeom

theorem solution
    {O : Type u} [CommRing O] [IsNoetherianRing O] (ϖ : O) (e : ℕ)
    [IsDomain (CrossingQuotient O (ϖ ^ e))] [IsIntegrallyClosed (CrossingQuotient O (ϖ ^ e))]
    {X : Scheme.{u}} [IsLocallyNoetherian X] (πX : X ⟶ Spec (CommRingCat.of O)) [LocallyOfFiniteType πX]
    (x : X) (hx : IsClosed ({x} : Set X))

    (g h : X.presheaf.stalk x)
    (hrel : g * h = (X.presheaf.germ ⊤ x trivial (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ))) ^ e)
    (hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
      Ideal.span {X.presheaf.germ ⊤ x trivial (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)), g, h})

    (hres : Function.Surjective fun o : O => IsLocalRing.residue (X.presheaf.stalk x)
      (X.presheaf.germ ⊤ x trivial (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))))

    (hdim : ringKrullDim (CrossingQuotient O (ϖ ^ e)) ≤ ringKrullDim (X.presheaf.stalk x)) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (gU hU : Γ(X, U))
      (f : (U : Scheme.{u}) ⟶ CrossingQuotient.crossingScheme (ϖ ^ e)),
      X.presheaf.germ U x hxU gU = g ∧ X.presheaf.germ U x hxU hU = h ∧
      gU * hU = (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ))) ^ e ∧

      f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (ϖ ^ e)))) = U.ι ≫ πX ∧

      (∀ y : ↥(U : Scheme.{u}),
          (CrossingQuotient.U (ϖ ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (ϖ ^ e) ∈ (f.base y).asIdeal) ↔ U.ι.base y = x) ∧

      (∀ y : ↥(U : Scheme.{u}), U.ι.base y = x →
          (f.stalkMap y).hom.Flat ∧
          Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
          IsIso (f.residueFieldMap y)) ∧

      (∀ y : ↥(U : Scheme.{u}), CrossingQuotient.U (ϖ ^ e) ∈ (f.base y).asIdeal ↔ U.ι.base y ∉ X.basicOpen gU) ∧
      (∀ y : ↥(U : Scheme.{u}), CrossingQuotient.V (ϖ ^ e) ∈ (f.base y).asIdeal ↔ U.ι.base y ∉ X.basicOpen hU) := by
  classical

  obtain ⟨U₁, hx₁, g₁, h₁, hg₁, hh₁, hrel₁⟩ := BGeom.exists_representatives πX x (ϖ ^ e) g h
    (by rw [map_pow, map_pow, map_pow]; exact hrel)
  have hmax₁ : IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
      Ideal.span {X.presheaf.germ U₁ x hx₁ (BGeom.toΓU πX U₁ ϖ), X.presheaf.germ U₁ x hx₁ g₁, X.presheaf.germ U₁ x hx₁ h₁} := by
    rw [hmax, BGeom.germ_toΓU, hg₁, hh₁]

  obtain ⟨V, hxV, hVU₁, hV⟩ := BGeom.exists_open_forall_eq_of_maximalIdeal_eq_span hx₁ hx _ _ _ hmax₁
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV'⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  have hWV : W ≤ V := hWV'
  have hWU₁ : W ≤ U₁ := hWV.trans hVU₁
  let gW : Γ(X, W) := X.presheaf.map (homOfLE hWU₁).op g₁
  let hW' : Γ(X, W) := X.presheaf.map (homOfLE hWU₁).op h₁
  have hrelW : gW * hW' = BGeom.toΓU πX W (ϖ ^ e) := by
    simp only [gW, hW', ← map_mul, hrel₁, BGeom.map_toΓU]
  have hgW : X.presheaf.germ W x hxW gW = g := by
    simp only [gW]; rw [TopCat.Presheaf.germ_res_apply]; exact hg₁
  have hhW : X.presheaf.germ W x hxW hW' = h := by
    simp only [hW']; rw [TopCat.Presheaf.germ_res_apply]; exact hh₁
  have hmaxW : IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
      Ideal.span {X.presheaf.germ W x hxW (BGeom.toΓU πX W ϖ), X.presheaf.germ W x hxW gW, X.presheaf.germ W x hxW hW'} := by
    rw [hmax, BGeom.germ_toΓU, hgW, hhW]

  have hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [hmax]; exact Ideal.subset_span (Or.inr (Or.inl rfl))
  have hhm : h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [hmax]; exact Ideal.subset_span (Or.inr (Or.inr rfl))
  refine ⟨W, hxW, gW, hW', BGeom.chart πX W (ϖ ^ e) gW hW' hrelW, hgW, hhW, ?_,
    BGeom.chart_over πX W (ϖ ^ e) gW hW' hrelW, ?_, ?_,
    BGeom.U_mem_asIdeal_chart_iff πX W (ϖ ^ e) gW hW' hrelW, BGeom.V_mem_asIdeal_chart_iff πX W (ϖ ^ e) gW hW' hrelW⟩
  ·
    rw [hrelW, map_pow]; rfl
  ·
    intro y
    rw [BGeom.U_mem_asIdeal_chart_iff, BGeom.V_mem_asIdeal_chart_iff]
    change (y.1 ∉ X.basicOpen gW ∧ y.1 ∉ X.basicOpen hW') ↔ y.1 = x
    constructor
    · rintro ⟨hyg, hyh⟩
      have hyW : y.1 ∈ W := y.2
      refine hV y.1 (hWV hyW) ?_ ?_ ?_
      ·
        intro hyϖ
        apply hyg
        have hunitϖ : IsUnit (X.presheaf.germ ⊤ y.1 trivial (πX.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ))) := by
          rw [← BGeom.germ_toΓU πX U₁ y.1 (hWU₁ hyW)]
          exact (X.mem_basicOpen _ y.1 (hWU₁ hyW)).mp hyϖ
        have hunit : IsUnit (X.presheaf.germ W y.1 hyW (gW * hW')) := by
          rw [hrelW, map_pow, map_pow, BGeom.germ_toΓU]
          exact hunitϖ.pow e
        rw [map_mul] at hunit
        exact (X.mem_basicOpen gW y.1 hyW).mpr (isUnit_of_mul_isUnit_left hunit)
      · intro hy; apply hyg
        have : y.1 ∈ X.basicOpen (X.presheaf.map (homOfLE hWU₁).op g₁) := by
          rw [Scheme.basicOpen_res]; exact ⟨hyW, hy⟩
        exact this
      · intro hy; apply hyh
        have : y.1 ∈ X.basicOpen (X.presheaf.map (homOfLE hWU₁).op h₁) := by
          rw [Scheme.basicOpen_res]; exact ⟨hyW, hy⟩
        exact this
    · intro hyx
      subst hyx
      constructor
      · intro hy
        have hu := (X.mem_basicOpen gW y.1 hxW).mp hy
        rw [hgW] at hu
        exact (IsLocalRing.mem_maximalIdeal _).mp hgm hu
      · intro hy
        have hu := (X.mem_basicOpen hW' y.1 hxW).mp hy
        rw [hhW] at hu
        exact (IsLocalRing.mem_maximalIdeal _).mp hhm hu
  ·
    intro y hyx
    change y.1 = x at hyx
    subst hyx
    have hgen : IsLocalRing.maximalIdeal (X.presheaf.stalk y.1) =
        Ideal.span {X.presheaf.germ W y.1 y.2 (BGeom.toΓU πX W ϖ), X.presheaf.germ W y.1 y.2 gW, X.presheaf.germ W y.1 y.2 hW'} :=
      hmaxW
    have hsurj : Function.Surjective fun o : O =>
        IsLocalRing.residue (X.presheaf.stalk y.1) (X.presheaf.germ W y.1 y.2 (BGeom.toΓU πX W o)) := by
      intro z
      obtain ⟨o, ho⟩ := hres z
      refine ⟨o, ?_⟩
      show IsLocalRing.residue _ (X.presheaf.germ W y.1 y.2 (BGeom.toΓU πX W o)) = z
      rw [BGeom.germ_toΓU]
      exact ho
    exact ⟨BGeom.flat_stalkMap_chart πX W (ϖ ^ e) gW hW' hrelW hW ϖ y hgen hsurj hdim,
      BGeom.map_stalkMap_chart_maximalIdeal πX W (ϖ ^ e) gW hW' hrelW ϖ y hgen,
      BGeom.isIso_residueFieldMap_chart πX W (ϖ ^ e) gW hW' hrelW y hsurj⟩

end

end S_AlgebraicGeometry_Scheme_exists_crossingChart_of_crossingPresentation_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_crossingChart_of_crossingPresentation_stalk (solution)
