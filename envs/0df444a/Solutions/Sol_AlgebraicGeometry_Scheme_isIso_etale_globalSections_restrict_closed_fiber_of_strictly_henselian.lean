-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.isIso_etale_globalSections_restrict_closed_fiber_of_strictly_henselian
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-22T06:04:03.213909+00:00
-- url     : https://prove2.me/submissions/ea7569e7-ec20-48a1-934d-47ed40dff252

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionDescent
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_appTop_eq_idempotent_closed_fiber_of_isProper
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_coproduct_strictlyHenselian_of_finite
import Theorems.Thm_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite

noncomputable section

section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PhilipponSchemeIdempotents

universe u

/-- The characteristic section of a clopen subset is a global idempotent. -/
theorem exists_idempotent_of_clopen (X : Scheme.{u}) {s : Set X} (hs : IsClopen s) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧
      (∀ x ∈ s, X.presheaf.Γgerm x e = 1) ∧
      (∀ x ∉ s, X.presheaf.Γgerm x e = 0) := by
  classical
  let U : Bool → X.Opens := fun i => if i then ⟨s, hs.2⟩ else ⟨sᶜ, hs.1.isOpen_compl⟩
  let a (i : Bool) : Γ(X, U i) := if i then 1 else 0
  let k (i : Bool) : U i ⟶ ⊤ := homOfLE le_top
  have hDisj : ∀ i j : Bool, i ≠ j → U i ⊓ U j = ⊥ := by
    intro i j hij
    cases i <;> cases j <;> simp_all [U]
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    rw [Opens.mem_iSup]
    by_cases hx : x ∈ s
    · exact ⟨true, by simpa [U] using hx⟩
    · exact ⟨false, by simpa [U] using hx⟩
  have hCompatible : TopCat.Presheaf.IsCompatible X.presheaf U a := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · exact (CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty (hDisj i j hij))).elim _ _
  obtain ⟨e, hRes, hUnique⟩ := X.sheaf.existsUnique_gluing' U ⊤ k hcover a hCompatible
  have hRes' (i : Bool) : (X.presheaf.map (k i).op).hom e = a i := hRes i
  have he : IsIdempotentElem e := by
    change e * e = e
    apply hUnique
    intro i
    let g := (X.presheaf.map (k i).op).hom
    calc
      g (e * e) = g e * g e := map_mul g e e
      _ = a i * a i := congrArg (fun z : Γ(X, U i) => z * z) (hRes' i)
      _ = a i := by cases i <;> simp [a]
  have hg (i : Bool) (x : X) (hx : x ∈ U i) :
      X.presheaf.Γgerm x e = X.presheaf.germ (U i) x hx (a i) := by
    rw [← hRes' i]
    exact (X.presheaf.germ_res_apply (k i) x hx e).symm
  refine ⟨e, he, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ U true := by simpa [U] using hx
    simpa only [a, if_true, map_one] using hg true x hx'
  · intro x hx
    have hx' : x ∈ U false := by simpa [U] using hx
    simpa only [a, Bool.false_eq_true, if_false, map_zero] using hg false x hx'

/-- A scheme whose global functions have only trivial idempotents has
preconnected underlying space. -/
theorem preconnectedSpace_of_trivial_idempotents (X : Scheme.{u})
    (h : ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1) : PreconnectedSpace X := by
  apply preconnectedSpace_iff_clopen.2
  intro s hs
  obtain ⟨e, he, h1, h0⟩ := exists_idempotent_of_clopen X hs
  rcases h e he with he₀ | he₁
  · left
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    exact zero_ne_one (by simpa only [he₀, map_zero] using h1 x hx)
  · right
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    exact one_ne_zero (by simpa only [he₁, map_one] using h0 x hx)

end PhilipponSchemeIdempotents

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponClosedFiberIdempotents

universe u

private theorem idempotent_of_scalar {K B : Type u} [Field K] [CommRing B] (g : K →+* B)
    (c : K) (hc : IsIdempotentElem (g c)) : g c = 0 ∨ g c = 1 := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact Or.inl (hB.elim _ _)
  have hi : c * c = c := g.injective (by rw [map_mul]; exact hc.eq)
  have hZero : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hi, sub_self]
  rcases mul_eq_zero.mp hZero with h | h
  · exact Or.inl (by rw [h, map_zero])
  · exact Or.inr (by rw [sub_eq_zero.mp h, map_one])

variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R))

private abbrev residue := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
private abbrev Fiber := pullback (residue (R := R)) f
private abbrev inclusion : Fiber f ⟶ X := pullback.snd (residue (R := R)) f

/-- When a map to a local spectrum induces an isomorphism on global
functions, lifting idempotents suffices for closed-fiber connectedness. -/
theorem closedFiber_preconnected_of_idempotents_lift [IsIso f.appTop]
    (hLift : ∀ e : Γ(Fiber f, ⊤), IsIdempotentElem e →
      ∃ x : Γ(X, ⊤), (inclusion f).appTop.hom x = e) :
    _root_.IsPreconnected (f ⁻¹' {IsLocalRing.closedPoint R}) := by
  let K := IsLocalRing.ResidueField R
  let i := inclusion f
  let q : Fiber f ⟶ Spec (.of K) := pullback.fst (residue (R := R)) f
  let r := residue (R := R)
  let eK := Scheme.ΓSpecIso (CommRingCat.of K)
  let scalar : K →+* Γ(Fiber f, ⊤) := q.appTop.hom.comp eK.inv.hom
  have hComp : f.appTop ≫ i.appTop = r.appTop ≫ q.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
    exact congrArg Scheme.Hom.appTop (pullback.condition (f := r) (g := f)).symm
  let : PreconnectedSpace (Fiber f) := by
    apply PhilipponSchemeIdempotents.preconnectedSpace_of_trivial_idempotents
    intro e he
    obtain ⟨x, hx⟩ := hLift e he
    let b := (inv f.appTop).hom x
    let c := eK.hom.hom (r.appTop.hom b)
    have hb : f.appTop.hom b = x := ConcreteCategory.congr_hom (IsIso.inv_hom_id f.appTop) x
    have hc : scalar c = e := by
      change q.appTop.hom (eK.inv.hom (eK.hom.hom (r.appTop.hom b))) = e
      calc
        _ = q.appTop.hom (r.appTop.hom b) :=
          congrArg q.appTop.hom (ConcreteCategory.congr_hom eK.hom_inv_id (r.appTop.hom b))
        _ = i.appTop.hom (f.appTop.hom b) := (ConcreteCategory.congr_hom hComp b).symm
        _ = e := by rw [hb]; exact hx
    rw [← hc]
    exact idempotent_of_scalar scalar c (hc.symm ▸ he)
  rw [← PhilipponEtaleClosedFiberSections.range_closedFiberι f]
  exact isPreconnected_range i.continuous

end PhilipponClosedFiberIdempotents

end

section

set_option autoImplicit false

namespace PhilipponHenselianIntegralConnectedness

universe u

private theorem trivial_idempotents {B : Type u} [CommRing B]
    [PreconnectedSpace (PrimeSpectrum B)] (e : B) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  let φ := PrimeSpectrum.isIdempotentElemEquivClopens (R := B)
  let V := φ ⟨e, he⟩
  rcases preconnectedSpace_iff_clopen.mp inferInstance (V : Set (PrimeSpectrum B)) V.isClopen with h | h
  · have hb : V = ⊥ := SetLike.coe_injective h
    have hx := congrArg (fun C => (φ.symm C).val) hb
    left
    simpa only [V, φ, OrderIso.symm_apply_apply, PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot] using hx
  · have ht : V = ⊤ := SetLike.coe_injective h
    have hx := congrArg (fun C => (φ.symm C).val) ht
    right
    simpa only [V, φ, OrderIso.symm_apply_apply, PrimeSpectrum.isIdempotentElemEquivClopens_symm_top] using hx

private theorem local_of_components {A : Type u} [CommRing A] [Nontrivial A]
    [Fintype (MaximalSpectrum A)] (e : MaximalSpectrum A → A)
    (he : CompleteOrthogonalIdempotents e)
    (hLocal : ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - e i}))
    (hTrivial : ∀ x : A, IsIdempotentElem x → x = 0 ∨ x = 1) : IsLocalRing A := by
  have hOne (i : MaximalSpectrum A) : e i = 1 := (hTrivial (e i) (he.idem i)).resolve_left (by
    intro h
    have hTop : Ideal.span {1 - e i} = ⊤ := by rw [h, sub_zero, Ideal.span_singleton_one]
    have hNontrivial : Nontrivial (A ⧸ Ideal.span {1 - e i}) := (hLocal i).toNontrivial
    exact (Ideal.Quotient.nontrivial_iff.mp hNontrivial) hTop)
  let : Subsingleton (MaximalSpectrum A) :=
    ⟨fun i j => Classical.byContradiction fun h =>
      one_ne_zero (by simpa only [hOne i, hOne j, one_mul] using he.ortho h)⟩
  exact IsLocalRing.of_singleton_maximalSpectrum

/-- A nonzero integral algebra with preconnected spectrum over a base
whose finite algebras split into local factors is local. -/
theorem isLocalRing_of_integral_of_preconnected
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.IsIntegral R B] [Nontrivial B] [PreconnectedSpace (PrimeSpectrum B)]
    (decompose : ∀ (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A],
      ∃ (_ : Fintype (MaximalSpectrum A)) (e : MaximalSpectrum A → A),
        CompleteOrthogonalIdempotents e ∧
          ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - e i})) :
    IsLocalRing B := by
  let : Subsingleton (MaximalSpectrum B) := ⟨fun m n => by
    apply MaximalSpectrum.ext
    apply SetLike.ext
    intro b
    let A := Algebra.adjoin R ({b} : Set B)
    let : Module.Finite R A := .of_fg (Algebra.IsIntegral.isIntegral (R := R) b).fg_adjoin_singleton
    let a : A := ⟨b, Algebra.subset_adjoin rfl⟩
    have hTrivial (x : A) (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
      rcases trivial_idempotents (x : B) (hx.map A.val) with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    obtain ⟨_, e, he, hLocal⟩ := decompose A
    let : IsLocalRing A := local_of_components e he hLocal hTrivial
    let : Algebra.IsIntegral A B := Algebra.IsIntegral.tower_top (R := R)
    have hm := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) m.asIdeal
    have hn := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) n.asIdeal
    have hEq := (IsLocalRing.eq_maximalIdeal hm).trans (IsLocalRing.eq_maximalIdeal hn).symm
    exact iff_of_eq (congrArg (fun I : Ideal A => a ∈ I) hEq)⟩
  exact IsLocalRing.of_singleton_maximalSpectrum

end PhilipponHenselianIntegralConnectedness

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace PhilipponHenselianClosedFiberConnectedness

universe u

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  [IsLocalRing R] [Algebra.IsIntegral R B]

private theorem comap_eq_closedPoint [IsLocalRing B] :
    PrimeSpectrum.comap (algebraMap R B) (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint R := by
  apply PrimeSpectrum.ext
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (IsLocalRing.maximalIdeal B))

private theorem eq_closedPoint_of_comap_eq [IsLocalRing B] (b : PrimeSpectrum B)
    (hb : PrimeSpectrum.comap (algebraMap R B) b = IsLocalRing.closedPoint R) :
    b = IsLocalRing.closedPoint B := by
  apply PrimeSpectrum.ext
  have hI : b.asIdeal.comap (algebraMap R B) = IsLocalRing.maximalIdeal R :=
    congrArg PrimeSpectrum.asIdeal hb
  have hMax : (b.asIdeal.comap (algebraMap R B)).IsMaximal :=
    hI ▸ IsLocalRing.maximalIdeal.isMaximal R
  exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap b.asIdeal hMax)

set_option maxRecDepth 4096 in
/-- A surjective factorization through an integral algebra transfers
preconnectedness of its closed fiber to the original closed fiber. -/
theorem closedFiber_preconnected_of_integral_factorization
    {Y : Scheme.{u}} [PreconnectedSpace Y] (f : Y ⟶ Spec (.of R))
    (g : Y ⟶ Spec (.of B)) [Surjective g]
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) = f)
    (hConnected : ∀ [IsLocalRing B], _root_.IsPreconnected (g ⁻¹' {IsLocalRing.closedPoint B}))
    (decompose : ∀ (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A],
      ∃ (_ : Fintype (MaximalSpectrum A)) (e : MaximalSpectrum A → A),
        CompleteOrthogonalIdempotents e ∧
          ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - e i})) :
    _root_.IsPreconnected (f ⁻¹' {IsLocalRing.closedPoint R}) := by
  classical
  rcases isEmpty_or_nonempty Y with hY | hY
  · let : IsEmpty Y := hY
    rw [Set.eq_empty_of_isEmpty (f ⁻¹' {IsLocalRing.closedPoint R})]
    exact isPreconnected_empty
  let : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨g (Classical.choice hY)⟩
  let : PreconnectedSpace (PrimeSpectrum B) := ⟨by
    change _root_.IsPreconnected (Set.univ : Set (Spec (.of B)))
    rw [← g.surjective.range_eq]
    exact isPreconnected_range g.continuous⟩
  let : IsLocalRing B :=
    PhilipponHenselianIntegralConnectedness.isLocalRing_of_integral_of_preconnected R B decompose
  have h : f ⁻¹' {IsLocalRing.closedPoint R} = g ⁻¹' {IsLocalRing.closedPoint B} := by
    ext y
    simp only [Set.mem_preimage]
    rw [← hg, Scheme.Hom.comp_apply]
    change PrimeSpectrum.comap (algebraMap R B) (g y) = IsLocalRing.closedPoint R ↔
      g y = IsLocalRing.closedPoint B
    exact ⟨eq_closedPoint_of_comap_eq (g y), fun h => h ▸ comap_eq_closedPoint⟩
  rw [h]
  exact hConnected

/-- For a proper scheme, its global-section algebra is integral over the
base. It suffices to check closed-fiber connectedness for proper maps
over a local ring that induce an isomorphism on global sections. -/
theorem closedFiber_preconnected_of_affinization
    {Y : Scheme.{u}} [PreconnectedSpace Y] (f : Y ⟶ Spec (.of R)) [IsProper f]
    (hConnected : ∀ {A : Type u} [CommRing A] [IsLocalRing A] {V : Scheme.{u}}
      (g : V ⟶ Spec (.of A)) [IsProper g] [IsIso g.appTop],
      _root_.IsPreconnected (g ⁻¹' {IsLocalRing.closedPoint A}))
    (decompose : ∀ (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A],
      ∃ (_ : Fintype (MaximalSpectrum A)) (e : MaximalSpectrum A → A),
        CompleteOrthogonalIdempotents e ∧
          ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - e i})) :
    _root_.IsPreconnected (f ⁻¹' {IsLocalRing.closedPoint R}) := by
  let B := Γ(Y, ⊤)
  let φ : CommRingCat.of R ⟶ B := (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop
  let : Algebra R B := φ.hom.toAlgebra
  have hφ : φ.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  let : Algebra.IsIntegral R B := ⟨hφ⟩
  have h : Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) = f := by
    change Y.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop) = f
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  let : CompactSpace Y := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : IsProper (Y.toSpecΓ ≫ Spec.map φ) := by
    change IsProper (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)))
    rw [h]
    infer_instance
  let : IsProper Y.toSpecΓ := IsProper.of_comp Y.toSpecΓ (Spec.map φ)
  let : IsIso Y.toSpecΓ.appTop := by
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  exact closedFiber_preconnected_of_integral_factorization f Y.toSpecΓ h
    (fun [_] => hConnected Y.toSpecΓ) decompose

end PhilipponHenselianClosedFiberConnectedness

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleGeometricStalks (algebraicallyClosedGeometricMap)
open PhilipponEtaleStrictHenselization (toBase)
open PhilipponFiniteEtaleDescent (HasClosedStrictLocalComponents)

namespace PhilipponClosedFiberDegreeZeroReduction

universe u

theorem hasClosedStrictLocalComponents {X P : Scheme.{u}} (p : P ⟶ X) [IsFinite p] (x : X) :
    HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap x)) p) := by
  let s := algebraicallyClosedGeometricMap x
  let A : Type u := PhilipponEtaleLocalRing.stalkRing s
  let hA : HenselianLocalRing A := PhilipponEtaleHenselianStalk.henselianLocalRing s
  let _ := hA
  let hSep : IsSepClosed (IsLocalRing.ResidueField A) :=
    PhilipponEtaleHenselianStalk.residueFieldIsSepClosed s
  let q := pullback.fst (toBase s) p
  have hq : IsFinite q := inferInstanceAs (IsFinite (pullback.fst (toBase s) p))
  obtain ⟨I, _, B, hRing, hH, hB, c, hClosed⟩ :=
    @Scheme.exists_finite_coproduct_strictlyHenselian_of_finite A _ hA hSep _ q hq
  exact ⟨I, B, hRing, hH, hB, c, hClosed⟩

theorem closedFiber_preconnected {R : Type u} [CommRing R] [HenselianLocalRing R]
    {V : Scheme.{u}} (g : V ⟶ Spec (.of R)) [IsProper g] [PreconnectedSpace V] :
    _root_.IsPreconnected (g ⁻¹' {IsLocalRing.closedPoint R}) := by
  apply PhilipponHenselianClosedFiberConnectedness.closedFiber_preconnected_of_affinization g
  · intro A _ _ W a _ _
    exact PhilipponClosedFiberIdempotents.closedFiber_preconnected_of_idempotents_lift a
      (Scheme.exists_appTop_eq_idempotent_closed_fiber_of_isProper a)
  · intro A _ _ _
    obtain ⟨hI, e, hE, _, _, hLocal⟩ :=
      HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
        (R := R) (S := A)
    exact ⟨hI, e, hE, hLocal⟩

end PhilipponClosedFiberDegreeZeroReduction

universe u

theorem solution
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso ((PhilipponEtaleAcyclicCohomology.globalSections Y).map
      ((PhilipponEtaleSmallSite.pullbackAdjunction (pullback.snd
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) f)).unit.app F)) :=
  PhilipponEtaleClosedFiberDegreeZero.isIso_unitSections_of_connectedness f
    (fun g => PhilipponClosedFiberDegreeZeroReduction.closedFiber_preconnected g)
    (fun g => PhilipponClosedFiberDegreeZeroReduction.hasClosedStrictLocalComponents g) F

end

end
