-- Prove2me | Definitions.Def_RPLib_S4_CDPack49
-- name    : RPLib_S4_CDPack49
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:15:48.080961+00:00
-- url     : https://prove2.me/theorems/8e6eb969-6a44-47f6-8653-1c43ce6ff3cd
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 49 of 71
-- statement:
--   Part 49 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_IntersectB_Pen1`: S4-IntersectB, O9 part 1: fibres of the pencil family over the affine line
--   * `Def_RP_IntersectB_Pen2`: S4-IntersectB, O9 part 2: flatness of the pencil family at fibre points
--   * `Def_RP_IntersectB_Fam1`: S4-IntersectB, file Fam1: flat neighbourhoods of finite fibres (O8, part 1)
--   * `Def_RP_JacAlg_Multiset`: Core B algebra, part 3: the multiset lemma with RH (A6, L7)
--   * `Def_RP_JacAlg_Res`: Core B algebra, part 7: resultants (unit S4-JacAlg, lemma L4 = Milne 10.21, steps R1 and R2)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S3_ExpSum

/-!
# Curve-duality library package, part 49 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_IntersectB_Pen1`: S4-IntersectB, O9 part 1: fibres of the pencil family over the affine line
* `Def_RP_IntersectB_Pen2`: S4-IntersectB, O9 part 2: flatness of the pencil family at fibre points
* `Def_RP_IntersectB_Fam1`: S4-IntersectB, file Fam1: flat neighbourhoods of finite fibres (O8, part 1)
* `Def_RP_JacAlg_Multiset`: Core B algebra, part 3: the multiset lemma with RH (A6, L7)
* `Def_RP_JacAlg_Res`: Core B algebra, part 7: resultants (unit S4-JacAlg, lemma L4 = Milne 10.21, steps R1 and R2)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_IntersectB_Pen1 =====
section

/-!
# S4-IntersectB, O9 part 1: fibres of the pencil family over the affine line

`π : X ⟶ S`, a closed subscheme `C` of `X`, an open `O ⊆ X` and `g ∈ Γ(X, O)`. The graph of `g` on
`C ∩ O` is `gam : C ∩ O ⟶ 𝔸¹_X`; its scheme-theoretic image maps to `𝔸¹_S` by `famL`. For a
section `l` of `S`, `isPullback_fibre` identifies the fibre of `famL` over the `l`-point of `𝔸¹_S`
with a closed subscheme `J ⊇ C` of `X`, given that `g = l` on `J` and that, on an affine cover,
`J` is cut out by `C` and one element `h` with `a (g - l) = h` on `C ∩ O`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace RamanujanPetersson.IntersectB

/-- The affine line over `X`. -/
noncomputable abbrev Ln (X : Scheme.{u}) : Scheme.{u} := 𝔸(PUnit.{u+1}; X)

/-- The projection of the affine line. -/
noncomputable abbrev prL (X : Scheme.{u}) : Ln X ⟶ X := 𝔸(PUnit.{u+1}; X) ↘ X

lemma appLE_congr_hom {X Y : Scheme.{u}} {f f' : X ⟶ Y} (hf : f = f') (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = f'.appLE U V (hf ▸ e) := by
  subst hf; rfl

/-- Pulling back an element of an ideal sheaf lands in the pulled back ideal sheaf. -/
lemma appLE_mem_comap {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (U : Y.affineOpens)
    (W : X.affineOpens) (e : W.1 ≤ f ⁻¹ᵁ U.1) {r : Γ(Y, U)} (hr : r ∈ I.ideal U) :
    f.appLE U W e r ∈ (I.comap f).ideal W := by
  have hr' : I.subschemeι.app U r = 0 := by
    rw [← RingHom.mem_ker, ← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
    exact hr
  rw [Scheme.IdealSheafData.comap, Scheme.Hom.ker_apply, RingHom.mem_ker,
    Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom pullback.condition, Scheme.Hom.comp_appLE, CommRingCat.comp_apply, hr',
    map_zero]

lemma comap_self_eq_bot {X : Scheme.{u}} (C : X.IdealSheafData) :
    C.comap C.subschemeι = ⊥ :=
  Scheme.Hom.ker_eq_bot_of_isIso (pullback.fst C.subschemeι C.subschemeι)

section Line
variable {X S : Scheme.{u}} (π : X ⟶ S)

/-- The `l`-point of the affine line over `S`. -/
noncomputable def ptL (l : Γ(S, ⊤)) : S ⟶ Ln S := AffineSpace.homOfVector (𝟙 S) fun _ => l

/-- The `l`-section of the affine line over `X`. -/
noncomputable def secL (l : Γ(S, ⊤)) : X ⟶ Ln X :=
  AffineSpace.homOfVector (𝟙 X) fun _ => π.appTop l

@[reassoc (attr := simp)]
lemma secL_prL (l : Γ(S, ⊤)) : secL π l ≫ prL X = 𝟙 X := AffineSpace.homOfVector_over _ _

@[reassoc (attr := simp)]
lemma ptL_prL (l : Γ(S, ⊤)) : ptL l ≫ prL S = 𝟙 S := AffineSpace.homOfVector_over _ _

lemma isPullback_secL (l : Γ(S, ⊤)) :
    IsPullback (secL π l) π (AffineSpace.map PUnit.{u+1} π) (ptL l) := by
  refine IsPullback.of_right ?_ ?_ (AffineSpace.isPullback_map (n := PUnit.{u+1}) π).flip
  · rw [secL_prL, ptL_prL]
    exact IsPullback.id_horiz π
  · refine AffineSpace.hom_ext ?_ ?_
    · simp
    · intro i
      change (AffineSpace.homOfVector (𝟙 X) _).appTop
          ((AffineSpace.map PUnit.{u+1} π).appTop (AffineSpace.coord S i)) =
        π.appTop ((AffineSpace.homOfVector (𝟙 S) _).appTop (AffineSpace.coord S i))
      rw [AffineSpace.map_appTop_coord, AffineSpace.homOfVector_appTop_coord,
        AffineSpace.homOfVector_appTop_coord]

end Line

section Graph
variable {X S : Scheme.{u}} (π : X ⟶ S) (C : X.IdealSheafData) (O : X.Opens)

/-- The open part `C ∩ O` of the closed subscheme `C`. -/
noncomputable abbrev COo : C.subscheme.Opens := C.subschemeι ⁻¹ᵁ O

/-- Its inclusion into `X`. -/
noncomputable def ιCO : (COo C O).toScheme ⟶ X := (COo C O).ι ≫ C.subschemeι

lemma le_ιCO_preimage : (⊤ : (COo C O).toScheme.Opens) ≤ ιCO C O ⁻¹ᵁ O := by
  rintro ⟨x, hx⟩ -
  exact hx

/-- `g` restricted to `C ∩ O`. -/
noncomputable def gCO (g : Γ(X, O)) : Γ((COo C O).toScheme, ⊤) :=
  (ιCO C O).appLE O ⊤ (le_ιCO_preimage C O) g

/-- The graph of `g` on `C ∩ O`, a morphism to the affine line over `X`. -/
noncomputable def gam (g : Γ(X, O)) : (COo C O).toScheme ⟶ Ln X :=
  AffineSpace.homOfVector (ιCO C O) fun _ => gCO C O g

@[reassoc (attr := simp)]
lemma gam_prL (g : Γ(X, O)) : gam C O g ≫ prL X = ιCO C O := AffineSpace.homOfVector_over _ _

/-- The pencil family: the closure of the graph, over the affine line of `S`. -/
noncomputable def famL (g : Γ(X, O)) : (gam C O g).image ⟶ Ln S :=
  (gam C O g).imageι ≫ AffineSpace.map PUnit.{u+1} π

lemma comap_prL_le_ker (g : Γ(X, O)) : C.comap (prL X) ≤ (gam C O g).ker := by
  rw [← Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.le_map_iff_comap_le,
    ← Scheme.IdealSheafData.comap_comp, gam_prL, ιCO, Scheme.IdealSheafData.comap_comp,
    comap_self_eq_bot, ← Scheme.IdealSheafData.le_map_iff_comap_le]
  exact bot_le

/-- The element `a (t - l) - h` of the affine line over `W` vanishes on the graph. -/
lemma mem_ker_gam (g : Γ(X, O)) [QuasiCompact (gam C O g)] (l : Γ(S, ⊤)) (W : X.affineOpens)
    (a h : Γ(X, W))
    (hid : (ιCO C O).app W a * (COo C O).toScheme.presheaf.map (homOfLE le_top).op
      (gCO C O g - (ιCO C O ≫ π).appTop l) = (ιCO C O).app W h) :
    (prL X).app W a * (Ln X).presheaf.map (homOfLE le_top).op
      (AffineSpace.coord X PUnit.unit - (prL X ≫ π).appTop l) - (prL X).app W h ∈
      (gam C O g).ker.ideal ⟨prL X ⁻¹ᵁ W.1, W.2.preimage _⟩ := by
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  have e1 : ∀ r : Γ(X, W), (gam C O g).app (prL X ⁻¹ᵁ W.1) ((prL X).app W r) =
      (ιCO C O).appLE W _ (le_of_eq (by rw [← Scheme.Hom.comp_preimage, gam_prL])) r := by
    intro r
    rw [Scheme.Hom.app_eq_appLE (gam C O g), ← CommRingCat.comp_apply,
      Scheme.Hom.app_eq_appLE (prL X), Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom (gam_prL C O g)]
  have hV : (gam C O g) ⁻¹ᵁ (prL X ⁻¹ᵁ W.1) ≤ ιCO C O ⁻¹ᵁ W.1 :=
    le_of_eq (by rw [← Scheme.Hom.comp_preimage, gam_prL])
  have e2 : ∀ x : Γ(Ln X, ⊤), (gam C O g).app (prL X ⁻¹ᵁ W.1)
      ((Ln X).presheaf.map (homOfLE le_top).op x) =
      (COo C O).toScheme.presheaf.map (homOfLE hV).op
        ((COo C O).toScheme.presheaf.map (homOfLE le_top).op ((gam C O g).appTop x)) := by
    intro x
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, ← CommRingCat.comp_apply,
      ← Functor.map_comp, CommRingCat.comp_apply]
    rfl
  have e3 : (gam C O g).appTop (AffineSpace.coord X PUnit.unit - (prL X ≫ π).appTop l) =
      gCO C O g - (ιCO C O ≫ π).appTop l := by
    rw [map_sub, gam, AffineSpace.homOfVector_appTop_coord, ← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop, ← Category.assoc, AffineSpace.homOfVector_over]
  rw [map_sub, map_mul, e1, e1, e2, e3]
  change (COo C O).toScheme.presheaf.map (homOfLE hV).op ((ιCO C O).app W a) * _ -
    (COo C O).toScheme.presheaf.map (homOfLE hV).op ((ιCO C O).app W h) = 0
  rw [← map_mul, ← map_sub, hid, sub_self, map_zero]

/-- The fibre of the pencil family over the `l`-point of `𝔸¹_S` is the closed subscheme `J`. -/
theorem isPullback_fibre (g : Γ(X, O)) [QuasiCompact (gam C O g)] (l : Γ(S, ⊤))
    (J : X.IdealSheafData) (m : J.subscheme ⟶ (COo C O).toScheme)
    (hm : m ≫ ιCO C O = J.subschemeι)
    (hg : m.appTop (gCO C O g) = (J.subschemeι ≫ π).appTop l)
    (H : ∀ x : X, ∃ W : X.affineOpens, x ∈ W.1 ∧ ∃ a h : Γ(X, W),
      J.ideal W ≤ Ideal.span {h} ⊔ C.ideal W ∧
      (ιCO C O).app W a * (COo C O).toScheme.presheaf.map (homOfLE le_top).op
        (gCO C O g - (ιCO C O ≫ π).appTop l) = (ιCO C O).app W h) :
    IsPullback (m ≫ (gam C O g).toImage) (J.subschemeι ≫ π) (famL π C O g) (ptL l) := by
  have h1 : J.subschemeι ≫ secL π l = (m ≫ (gam C O g).toImage) ≫ (gam C O g).imageι := by
    rw [Category.assoc, Scheme.Hom.toImage_imageι]
    refine AffineSpace.hom_ext ?_ ?_
    · simp only [Category.assoc, secL_prL, gam_prL, hm, Category.comp_id]
    · intro i
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        CommRingCat.comp_apply, secL, gam, AffineSpace.homOfVector_appTop_coord,
        AffineSpace.homOfVector_appTop_coord, hg, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have h2 : (gam C O g).imageι.ker.comap (secL π l) = J.subschemeι.ker := by
    simp only [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]
    refine le_antisymm ?_ ?_
    · rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
      conv_rhs => rw [← Scheme.IdealSheafData.ker_subschemeι J]
      rw [Scheme.IdealSheafData.map_ker, h1, Category.assoc, Scheme.Hom.toImage_imageι]
      exact Scheme.Hom.le_ker_comp _ _
    · choose W hxW a h hJ hid using H
      refine Scheme.IdealSheafData.le_of_iSup_eq_top W ?_ fun x => ?_
      · exact top_le_iff.mp fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxW y⟩
      refine (hJ x).trans (sup_le ?_ ?_)
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        have hle : (W x).1 ≤ secL π l ⁻¹ᵁ (prL X ⁻¹ᵁ (W x).1) :=
          le_of_eq (by rw [← Scheme.Hom.comp_preimage, secL_prL] <;> rfl)
        have hE := appLE_mem_comap _ (secL π l) ⟨prL X ⁻¹ᵁ (W x).1, (W x).2.preimage _⟩ (W x) hle
          (mem_ker_gam π C O g l (W x) (a x) (h x) (hid x))
        have eA : ∀ r : Γ(X, (W x).1), (secL π l).appLE _ (W x).1 hle ((prL X).app (W x).1 r) = r := by
          intro r
          rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
            appLE_congr_hom (secL_prL π l)]
          change (X.presheaf.map (homOfLE (le_refl (W x).1)).op) r = r
          first
          | (rw [show (homOfLE (le_refl (W x).1)).op = 𝟙 (Opposite.op (W x).1) from rfl,
              CategoryTheory.Functor.map_id]; rfl)
          | exact congrArg (fun φ => (ConcreteCategory.hom φ) r)
              (X.presheaf.map_id (Opposite.op (W x).1))
        have eM : ∀ y : Γ(Ln X, ⊤), (secL π l).appLE _ (W x).1 hle
            ((Ln X).presheaf.map (homOfLE le_top).op y) =
            X.presheaf.map (homOfLE le_top).op ((secL π l).appTop y) := by
          intro y
          rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
          rfl
        have eT : (secL π l).appTop (AffineSpace.coord X PUnit.unit - (prL X ≫ π).appTop l) = 0 := by
          rw [map_sub, secL, AffineSpace.homOfVector_appTop_coord, ← CommRingCat.comp_apply,
            ← Scheme.Hom.comp_appTop, ← Category.assoc, AffineSpace.homOfVector_over,
            Category.id_comp, sub_self]
        rw [map_sub, map_mul, eA, eA, eM, eT, map_zero, mul_zero, zero_sub] at hE
        exact (neg_mem_iff).mp hE
      · calc C.ideal (W x) ≤ ((C.comap (prL X)).comap (secL π l)).ideal (W x) :=
              le_of_eq (by rw [← Scheme.IdealSheafData.comap_comp, secL_prL,
                Scheme.IdealSheafData.comap_id])
          _ ≤ _ := Scheme.IdealSheafData.le_def.mp
              (Scheme.IdealSheafData.comap_mono (secL π l) (comap_prL_le_ker C O g)) (W x)
  exact (isPullback_of_isClosedImmersion J.subschemeι (gam C O g).imageι
    (m ≫ (gam C O g).toImage) (secL π l) h1 h2).flip.paste_vert (isPullback_secL π l)

end Graph

end RamanujanPetersson.IntersectB

end

-- ===== S4.Def_RP_IntersectB_Pen2 =====
section

/-!
# S4-IntersectB, O9 part 2: flatness of the pencil family at fibre points

* `flat_of_poly`: a local algebra `B` over `R ≅ K[X]` is flat when `X - l` acts on `B` as a
  non-zero-divisor lying in the maximal ideal.
* `lineEquiv`: `Γ(𝔸¹_S) ≅ Γ(S)[X]` for affine `S`.
* `stalkMap_flat_of_stalk`: flatness of a stalk map from flatness over sections of an affine open.
* `flat_famL`: the pencil family is flat at the image of a point `x` of `C ∩ O` where the germ of
  `g - l` is a non-zero-divisor in the maximal ideal.
* `preimage_subset_range`, `isImmersion_gam`, `isProper_famL`: the remaining inputs of
  `finrank_eq_of_fibres`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry Polynomial

namespace RamanujanPetersson.IntersectB

/-- Flatness over `K[X]` from a non-zero-divisor condition at one point. -/
theorem flat_of_poly {K R B : Type*} [Field K] [CommRing R] [CommRing B] [IsLocalRing B]
    [Algebra R B] (e : K[X] ≃+* R) (l : K)
    (hy : ∀ b : B, algebraMap R B (e (X - C l)) * b = 0 → b = 0)
    (hm : algebraMap R B (e (X - C l)) ∈ IsLocalRing.maximalIdeal B) : Module.Flat R B := by
  have : IsDomain R := MulEquiv.isDomain K[X] e.symm.toMulEquiv
  have : IsPrincipalIdealRing R := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro b hb
  rw [Submodule.mem_torsion_iff] at hb
  obtain ⟨⟨r, hr⟩, hrb⟩ := hb
  rw [Submodule.mem_bot]
  obtain ⟨p, rfl⟩ := e.surjective r
  have hp : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hr
    exact zero_notMem_nonZeroDivisors hr
  obtain ⟨s, hps, hs⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp l
  set y := algebraMap R B (e (X - C l)) with hy_def
  have hunit : IsUnit (algebraMap R B (e s)) := by
    have hs0 : s.eval l ≠ 0 := fun h => hs (Polynomial.dvd_iff_isRoot.mpr h)
    have h1 : IsUnit (algebraMap R B (e (C (s.eval l)))) :=
      ((Polynomial.isUnit_C.mpr (Ne.isUnit hs0)).map e).map (algebraMap R B)
    obtain ⟨t, ht⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := s) (a := l)
    have hst : s = C (s.eval l) + (X - C l) * t := by rw [← ht]; ring
    have h2 : algebraMap R B (e s) =
        algebraMap R B (e (C (s.eval l))) + y * algebraMap R B (e t) := by
      conv_lhs => rw [hst]
      rw [map_add, map_mul, map_add, map_mul]
    rw [h2]
    by_contra hnu
    have h3 : algebraMap R B (e (C (s.eval l))) + y * algebraMap R B (e t) ∈
        IsLocalRing.maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h4 := sub_mem h3 (Ideal.mul_mem_right (algebraMap R B (e t)) _ hm)
    rw [add_sub_cancel_right] at h4
    exact (IsLocalRing.mem_maximalIdeal _).mp h4 h1
  rw [Submonoid.smul_def, Algebra.smul_def] at hrb
  have hrb2 : algebraMap R B (e p) * b = 0 := hrb
  have hrb' : y ^ (rootMultiplicity l p) * (algebraMap R B (e s) * b) = 0 := by
    rw [hps, map_mul, map_mul, map_pow, map_pow] at hrb2
    rw [← mul_assoc]
    exact hrb2
  have hpow : ∀ n : ℕ, ∀ c : B, y ^ n * c = 0 → c = 0 := by
    intro n
    induction n with
    | zero => intro c hc; simpa using hc
    | succ n ih =>
      intro c hc
      apply ih
      apply hy
      rw [← mul_assoc, ← pow_succ']
      exact hc
  exact (hunit.mul_right_eq_zero).mp (hpow _ _ hrb')

/-- The ring of functions on the affine line over an affine scheme. -/
noncomputable def lineEquiv (S : Scheme.{u}) [IsAffine S] : Γ(S, ⊤)[X] ≃+* Γ(Ln S, ⊤) :=
  (MvPolynomial.uniqueAlgEquiv Γ(S, ⊤) PUnit.{u+1}).symm.toRingEquiv.trans
    (RingEquiv.ofBijective (MvPolynomial.eval₂Hom ((prL S).appTop).hom (AffineSpace.coord S)) (by
      have h : MvPolynomial.eval₂Hom ((prL S).appTop).hom (AffineSpace.coord S) =
          ((Scheme.ΓSpecIso (.of (MvPolynomial PUnit.{u+1} Γ(S, ⊤)))).inv ≫
            (AffineSpace.isoOfIsAffine PUnit.{u+1} S).hom.appTop).hom := by
        rw [AffineSpace.isoOfIsAffine_hom_appTop, Iso.inv_hom_id_assoc]
        rfl
      haveI : IsIso (AffineSpace.isoOfIsAffine PUnit.{u+1} S).hom.appTop :=
        inferInstanceAs (IsIso ((AffineSpace.isoOfIsAffine PUnit.{u+1} S).hom.app ⊤))
      rw [h]
      exact ConcreteCategory.bijective_of_isIso _))

lemma lineEquiv_apply (S : Scheme.{u}) [IsAffine S] (p : Γ(S, ⊤)[X]) :
    lineEquiv S p = p.eval₂ ((prL S).appTop).hom (AffineSpace.coord S PUnit.unit) := by
  change MvPolynomial.eval₂Hom _ _ ((MvPolynomial.uniqueAlgEquiv _ _).symm p) = _
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_uniqueAlgEquiv_symm]

/-- A stalk map is flat when the stalk is flat over the sections of an affine open below. -/
theorem stalkMap_flat_of_stalk {X Y : Scheme.{u}} (p : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : p x ∈ U)
    (h : letI := ((p.stalkMap x).hom.comp (Y.presheaf.germ U (p x) hx).hom).toAlgebra
      Module.Flat Γ(Y, U) (X.presheaf.stalk x)) :
    (p.stalkMap x).hom.Flat := by
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨p x, hx⟩
  have hlt := hU.isLocalization_stalk ⟨p x, hx⟩
  letI : Algebra (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) := (p.stalkMap x).hom.toAlgebra
  letI : Algebra Γ(Y, U) (X.presheaf.stalk x) :=
    ((p.stalkMap x).hom.comp (Y.presheaf.germ U (p x) hx).hom).toAlgebra
  have : IsScalarTower Γ(Y, U) (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  change Module.Flat (Y.presheaf.stalk (p x)) (X.presheaf.stalk x)
  rw [Module.flat_iff_of_isLocalization (Y.presheaf.stalk (p x))
    (hU.primeIdealOf ⟨p x, hx⟩).asIdeal.primeCompl]
  exact h

/-- Points of `p` over a point of the base of a pullback square come from the square. -/
lemma preimage_subset_range {P Z S T : Scheme.{u}} {fst : P ⟶ Z} {snd : P ⟶ S} {p : Z ⟶ T}
    {c : S ⟶ T} (h : IsPullback fst snd p c) (s : S) : p ⁻¹' {c s} ⊆ Set.range fst := by
  intro z hz
  obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := c) z s hz
  refine ⟨h.isoPullback.inv w, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  exact hw1

section Graph
variable {X S : Scheme.{u}} (π : X ⟶ S) (C : X.IdealSheafData) (O : X.Opens)

instance isImmersion_gam (g : Γ(X, O)) : IsImmersion (gam C O g) := by
  have : IsImmersion (gam C O g ≫ prL X) := by
    rw [gam_prL, ιCO]
    infer_instance
  exact IsImmersion.of_comp _ (prL X)

instance isProper_famL [IsProper π] (g : Γ(X, O)) : IsProper (famL π C O g) := by
  have : IsProper (AffineSpace.map PUnit.{u+1} π) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
      (AffineSpace.isPullback_map (n := PUnit.{u+1}) π).flip inferInstance
  unfold famL
  infer_instance

/-- Flatness of the pencil family at the image of `x ∈ C ∩ O`, when the germ of `g - l` at `x`
is a non-zero-divisor in the maximal ideal. -/
theorem flat_famL [IsAffine S] {K : Type u} [Field K] (σ : K ≃+* Γ(S, ⊤)) (g : Γ(X, O))
    [QuasiCompact (gam C O g)] (l : K) (x : (COo C O).toScheme)
    (hy : ∀ b : (COo C O).toScheme.presheaf.stalk x,
      (COo C O).toScheme.presheaf.germ ⊤ x trivial
        (gCO C O g - (ιCO C O ≫ π).appTop (σ l)) * b = 0 → b = 0)
    (hm : (COo C O).toScheme.presheaf.germ ⊤ x trivial
        (gCO C O g - (ιCO C O ≫ π).appTop (σ l)) ∈ IsLocalRing.maximalIdeal _) :
    ((famL π C O g).stalkMap ((gam C O g).toImage x)).hom.Flat := by
  have hq : (gam C O g).toImage ≫ famL π C O g = gam C O g ≫ AffineSpace.map PUnit.{u+1} π := by
    rw [famL, Scheme.Hom.toImage_imageι_assoc]
  let e : K[X] ≃+* Γ(Ln S, ⊤) := (Polynomial.mapEquiv σ).trans (lineEquiv S)
  have he : e (Polynomial.X - Polynomial.C l) =
      AffineSpace.coord S PUnit.unit - (prL S).appTop (σ l) := by
    change lineEquiv S ((Polynomial.X - Polynomial.C l).map (σ : K →+* Γ(S, ⊤))) = _
    rw [lineEquiv_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
    rfl
  have hγ : ((gam C O g).toImage ≫ famL π C O g).appTop (e (Polynomial.X - Polynomial.C l)) =
      gCO C O g - (ιCO C O ≫ π).appTop (σ l) := by
    rw [he, map_sub, hq]
    congr 1
    · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord, gam,
        AffineSpace.homOfVector_appTop_coord]
    · have h2 : (gam C O g ≫ AffineSpace.map PUnit.{u+1} π) ≫ prL S = ιCO C O ≫ π := by
        simp [AffineSpace.map_over]
      rw [← h2, Scheme.Hom.comp_appTop _ (prL S), CommRingCat.comp_apply]
  have hflat : (((gam C O g).toImage ≫ famL π C O g).stalkMap x).hom.Flat := by
    refine stalkMap_flat_of_stalk _ ⊤ (isAffineOpen_top _) x trivial ?_
    letI := ((((gam C O g).toImage ≫ famL π C O g).stalkMap x).hom.comp
      ((Ln S).presheaf.germ ⊤ _ trivial).hom).toAlgebra
    have halg : algebraMap Γ(Ln S, ⊤) _ (e (Polynomial.X - Polynomial.C l)) =
        (COo C O).toScheme.presheaf.germ ⊤ x trivial (gCO C O g - (ιCO C O ≫ π).appTop (σ l)) := by
      change (((gam C O g).toImage ≫ famL π C O g).stalkMap x)
        ((Ln S).presheaf.germ ⊤ _ trivial (e (Polynomial.X - Polynomial.C l))) = _
      exact (Scheme.Hom.germ_stalkMap_apply ((gam C O g).toImage ≫ famL π C O g) ⊤ x trivial
        _).trans (congrArg ((COo C O).toScheme.presheaf.germ ⊤ x trivial) hγ)
    exact flat_of_poly e l (fun b hb => hy b (halg ▸ hb)) (halg ▸ hm)
  rw [Scheme.Hom.stalkMap_comp] at hflat
  have key : (famL π C O g).stalkMap ((gam C O g).toImage x) =
      ((famL π C O g).stalkMap ((gam C O g).toImage x) ≫ (gam C O g).toImage.stalkMap x) ≫
        inv ((gam C O g).toImage.stalkMap x) := by
    simp
  rw [key, CommRingCat.hom_comp]
  exact RingHom.Flat.comp hflat (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))

end Graph

end RamanujanPetersson.IntersectB

end

-- ===== S4.Def_RP_IntersectB_Fam1 =====
section

/-!
# S4-IntersectB, file Fam1: flat neighbourhoods of finite fibres (O8, part 1)

* `flat_atPrime_of_flat_away`: if `M_b` is flat over `B` then so is `M_𝔮` for every prime `𝔮 ∌ b`.
* `flat_away_of_projective`: `M_b` is flat over `B` when `(M_b)` is projective over `B_b`.
* `flat_semilocal`: for `M` finite over `B` with `M_𝔮` flat over `B` for all `𝔮` over `𝔭`, the
  semilocal ring `M_𝔭` is flat over `B`.
* `exists_flat_basicOpen`: (ring form of the open flat locus) there is `b ∉ 𝔭` such that `M_𝔮` is
  flat over `B` for every prime `𝔮` of `M` not containing `b`.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace RamanujanPetersson.IntersectB

section Ring

variable {B M : Type u} [CommRing B] [CommRing M] [Algebra B M]

theorem flat_atPrime_of_flat_away (b : B) (𝔮 : Ideal M) [𝔮.IsPrime]
    (hb : algebraMap B M b ∉ 𝔮)
    (hN : Module.Flat B (Localization (Algebra.algebraMapSubmonoid M (Submonoid.powers b)))) :
    Module.Flat B (Localization.AtPrime 𝔮) := by
  set S := Algebra.algebraMapSubmonoid M (Submonoid.powers b) with hSdef
  have hS : S ≤ 𝔮.primeCompl := by
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    show _ ∉ 𝔮
    rw [map_pow]
    exact fun h => hb (‹𝔮.IsPrime›.mem_of_pow_mem n h)
  letI : Algebra (Localization S) (Localization.AtPrime 𝔮) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ S 𝔮.primeCompl hS
  have : IsScalarTower M (Localization S) (Localization.AtPrime 𝔮) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ S 𝔮.primeCompl hS
  have : IsLocalization (𝔮.primeCompl.map (algebraMap M (Localization S)))
      (Localization.AtPrime 𝔮) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ S 𝔮.primeCompl hS
  have : Module.Flat (Localization S) (Localization.AtPrime 𝔮) :=
    IsLocalization.flat _ (𝔮.primeCompl.map (algebraMap M (Localization S)))
  have : IsScalarTower B (Localization S) (Localization.AtPrime 𝔮) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply B M (Localization S),
        IsScalarTower.algebraMap_apply B M (Localization.AtPrime 𝔮),
        ← IsScalarTower.algebraMap_apply M (Localization S) (Localization.AtPrime 𝔮)]
  exact Module.Flat.trans B (Localization S) (Localization.AtPrime 𝔮)

theorem flat_away_of_projective (b : B)
    [Module.Projective (Localization.Away b) (LocalizedModule.Away b M)] :
    Module.Flat B (Localization (Algebra.algebraMapSubmonoid M (Submonoid.powers b))) := by
  have : Module.Flat B (LocalizedModule.Away b M) :=
    (Module.flat_iff_of_isLocalization (Localization.Away b) (Submonoid.powers b) _).mp
      inferInstance
  have : IsLocalizedModule (Submonoid.powers b) (IsScalarTower.toAlgHom B M
      (Localization (Algebra.algebraMapSubmonoid M (Submonoid.powers b)))).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  exact Module.Flat.of_linearEquiv (IsLocalizedModule.iso (Submonoid.powers b) (IsScalarTower.toAlgHom
    B M (Localization (Algebra.algebraMapSubmonoid M (Submonoid.powers b)))).toLinearMap).symm

theorem flat_semilocal [Module.Finite B M] (𝔭 : Ideal B) [𝔭.IsPrime]
    (h : ∀ (𝔮 : Ideal M) [𝔮.IsPrime], 𝔮.comap (algebraMap B M) = 𝔭 →
      Module.Flat B (Localization.AtPrime 𝔮)) :
    Module.Flat B (Localization (Algebra.algebraMapSubmonoid M 𝔭.primeCompl)) := by
  set Sp := Algebra.algebraMapSubmonoid M 𝔭.primeCompl
  refine Module.flat_of_isLocalized_maximal (Localization Sp) (Localization Sp)
    (fun P _ => Localization.AtPrime P) (fun P _ => Algebra.linearMap _ _) (fun P hP => ?_)
  have hmax : (P.comap (algebraMap (Localization.AtPrime 𝔭) (Localization Sp))).IsMaximal :=
    Ideal.IsMaximal.under (Localization.AtPrime 𝔭) P
  have h𝔮 : (P.comap (algebraMap M (Localization Sp))).comap (algebraMap B M) = 𝔭 := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq B (Localization.AtPrime 𝔭) (Localization Sp),
      ← Ideal.comap_comap, IsLocalRing.eq_maximalIdeal hmax]
    exact Localization.AtPrime.under_maximalIdeal (I := 𝔭)
  have := h _ h𝔮
  exact Module.Flat.of_linearEquiv
    ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization Sp P).restrictScalars
      B).toLinearEquiv.symm

theorem exists_flat_basicOpen [IsNoetherianRing B] [Module.Finite B M] (𝔭 : Ideal B) [𝔭.IsPrime]
    (h : ∀ (𝔮 : Ideal M) [𝔮.IsPrime], 𝔮.comap (algebraMap B M) = 𝔭 →
      Module.Flat B (Localization.AtPrime 𝔮)) :
    ∃ b ∉ 𝔭, ∀ (𝔮 : Ideal M) [𝔮.IsPrime], algebraMap B M b ∉ 𝔮 →
      Module.Flat B (Localization.AtPrime 𝔮) := by
  set Sp := Algebra.algebraMapSubmonoid M 𝔭.primeCompl
  have := Module.finitePresentation_of_finite B M
  have := flat_semilocal 𝔭 h
  have : Module.Flat (Localization.AtPrime 𝔭) (Localization Sp) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime 𝔭) 𝔭.primeCompl _).mpr
      inferInstance
  have : Module.Free (Localization.AtPrime 𝔭) (Localization Sp) :=
    Module.free_of_flat_of_isLocalRing
  have : IsLocalizedModule 𝔭.primeCompl
      (IsScalarTower.toAlgHom B M (Localization Sp)).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  have hmem : (⟨𝔭, inferInstance⟩ : PrimeSpectrum B) ∈ Module.freeLocus B M :=
    (Module.mem_freeLocus_of_isLocalization _ (Localization.AtPrime 𝔭) (Localization Sp)
      (IsScalarTower.toAlgHom B M (Localization Sp)).toLinearMap).mpr inferInstance
  obtain ⟨_, ⟨b, rfl⟩, hb, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem
      Module.isOpen_freeLocus
  have := Module.basicOpen_subset_freeLocus_iff.mp hsub
  exact ⟨b, hb, fun 𝔮 _ h𝔮 => flat_atPrime_of_flat_away b 𝔮 h𝔮 (flat_away_of_projective b)⟩

end Ring

section Scheme

theorem isFinite_restrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (hUV : U ≤ V)
    [IsFinite (f ∣_ V)] : IsFinite (f ∣_ U) := by
  have hE : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by simpa [Scheme.Hom.image_preimage_eq_opensRange_inf]
  have : MorphismProperty.RespectsIso @IsFinite :=
    MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) => inferInstance
  exact (MorphismProperty.arrow_mk_iso_iff @IsFinite
    (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U) ≪≫ morphismRestrictEq f hE)).mp inferInstance

theorem finite_app_of_isFinite_restrict {X Y : Scheme.{u}} (p : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) [IsFinite (p ∣_ U)] : (p.app U).hom.Finite := by
  have : IsAffine U := hU
  have h := Scheme.Hom.finite_appTop (p ∣_ U)
  change ((p ∣_ U).app ⊤).hom.Finite at h
  rw [morphismRestrict_app'] at h
  rw [Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_congr _ _ (Scheme.Opens.ι_image_top U) (by simp)
    (fun φ => φ.hom.Finite)).mp h

theorem mem_basicOpen_iff_primeIdealOf {Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U)
    (y : Y) (hy : y ∈ U) (b : Γ(Y, U)) :
    y ∈ Y.basicOpen b ↔ b ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
  have := hU.isLocalization_stalk ⟨y, hy⟩
  rw [Scheme.mem_basicOpen Y b y hy]
  exact IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y) _ b

theorem stalkMap_flat_iff {X Y : Scheme.{u}} (p : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen (p ⁻¹ᵁ U)) (x : X) (hx : p x ∈ U) :
    (p.stalkMap x).hom.Flat ↔
      letI := (p.app U).hom.toAlgebra
      Module.Flat Γ(Y, U) (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal) := by
  letI := (p.app U).hom.toAlgebra
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨p x, hx⟩
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : p ⁻¹ᵁ U)
  have hlt := hU.isLocalization_stalk ⟨p x, hx⟩
  have hlx := hV.isLocalization_stalk ⟨x, hx⟩
  letI : Algebra (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) := (p.stalkMap x).hom.toAlgebra
  letI : Algebra Γ(Y, U) (X.presheaf.stalk x) :=
    ((p.stalkMap x).hom.comp (Y.presheaf.germ U (p x) hx).hom).toAlgebra
  have : IsScalarTower Γ(Y, U) (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(Y, U) Γ(X, p ⁻¹ᵁ U) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun r => Scheme.Hom.germ_stalkMap_apply p U x hx r
  change Module.Flat (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) ↔ _
  rw [Module.flat_iff_of_isLocalization (Y.presheaf.stalk (p x))
    (hU.primeIdealOf ⟨p x, hx⟩).asIdeal.primeCompl]
  let e : Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal ≃ₐ[Γ(X, p ⁻¹ᵁ U)]
      X.presheaf.stalk x :=
    IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ _
  exact ⟨fun _ => Module.Flat.of_linearEquiv (e.restrictScalars Γ(Y, U)).toLinearEquiv,
    fun _ => Module.Flat.of_linearEquiv (e.restrictScalars Γ(Y, U)).toLinearEquiv.symm⟩

theorem exists_basicOpen_flat_stalk {X Y : Scheme.{u}} (p : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen (p ⁻¹ᵁ U)) (hfin : (p.app U).hom.Finite)
    [IsNoetherianRing Γ(Y, U)] (y : Y) (hy : y ∈ U)
    (hflat : ∀ x, p x = y → (p.stalkMap x).hom.Flat) :
    ∃ b : Γ(Y, U), y ∈ Y.basicOpen b ∧ ∀ x, p x ∈ Y.basicOpen b → (p.stalkMap x).hom.Flat := by
  letI := (p.app U).hom.toAlgebra
  have : Module.Finite Γ(Y, U) Γ(X, p ⁻¹ᵁ U) := hfin
  have hcomap : ∀ x (hx : p x ∈ U), (hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap
      (algebraMap Γ(Y, U) Γ(X, p ⁻¹ᵁ U)) = (hU.primeIdealOf ⟨p x, hx⟩).asIdeal := by
    intro x hx
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := p) U hU (p ⁻¹ᵁ U) hV le_rfl hx
    rw [Scheme.Hom.appLE_eq_app] at h
    exact congrArg PrimeSpectrum.asIdeal h
  have hsub : ∀ (q q' : PrimeSpectrum Γ(X, p ⁻¹ᵁ U)), q' = q →
      Module.Flat Γ(Y, U) (Localization.AtPrime q'.asIdeal) →
      Module.Flat Γ(Y, U) (Localization.AtPrime q.asIdeal) := by
    rintro _ _ rfl h; exact h
  have hfib : ∀ (𝔮 : Ideal Γ(X, p ⁻¹ᵁ U)) [𝔮.IsPrime],
      𝔮.comap (algebraMap Γ(Y, U) Γ(X, p ⁻¹ᵁ U)) = (hU.primeIdealOf ⟨y, hy⟩).asIdeal →
      Module.Flat Γ(Y, U) (Localization.AtPrime 𝔮) := by
    intro 𝔮 _ h𝔮
    let q : PrimeSpectrum Γ(X, p ⁻¹ᵁ U) := ⟨𝔮, inferInstance⟩
    have hxV : hV.fromSpec q ∈ p ⁻¹ᵁ U := by
      rw [← SetLike.mem_coe, ← hV.range_fromSpec]; exact ⟨q, rfl⟩
    have hq : hV.primeIdealOf ⟨hV.fromSpec q, hxV⟩ = q :=
      hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨_, hxV⟩)
    have hpx : p (hV.fromSpec q) = y := by
      have h1 := hcomap _ hxV
      rw [hq] at h1
      have h2 : hU.primeIdealOf ⟨p (hV.fromSpec q), hxV⟩ = hU.primeIdealOf ⟨y, hy⟩ :=
        PrimeSpectrum.ext (h1.symm.trans h𝔮)
      have h3 := congrArg hU.fromSpec h2
      rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at h3
    exact hsub q _ hq ((stalkMap_flat_iff p U hU hV _ hxV).mp (hflat _ hpx))
  obtain ⟨b, hb, H⟩ := exists_flat_basicOpen (B := Γ(Y, U)) (M := Γ(X, p ⁻¹ᵁ U))
    (hU.primeIdealOf ⟨y, hy⟩).asIdeal hfib
  refine ⟨b, (mem_basicOpen_iff_primeIdealOf hU y hy b).mpr hb, fun x hx => ?_⟩
  have hxU : p x ∈ U := Y.basicOpen_le b hx
  rw [stalkMap_flat_iff p U hU hV x hxU]
  refine H _ fun hmem => (mem_basicOpen_iff_primeIdealOf hU (p x) hxU b).mp hx ?_
  rw [← hcomap x hxU]
  exact hmem

/-- (B') A proper morphism to a locally Noetherian scheme with a finite fibre at `t` whose stalk
maps over `t` are flat is finite over an open neighbourhood `V` of `t`, with flat stalk maps at
every point over `V`. -/
theorem exists_flat_nbhd {Z T : Scheme.{u}} (p : Z ⟶ T) [IsProper p] [IsLocallyNoetherian T]
    (t : T) (hfin : (p ⁻¹' {t}).Finite) (hflat : ∀ z, p z = t → (p.stalkMap z).hom.Flat) :
    ∃ V : T.Opens, t ∈ V ∧ IsFinite (p ∣_ V) ∧ ∀ z, p z ∈ V → (p.stalkMap z).hom.Flat := by
  obtain ⟨V1, htV1, hV1⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton p t hfin
  obtain ⟨U, hU, htU, hUV1⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens htV1
  have hU' : IsAffineOpen U := hU
  have : IsFinite (p ∣_ U) := isFinite_restrict_of_le p hUV1
  have : IsAffine U := hU'
  have hV : IsAffineOpen (p ⁻¹ᵁ U) := isAffine_of_isAffineHom (p ∣_ U)
  have : IsNoetherianRing Γ(T, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU'⟩
  obtain ⟨b, htb, H⟩ := exists_basicOpen_flat_stalk p U hU' hV
    (finite_app_of_isFinite_restrict p U hU') t htU hflat
  exact ⟨T.basicOpen b, htb, isFinite_restrict_of_le p ((T.basicOpen_le b).trans hUV1), H⟩

end Scheme

section Const

theorem flat_restrict_of_stalk {Z T : Scheme.{u}} (p : Z ⟶ T) (V : T.Opens)
    (H : ∀ z, p z ∈ V → (p.stalkMap z).hom.Flat) : Flat (p ∣_ V) :=
  Flat.of_stalkMap _ fun x =>
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff (morphismRestrictStalkMap p V x)).mpr (H x.1 x.2)

theorem finrank_pullback_eq_restrict {Z T P S : Scheme.{u}} (p : Z ⟶ T) (V : T.Opens)
    [Flat (p ∣_ V)] [IsFinite (p ∣_ V)] (fst : P ⟶ Z) (snd : P ⟶ S) (c : S ⟶ T)
    (h : IsPullback fst snd p c) (hc : Set.range c ⊆ V) (s : S) :
    ∃ a : V.toScheme, snd.finrank s = (p ∣_ V).finrank a := by
  let c' : S ⟶ V.toScheme := IsOpenImmersion.lift V.ι c (by rw [Scheme.Opens.range_ι]; exact hc)
  have hc' : c' ≫ V.ι = c := IsOpenImmersion.lift_fac _ _ _
  have hr := (isPullback_morphismRestrict p V).flip
  let fst' : P ⟶ (p ⁻¹ᵁ V).toScheme :=
    hr.lift fst (snd ≫ c') (by rw [h.w, Category.assoc, hc'])
  have e1 : fst' ≫ (p ⁻¹ᵁ V).ι = fst := hr.lift_fst _ _ _
  have h' : IsPullback fst' snd (p ∣_ V) c' := by
    refine IsPullback.of_right ?_ (hr.lift_snd _ _ _) hr
    rw [e1, hc']
    exact h
  exact ⟨c' s, Scheme.Hom.finrank_of_isPullback fst' snd (p ∣_ V) c' h' s⟩

theorem finrank_restrict_eq {Z T : Scheme.{u}} [IrreducibleSpace T] [IsLocallyNoetherian T]
    (p : Z ⟶ T) (V : T.Opens) [Flat (p ∣_ V)] [IsFinite (p ∣_ V)] (a b : V.toScheme) :
    (p ∣_ V).finrank a = (p ∣_ V).finrank b := by
  have hV : _root_.IsPreconnected (V : Set T) :=
    ((IrreducibleSpace.isIrreducible_univ (X := T)).isPreirreducible.open_subset V.2
      (Set.subset_univ _)).isPreconnected
  have : _root_.PreconnectedSpace V.toScheme := isPreconnected_iff_preconnectedSpace.mp hV
  exact (Scheme.Hom.isLocallyConstant_finrank (p ∣_ V)).apply_eq_of_preconnectedSpace a b

/-- (C') Fibre ranks of a proper family over an irreducible locally Noetherian base agree at two
points with finite fibres and flat stalk maps, read through any base changes concentrated there. -/
theorem finrank_eq_of_fibres {Z T P0 S0 P1 S1 : Scheme.{u}} (p : Z ⟶ T) [IsProper p]
    [IsLocallyNoetherian T] [IrreducibleSpace T] (t0 t1 : T)
    (hfin0 : (p ⁻¹' {t0}).Finite) (hfin1 : (p ⁻¹' {t1}).Finite)
    (hflat0 : ∀ z, p z = t0 → (p.stalkMap z).hom.Flat)
    (hflat1 : ∀ z, p z = t1 → (p.stalkMap z).hom.Flat)
    (fst0 : P0 ⟶ Z) (snd0 : P0 ⟶ S0) (c0 : S0 ⟶ T) (h0 : IsPullback fst0 snd0 p c0)
    (hc0 : ∀ s, c0 s = t0)
    (fst1 : P1 ⟶ Z) (snd1 : P1 ⟶ S1) (c1 : S1 ⟶ T) (h1 : IsPullback fst1 snd1 p c1)
    (hc1 : ∀ s, c1 s = t1) (s0 : S0) (s1 : S1) :
    snd0.finrank s0 = snd1.finrank s1 := by
  obtain ⟨V0, ht0, hfV0, hV0⟩ := exists_flat_nbhd p t0 hfin0 hflat0
  obtain ⟨V1, ht1, hfV1, hV1⟩ := exists_flat_nbhd p t1 hfin1 hflat1
  have := flat_restrict_of_stalk p V0 hV0
  have := flat_restrict_of_stalk p V1 hV1
  obtain ⟨w, hw0, hw1⟩ := nonempty_preirreducible_inter V0.2 V1.2 ⟨t0, ht0⟩ ⟨t1, ht1⟩
  let W : T.Opens := V0 ⊓ V1
  have hwW : w ∈ W := ⟨hw0, hw1⟩
  have hWr : ∀ (V : T.Opens), W ≤ V → Set.range W.ι ⊆ V := fun V hV => by
    rw [Scheme.Opens.range_ι]; exact hV
  obtain ⟨a0, e0⟩ := finrank_pullback_eq_restrict p V0 fst0 snd0 c0 h0
    (by rintro _ ⟨s, rfl⟩; rw [hc0]; exact ht0) s0
  obtain ⟨a1, e1⟩ := finrank_pullback_eq_restrict p V1 fst1 snd1 c1 h1
    (by rintro _ ⟨s, rfl⟩; rw [hc1]; exact ht1) s1
  have hpb := IsPullback.of_hasPullback p W.ι
  obtain ⟨b0, f0⟩ := finrank_pullback_eq_restrict p V0 _ _ _ hpb (hWr V0 inf_le_left)
    (⟨w, hwW⟩ : W)
  obtain ⟨b1, f1⟩ := finrank_pullback_eq_restrict p V1 _ _ _ hpb (hWr V1 inf_le_right)
    (⟨w, hwW⟩ : W)
  rw [e0, e1, finrank_restrict_eq p V0 a0 b0, finrank_restrict_eq p V1 a1 b1, ← f0, ← f1]

end Const

end RamanujanPetersson.IntersectB

end

-- ===== S4.Def_RP_JacAlg_Multiset =====
section

/-!
# Core B algebra, part 3: the multiset lemma with RH (A6, L7)

If `∏_{a ∈ A} (1 - a^m) = ∏_{b ∈ B} (1 - b^m)` for every `m ≥ 1`, the `a` are nonzero and every `b`
has `‖b‖ = r > 1`, then `A = B` (`multiset_eq_of_prod_one_sub_pow`; RH enters as `‖b‖ = r`).

Method (group rings, no analysis): put `onePoly Y = ∏_{y ∈ Y} (1 - [y])` in `ℤ[H]`.
1. `onePoly_eq_of_prod_eq`: the identity for all `m ≥ 1` gives `onePoly A = onePoly B` in `ℤ[ℂˣ]`
   (S3-ExpSum's exponential-polynomial uniqueness).
2. Push to `ℤ[Multiplicative ℝ]` along `z ↦ log ‖z‖` (a domain): `eq_replicate_of_onePoly_eq` shows
   `∏ (1 - [y]) = (1 - [c])^n` with `c > 0` forces `Y = {c, ..., c}` (lowest-term arguments
   `onePoly_coeff_inf`, `onePoly_coeff_of_lt`, then cancel one factor and induct).
3. So `‖a‖ = r` for all `a`, and the coefficients at `‖t‖ = r` are `-count t A = -count t B`.
Without RH this fails: `{2, 3, 5, 1/30}` and `{1/2, 1/3, 1/5, 30}`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open MonoidAlgebra

section Graded

variable {H : Type*} [CommGroup H] [DecidableEq H]

/-- `∏_{y ∈ Y} (1 - [y])` in the group ring `ℤ[H]`. -/
noncomputable def onePoly (Y : Multiset H) : MonoidAlgebra ℤ H :=
  (Y.map fun y => (1 - MonoidAlgebra.single y (1 : ℤ))).prod

omit [DecidableEq H] in
theorem onePoly_zero : onePoly (0 : Multiset H) = 1 := by simp [onePoly]

omit [DecidableEq H] in
theorem onePoly_cons (y : H) (Y : Multiset H) :
    onePoly (y ::ₘ Y) = (1 - MonoidAlgebra.single y (1 : ℤ)) * onePoly Y := by
  simp [onePoly]

theorem coeff_one_apply (t : H) : (1 : MonoidAlgebra ℤ H).coeff t = if t = 1 then 1 else 0 := by
  rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp only [eq_comm]

omit [DecidableEq H] in
theorem coeff_one_sub_mul (y t : H) (P : MonoidAlgebra ℤ H) :
    ((1 - MonoidAlgebra.single y (1 : ℤ)) * P).coeff t = P.coeff t - P.coeff (y⁻¹ * t) := by
  rw [sub_mul, one_mul, MonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    MonoidAlgebra.coeff_single_mul_apply, one_mul]

variable (φ : H → ℝ) (hφ : ∀ x y, φ (x * y) = φ x + φ y)
include hφ

omit [DecidableEq H] in
theorem grade_one : φ 1 = 0 := by
  have := hφ 1 1
  rw [one_mul] at this
  linarith

omit [DecidableEq H] in
theorem grade_inv_mul (y t : H) : φ (y⁻¹ * t) = φ t - φ y := by
  have := hφ y (y⁻¹ * t)
  rw [mul_inv_cancel_left] at this
  linarith

/-- Lowest terms when every `φ y ≥ μ > 0`: below `μ` only the constant `1`, at height `μ` the
coefficient of `t` is `-count t Y`. -/
theorem onePoly_coeff_of_lt {μ : ℝ} (hμ : 0 < μ) (Y : Multiset H) (hY : ∀ y ∈ Y, μ ≤ φ y) :
    (∀ t, φ t < μ → (onePoly Y).coeff t = if t = 1 then 1 else 0) ∧
    (∀ t, φ t = μ → (onePoly Y).coeff t = -(Y.count t : ℤ)) := by
  induction Y using Multiset.induction_on with
  | empty =>
    refine ⟨fun t _ => by rw [onePoly_zero, coeff_one_apply], fun t ht => ?_⟩
    have h1 : t ≠ 1 := by
      intro h
      rw [h, grade_one φ hφ] at ht
      linarith
    simp [onePoly_zero, coeff_one_apply, h1]
  | cons y Y ih =>
    have hy := hY y (Multiset.mem_cons.2 (Or.inl rfl))
    obtain ⟨ih1, ih2⟩ := ih (fun z hz => hY z (Multiset.mem_cons_of_mem hz))
    rw [onePoly_cons]
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have hne : y⁻¹ * t ≠ 1 := by
        intro h
        have := congrArg φ h
        rw [grade_inv_mul φ hφ, grade_one φ hφ] at this
        linarith
      rw [coeff_one_sub_mul, ih1 t ht,
        ih1 (y⁻¹ * t) (by rw [grade_inv_mul φ hφ]; linarith), if_neg hne, sub_zero]
    · rw [coeff_one_sub_mul, ih2 t ht, ih1 (y⁻¹ * t) (by rw [grade_inv_mul φ hφ]; linarith),
        Multiset.count_cons]
      by_cases h : t = y
      · subst h
        simp only [inv_mul_cancel, if_true]
        push_cast
        ring
      · have hne : y⁻¹ * t ≠ 1 := by
          rw [ne_eq, inv_mul_eq_one]
          exact fun h' => h h'.symm
        simp [h, hne]

/-- The lowest term of `onePoly Y` when no `φ y` is `0`: it sits at height `σ ≤ 0`, and `σ = 0`
only when every `φ y > 0`. -/
theorem onePoly_coeff_inf (Y : Multiset H) (hY : ∀ y ∈ Y, φ y ≠ 0) :
    ∃ σ : ℝ, σ ≤ 0 ∧ (σ = 0 → ∀ y ∈ Y, 0 < φ y) ∧ (∃ t, φ t = σ ∧ (onePoly Y).coeff t ≠ 0) ∧
      ∀ t, φ t < σ → (onePoly Y).coeff t = 0 := by
  induction Y using Multiset.induction_on with
  | empty =>
    refine ⟨0, le_rfl, fun _ y hy => by simp at hy, ⟨1, grade_one φ hφ, ?_⟩, fun t ht => ?_⟩
    · simp [onePoly_zero]
    · have h1 : t ≠ 1 := by
        intro h
        rw [h, grade_one φ hφ] at ht
        exact lt_irrefl _ ht
      simp [onePoly_zero, coeff_one_apply, h1]
  | cons y Y ih =>
    obtain ⟨σ, hσ, h0, ⟨t₀, ht₀, hc⟩, hlow⟩ :=
      ih (fun z hz => hY z (Multiset.mem_cons_of_mem hz))
    rcases lt_or_gt_of_ne (hY y (Multiset.mem_cons.2 (Or.inl rfl))) with hneg | hpos
    · refine ⟨φ y + σ, by linarith, fun h => by linarith, ⟨y * t₀, by rw [hφ, ht₀], ?_⟩,
        fun t ht => ?_⟩
      · rw [onePoly_cons, coeff_one_sub_mul, inv_mul_cancel_left,
          hlow (y * t₀) (by rw [hφ, ht₀]; linarith), zero_sub, neg_ne_zero]
        exact hc
      · rw [onePoly_cons, coeff_one_sub_mul, hlow t (by linarith),
          hlow (y⁻¹ * t) (by rw [grade_inv_mul φ hφ]; linarith), sub_zero]
    · refine ⟨σ, hσ, fun h z hz => ?_, ⟨t₀, ht₀, ?_⟩, fun t ht => ?_⟩
      · rcases Multiset.mem_cons.1 hz with rfl | hz
        · exact hpos
        · exact h0 h z hz
      · rw [onePoly_cons, coeff_one_sub_mul,
          hlow (y⁻¹ * t₀) (by rw [grade_inv_mul φ hφ, ht₀]; linarith), sub_zero]
        exact hc
      · rw [onePoly_cons, coeff_one_sub_mul, hlow t ht,
          hlow (y⁻¹ * t) (by rw [grade_inv_mul φ hφ]; linarith), sub_zero]

end Graded

/-! ### Step 2: in `ℤ[Multiplicative ℝ]`, `∏ (1 - [y]) = (1 - [c])^n` forces `Y = {c, ..., c}` -/

section Real


theorem toAdd_hom : ∀ x y : (Multiplicative ℝ), Multiplicative.toAdd (x * y) =
    Multiplicative.toAdd x + Multiplicative.toAdd y := fun _ _ => rfl

theorem one_sub_single_ne_zero (c : (Multiplicative ℝ)) (hc : c ≠ 1) :
    (1 - MonoidAlgebra.single c (1 : ℤ) : MonoidAlgebra ℤ (Multiplicative ℝ)) ≠ 0 := by
  intro h
  have := congrArg (fun f : MonoidAlgebra ℤ (Multiplicative ℝ) => f.coeff 1) h
  simp [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_single,
    hc] at this

theorem rep_coeff_of_lt {c : (Multiplicative ℝ)} (hc : 0 < Multiplicative.toAdd c) (n : ℕ) (t : (Multiplicative ℝ))
    (ht : Multiplicative.toAdd t < Multiplicative.toAdd c) :
    (onePoly (Multiset.replicate n c)).coeff t = if t = 1 then 1 else 0 :=
  (onePoly_coeff_of_lt _ toAdd_hom hc _
    (fun y hy => by rw [Multiset.eq_of_mem_replicate hy])).1 t ht

theorem rep_coeff_self {c : (Multiplicative ℝ)} (hc : 0 < Multiplicative.toAdd c) (n : ℕ) :
    (onePoly (Multiset.replicate n c)).coeff c = -(n : ℤ) := by
  rw [(onePoly_coeff_of_lt _ toAdd_hom hc _
    (fun y hy => by rw [Multiset.eq_of_mem_replicate hy])).2 c rfl, Multiset.count_replicate_self]

theorem ne_one_of_toAdd_ne {t : (Multiplicative ℝ)} (ht : Multiplicative.toAdd t ≠ 0) : t ≠ 1 := by
  rintro rfl
  exact ht rfl

theorem eq_replicate_of_onePoly_eq {c : (Multiplicative ℝ)} (hc : 0 < Multiplicative.toAdd c) :
    ∀ (k : ℕ) (Y : Multiset (Multiplicative ℝ)) (n : ℕ), Multiset.card Y = k →
      onePoly Y = onePoly (Multiset.replicate n c) → Y = Multiset.replicate n c := by
  have hc1 : c ≠ 1 := ne_one_of_toAdd_ne hc.ne'
  intro k
  induction k with
  | zero =>
    intro Y n hk h
    rw [Multiset.card_eq_zero] at hk
    subst hk
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rfl
    · exfalso
      have e := rep_coeff_self hc n
      rw [← h, onePoly_zero, coeff_one_apply, if_neg hc1] at e
      omega
  | succ k ih =>
    intro Y n hk h
    have hY0 : ∀ y ∈ Y, Multiplicative.toAdd y ≠ 0 := by
      intro y hy hy0
      have hy1 : y = 1 := by rw [← ofAdd_toAdd y, hy0, ofAdd_zero]
      have h0 : onePoly Y = 0 := by
        unfold onePoly
        apply Multiset.prod_eq_zero
        rw [Multiset.mem_map]
        refine ⟨y, hy, ?_⟩
        show (1 : MonoidAlgebra ℤ (Multiplicative ℝ)) - MonoidAlgebra.single y 1 = 0
        rw [hy1, ← MonoidAlgebra.one_def, sub_self]
      have e := rep_coeff_of_lt hc n 1 (by simpa using hc)
      rw [← h, h0, if_pos rfl] at e
      simp at e
    have hpos : ∀ y ∈ Y, 0 < Multiplicative.toAdd y := by
      obtain ⟨σ, hσ, h0, ⟨t₀, ht₀, hcoef⟩, -⟩ := onePoly_coeff_inf _ toAdd_hom Y hY0
      rcases hσ.lt_or_eq with hlt | heq
      · exfalso
        have ht1 : t₀ ≠ 1 := ne_one_of_toAdd_ne (by rw [ht₀]; exact hlt.ne)
        have e := rep_coeff_of_lt hc n t₀ (by rw [ht₀]; linarith)
        rw [← h, if_neg ht1] at e
        exact hcoef e
      · exact h0 heq
    have hYne : Y ≠ 0 := by
      intro h0
      rw [h0] at hk
      simp at hk
    obtain ⟨y₀, hy₀, hmin⟩ := Finset.exists_min_image Y.toFinset Multiplicative.toAdd
      (Multiset.toFinset_nonempty.2 hYne)
    rw [Multiset.mem_toFinset] at hy₀
    have hμ := hpos y₀ hy₀
    obtain ⟨hY1, hY2⟩ := onePoly_coeff_of_lt _ toAdd_hom hμ Y
      (fun y hy => hmin y (Multiset.mem_toFinset.2 hy))
    have hy₀c : (onePoly Y).coeff y₀ ≠ 0 := by
      rw [hY2 y₀ rfl, neg_ne_zero, Nat.cast_ne_zero]
      exact Multiset.count_ne_zero.2 hy₀
    have hy₀1 : y₀ ≠ 1 := ne_one_of_toAdd_ne hμ.ne'
    rcases lt_trichotomy (Multiplicative.toAdd y₀) (Multiplicative.toAdd c) with hlt | heq | hgt
    · exfalso
      apply hy₀c
      rw [h, rep_coeff_of_lt hc n y₀ hlt, if_neg hy₀1]
    · have hyc : y₀ = c := Multiplicative.toAdd.injective heq
      subst hyc
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
        rcases n with _ | n'
        · exfalso
          apply hy₀c
          rw [h, rep_coeff_self hc 0]
          simp
        · exact ⟨n', rfl⟩
      have hYe := Multiset.cons_erase hy₀
      rw [← hYe, onePoly_cons, Multiset.replicate_succ, onePoly_cons] at h
      have h' := mul_left_cancel₀ (one_sub_single_ne_zero _ hc1) h
      have hcard : Multiset.card (Y.erase y₀) = k := by
        rw [Multiset.card_erase_of_mem hy₀, hk]
        rfl
      rw [← hYe, ih _ _ hcard h', Multiset.replicate_succ]
    · exfalso
      have h1 := hY1 c hgt
      rw [h, rep_coeff_self hc n, if_neg hc1, neg_eq_zero, Nat.cast_eq_zero] at h1
      subst h1
      apply hy₀c
      rw [h, Multiset.replicate_zero, onePoly_zero, coeff_one_apply, if_neg hy₀1]

end Real

/-! ### Steps 1 and 3: from `ℂ` to the group rings and back -/

section Complex

/-- Evaluation `[z] ↦ z^m` on `ℤ[ℂˣ]`. -/
noncomputable def evPow (m : ℕ) : MonoidAlgebra ℤ ℂˣ →ₐ[ℤ] ℂ :=
  MonoidAlgebra.lift ℤ ℂ ℂˣ ((powMonoidHom m).comp (Units.coeHom ℂ))

theorem evPow_onePoly (m : ℕ) (Y : Multiset ℂˣ) :
    evPow m (onePoly Y) = (Y.map fun y : ℂˣ => 1 - (y : ℂ) ^ m).prod := by
  rw [onePoly, map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro y _
  simp [evPow, MonoidAlgebra.lift_single]

theorem evPow_apply (m : ℕ) (f : MonoidAlgebra ℤ ℂˣ) :
    evPow m f = ∑ w ∈ f.coeff.support, (f.coeff w : ℂ) * (w : ℂ) ^ m := by
  rw [evPow, MonoidAlgebra.lift_apply', Finsupp.sum]
  simp

theorem eq_zero_of_evPow (f : MonoidAlgebra ℤ ℂˣ) (h : ∀ m : ℕ, 1 ≤ m → evPow m f = 0) :
    f = 0 := by
  classical
  let cf : ℂ → ℂ := fun z => if hz : z = 0 then 0 else (f.coeff (Units.mk0 z hz) : ℂ)
  have hcf : ∀ w : ℂˣ, cf w = (f.coeff w : ℂ) := fun w => by simp [cf, w.ne_zero]
  have key := RamanujanPetersson.ExpSum.expSum_coeff_eq_zero_of_ne_zero
    (f.coeff.support.map ⟨Units.val, Units.val_injective⟩) cf (fun m hm => by
      rw [Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, hcf]
      rw [← evPow_apply]
      exact h m hm)
  rw [← MonoidAlgebra.coeff_eq_zero]
  ext w
  by_contra hw
  have e := key (w : ℂ) (Finset.mem_map_of_mem _ (Finsupp.mem_support_iff.2 hw)) w.ne_zero
  rw [hcf, Int.cast_eq_zero] at e
  exact hw e

/-- Step 1: the identity for all `m ≥ 1` is an identity in `ℤ[ℂˣ]`. -/
theorem onePoly_eq_of_prod_eq (A B : Multiset ℂˣ)
    (h : ∀ m : ℕ, 1 ≤ m →
      (A.map fun a : ℂˣ => 1 - (a : ℂ) ^ m).prod = (B.map fun b : ℂˣ => 1 - (b : ℂ) ^ m).prod) :
    onePoly A = onePoly B := by
  rw [← sub_eq_zero]
  apply eq_zero_of_evPow
  intro m hm
  rw [map_sub, evPow_onePoly, evPow_onePoly, h m hm, sub_self]

/-- `z ↦ log ‖z‖` as a hom `ℂˣ →* Multiplicative ℝ`. -/
noncomputable def logNorm : ℂˣ →* Multiplicative ℝ where
  toFun z := Multiplicative.ofAdd (Real.log ‖(z : ℂ)‖)
  map_one' := by simp
  map_mul' x y := by
    rw [Units.val_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 x.ne_zero) (norm_ne_zero_iff.2 y.ne_zero), ofAdd_add]

theorem logNorm_hom (x y : ℂˣ) :
    Real.log ‖((x * y : ℂˣ) : ℂ)‖ = Real.log ‖(x : ℂ)‖ + Real.log ‖(y : ℂ)‖ := by
  rw [Units.val_mul, norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 x.ne_zero) (norm_ne_zero_iff.2 y.ne_zero)]

theorem mapDomain_onePoly (Y : Multiset ℂˣ) :
    MonoidAlgebra.mapDomainRingHom ℤ logNorm (onePoly Y) = onePoly (Y.map logNorm) := by
  rw [onePoly, onePoly, map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro y _
  simp only [Function.comp_apply, map_sub, map_one]
  congr 1
  exact MonoidAlgebra.mapDomain_single

/-- **A6 over `ℂˣ`.** -/
theorem units_multiset_eq (A B : Multiset ℂˣ) {r : ℝ} (hr : 1 < r)
    (hB : ∀ b ∈ B, ‖(b : ℂ)‖ = r)
    (h : ∀ m : ℕ, 1 ≤ m →
      (A.map fun a : ℂˣ => 1 - (a : ℂ) ^ m).prod = (B.map fun b : ℂˣ => 1 - (b : ℂ) ^ m).prod) :
    A = B := by
  have h1 := onePoly_eq_of_prod_eq A B h
  have hμ : 0 < Real.log r := Real.log_pos hr
  have hc : 0 < Multiplicative.toAdd (Multiplicative.ofAdd (Real.log r)) := hμ
  have hBc : B.map logNorm =
      Multiset.replicate (Multiset.card B) (Multiplicative.ofAdd (Real.log r)) := by
    rw [Multiset.eq_replicate]
    refine ⟨Multiset.card_map _ _, fun x hx => ?_⟩
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hx
    show Multiplicative.ofAdd (Real.log ‖(b : ℂ)‖) = _
    rw [hB b hb]
  have h2 : onePoly (A.map logNorm) =
      onePoly (Multiset.replicate (Multiset.card B) (Multiplicative.ofAdd (Real.log r))) := by
    rw [← hBc, ← mapDomain_onePoly, ← mapDomain_onePoly, h1]
  have hA := eq_replicate_of_onePoly_eq hc _ _ _ rfl h2
  have hAeq : ∀ a ∈ A, Real.log ‖(a : ℂ)‖ = Real.log r := by
    intro a ha
    have e := Multiset.eq_of_mem_replicate (hA ▸ Multiset.mem_map_of_mem logNorm ha)
    exact congrArg Multiplicative.toAdd e
  have hBeq : ∀ b ∈ B, Real.log ‖(b : ℂ)‖ = Real.log r := fun b hb => by rw [hB b hb]
  ext t
  by_cases ht : Real.log ‖(t : ℂ)‖ = Real.log r
  · have eA := (onePoly_coeff_of_lt (fun z : ℂˣ => Real.log ‖(z : ℂ)‖) logNorm_hom hμ A
      (fun a ha => (hAeq a ha).ge)).2 t ht
    have eB := (onePoly_coeff_of_lt (fun z : ℂˣ => Real.log ‖(z : ℂ)‖) logNorm_hom hμ B
      (fun b hb => (hBeq b hb).ge)).2 t ht
    rw [h1, eB, neg_inj, Nat.cast_inj] at eA
    exact eA.symm
  · rw [Multiset.count_eq_zero.2 (fun ht' => ht (hAeq t ht')),
      Multiset.count_eq_zero.2 (fun ht' => ht (hBeq t ht'))]

/-- **A6 (L7), the multiset lemma with RH.** If `∏_{a ∈ A} (1 - a^m) = ∏_{b ∈ B} (1 - b^m)` for all
`m ≥ 1`, `0 ∉ A` and `‖b‖ = r > 1` for every `b ∈ B`, then `A = B`. -/
theorem multiset_eq_of_prod_one_sub_pow (A B : Multiset ℂ) {r : ℝ} (hr : 1 < r)
    (hA : (0 : ℂ) ∉ A) (hB : ∀ b ∈ B, ‖b‖ = r)
    (h : ∀ m : ℕ, 1 ≤ m → (A.map fun a => 1 - a ^ m).prod = (B.map fun b => 1 - b ^ m).prod) :
    A = B := by
  classical
  let u : ℂ → ℂˣ := fun z => if hz : z = 0 then 1 else Units.mk0 z hz
  have hu : ∀ S : Multiset ℂ, (0 : ℂ) ∉ S → (S.map u).map (fun w : ℂˣ => (w : ℂ)) = S := by
    intro S hS
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id S]
    apply Multiset.map_congr rfl
    intro z hz
    have hz0 : z ≠ 0 := fun h0 => hS (h0 ▸ hz)
    simp [u, hz0]
  have hB0 : (0 : ℂ) ∉ B := by
    intro h0
    have e := hB 0 h0
    rw [norm_zero] at e
    linarith
  have hprod : ∀ S : Multiset ℂ, (0 : ℂ) ∉ S → ∀ m : ℕ,
      ((S.map u).map fun a : ℂˣ => 1 - (a : ℂ) ^ m).prod = (S.map fun a => 1 - a ^ m).prod := by
    intro S hS m
    rw [Multiset.map_map]
    conv_rhs => rw [← hu S hS, Multiset.map_map, Multiset.map_map]
    rfl
  have key := units_multiset_eq (A.map u) (B.map u) hr
    (fun b hb => by
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hb
      have hz0 : z ≠ 0 := fun h0 => hB0 (h0 ▸ hz)
      simp [u, hz0, hB z hz])
    (fun m hm => by rw [hprod A hA, hprod B hB0]; exact h m hm)
  rw [← hu A hA, ← hu B hB0, key]

/-- The same with `‖b‖ = √q`, `q > 1` (the RH shape of S3-ZetaSB). -/
theorem multiset_eq_of_prod_one_sub_pow_sqrt (A B : Multiset ℂ) {q : ℝ} (hq : 1 < q)
    (hA : (0 : ℂ) ∉ A) (hB : ∀ b ∈ B, ‖b‖ = Real.sqrt q)
    (h : ∀ m : ℕ, 1 ≤ m → (A.map fun a => 1 - a ^ m).prod = (B.map fun b => 1 - b ^ m).prod) :
    A = B := by
  refine multiset_eq_of_prod_one_sub_pow A B ?_ hA hB h
  rw [← Real.sqrt_one]
  exact Real.sqrt_lt_sqrt zero_le_one hq

end Complex

end RamanujanPetersson.JacAlg

end

-- ===== S4.Def_RP_JacAlg_Res =====
section

/-!
# Core B algebra, part 7: resultants (unit S4-JacAlg, lemma L4 = Milne 10.21, steps R1 and R2)

* R1 `det_aeval_eq_resultant`: for a square matrix `A` over a domain, `det F(A) = Res(χ_A, F)` (degree
  parameters `card n`, `natDegree F`); `linearMap_det_aeval_eq_resultant`: the same for an endomorphism of a
  free finite module (parameters `finrank`, `natDegree F`).
* R2 `eq_of_norm_resultant_eq`: over an ultrametric nontrivially normed field, monic `P, Q` with
  `‖Res(P, G)‖ = ‖Res(Q, G)‖` for all `G` are equal. For a monic irreducible `φ` with `P = φ^d P₁`, `φ ∤ P₁`,
  `‖Res(P, φ + c)‖ = ‖c‖^(d deg φ) · ‖Res(P₁, φ)‖` for small `c` (`exists_norm_resultant_add_C`) reads off `d`;
  equal multiplicities give equal normalized factors. Milne's Lemma 10.21 without a Galois closure.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Polynomial UniqueFactorizationMonoid

section Det

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma det_sub_algebraMap {K : Type*} [CommRing K] (A : Matrix n n K) (r : K) :
    (A - algebraMap K (Matrix n n K) r).det = (-1) ^ Fintype.card n * A.charpoly.eval r := by
  rw [Matrix.eval_charpoly, ← Matrix.det_neg, neg_sub]
  congr 2

theorem det_aeval_eq_resultant_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    (A : Matrix n n K) (F : K[X]) :
    (aeval A F).det = resultant A.charpoly F (Fintype.card n) F.natDegree := by
  have hF : F.Splits := IsAlgClosed.splits F
  have hcard : Multiset.card F.roots = F.natDegree := hF.natDegree_eq_card_roots.symm
  rw [resultant_comm, resultant_eq_prod_eval F A.charpoly _ (Matrix.charpoly_natDegree_eq_dim A).le hF]
  let ψ : K[X] →* K := Matrix.detMonoidHom.comp (aeval A).toRingHom.toMonoidHom
  have hψ : ∀ G : K[X], ψ G = (aeval A G).det := fun G => rfl
  rw [← hψ]
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
  rw [map_mul, map_multiset_prod, Multiset.map_map, hψ, aeval_C, Algebra.algebraMap_eq_smul_one,
    Matrix.det_smul, Matrix.det_one, mul_one]
  have h1 : ∀ a : K, (⇑ψ ∘ fun a => X - C a) a =
      (-1) ^ Fintype.card n * A.charpoly.eval a := by
    intro a
    show (aeval A (X - C a)).det = _
    rw [map_sub, aeval_X, aeval_C, det_sub_algebraMap]
  rw [Multiset.map_congr rfl (fun a _ => h1 a), Multiset.prod_map_mul, Multiset.map_const',
    Multiset.prod_replicate, hcard, ← pow_mul]
  ring

theorem det_aeval_eq_resultant {R : Type*} [CommRing R] [IsDomain R] (A : Matrix n n R) (F : R[X]) :
    (aeval A F).det = resultant A.charpoly F (Fintype.card n) F.natDegree := by
  let L := AlgebraicClosure (FractionRing R)
  let φ : R →+* L := (algebraMap (FractionRing R) L).comp (algebraMap R (FractionRing R))
  have hφ : Function.Injective φ :=
    (algebraMap (FractionRing R) L).injective.comp (IsFractionRing.injective R (FractionRing R))
  apply hφ
  have hmap : φ.mapMatrix (aeval A F) = aeval (φ.mapMatrix A) (F.map φ) := by
    refine map_aeval_eq_aeval_map ?_ F A
    ext r i j
    simp only [RingHom.comp_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp
  rw [RingHom.map_det, hmap, det_aeval_eq_resultant_of_isAlgClosed, ← resultant_map_map,
    RingHom.mapMatrix_apply, Matrix.charpoly_map, natDegree_map_eq_of_injective hφ]

theorem linearMap_det_aeval_eq_resultant {R : Type*} [CommRing R] [IsDomain R] {T : Type*}
    [AddCommGroup T] [Module R T] [Module.Free R T] [Module.Finite R T] (M : Module.End R T)
    (F : R[X]) :
    LinearMap.det (aeval M F) = resultant M.charpoly F (Module.finrank R T) F.natDegree := by
  let b := Module.Free.chooseBasis R T
  have hM : LinearMap.toMatrix b b (aeval M F) = aeval (LinearMap.toMatrix b b M) F := by
    have h := aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b) M F
    have he : ∀ f : Module.End R T, LinearMap.toMatrixAlgEquiv b f = LinearMap.toMatrix b b f :=
      fun f => Matrix.ext fun i j => by
        simp [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
    rw [he, he] at h
    exact h.symm
  rw [← LinearMap.det_toMatrix b, ← LinearMap.charpoly_toMatrix M b,
    Module.finrank_eq_card_chooseBasisIndex, hM, det_aeval_eq_resultant]

end Det

/-- For monic `P` the resultant `Res(P, G, deg P, n)` does not depend on `n ≥ deg G`. -/
lemma resultant_monic_eq {R : Type*} [CommRing R] {P G : R[X]} (hP : P.Monic) {n : ℕ} (hn : G.natDegree ≤ n) :
    resultant P G P.natDegree n = resultant P G := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [resultant_add_right_deg P G P.natDegree G.natDegree k le_rfl, hP.coeff_natDegree, one_pow,
    one_mul]

section Field

variable {K : Type*} [Field K]

/-- `Res(φ, φ + c) = c ^ deg φ` for monic `φ`. -/
lemma resultant_self_add_C {φ : K[X]} (hφ : φ.Monic) (c : K) :
    resultant φ (φ + C c) φ.natDegree φ.natDegree = c ^ φ.natDegree := by
  have h := resultant_add_mul_right φ (C c) 1 φ.natDegree φ.natDegree (by simp) le_rfl
  rw [mul_one, add_comm] at h
  rw [h, resultant_C_right, hφ.coeff_natDegree, one_pow, one_mul]

lemma count_normalizedFactors_of_decomp [DecidableEq K] {φ P c : K[X]} {d : ℕ} (hirr : Irreducible φ)
    (hnorm : normalize φ = φ) (hP : P = φ ^ d * c) (hc : ¬ φ ∣ c) :
    (normalizedFactors P).count φ = d := by
  refine count_normalizedFactors_eq hirr hnorm (hP ▸ dvd_mul_right _ _) ?_
  intro h
  rw [hP, pow_succ] at h
  exact hc ((mul_dvd_mul_iff_left (pow_ne_zero _ hirr.ne_zero)).mp h)

end Field

section Ultra

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- Near `c = 0`: `‖Res(P, φ + c)‖ = ‖c‖ ^ (deg φ · d) · A` with `A > 0`, when `P = φ^d P₁` and `φ ∤ P₁`. -/
lemma exists_norm_resultant_add_C {P φ P₁ : K[X]} {d : ℕ} (hP : P.Monic) (hφ : φ.Monic)
    (hirr : Irreducible φ) (hdec : P = φ ^ d * P₁) (hnd : ¬ φ ∣ P₁) :
    ∃ A > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ c : K, ‖c‖ < δ →
      ‖resultant P (φ + C c)‖ = ‖c‖ ^ (φ.natDegree * d) * A := by
  have hP₁ : P₁.Monic := (hφ.pow d).of_mul_monic_left (hdec ▸ hP)
  -- the resultant `Res(P₁, φ + c)` as a polynomial in `c`
  obtain ⟨R, hR⟩ : ∃ R : K[X], R = resultant (P₁.map C) (φ.map C + C X) P₁.natDegree φ.natDegree :=
    ⟨_, rfl⟩
  have hev : ∀ c : K, R.eval c = resultant P₁ (φ + C c) P₁.natDegree φ.natDegree := by
    intro c
    rw [hR, ← coe_evalRingHom, ← resultant_map_map]
    congr 1
    · ext i; simp [coeff_map]
    · ext i; simp [coeff_map, Polynomial.map_map]
  have hR0 : R.eval 0 ≠ 0 := by
    rw [hev, map_zero, add_zero]
    exact resultant_ne_zero P₁ φ ((hirr.coprime_iff_not_dvd).mpr hnd).symm
  have hA : 0 < ‖R.eval 0‖ := norm_pos_iff.mpr hR0
  obtain ⟨δ, hδ, hcont⟩ :=
    Metric.continuousAt_iff.mp (R.continuous.continuousAt : ContinuousAt (fun x => R.eval x) 0) _ hA
  refine ⟨‖R.eval 0‖, hA, δ, hδ, fun c hc => ?_⟩
  have hnear : ‖R.eval c‖ = ‖R.eval 0‖ := by
    have h1 : ‖R.eval c - R.eval 0‖ < ‖R.eval 0‖ := by
      rw [← dist_eq_norm]; exact hcont (by rwa [dist_zero_right])
    have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne
    rw [sub_add_cancel] at h2
    rw [h2, max_eq_right h1.le]
  have hdeg : P.natDegree = (φ ^ d).natDegree + P₁.natDegree := by
    rw [hdec, (hφ.pow d).natDegree_mul hP₁]
  have hG : (φ + C c).natDegree ≤ φ.natDegree := by rw [natDegree_add_C]
  have hsplit : resultant P (φ + C c) = (c ^ φ.natDegree) ^ d * R.eval c := by
    rw [← resultant_monic_eq hP hG, hdeg]
    conv_lhs => rw [hdec]
    rw [resultant_mul_left _ _ _ _ hG,
      resultant_pow_left φ (φ + C c) d φ.natDegree (by simp [hφ.leadingCoeff]) hG,
      resultant_self_add_C hφ, ← hev]
  rw [hsplit, norm_mul, hnear, norm_pow, norm_pow, ← pow_mul]

/-- **Milne Lemma 10.21 (resultant form).** Monic polynomials over an ultrametric nontrivially normed field
with `‖Res(P, G)‖ = ‖Res(Q, G)‖` for all `G` are equal. -/
theorem eq_of_norm_resultant_eq {P Q : K[X]} (hP : P.Monic) (hQ : Q.Monic)
    (H : ∀ G : K[X], ‖resultant P G‖ = ‖resultant Q G‖) : P = Q := by
  classical
  -- equal multiplicity of every monic irreducible factor
  have key : ∀ φ : K[X], φ.Monic → Irreducible φ → ∀ (d e : ℕ) (P₁ Q₁ : K[X]), P = φ ^ d * P₁ →
      ¬ φ ∣ P₁ → Q = φ ^ e * Q₁ → ¬ φ ∣ Q₁ → d = e := by
    intro φ hφ hirr d e P₁ Q₁ hPd hP₁ hQe hQ₁
    obtain ⟨A, hA, δ, hδ, hPn⟩ := exists_norm_resultant_add_C hP hφ hirr hPd hP₁
    obtain ⟨B, hB, δ', hδ', hQn⟩ := exists_norm_resultant_add_C hQ hφ hirr hQe hQ₁
    obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt K (lt_min (lt_min hδ hδ') one_pos)
    have hc1 : ‖c‖ < 1 := hc.trans_le (min_le_right _ _)
    have hcδ : ‖c‖ < δ := hc.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hcδ' : ‖c‖ < δ' := hc.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hc2 : ‖c ^ 2‖ ≤ ‖c‖ := by
      rw [norm_pow, sq]; exact mul_le_of_le_one_left hc0.le hc1.le
    have h1 := H (φ + C c)
    rw [hPn c hcδ, hQn c hcδ'] at h1
    have h2 := H (φ + C (c ^ 2))
    rw [hPn _ (hc2.trans_lt hcδ), hQn _ (hc2.trans_lt hcδ'), norm_pow, ← pow_mul, ← pow_mul] at h2
    set x := ‖c‖
    set a := φ.natDegree * d
    set b := φ.natDegree * e
    -- h1 : x^a A = x^b B,  h2 : x^(2a) A = x^(2b) B
    have h3 : x ^ (2 * b) * B = x ^ (a + b) * B := by
      rw [← h2, two_mul, pow_add, mul_assoc, h1, ← mul_assoc, ← pow_add]
    have h4 : 2 * b = a + b := pow_right_injective₀ hc0 hc1.ne (mul_right_cancel₀ hB.ne' h3)
    have hab : a = b := by omega
    exact Nat.eq_of_mul_eq_mul_left (Irreducible.natDegree_pos hirr) hab
  -- equal normalized factors
  have hcount : ∀ φ ∈ normalizedFactors P ∪ normalizedFactors Q,
      (normalizedFactors P).count φ = (normalizedFactors Q).count φ := by
    intro φ hmem
    have hmem' : φ ∈ normalizedFactors P ∨ φ ∈ normalizedFactors Q := Multiset.mem_union.mp hmem
    have hirr : Irreducible φ := by
      rcases hmem' with h | h <;> exact irreducible_of_normalized_factor φ h
    have hnorm : normalize φ = φ := by
      rcases hmem' with h | h <;> exact normalize_normalized_factor φ h
    have hφ : φ.Monic := hnorm ▸ monic_normalize hirr.ne_zero
    have hfin : ∀ S : K[X], S ≠ 0 → FiniteMultiplicity φ S := fun S hS =>
      finiteMultiplicity_of_degree_pos_of_monic (degree_pos_of_irreducible hirr) hφ hS
    obtain ⟨P₁, hPd, hP₁⟩ := (hfin P hP.ne_zero).exists_eq_pow_mul_and_not_dvd
    obtain ⟨Q₁, hQe, hQ₁⟩ := (hfin Q hQ.ne_zero).exists_eq_pow_mul_and_not_dvd
    rw [count_normalizedFactors_of_decomp hirr hnorm hPd hP₁,
      count_normalizedFactors_of_decomp hirr hnorm hQe hQ₁]
    exact key φ hφ hirr _ _ P₁ Q₁ hPd hP₁ hQe hQ₁
  have hnf : normalizedFactors P = normalizedFactors Q := by
    ext φ
    by_cases hmem : φ ∈ normalizedFactors P ∪ normalizedFactors Q
    · exact hcount φ hmem
    · rw [Multiset.mem_union, not_or] at hmem
      rw [Multiset.count_eq_zero.mpr hmem.1, Multiset.count_eq_zero.mpr hmem.2]
  have hassoc : Associated P Q :=
    (prod_normalizedFactors hP.ne_zero).symm.trans (hnf ▸ prod_normalizedFactors hQ.ne_zero)
  exact eq_of_monic_of_associated hP hQ hassoc

end Ultra

end RamanujanPetersson.JacAlg

end


