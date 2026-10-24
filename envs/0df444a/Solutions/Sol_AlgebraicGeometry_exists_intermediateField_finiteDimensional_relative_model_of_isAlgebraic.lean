-- Prove2me | solution 1 for AlgebraicGeometry.exists_intermediateField_finiteDimensional_relative_model_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-24T00:08:27.148044+00:00
-- url     : https://prove2.me/submissions/4a7c08f0-2285-40c6-8dd1-19e9b048675a

/-
The open, isomorphism, morphism and gluing constructions below generalize the
accepted Prove2Me sources 55fe5d4b-b198-5f6d-9cfa-aca080243121,
053e91e1-cf68-5cc1-a30b-796cc221bea5, f910075b-201e-550e-9756-da1c73c02076
and 3bc798c4-6b03-5471-aee2-8579181005bf from universe zero to arbitrary universes.
The original accepted sources and submission ids are archived with this work.
-/
import Definitions.Def_P2M_Util
import Mathlib
import Theorems.Thm_Algebra_exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic

universe u
set_option linter.style.haveILetI false



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_preimage_pullback_map_eq_of_isCompact_of_isAlgebraic

set_option autoImplicit false

open scoped IntermediateField

namespace PhilipponOpenSpread

namespace FinSubfield

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

abbrev FinIF (k K : Type u) [Field k] [Field K] [Algebra k K] := {L : IntermediateField k K // FiniteDimensional k L}

scoped instance (L : FinIF k K) : FiniteDimensional k L.1 := L.2

noncomputable def adj [Algebra.IsAlgebraic k K] (x : K) : FinIF k K :=
  ⟨k⟮x⟯, IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩

theorem mem_adj [Algebra.IsAlgebraic k K] (x : K) : x ∈ (adj (k := k) x).1 :=
  IntermediateField.mem_adjoin_simple_self k x

noncomputable def sup2 (L L' : FinIF k K) : FinIF k K :=
  ⟨L.1 ⊔ L'.1, IntermediateField.finiteDimensional_sup L.1 L'.1⟩

theorem existsUnique_ringHom_forall_comp_eq [Algebra.IsAlgebraic k K]
    (R : Type u) [CommRing R] (φ : ∀ L : FinIF k K, L.1 →+* R)
    (hφ : ∀ (L L' : FinIF k K) (h : L.1 ≤ L'.1) (x : L.1), φ L' ⟨x.1, h x.2⟩ = φ L x) :
    ∃! ψ : K →+* R, ∀ (L : FinIF k K) (x : L.1), ψ x.1 = φ L x := by
  classical
  have hwd : ∀ (L L' : FinIF k K) (x : K) (hx : x ∈ L.1) (hx' : x ∈ L'.1), φ L ⟨x, hx⟩ = φ L' ⟨x, hx'⟩ := by
    intro L L' x hx hx'
    rw [← hφ L (sup2 L L') le_sup_left ⟨x, hx⟩, ← hφ L' (sup2 L L') le_sup_right ⟨x, hx'⟩]
  let ψf : K → R := fun x => φ (adj x) ⟨x, mem_adj x⟩
  have hψf : ∀ (L : FinIF k K) (x : K) (hx : x ∈ L.1), ψf x = φ L ⟨x, hx⟩ := fun L x hx => hwd _ _ _ _ _
  let ψ : K →+* R :=
    { toFun := ψf
      map_one' := by rw [hψf ⟨⊥, inferInstance⟩ 1 (one_mem _)]; exact map_one _
      map_zero' := by rw [hψf ⟨⊥, inferInstance⟩ 0 (zero_mem _)]; exact map_zero _
      map_mul' := by
        intro x y
        let L := sup2 (adj (k := k) x) (adj y)
        have hx : x ∈ L.1 := (le_sup_left : (adj (k := k) x).1 ≤ L.1) (mem_adj x)
        have hy : y ∈ L.1 := (le_sup_right : (adj (k := k) y).1 ≤ L.1) (mem_adj y)
        rw [hψf L x hx, hψf L y hy, hψf L (x * y) (mul_mem hx hy), ← map_mul]
        rfl
      map_add' := by
        intro x y
        let L := sup2 (adj (k := k) x) (adj y)
        have hx : x ∈ L.1 := (le_sup_left : (adj (k := k) x).1 ≤ L.1) (mem_adj x)
        have hy : y ∈ L.1 := (le_sup_right : (adj (k := k) y).1 ≤ L.1) (mem_adj y)
        rw [hψf L x hx, hψf L y hy, hψf L (x + y) (add_mem hx hy), ← map_add]
        rfl }
  refine ⟨ψ, fun L x => hψf L x.1 x.2, ?_⟩
  intro ψ' hψ'
  ext x
  change ψ' x = ψf x
  rw [hψf (adj x) x (mem_adj x)]
  exact hψ' (adj x) ⟨x, mem_adj x⟩

end FinSubfield
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_preimage_pullback_map_eq_of_isCompact_of_isAlgebraic.PhilipponOpenSpread.FinSubfield"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

section Aux

variable (k K : Type u) [Field k] [Field K] [Algebra k K] (X : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of k))

private abbrev _root_.PhilipponOpenSpread.FinIF := FinSubfield.FinIF k K

p2m_export "PhilipponOpenSpread" "FinIF"

noncomputable abbrev gF (L : FinIF k K) : Spec (CommRingCat.of L.1) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k L.1))

noncomputable abbrev gK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

theorem incl_comp_gF {L₂ L₁ : FinIF k K} (h : L₂.1 ≤ L₁.1) :
    Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) ≫ gF k K L₂ = gF k K L₁ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem toK_comp_gF (L : FinIF k K) :
    Spec.map (CommRingCat.ofHom (algebraMap L.1 K)) ≫ gF k K L = gK k K := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

noncomputable def D : (FinIF k K)ᵒᵖ ⥤ Scheme.{u} where
  obj i := pullback fX (gF k K i.unop)
  map {i j} f := pullback.map fX (gF k K i.unop) fX (gF k K j.unop) (𝟙 X)
      (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, incl_comp_gF])
  map_id i := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.id_comp, Category.comp_id]
    · rw [pullback.lift_snd, Category.id_comp]
      convert Category.comp_id _
      rw [← Spec.map_id]
      rfl
  map_comp {i j l} f g := by
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.assoc, Category.comp_id]
    · simp only [pullback.lift_snd, Category.assoc, pullback.lift_snd_assoc]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl

noncomputable def t : D k K X fX ⟶ (Functor.const _).obj (Spec (CommRingCat.of k)) where
  app i := pullback.fst fX (gF k K i.unop) ≫ fX
  naturality {i j} f := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, D]
    rw [← Category.assoc, pullback.lift_fst, Category.comp_id]

noncomputable def c : Cone (D k K X fX) where
  pt := pullback fX (gK k K)
  π :=
    { app := fun i => pullback.map fX (gK k K) fX (gF k K i.unop) (𝟙 X)
          (Spec.map (CommRingCat.ofHom (algebraMap (i.unop).1 K))) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, toK_comp_gF])
      naturality := by
        intro i j f
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, D]
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
        · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
          rfl }

scoped instance : IsDirectedOrder (FinIF k K) :=
  ⟨fun L L' => ⟨FinSubfield.sup2 L L', le_sup_left (a := L.1), le_sup_right (a := L.1)⟩⟩

scoped instance : Nonempty (FinIF k K) := ⟨⟨⊥, inferInstance⟩⟩

scoped instance : IsFiltered (FinIF k K) := inferInstance

scoped instance : IsCofiltered (FinIF k K)ᵒᵖ := inferInstance

section RingOf

noncomputable def ringOf {W : Scheme.{u}} {B : CommRingCat.{u}} (g : W ⟶ Spec B) : B ⟶ Γ(W, ⊤) :=
  (Scheme.ΓSpecIso B).inv ≫ g.appTop

noncomputable def toSpec {W : Scheme.{u}} {B : CommRingCat.{u}} (φ : B ⟶ Γ(W, ⊤)) : W ⟶ Spec B :=
  ΓSpec.adjunction.homEquiv W (op B) φ.op

theorem ringOf_toSpec {W : Scheme.{u}} {B : CommRingCat.{u}} (φ : B ⟶ Γ(W, ⊤)) : ringOf (toSpec φ) = φ :=
  ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ

theorem ext_ringOf {W : Scheme.{u}} {B : CommRingCat.{u}} {g₁ g₂ : W ⟶ Spec B} (h : ringOf g₁ = ringOf g₂) : g₁ = g₂ := by
  apply ext_of_isAffine
  simpa [ringOf, Iso.cancel_iso_inv_left] using h

theorem toSpec_ringOf {W : Scheme.{u}} {B : CommRingCat.{u}} (g : W ⟶ Spec B) : toSpec (ringOf g) = g :=
  ext_ringOf (ringOf_toSpec _)

theorem ringOf_comp_specMap {W : Scheme.{u}} {B B' : CommRingCat.{u}} (g : W ⟶ Spec B) (u : B' ⟶ B) :
    ringOf (g ≫ Spec.map u) = u ≫ ringOf g := by
  simp only [ringOf, Scheme.Hom.comp_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

theorem ringOf_precomp {W W' : Scheme.{u}} {B : CommRingCat.{u}} (m : W' ⟶ W) (g : W ⟶ Spec B) :
    ringOf (m ≫ g) = ringOf g ≫ m.appTop := by
  simp only [ringOf, Scheme.Hom.comp_appTop, Category.assoc]

end RingOf
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_preimage_pullback_map_eq_of_isCompact_of_isAlgebraic.PhilipponOpenSpread.FinSubfield"

section Limit

variable {k K X fX}

noncomputable def bot' : FinIF k K := ⟨⊥, inferInstance⟩

noncomputable def conePhi (s : Cone (D k K X fX)) (L : FinIF k K) : L.1 →+* Γ(s.pt, ⊤) :=
  (ringOf (s.π.app (op L) ≫ pullback.snd fX (gF k K L))).hom

theorem ringOf_π_snd (s : Cone (D k K X fX)) (L : FinIF k K) :
    ringOf (s.π.app (op L) ≫ pullback.snd fX (gF k K L)) = CommRingCat.ofHom (conePhi s L) := rfl

theorem D_obj (i : (FinIF k K)ᵒᵖ) : (D k K X fX).obj i = pullback fX (gF k K i.unop) := rfl

theorem D_map_fst {i j : (FinIF k K)ᵒᵖ} (f : i ⟶ j) :
    (D k K X fX).map f ≫ pullback.fst fX (gF k K j.unop) = pullback.fst fX (gF k K i.unop) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem D_map_snd {i j : (FinIF k K)ᵒᵖ} (f : i ⟶ j) :
    (D k K X fX).map f ≫ pullback.snd fX (gF k K j.unop) =
      pullback.snd fX (gF k K i.unop) ≫ Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom) :=
  pullback.lift_snd _ _ _

theorem c_π_fst (i : (FinIF k K)ᵒᵖ) :
    (c k K X fX).π.app i ≫ pullback.fst fX (gF k K i.unop) = pullback.fst fX (gK k K) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem c_π_snd (i : (FinIF k K)ᵒᵖ) :
    (c k K X fX).π.app i ≫ pullback.snd fX (gF k K i.unop) =
      pullback.snd fX (gK k K) ≫ Spec.map (CommRingCat.ofHom (algebraMap (i.unop).1 K)) :=
  pullback.lift_snd _ _ _

theorem π_snd_eq (s : Cone (D k K X fX)) {L L' : FinIF k K} (h : L.1 ≤ L'.1) :
    s.π.app (op L) ≫ pullback.snd fX (gF k K L) =
      (s.π.app (op L') ≫ pullback.snd fX (gF k K L')) ≫
        Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) := by
  have hw := s.w (homOfLE (show L ≤ L' from h)).op
  have := congrArg (· ≫ pullback.snd fX (gF k K L)) hw
  beta_reduce at this
  erw [Category.assoc, D_map_snd] at this
  erw [Category.assoc]
  exact this.symm

theorem π_fst_eq (s : Cone (D k K X fX)) {L L' : FinIF k K} (h : L.1 ≤ L'.1) :
    s.π.app (op L) ≫ pullback.fst fX (gF k K L) = s.π.app (op L') ≫ pullback.fst fX (gF k K L') := by
  have hw := s.w (homOfLE (show L ≤ L' from h)).op
  have := congrArg (· ≫ pullback.fst fX (gF k K L)) hw
  beta_reduce at this
  erw [Category.assoc, D_map_fst] at this
  exact this.symm

theorem conePhi_compat (s : Cone (D k K X fX)) (L L' : FinIF k K) (h : L.1 ≤ L'.1) (x : L.1) :
    conePhi s L' ⟨x.1, h x.2⟩ = conePhi s L x := by
  have h2 := (congrArg ringOf (π_snd_eq s h)).trans
    (ringOf_comp_specMap (s.π.app (op L') ≫ pullback.snd fX (gF k K L'))
      (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom))
  change CommRingCat.ofHom (conePhi s L) = _ ≫ CommRingCat.ofHom (conePhi s L') at h2
  have h3 := congrArg (fun φ : CommRingCat.of L.1 ⟶ Γ(s.pt, ⊤) => φ.hom x) h2
  exact h3.symm

variable [Algebra.IsAlgebraic k K]

noncomputable def conePsi (s : Cone (D k K X fX)) : K →+* Γ(s.pt, ⊤) :=
  (FinSubfield.existsUnique_ringHom_forall_comp_eq Γ(s.pt, ⊤) (conePhi s) (conePhi_compat s)).exists.choose

theorem conePsi_spec (s : Cone (D k K X fX)) (L : FinIF k K) (x : L.1) : conePsi s x.1 = conePhi s L x :=
  (FinSubfield.existsUnique_ringHom_forall_comp_eq Γ(s.pt, ⊤) (conePhi s) (conePhi_compat s)).exists.choose_spec L x

theorem conePsi_unique (s : Cone (D k K X fX)) (ψ' : K →+* Γ(s.pt, ⊤))
    (h : ∀ (L : FinIF k K) (x : L.1), ψ' x.1 = conePhi s L x) : ψ' = conePsi s :=
  (FinSubfield.existsUnique_ringHom_forall_comp_eq Γ(s.pt, ⊤) (conePhi s) (conePhi_compat s)).unique h
    (conePsi_spec s)

noncomputable def toSpecK (s : Cone (D k K X fX)) : s.pt ⟶ Spec (CommRingCat.of K) :=
  toSpec (CommRingCat.ofHom (conePsi s))

theorem toSpecK_comp (s : Cone (D k K X fX)) (L : FinIF k K) :
    toSpecK s ≫ Spec.map (CommRingCat.ofHom (algebraMap L.1 K)) = s.π.app (op L) ≫ pullback.snd fX (gF k K L) := by
  apply ext_ringOf
  refine (ringOf_comp_specMap _ _).trans ?_
  rw [toSpecK, ringOf_toSpec]
  change _ = CommRingCat.ofHom (conePhi s L)
  rw [← CommRingCat.ofHom_comp]
  congr 1
  ext x
  exact conePsi_spec s L x

theorem lift_w (s : Cone (D k K X fX)) :
    (s.π.app (op bot') ≫ pullback.fst fX (gF k K bot')) ≫ fX = toSpecK s ≫ gK k K := by
  have e1 := congrArg (s.π.app (op bot') ≫ ·) (pullback.condition (f := fX) (g := gF k K bot'))
  have e2 := congrArg (· ≫ gF k K bot') (toSpecK_comp s bot')
  have e3 : (toSpecK s ≫ Spec.map (CommRingCat.ofHom (algebraMap bot'.1 K))) ≫ gF k K bot' = toSpecK s ≫ gK k K := by
    erw [Category.assoc, toK_comp_gF]
    try rfl
  beta_reduce at e1 e2
  exact ((Category.assoc _ _ _).trans e1).trans (((Category.assoc _ _ _).symm.trans e2.symm).trans e3)

noncomputable def isLimitCone : IsLimit (c k K X fX) where
  lift s := pullback.lift (s.π.app (op bot') ≫ pullback.fst fX (gF k K bot')) (toSpecK s) (lift_w s)
  fac s j := by
    obtain ⟨L⟩ := j
    apply pullback.hom_ext
    · dsimp only [c, D, Opposite.unop_op]
      rw [Category.assoc, pullback.lift_fst, Category.comp_id, pullback.lift_fst]
      exact π_fst_eq s (show bot'.1 ≤ L.1 from bot_le)
    · dsimp only [c, D, Opposite.unop_op]
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
      exact toSpecK_comp s L
  uniq s m hm := by
    apply pullback.hom_ext
    · have := hm (op bot')
      dsimp only [c, D] at this ⊢
      rw [pullback.lift_fst, ← this, Category.assoc, pullback.lift_fst, Category.comp_id]
    · dsimp only [c, D] at hm ⊢
      rw [pullback.lift_snd]
      apply ext_ringOf
      rw [toSpecK, ringOf_toSpec]
      have key : (ringOf (m ≫ pullback.snd fX (gK k K))).hom = conePsi s := by
        apply conePsi_unique
        intro L x
        have hL := hm (op L)
        dsimp only [Opposite.unop_op] at hL
        have a1 := congrArg (· ≫ pullback.snd fX (gF k K L)) hL
        have a3 := c_π_snd (k := k) (K := K) (X := X) (fX := fX) (op L)
        dsimp only [c, D, Opposite.unop_op] at a1 a3
        have h1 : s.π.app (op L) ≫ pullback.snd fX (gF k K L) =
            (m ≫ pullback.snd fX (gK k K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap L.1 K)) :=
          a1.symm.trans ((Category.assoc _ _ _).trans (((congrArg (m ≫ ·) a3)).trans (Category.assoc _ _ _).symm))
        have h2 := (congrArg ringOf h1).trans (ringOf_comp_specMap _ _)
        change CommRingCat.ofHom (conePhi s L) = _ at h2
        have h3 := congrArg (fun φ : CommRingCat.of L.1 ⟶ Γ(s.pt, ⊤) => φ.hom x) h2
        simpa using h3.symm
      have : ringOf (m ≫ pullback.snd fX (gK k K)) = CommRingCat.ofHom (conePsi s) := by
        ext1; exact key
      exact this

end Limit
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_preimage_pullback_map_eq_of_isCompact_of_isAlgebraic.PhilipponOpenSpread.FinSubfield"

section Instances

scoped instance isAffineHom_D_map {i j : (FinIF k K)ᵒᵖ} (f : i ⟶ j) : IsAffineHom ((D k K X fX).map f) := by
  dsimp only [D]
  exact MorphismProperty.pullbackMap (P := @IsAffineHom)
    (f := fX) (g := gF k K i.unop) (f' := fX) (g' := gF k K j.unop) (i₁ := 𝟙 X)
    (i₂ := Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom))
    inferInstance inferInstance (Category.id_comp _).symm (incl_comp_gF k K _).symm

scoped instance compactSpace_pullback_gF [CompactSpace X] (L : FinIF k K) : CompactSpace ↥(pullback fX (gF k K L)) := by
  haveI : IsAffineHom (gF k K L) := inferInstance
  haveI : QuasiCompact (gF k K L) := inferInstance
  infer_instance

scoped instance compactSpace_D_obj [CompactSpace X] (i : (FinIF k K)ᵒᵖ) : CompactSpace ((D k K X fX).obj i) :=
  compactSpace_pullback_gF k K X fX i.unop

scoped instance quasiSeparatedSpace_pullback_gF [QuasiSeparatedSpace X] (L : FinIF k K) :
    QuasiSeparatedSpace ↥(pullback fX (gF k K L)) := by
  haveI : QuasiSeparated (pullback.fst fX (gF k K L)) := inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst fX (gF k K L))

scoped instance quasiSeparatedSpace_D_obj [QuasiSeparatedSpace X] (i : (FinIF k K)ᵒᵖ) :
    QuasiSeparatedSpace ((D k K X fX).obj i) := by
  dsimp only [D]
  haveI : QuasiSeparated (pullback.fst fX (gF k K i.unop)) := inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst fX (gF k K i.unop))

end Instances
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_preimage_pullback_map_eq_of_isCompact_of_isAlgebraic.PhilipponOpenSpread.FinSubfield"

end Aux
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_preimage_pullback_map_eq_of_isCompact_of_isAlgebraic.PhilipponOpenSpread.FinSubfield"

end PhilipponOpenSpread
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_preimage_pullback_map_eq_of_isCompact_of_isAlgebraic.PhilipponOpenSpread.FinSubfield P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_preimage_pullback_map_eq_of_isCompact_of_isAlgebraic.PhilipponOpenSpread"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite PhilipponOpenSpread in
theorem solution
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of k))
    (U : (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Opens)
    (hU : IsCompact (U : Set ↥(pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) :
    ∃ (L : IntermediateField k K) (_ : FiniteDimensional k L)
      (hι : Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (V : (pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))).Opens),
      IsCompact (V : Set ↥(pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k L))))) ∧
      pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))
          (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) ⁻¹ᵁ V = U := by
  classical
  obtain ⟨i, V, hV, hVU⟩ := exists_preimage_eq (D k K X fX) (c k K X fX) isLimitCone U hU
  obtain ⟨L⟩ := i
  exact ⟨L.1, L.2, toK_comp_gF k K L, V, hV, hVU⟩

end S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_preimage_pullback_map_eq_of_isCompact_of_isAlgebraic
end P2MW




set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic

set_option autoImplicit false

open scoped IntermediateField

namespace PhilipponIsoSpread

namespace FinSubfield

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

abbrev FinIF (k K : Type u) [Field k] [Field K] [Algebra k K] := {L : IntermediateField k K // FiniteDimensional k L}

scoped instance (L : FinIF k K) : FiniteDimensional k L.1 := L.2

noncomputable def adj [Algebra.IsAlgebraic k K] (x : K) : FinIF k K :=
  ⟨k⟮x⟯, IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩

theorem mem_adj [Algebra.IsAlgebraic k K] (x : K) : x ∈ (adj (k := k) x).1 :=
  IntermediateField.mem_adjoin_simple_self k x

noncomputable def sup2 (L L' : FinIF k K) : FinIF k K :=
  ⟨L.1 ⊔ L'.1, IntermediateField.finiteDimensional_sup L.1 L'.1⟩

theorem existsUnique_ringHom_forall_comp_eq [Algebra.IsAlgebraic k K]
    (R : Type u) [CommRing R] (φ : ∀ L : FinIF k K, L.1 →+* R)
    (hφ : ∀ (L L' : FinIF k K) (h : L.1 ≤ L'.1) (x : L.1), φ L' ⟨x.1, h x.2⟩ = φ L x) :
    ∃! ψ : K →+* R, ∀ (L : FinIF k K) (x : L.1), ψ x.1 = φ L x := by
  classical
  have hwd : ∀ (L L' : FinIF k K) (x : K) (hx : x ∈ L.1) (hx' : x ∈ L'.1), φ L ⟨x, hx⟩ = φ L' ⟨x, hx'⟩ := by
    intro L L' x hx hx'
    rw [← hφ L (sup2 L L') le_sup_left ⟨x, hx⟩, ← hφ L' (sup2 L L') le_sup_right ⟨x, hx'⟩]
  let ψf : K → R := fun x => φ (adj x) ⟨x, mem_adj x⟩
  have hψf : ∀ (L : FinIF k K) (x : K) (hx : x ∈ L.1), ψf x = φ L ⟨x, hx⟩ := fun L x hx => hwd _ _ _ _ _
  let ψ : K →+* R :=
    { toFun := ψf
      map_one' := by rw [hψf ⟨⊥, inferInstance⟩ 1 (one_mem _)]; exact map_one _
      map_zero' := by rw [hψf ⟨⊥, inferInstance⟩ 0 (zero_mem _)]; exact map_zero _
      map_mul' := by
        intro x y
        let L := sup2 (adj (k := k) x) (adj y)
        have hx : x ∈ L.1 := (le_sup_left : (adj (k := k) x).1 ≤ L.1) (mem_adj x)
        have hy : y ∈ L.1 := (le_sup_right : (adj (k := k) y).1 ≤ L.1) (mem_adj y)
        rw [hψf L x hx, hψf L y hy, hψf L (x * y) (mul_mem hx hy), ← map_mul]
        rfl
      map_add' := by
        intro x y
        let L := sup2 (adj (k := k) x) (adj y)
        have hx : x ∈ L.1 := (le_sup_left : (adj (k := k) x).1 ≤ L.1) (mem_adj x)
        have hy : y ∈ L.1 := (le_sup_right : (adj (k := k) y).1 ≤ L.1) (mem_adj y)
        rw [hψf L x hx, hψf L y hy, hψf L (x + y) (add_mem hx hy), ← map_add]
        rfl }
  refine ⟨ψ, fun L x => hψf L x.1 x.2, ?_⟩
  intro ψ' hψ'
  ext x
  change ψ' x = ψf x
  rw [hψf (adj x) x (mem_adj x)]
  exact hψ' (adj x) ⟨x, mem_adj x⟩

end FinSubfield
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.PhilipponIsoSpread.FinSubfield"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

section Aux

variable (k K : Type u) [Field k] [Field K] [Algebra k K] (X : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of k))

private abbrev _root_.PhilipponIsoSpread.FinIF := FinSubfield.FinIF k K

p2m_export "PhilipponIsoSpread" "FinIF"

noncomputable abbrev gF (L : FinIF k K) : Spec (CommRingCat.of L.1) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k L.1))

noncomputable abbrev gK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

theorem incl_comp_gF {L₂ L₁ : FinIF k K} (h : L₂.1 ≤ L₁.1) :
    Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) ≫ gF k K L₂ = gF k K L₁ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem toK_comp_gF (L : FinIF k K) :
    Spec.map (CommRingCat.ofHom (algebraMap L.1 K)) ≫ gF k K L = gK k K := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

noncomputable def D : (FinIF k K)ᵒᵖ ⥤ Scheme.{u} where
  obj i := pullback fX (gF k K i.unop)
  map {i j} f := pullback.map fX (gF k K i.unop) fX (gF k K j.unop) (𝟙 X)
      (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, incl_comp_gF])
  map_id i := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.id_comp, Category.comp_id]
    · rw [pullback.lift_snd, Category.id_comp]
      convert Category.comp_id _
      rw [← Spec.map_id]
      rfl
  map_comp {i j l} f g := by
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.assoc, Category.comp_id]
    · simp only [pullback.lift_snd, Category.assoc, pullback.lift_snd_assoc]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl

noncomputable def t : D k K X fX ⟶ (Functor.const _).obj (Spec (CommRingCat.of k)) where
  app i := pullback.fst fX (gF k K i.unop) ≫ fX
  naturality {i j} f := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, D]
    rw [← Category.assoc, pullback.lift_fst, Category.comp_id]

noncomputable def c : Cone (D k K X fX) where
  pt := pullback fX (gK k K)
  π :=
    { app := fun i => pullback.map fX (gK k K) fX (gF k K i.unop) (𝟙 X)
          (Spec.map (CommRingCat.ofHom (algebraMap (i.unop).1 K))) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, toK_comp_gF])
      naturality := by
        intro i j f
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, D]
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
        · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
          rfl }

scoped instance : IsDirectedOrder (FinIF k K) :=
  ⟨fun L L' => ⟨FinSubfield.sup2 L L', le_sup_left (a := L.1), le_sup_right (a := L.1)⟩⟩

scoped instance : Nonempty (FinIF k K) := ⟨⟨⊥, inferInstance⟩⟩

scoped instance : IsFiltered (FinIF k K) := inferInstance

scoped instance : IsCofiltered (FinIF k K)ᵒᵖ := inferInstance

section RingOf

noncomputable def ringOf {W : Scheme.{u}} {B : CommRingCat.{u}} (g : W ⟶ Spec B) : B ⟶ Γ(W, ⊤) :=
  (Scheme.ΓSpecIso B).inv ≫ g.appTop

noncomputable def toSpec {W : Scheme.{u}} {B : CommRingCat.{u}} (φ : B ⟶ Γ(W, ⊤)) : W ⟶ Spec B :=
  ΓSpec.adjunction.homEquiv W (op B) φ.op

theorem ringOf_toSpec {W : Scheme.{u}} {B : CommRingCat.{u}} (φ : B ⟶ Γ(W, ⊤)) : ringOf (toSpec φ) = φ :=
  ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ

theorem ext_ringOf {W : Scheme.{u}} {B : CommRingCat.{u}} {g₁ g₂ : W ⟶ Spec B} (h : ringOf g₁ = ringOf g₂) : g₁ = g₂ := by
  apply ext_of_isAffine
  simpa [ringOf, Iso.cancel_iso_inv_left] using h

theorem toSpec_ringOf {W : Scheme.{u}} {B : CommRingCat.{u}} (g : W ⟶ Spec B) : toSpec (ringOf g) = g :=
  ext_ringOf (ringOf_toSpec _)

theorem ringOf_comp_specMap {W : Scheme.{u}} {B B' : CommRingCat.{u}} (g : W ⟶ Spec B) (u : B' ⟶ B) :
    ringOf (g ≫ Spec.map u) = u ≫ ringOf g := by
  simp only [ringOf, Scheme.Hom.comp_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

theorem ringOf_precomp {W W' : Scheme.{u}} {B : CommRingCat.{u}} (m : W' ⟶ W) (g : W ⟶ Spec B) :
    ringOf (m ≫ g) = ringOf g ≫ m.appTop := by
  simp only [ringOf, Scheme.Hom.comp_appTop, Category.assoc]

end RingOf
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.PhilipponIsoSpread.FinSubfield"

section Limit

variable {k K X fX}

noncomputable def bot' : FinIF k K := ⟨⊥, inferInstance⟩

noncomputable def conePhi (s : Cone (D k K X fX)) (L : FinIF k K) : L.1 →+* Γ(s.pt, ⊤) :=
  (ringOf (s.π.app (op L) ≫ pullback.snd fX (gF k K L))).hom

theorem ringOf_π_snd (s : Cone (D k K X fX)) (L : FinIF k K) :
    ringOf (s.π.app (op L) ≫ pullback.snd fX (gF k K L)) = CommRingCat.ofHom (conePhi s L) := rfl

theorem D_obj (i : (FinIF k K)ᵒᵖ) : (D k K X fX).obj i = pullback fX (gF k K i.unop) := rfl

theorem D_map_fst {i j : (FinIF k K)ᵒᵖ} (f : i ⟶ j) :
    (D k K X fX).map f ≫ pullback.fst fX (gF k K j.unop) = pullback.fst fX (gF k K i.unop) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem D_map_snd {i j : (FinIF k K)ᵒᵖ} (f : i ⟶ j) :
    (D k K X fX).map f ≫ pullback.snd fX (gF k K j.unop) =
      pullback.snd fX (gF k K i.unop) ≫ Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom) :=
  pullback.lift_snd _ _ _

theorem c_π_fst (i : (FinIF k K)ᵒᵖ) :
    (c k K X fX).π.app i ≫ pullback.fst fX (gF k K i.unop) = pullback.fst fX (gK k K) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem c_π_snd (i : (FinIF k K)ᵒᵖ) :
    (c k K X fX).π.app i ≫ pullback.snd fX (gF k K i.unop) =
      pullback.snd fX (gK k K) ≫ Spec.map (CommRingCat.ofHom (algebraMap (i.unop).1 K)) :=
  pullback.lift_snd _ _ _

theorem π_snd_eq (s : Cone (D k K X fX)) {L L' : FinIF k K} (h : L.1 ≤ L'.1) :
    s.π.app (op L) ≫ pullback.snd fX (gF k K L) =
      (s.π.app (op L') ≫ pullback.snd fX (gF k K L')) ≫
        Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) := by
  have hw := s.w (homOfLE (show L ≤ L' from h)).op
  have := congrArg (· ≫ pullback.snd fX (gF k K L)) hw
  beta_reduce at this
  erw [Category.assoc, D_map_snd] at this
  erw [Category.assoc]
  exact this.symm

theorem π_fst_eq (s : Cone (D k K X fX)) {L L' : FinIF k K} (h : L.1 ≤ L'.1) :
    s.π.app (op L) ≫ pullback.fst fX (gF k K L) = s.π.app (op L') ≫ pullback.fst fX (gF k K L') := by
  have hw := s.w (homOfLE (show L ≤ L' from h)).op
  have := congrArg (· ≫ pullback.fst fX (gF k K L)) hw
  beta_reduce at this
  erw [Category.assoc, D_map_fst] at this
  exact this.symm

theorem conePhi_compat (s : Cone (D k K X fX)) (L L' : FinIF k K) (h : L.1 ≤ L'.1) (x : L.1) :
    conePhi s L' ⟨x.1, h x.2⟩ = conePhi s L x := by
  have h2 := (congrArg ringOf (π_snd_eq s h)).trans
    (ringOf_comp_specMap (s.π.app (op L') ≫ pullback.snd fX (gF k K L'))
      (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom))
  change CommRingCat.ofHom (conePhi s L) = _ ≫ CommRingCat.ofHom (conePhi s L') at h2
  have h3 := congrArg (fun φ : CommRingCat.of L.1 ⟶ Γ(s.pt, ⊤) => φ.hom x) h2
  exact h3.symm

variable [Algebra.IsAlgebraic k K]

noncomputable def conePsi (s : Cone (D k K X fX)) : K →+* Γ(s.pt, ⊤) :=
  (FinSubfield.existsUnique_ringHom_forall_comp_eq Γ(s.pt, ⊤) (conePhi s) (conePhi_compat s)).exists.choose

theorem conePsi_spec (s : Cone (D k K X fX)) (L : FinIF k K) (x : L.1) : conePsi s x.1 = conePhi s L x :=
  (FinSubfield.existsUnique_ringHom_forall_comp_eq Γ(s.pt, ⊤) (conePhi s) (conePhi_compat s)).exists.choose_spec L x

theorem conePsi_unique (s : Cone (D k K X fX)) (ψ' : K →+* Γ(s.pt, ⊤))
    (h : ∀ (L : FinIF k K) (x : L.1), ψ' x.1 = conePhi s L x) : ψ' = conePsi s :=
  (FinSubfield.existsUnique_ringHom_forall_comp_eq Γ(s.pt, ⊤) (conePhi s) (conePhi_compat s)).unique h
    (conePsi_spec s)

noncomputable def toSpecK (s : Cone (D k K X fX)) : s.pt ⟶ Spec (CommRingCat.of K) :=
  toSpec (CommRingCat.ofHom (conePsi s))

theorem toSpecK_comp (s : Cone (D k K X fX)) (L : FinIF k K) :
    toSpecK s ≫ Spec.map (CommRingCat.ofHom (algebraMap L.1 K)) = s.π.app (op L) ≫ pullback.snd fX (gF k K L) := by
  apply ext_ringOf
  refine (ringOf_comp_specMap _ _).trans ?_
  rw [toSpecK, ringOf_toSpec]
  change _ = CommRingCat.ofHom (conePhi s L)
  rw [← CommRingCat.ofHom_comp]
  congr 1
  ext x
  exact conePsi_spec s L x

theorem lift_w (s : Cone (D k K X fX)) :
    (s.π.app (op bot') ≫ pullback.fst fX (gF k K bot')) ≫ fX = toSpecK s ≫ gK k K := by
  have e1 := congrArg (s.π.app (op bot') ≫ ·) (pullback.condition (f := fX) (g := gF k K bot'))
  have e2 := congrArg (· ≫ gF k K bot') (toSpecK_comp s bot')
  have e3 : (toSpecK s ≫ Spec.map (CommRingCat.ofHom (algebraMap bot'.1 K))) ≫ gF k K bot' = toSpecK s ≫ gK k K := by
    erw [Category.assoc, toK_comp_gF]
    try rfl
  beta_reduce at e1 e2
  exact ((Category.assoc _ _ _).trans e1).trans (((Category.assoc _ _ _).symm.trans e2.symm).trans e3)

noncomputable def isLimitCone : IsLimit (c k K X fX) where
  lift s := pullback.lift (s.π.app (op bot') ≫ pullback.fst fX (gF k K bot')) (toSpecK s) (lift_w s)
  fac s j := by
    obtain ⟨L⟩ := j
    apply pullback.hom_ext
    · dsimp only [c, D, Opposite.unop_op]
      rw [Category.assoc, pullback.lift_fst, Category.comp_id, pullback.lift_fst]
      exact π_fst_eq s (show bot'.1 ≤ L.1 from bot_le)
    · dsimp only [c, D, Opposite.unop_op]
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
      exact toSpecK_comp s L
  uniq s m hm := by
    apply pullback.hom_ext
    · have := hm (op bot')
      dsimp only [c, D] at this ⊢
      rw [pullback.lift_fst, ← this, Category.assoc, pullback.lift_fst, Category.comp_id]
    · dsimp only [c, D] at hm ⊢
      rw [pullback.lift_snd]
      apply ext_ringOf
      rw [toSpecK, ringOf_toSpec]
      have key : (ringOf (m ≫ pullback.snd fX (gK k K))).hom = conePsi s := by
        apply conePsi_unique
        intro L x
        have hL := hm (op L)
        dsimp only [Opposite.unop_op] at hL
        have a1 := congrArg (· ≫ pullback.snd fX (gF k K L)) hL
        have a3 := c_π_snd (k := k) (K := K) (X := X) (fX := fX) (op L)
        dsimp only [c, D, Opposite.unop_op] at a1 a3
        have h1 : s.π.app (op L) ≫ pullback.snd fX (gF k K L) =
            (m ≫ pullback.snd fX (gK k K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap L.1 K)) :=
          a1.symm.trans ((Category.assoc _ _ _).trans (((congrArg (m ≫ ·) a3)).trans (Category.assoc _ _ _).symm))
        have h2 := (congrArg ringOf h1).trans (ringOf_comp_specMap _ _)
        change CommRingCat.ofHom (conePhi s L) = _ at h2
        have h3 := congrArg (fun φ : CommRingCat.of L.1 ⟶ Γ(s.pt, ⊤) => φ.hom x) h2
        simpa using h3.symm
      have : ringOf (m ≫ pullback.snd fX (gK k K)) = CommRingCat.ofHom (conePsi s) := by
        ext1; exact key
      exact this

end Limit
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.PhilipponIsoSpread.FinSubfield"

section Instances

scoped instance isAffineHom_D_map {i j : (FinIF k K)ᵒᵖ} (f : i ⟶ j) : IsAffineHom ((D k K X fX).map f) := by
  dsimp only [D]
  exact MorphismProperty.pullbackMap (P := @IsAffineHom)
    (f := fX) (g := gF k K i.unop) (f' := fX) (g' := gF k K j.unop) (i₁ := 𝟙 X)
    (i₂ := Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom))
    inferInstance inferInstance (Category.id_comp _).symm (incl_comp_gF k K _).symm

scoped instance compactSpace_pullback_gF [CompactSpace X] (L : FinIF k K) : CompactSpace ↥(pullback fX (gF k K L)) := by
  haveI : IsAffineHom (gF k K L) := inferInstance
  haveI : QuasiCompact (gF k K L) := inferInstance
  infer_instance

scoped instance compactSpace_D_obj [CompactSpace X] (i : (FinIF k K)ᵒᵖ) : CompactSpace ((D k K X fX).obj i) :=
  compactSpace_pullback_gF k K X fX i.unop

scoped instance quasiSeparatedSpace_pullback_gF [QuasiSeparatedSpace X] (L : FinIF k K) :
    QuasiSeparatedSpace ↥(pullback fX (gF k K L)) := by
  haveI : QuasiSeparated (pullback.fst fX (gF k K L)) := inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst fX (gF k K L))

scoped instance quasiSeparatedSpace_D_obj [QuasiSeparatedSpace X] (i : (FinIF k K)ᵒᵖ) :
    QuasiSeparatedSpace ((D k K X fX).obj i) := by
  dsimp only [D]
  haveI : QuasiSeparated (pullback.fst fX (gF k K i.unop)) := inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst fX (gF k K i.unop))

end Instances
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.PhilipponIsoSpread.FinSubfield"

end Aux
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.PhilipponIsoSpread.FinSubfield"

section API

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {X : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of k)}

noncomputable def proj (fX : X ⟶ Spec (CommRingCat.of k)) (L : FinIF k K) :
    pullback fX (gK k K) ⟶ (D k K X fX).obj (op L) :=
  (c k K X fX).π.app (op L)

noncomputable def fstL (fX : X ⟶ Spec (CommRingCat.of k)) (L : FinIF k K) : (D k K X fX).obj (op L) ⟶ X :=
  pullback.fst fX (gF k K L)

noncomputable def sndL (fX : X ⟶ Spec (CommRingCat.of k)) (L : FinIF k K) :
    (D k K X fX).obj (op L) ⟶ Spec (CommRingCat.of L.1) :=
  pullback.snd fX (gF k K L)

theorem proj_def (L : FinIF k K) : (c k K X fX).π.app (op L) = proj fX L := rfl
theorem fstL_def (L : FinIF k K) : pullback.fst fX (gF k K L) = fstL fX L := rfl
theorem sndL_def (L : FinIF k K) : pullback.snd fX (gF k K L) = sndL fX L := rfl
theorem t_appL (L : FinIF k K) : (t k K X fX).app (op L) = fstL fX L ≫ fX := rfl

theorem hom_extL {L : FinIF k K} {W : Scheme.{u}} {a b : W ⟶ (D k K X fX).obj (op L)}
    (h₁ : a ≫ fstL fX L = b ≫ fstL fX L) (h₂ : a ≫ sndL fX L = b ≫ sndL fX L) : a = b :=
  pullback.hom_ext h₁ h₂

theorem conditionL (L : FinIF k K) : fstL fX L ≫ fX = sndL fX L ≫ gF k K L := pullback.condition

noncomputable def liftL (fX : X ⟶ Spec (CommRingCat.of k)) (L : FinIF k K) {W : Scheme.{u}} (a : W ⟶ X)
    (b : W ⟶ Spec (CommRingCat.of L.1)) (w : a ≫ fX = b ≫ gF k K L) : W ⟶ (D k K X fX).obj (op L) :=
  pullback.lift a b w

theorem liftL_fstL (L : FinIF k K) {W : Scheme.{u}} (a : W ⟶ X) (b : W ⟶ Spec (CommRingCat.of L.1))
    (w : a ≫ fX = b ≫ gF k K L) : liftL fX L a b w ≫ fstL fX L = a :=
  pullback.lift_fst _ _ _

theorem liftL_sndL (L : FinIF k K) {W : Scheme.{u}} (a : W ⟶ X) (b : W ⟶ Spec (CommRingCat.of L.1))
    (w : a ≫ fX = b ≫ gF k K L) : liftL fX L a b w ≫ sndL fX L = b :=
  pullback.lift_snd _ _ _

theorem D_map_eq {L L' : FinIF k K} (f f' : (op L' : (FinIF k K)ᵒᵖ) ⟶ op L) :
    (D k K X fX).map f = (D k K X fX).map f' := by
  rw [Subsingleton.elim f f']

theorem D_map_fstL {L L' : FinIF k K} (f : (op L' : (FinIF k K)ᵒᵖ) ⟶ op L) :
    (D k K X fX).map f ≫ fstL fX L = fstL fX L' :=
  D_map_fst f

theorem D_map_sndL {L L' : FinIF k K} (f : (op L' : (FinIF k K)ᵒᵖ) ⟶ op L) :
    (D k K X fX).map f ≫ sndL fX L =
      sndL fX L' ≫ Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom) :=
  D_map_snd f

theorem D_map_map {L L' L'' : FinIF k K} (f : (op L' : (FinIF k K)ᵒᵖ) ⟶ op L) (f' : (op L'' : (FinIF k K)ᵒᵖ) ⟶ op L')
    (f'' : (op L'' : (FinIF k K)ᵒᵖ) ⟶ op L) :
    (D k K X fX).map f' ≫ (D k K X fX).map f = (D k K X fX).map f'' := by
  rw [← Functor.map_comp, Subsingleton.elim (f' ≫ f) f'']

theorem proj_map {L L' : FinIF k K} (f : (op L' : (FinIF k K)ᵒᵖ) ⟶ op L) :
    proj fX L' ≫ (D k K X fX).map f = proj fX L :=
  (c k K X fX).w f

theorem proj_fstL (L : FinIF k K) : proj fX L ≫ fstL fX L = pullback.fst fX (gK k K) := c_π_fst _

theorem proj_sndL (L : FinIF k K) :
    proj fX L ≫ sndL fX L = pullback.snd fX (gK k K) ≫ Spec.map (CommRingCat.ofHom (algebraMap L.1 K)) :=
  c_π_snd _

def homOp {L L' : FinIF k K} (h : L.1 ≤ L'.1) : (op L' : (FinIF k K)ᵒᵖ) ⟶ op L :=
  (homOfLE (show L ≤ L' from h)).op

end API
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.PhilipponIsoSpread.FinSubfield"

section IsoSpread

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of k)}

theorem liftAt_w (fY : Y ⟶ Spec (CommRingCat.of k)) {L₀ N : FinIF k K} (g : (D k K X fX).obj (op L₀) ⟶ Y)
    (hg : g ≫ fY = (t k K X fX).app (op L₀)) (f : (op N : (FinIF k K)ᵒᵖ) ⟶ op L₀) :
    ((D k K X fX).map f ≫ g) ≫ fY = sndL fX N ≫ gF k K N := by
  rw [Category.assoc, hg, t_appL, ← Category.assoc, D_map_fstL]
  exact conditionL N

noncomputable def liftAt (fY : Y ⟶ Spec (CommRingCat.of k)) {L₀ N : FinIF k K} (g : (D k K X fX).obj (op L₀) ⟶ Y)
    (hg : g ≫ fY = (t k K X fX).app (op L₀)) (f : (op N : (FinIF k K)ᵒᵖ) ⟶ op L₀) :
    (D k K X fX).obj (op N) ⟶ (D k K Y fY).obj (op N) :=
  liftL fY N ((D k K X fX).map f ≫ g) (sndL fX N) (liftAt_w fY g hg f)

variable {fY : Y ⟶ Spec (CommRingCat.of k)}

theorem liftAt_fstL {L₀ N : FinIF k K} (g : (D k K X fX).obj (op L₀) ⟶ Y)
    (hg : g ≫ fY = (t k K X fX).app (op L₀)) (f : (op N : (FinIF k K)ᵒᵖ) ⟶ op L₀) :
    liftAt fY g hg f ≫ fstL fY N = (D k K X fX).map f ≫ g :=
  liftL_fstL _ _ _ _

theorem liftAt_sndL {L₀ N : FinIF k K} (g : (D k K X fX).obj (op L₀) ⟶ Y)
    (hg : g ≫ fY = (t k K X fX).app (op L₀)) (f : (op N : (FinIF k K)ᵒᵖ) ⟶ op L₀) :
    liftAt fY g hg f ≫ sndL fY N = sndL fX N :=
  liftL_sndL _ _ _ _

theorem liftAt_t {L₀ N : FinIF k K} (g : (D k K X fX).obj (op L₀) ⟶ Y)
    (hg : g ≫ fY = (t k K X fX).app (op L₀)) (f : (op N : (FinIF k K)ᵒᵖ) ⟶ op L₀) :
    liftAt fY g hg f ≫ fstL fY N ≫ fY = fstL fX N ≫ fX := by
  rw [conditionL, conditionL, ← Category.assoc, liftAt_sndL]

theorem liftAt_map {L₀ N N' : FinIF k K} (g : (D k K X fX).obj (op L₀) ⟶ Y)
    (hg : g ≫ fY = (t k K X fX).app (op L₀)) (f : (op N : (FinIF k K)ᵒᵖ) ⟶ op L₀)
    (f' : (op N' : (FinIF k K)ᵒᵖ) ⟶ op L₀) (u : (op N' : (FinIF k K)ᵒᵖ) ⟶ op N) :
    liftAt fY g hg f' ≫ (D k K Y fY).map u = (D k K X fX).map u ≫ liftAt fY g hg f := by
  apply hom_extL
  · rw [Category.assoc, D_map_fstL, liftAt_fstL, Category.assoc, liftAt_fstL, ← Category.assoc, D_map_map]
  · rw [Category.assoc, D_map_sndL, ← Category.assoc, liftAt_sndL, Category.assoc, liftAt_sndL, D_map_sndL]

theorem proj_liftAt {L₀ N : FinIF k K} (g : (D k K X fX).obj (op L₀) ⟶ Y)
    (hg : g ≫ fY = (t k K X fX).app (op L₀)) (f : (op N : (FinIF k K)ᵒᵖ) ⟶ op L₀)
    (φ : pullback fX (gK k K) ⟶ pullback fY (gK k K))
    (hφ : φ ≫ pullback.snd fY (gK k K) = pullback.snd fX (gK k K))
    (hga : proj fX L₀ ≫ g = φ ≫ pullback.fst fY (gK k K)) :
    proj fX N ≫ liftAt fY g hg f = φ ≫ proj fY N := by
  apply hom_extL
  · rw [Category.assoc, liftAt_fstL, ← Category.assoc, proj_map, hga, Category.assoc, proj_fstL]
  · rw [Category.assoc, liftAt_sndL, proj_sndL, Category.assoc, proj_sndL, ← Category.assoc, hφ]

end IsoSpread
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.PhilipponIsoSpread.FinSubfield"

end PhilipponIsoSpread
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.PhilipponIsoSpread.FinSubfield P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.PhilipponIsoSpread"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite PhilipponIsoSpread in
theorem solution
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X Y : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType fX]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [LocallyOfFiniteType fY]
    (e : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅
      pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (he : e.hom ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    ∃ (L : IntermediateField k K) (_ : FiniteDimensional k L)
      (e₀ : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≅
        pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (hι : Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K))),
      e₀.hom ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
        pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧
      e.hom ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 Y) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) =
        pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) ≫ e₀.hom := by
  classical

  have hcx : IsLimit (c k K X fX) := isLimitCone
  have hcy : IsLimit (c k K Y fY) := isLimitCone
  haveI : LocallyOfFinitePresentation fY := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : LocallyOfFinitePresentation fX := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI hCx : ∀ i : (FinIF k K)ᵒᵖ, CompactSpace ↥((D k K X fX).obj i) := fun i => compactSpace_pullback_gF k K X fX i.unop
  haveI hQx : ∀ i : (FinIF k K)ᵒᵖ, QuasiSeparatedSpace ↥((D k K X fX).obj i) :=
    fun i => quasiSeparatedSpace_pullback_gF k K X fX i.unop
  haveI hCy : ∀ i : (FinIF k K)ᵒᵖ, CompactSpace ↥((D k K Y fY).obj i) := fun i => compactSpace_pullback_gF k K Y fY i.unop
  haveI hQy : ∀ i : (FinIF k K)ᵒᵖ, QuasiSeparatedSpace ↥((D k K Y fY).obj i) :=
    fun i => quasiSeparatedSpace_pullback_gF k K Y fY i.unop
  have hinv : e.inv ≫ pullback.snd fX (gK k K) = pullback.snd fY (gK k K) := by
    rw [← he, Iso.inv_hom_id_assoc]

  let a : (c k K X fX).pt ⟶ Y := e.hom ≫ pullback.fst fY (gK k K)
  have ha : (c k K X fX).π ≫ t k K X fX = (Functor.const _).map (a ≫ fY) := by
    ext i
    change (c k K X fX).π.app i ≫ (pullback.fst fX (gF k K i.unop) ≫ fX) = a ≫ fY
    have e1 := c_π_fst (k := k) (K := K) (X := X) (fX := fX) i
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ fX) e1).trans (pullback.condition.trans
      ((congrArg (· ≫ gK k K) he).symm.trans ((Category.assoc e.hom _ _).trans
        ((congrArg (e.hom ≫ ·) pullback.condition.symm).trans (Category.assoc _ _ _).symm)))))
  obtain ⟨i, g, hga, hgf⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (D k K X fX) (t k K X fX) fY (c k K X fX) hcx a ha
  obtain ⟨Li⟩ := i
  have hga' : proj fX Li ≫ g = e.hom ≫ pullback.fst fY (gK k K) := hga

  let b : (c k K Y fY).pt ⟶ X := e.inv ≫ pullback.fst fX (gK k K)
  have hb : (c k K Y fY).π ≫ t k K Y fY = (Functor.const _).map (b ≫ fX) := by
    ext i
    change (c k K Y fY).π.app i ≫ (pullback.fst fY (gF k K i.unop) ≫ fY) = b ≫ fX
    have e1 := c_π_fst (k := k) (K := K) (X := Y) (fX := fY) i
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ fY) e1).trans (pullback.condition.trans
      ((congrArg (· ≫ gK k K) hinv).symm.trans ((Category.assoc e.inv _ _).trans
        ((congrArg (e.inv ≫ ·) pullback.condition.symm).trans (Category.assoc _ _ _).symm)))))
  obtain ⟨j, h, hhb, hhf⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (D k K Y fY) (t k K Y fY) fX (c k K Y fY) hcy b hb
  obtain ⟨Lj⟩ := j
  have hhb' : proj fY Lj ≫ h = e.inv ≫ pullback.fst fX (gK k K) := hhb

  let M : FinIF k K := FinSubfield.sup2 Li Lj
  have hiM : Li.1 ≤ M.1 := le_sup_left
  have hjM : Lj.1 ≤ M.1 := le_sup_right
  let G : ∀ (N : FinIF k K), M.1 ≤ N.1 → ((D k K X fX).obj (op N) ⟶ (D k K Y fY).obj (op N)) :=
    fun N hN => liftAt fY g hgf (homOp (hiM.trans hN))
  let H : ∀ (N : FinIF k K), M.1 ≤ N.1 → ((D k K Y fY).obj (op N) ⟶ (D k K X fX).obj (op N)) :=
    fun N hN => liftAt fX h hhf (homOp (hjM.trans hN))
  have hπG : ∀ (N : FinIF k K) (hN : M.1 ≤ N.1), proj fX N ≫ G N hN = e.hom ≫ proj fY N :=
    fun N hN => proj_liftAt g hgf _ e.hom he hga'
  have hπH : ∀ (N : FinIF k K) (hN : M.1 ≤ N.1), proj fY N ≫ H N hN = e.inv ≫ proj fX N :=
    fun N hN => proj_liftAt h hhf _ e.inv hinv hhb'
  have hGk : ∀ (N : FinIF k K) (hN : M.1 ≤ N.1), G N hN ≫ fstL fY N ≫ fY = fstL fX N ≫ fX :=
    fun N hN => liftAt_t g hgf _
  have hHk : ∀ (N : FinIF k K) (hN : M.1 ≤ N.1), H N hN ≫ fstL fX N ≫ fX = fstL fY N ≫ fY :=
    fun N hN => liftAt_t h hhf _

  have hu : (t k K X fX).app (op M) = (G M le_rfl ≫ H M le_rfl ≫ fstL fX M) ≫ fX := by
    change fstL fX M ≫ fX = (G M le_rfl ≫ H M le_rfl ≫ fstL fX M) ≫ fX
    simp only [Category.assoc]
    rw [hHk M le_rfl, hGk M le_rfl]
  have huv : proj fX M ≫ (G M le_rfl ≫ H M le_rfl ≫ fstL fX M) = proj fX M ≫ fstL fX M := by
    rw [← Category.assoc, hπG M le_rfl, Category.assoc, ← Category.assoc (proj fY M), hπH M le_rfl, Category.assoc,
      Iso.hom_inv_id_assoc]
  obtain ⟨n, hn, hGH⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType (D k K X fX) (t k K X fX) fX
    (c k K X fX) hcx (G M le_rfl ≫ H M le_rfl ≫ fstL fX M) (fstL fX M) hu (t_appL M) huv
  obtain ⟨Ln⟩ := n
  have hMn : M.1 ≤ Ln.1 := leOfHom hn.unop
  have hu' : (t k K Y fY).app (op M) = (H M le_rfl ≫ G M le_rfl ≫ fstL fY M) ≫ fY := by
    change fstL fY M ≫ fY = (H M le_rfl ≫ G M le_rfl ≫ fstL fY M) ≫ fY
    simp only [Category.assoc]
    rw [hGk M le_rfl, hHk M le_rfl]
  have huv' : proj fY M ≫ (H M le_rfl ≫ G M le_rfl ≫ fstL fY M) = proj fY M ≫ fstL fY M := by
    rw [← Category.assoc, hπH M le_rfl, Category.assoc, ← Category.assoc (proj fX M), hπG M le_rfl, Category.assoc,
      Iso.inv_hom_id_assoc]
  obtain ⟨n', hn', hHG⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType (D k K Y fY) (t k K Y fY) fY
    (c k K Y fY) hcy (H M le_rfl ≫ G M le_rfl ≫ fstL fY M) (fstL fY M) hu' (t_appL M) huv'
  obtain ⟨Ln'⟩ := n'
  have hMn' : M.1 ≤ Ln'.1 := leOfHom hn'.unop

  let N : FinIF k K := FinSubfield.sup2 Ln Ln'
  have hnN : Ln.1 ≤ N.1 := le_sup_left
  have hn'N : Ln'.1 ≤ N.1 := le_sup_right
  have hMN : M.1 ≤ N.1 := hMn.trans hnN

  have hGtr : G N hMN ≫ (D k K Y fY).map (homOp hMN) = (D k K X fX).map (homOp hMN) ≫ G M le_rfl :=
    liftAt_map g hgf _ _ _
  have hHtr : H N hMN ≫ (D k K X fX).map (homOp hMN) = (D k K Y fY).map (homOp hMN) ≫ H M le_rfl :=
    liftAt_map h hhf _ _ _
  have hHfst : H N hMN ≫ fstL fX N = (D k K Y fY).map (homOp hMN) ≫ H M le_rfl ≫ fstL fX M := by
    change liftAt fX h hhf _ ≫ _ = _ ≫ liftAt fX h hhf _ ≫ _
    rw [liftAt_fstL, liftAt_fstL, ← Category.assoc, D_map_map]
  have hGfst : G N hMN ≫ fstL fY N = (D k K X fX).map (homOp hMN) ≫ G M le_rfl ≫ fstL fY M := by
    change liftAt fY g hgf _ ≫ _ = _ ≫ liftAt fY g hgf _ ≫ _
    rw [liftAt_fstL, liftAt_fstL, ← Category.assoc, D_map_map]
  have hGH_N : G N hMN ≫ H N hMN = 𝟙 _ := by
    apply hom_extL
    · rw [Category.id_comp, Category.assoc, hHfst, ← Category.assoc, hGtr, Category.assoc,
        ← D_map_map (homOp hMn) (homOp hnN) (homOp hMN), Category.assoc, ← D_map_eq hn (homOp hMn), hGH,
        D_map_fstL, D_map_fstL]
    · rw [Category.id_comp, Category.assoc]
      change G N hMN ≫ liftAt fX h hhf _ ≫ sndL fX N = _
      rw [liftAt_sndL]
      exact liftAt_sndL g hgf _
  have hHG_N : H N hMN ≫ G N hMN = 𝟙 _ := by
    apply hom_extL
    · rw [Category.id_comp, Category.assoc, hGfst, ← Category.assoc, hHtr, Category.assoc,
        ← D_map_map (homOp hMn') (homOp hn'N) (homOp hMN), Category.assoc, ← D_map_eq hn' (homOp hMn'), hHG,
        D_map_fstL, D_map_fstL]
    · rw [Category.id_comp, Category.assoc]
      change H N hMN ≫ liftAt fY g hgf _ ≫ sndL fY N = _
      rw [liftAt_sndL]
      exact liftAt_sndL h hhf _

  refine ⟨N.1, N.2, ⟨G N hMN, H N hMN, hGH_N, hHG_N⟩, toK_comp_gF k K N, liftAt_sndL g hgf _, ?_⟩
  exact (hπG N hMN).symm

end S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic
end P2MW




set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic

set_option autoImplicit false

open scoped IntermediateField

namespace FinSubfield

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private abbrev _root_.FinSubfield.FinIF (k K : Type u) [Field k] [Field K] [Algebra k K] := {L : IntermediateField k K // FiniteDimensional k L}

p2m_export "FinSubfield" "FinIF"
scoped instance (L : FinIF k K) : FiniteDimensional k L.1 := L.2

noncomputable def adj [Algebra.IsAlgebraic k K] (x : K) : FinIF k K :=
  ⟨k⟮x⟯, IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩

theorem mem_adj [Algebra.IsAlgebraic k K] (x : K) : x ∈ (adj (k := k) x).1 :=
  IntermediateField.mem_adjoin_simple_self k x

noncomputable def sup2 (L L' : FinIF k K) : FinIF k K :=
  ⟨L.1 ⊔ L'.1, IntermediateField.finiteDimensional_sup L.1 L'.1⟩

theorem existsUnique_ringHom_forall_comp_eq [Algebra.IsAlgebraic k K]
    (R : Type u) [CommRing R] (φ : ∀ L : FinIF k K, L.1 →+* R)
    (hφ : ∀ (L L' : FinIF k K) (h : L.1 ≤ L'.1) (x : L.1), φ L' ⟨x.1, h x.2⟩ = φ L x) :
    ∃! ψ : K →+* R, ∀ (L : FinIF k K) (x : L.1), ψ x.1 = φ L x := by
  classical

  have hwd : ∀ (L L' : FinIF k K) (x : K) (hx : x ∈ L.1) (hx' : x ∈ L'.1), φ L ⟨x, hx⟩ = φ L' ⟨x, hx'⟩ := by
    intro L L' x hx hx'
    rw [← hφ L (sup2 L L') le_sup_left ⟨x, hx⟩, ← hφ L' (sup2 L L') le_sup_right ⟨x, hx'⟩]
  let ψf : K → R := fun x => φ (adj x) ⟨x, mem_adj x⟩
  have hψf : ∀ (L : FinIF k K) (x : K) (hx : x ∈ L.1), ψf x = φ L ⟨x, hx⟩ := fun L x hx => hwd _ _ _ _ _
  let ψ : K →+* R :=
    { toFun := ψf
      map_one' := by rw [hψf ⟨⊥, inferInstance⟩ 1 (one_mem _)]; exact map_one _
      map_zero' := by rw [hψf ⟨⊥, inferInstance⟩ 0 (zero_mem _)]; exact map_zero _
      map_mul' := by
        intro x y
        let L := sup2 (adj (k := k) x) (adj y)
        have hx : x ∈ L.1 := (le_sup_left : (adj (k := k) x).1 ≤ L.1) (mem_adj x)
        have hy : y ∈ L.1 := (le_sup_right : (adj (k := k) y).1 ≤ L.1) (mem_adj y)
        rw [hψf L x hx, hψf L y hy, hψf L (x * y) (mul_mem hx hy), ← map_mul]
        rfl
      map_add' := by
        intro x y
        let L := sup2 (adj (k := k) x) (adj y)
        have hx : x ∈ L.1 := (le_sup_left : (adj (k := k) x).1 ≤ L.1) (mem_adj x)
        have hy : y ∈ L.1 := (le_sup_right : (adj (k := k) y).1 ≤ L.1) (mem_adj y)
        rw [hψf L x hx, hψf L y hy, hψf L (x + y) (add_mem hx hy), ← map_add]
        rfl }
  refine ⟨ψ, fun L x => hψf L x.1 x.2, ?_⟩
  intro ψ' hψ'
  ext x
  change ψ' x = ψf x
  rw [hψf (adj x) x (mem_adj x)]
  exact hψ' (adj x) ⟨x, mem_adj x⟩

end FinSubfield
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic.FinSubfield"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FinSubfieldAux

variable (k K : Type u) [Field k] [Field K] [Algebra k K] (X : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of k))

private abbrev _root_.FinSubfieldAux.FinIF := FinSubfield.FinIF k K

p2m_export "FinSubfieldAux" "FinIF"

noncomputable abbrev gF (L : FinIF k K) : Spec (CommRingCat.of L.1) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k L.1))

noncomputable abbrev gK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

theorem incl_comp_gF {L₂ L₁ : FinIF k K} (h : L₂.1 ≤ L₁.1) :
    Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) ≫ gF k K L₂ = gF k K L₁ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem toK_comp_gF (L : FinIF k K) :
    Spec.map (CommRingCat.ofHom (algebraMap L.1 K)) ≫ gF k K L = gK k K := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

noncomputable def D : (FinIF k K)ᵒᵖ ⥤ Scheme.{u} where
  obj i := pullback fX (gF k K i.unop)
  map {i j} f := pullback.map fX (gF k K i.unop) fX (gF k K j.unop) (𝟙 X)
      (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, incl_comp_gF])
  map_id i := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.id_comp, Category.comp_id]
    · rw [pullback.lift_snd, Category.id_comp]
      convert Category.comp_id _
      rw [← Spec.map_id]
      rfl
  map_comp {i j l} f g := by
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.assoc, Category.comp_id]
    · simp only [pullback.lift_snd, Category.assoc, pullback.lift_snd_assoc]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl

noncomputable def t : D k K X fX ⟶ (Functor.const _).obj (Spec (CommRingCat.of k)) where
  app i := pullback.fst fX (gF k K i.unop) ≫ fX
  naturality {i j} f := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, D]
    rw [← Category.assoc, pullback.lift_fst, Category.comp_id]

noncomputable def c : Cone (D k K X fX) where
  pt := pullback fX (gK k K)
  π :=
    { app := fun i => pullback.map fX (gK k K) fX (gF k K i.unop) (𝟙 X)
          (Spec.map (CommRingCat.ofHom (algebraMap (i.unop).1 K))) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, toK_comp_gF])
      naturality := by
        intro i j f
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, D]
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
        · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
          rfl }

scoped instance : IsDirectedOrder (FinIF k K) :=
  ⟨fun L L' => ⟨FinSubfield.sup2 L L', le_sup_left (a := L.1), le_sup_right (a := L.1)⟩⟩

scoped instance : Nonempty (FinIF k K) := ⟨⟨⊥, inferInstance⟩⟩

scoped instance : IsFiltered (FinIF k K) := inferInstance

scoped instance : IsCofiltered (FinIF k K)ᵒᵖ := inferInstance

section RingOf

noncomputable def ringOf {W : Scheme.{u}} {B : CommRingCat.{u}} (g : W ⟶ Spec B) : B ⟶ Γ(W, ⊤) :=
  (Scheme.ΓSpecIso B).inv ≫ g.appTop

noncomputable def toSpec {W : Scheme.{u}} {B : CommRingCat.{u}} (φ : B ⟶ Γ(W, ⊤)) : W ⟶ Spec B :=
  ΓSpec.adjunction.homEquiv W (op B) φ.op

theorem ringOf_toSpec {W : Scheme.{u}} {B : CommRingCat.{u}} (φ : B ⟶ Γ(W, ⊤)) : ringOf (toSpec φ) = φ :=
  ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ

theorem ext_ringOf {W : Scheme.{u}} {B : CommRingCat.{u}} {g₁ g₂ : W ⟶ Spec B} (h : ringOf g₁ = ringOf g₂) : g₁ = g₂ := by
  apply ext_of_isAffine
  simpa [ringOf, Iso.cancel_iso_inv_left] using h

theorem toSpec_ringOf {W : Scheme.{u}} {B : CommRingCat.{u}} (g : W ⟶ Spec B) : toSpec (ringOf g) = g :=
  ext_ringOf (ringOf_toSpec _)

theorem ringOf_comp_specMap {W : Scheme.{u}} {B B' : CommRingCat.{u}} (g : W ⟶ Spec B) (u : B' ⟶ B) :
    ringOf (g ≫ Spec.map u) = u ≫ ringOf g := by
  simp only [ringOf, Scheme.Hom.comp_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

theorem ringOf_precomp {W W' : Scheme.{u}} {B : CommRingCat.{u}} (m : W' ⟶ W) (g : W ⟶ Spec B) :
    ringOf (m ≫ g) = ringOf g ≫ m.appTop := by
  simp only [ringOf, Scheme.Hom.comp_appTop, Category.assoc]

end RingOf
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic.FinSubfield"

section Limit

variable {k K X fX}

noncomputable def bot' : FinIF k K := ⟨⊥, inferInstance⟩

noncomputable def conePhi (s : Cone (D k K X fX)) (L : FinIF k K) : L.1 →+* Γ(s.pt, ⊤) :=
  (ringOf (s.π.app (op L) ≫ pullback.snd fX (gF k K L))).hom

theorem ringOf_π_snd (s : Cone (D k K X fX)) (L : FinIF k K) :
    ringOf (s.π.app (op L) ≫ pullback.snd fX (gF k K L)) = CommRingCat.ofHom (conePhi s L) := rfl

theorem D_obj (i : (FinIF k K)ᵒᵖ) : (D k K X fX).obj i = pullback fX (gF k K i.unop) := rfl

theorem D_map_fst {i j : (FinIF k K)ᵒᵖ} (f : i ⟶ j) :
    (D k K X fX).map f ≫ pullback.fst fX (gF k K j.unop) = pullback.fst fX (gF k K i.unop) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem D_map_snd {i j : (FinIF k K)ᵒᵖ} (f : i ⟶ j) :
    (D k K X fX).map f ≫ pullback.snd fX (gF k K j.unop) =
      pullback.snd fX (gF k K i.unop) ≫ Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom) :=
  pullback.lift_snd _ _ _

theorem c_π_fst (i : (FinIF k K)ᵒᵖ) :
    (c k K X fX).π.app i ≫ pullback.fst fX (gF k K i.unop) = pullback.fst fX (gK k K) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem c_π_snd (i : (FinIF k K)ᵒᵖ) :
    (c k K X fX).π.app i ≫ pullback.snd fX (gF k K i.unop) =
      pullback.snd fX (gK k K) ≫ Spec.map (CommRingCat.ofHom (algebraMap (i.unop).1 K)) :=
  pullback.lift_snd _ _ _

theorem π_snd_eq (s : Cone (D k K X fX)) {L L' : FinIF k K} (h : L.1 ≤ L'.1) :
    s.π.app (op L) ≫ pullback.snd fX (gF k K L) =
      (s.π.app (op L') ≫ pullback.snd fX (gF k K L')) ≫
        Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) := by
  have hw := s.w (homOfLE (show L ≤ L' from h)).op
  have := congrArg (· ≫ pullback.snd fX (gF k K L)) hw
  beta_reduce at this
  erw [Category.assoc, D_map_snd] at this
  erw [Category.assoc]
  exact this.symm

theorem π_fst_eq (s : Cone (D k K X fX)) {L L' : FinIF k K} (h : L.1 ≤ L'.1) :
    s.π.app (op L) ≫ pullback.fst fX (gF k K L) = s.π.app (op L') ≫ pullback.fst fX (gF k K L') := by
  have hw := s.w (homOfLE (show L ≤ L' from h)).op
  have := congrArg (· ≫ pullback.fst fX (gF k K L)) hw
  beta_reduce at this
  erw [Category.assoc, D_map_fst] at this
  exact this.symm

theorem conePhi_compat (s : Cone (D k K X fX)) (L L' : FinIF k K) (h : L.1 ≤ L'.1) (x : L.1) :
    conePhi s L' ⟨x.1, h x.2⟩ = conePhi s L x := by
  have h2 := (congrArg ringOf (π_snd_eq s h)).trans
    (ringOf_comp_specMap (s.π.app (op L') ≫ pullback.snd fX (gF k K L'))
      (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom))
  change CommRingCat.ofHom (conePhi s L) = _ ≫ CommRingCat.ofHom (conePhi s L') at h2
  have h3 := congrArg (fun φ : CommRingCat.of L.1 ⟶ Γ(s.pt, ⊤) => φ.hom x) h2
  exact h3.symm

variable [Algebra.IsAlgebraic k K]

noncomputable def conePsi (s : Cone (D k K X fX)) : K →+* Γ(s.pt, ⊤) :=
  (FinSubfield.existsUnique_ringHom_forall_comp_eq Γ(s.pt, ⊤) (conePhi s) (conePhi_compat s)).exists.choose

theorem conePsi_spec (s : Cone (D k K X fX)) (L : FinIF k K) (x : L.1) : conePsi s x.1 = conePhi s L x :=
  (FinSubfield.existsUnique_ringHom_forall_comp_eq Γ(s.pt, ⊤) (conePhi s) (conePhi_compat s)).exists.choose_spec L x

theorem conePsi_unique (s : Cone (D k K X fX)) (ψ' : K →+* Γ(s.pt, ⊤))
    (h : ∀ (L : FinIF k K) (x : L.1), ψ' x.1 = conePhi s L x) : ψ' = conePsi s :=
  (FinSubfield.existsUnique_ringHom_forall_comp_eq Γ(s.pt, ⊤) (conePhi s) (conePhi_compat s)).unique h
    (conePsi_spec s)

noncomputable def toSpecK (s : Cone (D k K X fX)) : s.pt ⟶ Spec (CommRingCat.of K) :=
  toSpec (CommRingCat.ofHom (conePsi s))

theorem toSpecK_comp (s : Cone (D k K X fX)) (L : FinIF k K) :
    toSpecK s ≫ Spec.map (CommRingCat.ofHom (algebraMap L.1 K)) = s.π.app (op L) ≫ pullback.snd fX (gF k K L) := by
  apply ext_ringOf
  refine (ringOf_comp_specMap _ _).trans ?_
  rw [toSpecK, ringOf_toSpec]
  change _ = CommRingCat.ofHom (conePhi s L)
  rw [← CommRingCat.ofHom_comp]
  congr 1
  ext x
  exact conePsi_spec s L x

theorem lift_w (s : Cone (D k K X fX)) :
    (s.π.app (op bot') ≫ pullback.fst fX (gF k K bot')) ≫ fX = toSpecK s ≫ gK k K := by
  have e1 := congrArg (s.π.app (op bot') ≫ ·) (pullback.condition (f := fX) (g := gF k K bot'))
  have e2 := congrArg (· ≫ gF k K bot') (toSpecK_comp s bot')
  have e3 : (toSpecK s ≫ Spec.map (CommRingCat.ofHom (algebraMap bot'.1 K))) ≫ gF k K bot' = toSpecK s ≫ gK k K := by
    erw [Category.assoc, toK_comp_gF]
    try rfl
  beta_reduce at e1 e2
  exact ((Category.assoc _ _ _).trans e1).trans (((Category.assoc _ _ _).symm.trans e2.symm).trans e3)

noncomputable def isLimitCone : IsLimit (c k K X fX) where
  lift s := pullback.lift (s.π.app (op bot') ≫ pullback.fst fX (gF k K bot')) (toSpecK s) (lift_w s)
  fac s j := by
    obtain ⟨L⟩ := j
    apply pullback.hom_ext
    · dsimp only [c, D, Opposite.unop_op]
      rw [Category.assoc, pullback.lift_fst, Category.comp_id, pullback.lift_fst]
      exact π_fst_eq s (show bot'.1 ≤ L.1 from bot_le)
    · dsimp only [c, D, Opposite.unop_op]
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
      exact toSpecK_comp s L
  uniq s m hm := by
    apply pullback.hom_ext
    · have := hm (op bot')
      dsimp only [c, D] at this ⊢
      rw [pullback.lift_fst, ← this, Category.assoc, pullback.lift_fst, Category.comp_id]
    · dsimp only [c, D] at hm ⊢
      rw [pullback.lift_snd]
      apply ext_ringOf
      rw [toSpecK, ringOf_toSpec]
      have key : (ringOf (m ≫ pullback.snd fX (gK k K))).hom = conePsi s := by
        apply conePsi_unique
        intro L x
        have hL := hm (op L)
        dsimp only [Opposite.unop_op] at hL
        have a1 := congrArg (· ≫ pullback.snd fX (gF k K L)) hL
        have a3 := c_π_snd (k := k) (K := K) (X := X) (fX := fX) (op L)
        dsimp only [c, D, Opposite.unop_op] at a1 a3
        have h1 : s.π.app (op L) ≫ pullback.snd fX (gF k K L) =
            (m ≫ pullback.snd fX (gK k K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap L.1 K)) :=
          a1.symm.trans ((Category.assoc _ _ _).trans (((congrArg (m ≫ ·) a3)).trans (Category.assoc _ _ _).symm))
        have h2 := (congrArg ringOf h1).trans (ringOf_comp_specMap _ _)
        change CommRingCat.ofHom (conePhi s L) = _ at h2
        have h3 := congrArg (fun φ : CommRingCat.of L.1 ⟶ Γ(s.pt, ⊤) => φ.hom x) h2
        simpa using h3.symm
      have : ringOf (m ≫ pullback.snd fX (gK k K)) = CommRingCat.ofHom (conePsi s) := by
        ext1; exact key
      exact this

end Limit
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic.FinSubfield"

section Instances

scoped instance isAffineHom_D_map {i j : (FinIF k K)ᵒᵖ} (f : i ⟶ j) : IsAffineHom ((D k K X fX).map f) := by
  dsimp only [D]
  exact MorphismProperty.pullbackMap (P := @IsAffineHom)
    (f := fX) (g := gF k K i.unop) (f' := fX) (g' := gF k K j.unop) (i₁ := 𝟙 X)
    (i₂ := Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom))
    inferInstance inferInstance (Category.id_comp _).symm (incl_comp_gF k K _).symm

scoped instance compactSpace_pullback_gF [CompactSpace X] (L : FinIF k K) : CompactSpace ↥(pullback fX (gF k K L)) := by
  haveI : IsAffineHom (gF k K L) := inferInstance
  haveI : QuasiCompact (gF k K L) := inferInstance
  infer_instance

scoped instance quasiSeparatedSpace_pullback_gF [QuasiSeparatedSpace X] (L : FinIF k K) :
    QuasiSeparatedSpace ↥(pullback fX (gF k K L)) := by
  haveI : QuasiSeparated (pullback.fst fX (gF k K L)) := inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst fX (gF k K L))

scoped instance quasiSeparatedSpace_D_obj [QuasiSeparatedSpace X] (i : (FinIF k K)ᵒᵖ) :
    QuasiSeparatedSpace ((D k K X fX).obj i) := by
  dsimp only [D]
  haveI : QuasiSeparated (pullback.fst fX (gF k K i.unop)) := inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst fX (gF k K i.unop))

end Instances
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic.FinSubfield"

end FinSubfieldAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic.FinSubfield P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic.FinSubfieldAux"

open FinSubfieldAux in
theorem solution
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X Y : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType fY]
    (f : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hf : f ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    ∃ (L : IntermediateField k K) (_ : FiniteDimensional k L)
      (g : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k L))))

      (hι : Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K))),

      g ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
        pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧

      f ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 Y) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) =
        pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) ≫ g := by
  classical
  let Dg := FinSubfieldAux.D k K X fX
  let tg := FinSubfieldAux.t k K X fX
  let cg := FinSubfieldAux.c k K X fX
  have hc : IsLimit cg := FinSubfieldAux.isLimitCone
  haveI : LocallyOfFinitePresentation fY := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  let a : cg.pt ⟶ Y := f ≫ pullback.fst fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have ha : cg.π ≫ tg = (Functor.const _).map (a ≫ fY) := by
    ext i
    change cg.π.app i ≫ (pullback.fst fX (gF k K i.unop) ≫ fX) = a ≫ fY
    have e1 := FinSubfieldAux.c_π_fst (k := k) (K := K) (X := X) (fX := fX) i
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ fX) e1).trans (pullback.condition.trans
      ((congrArg (· ≫ gK k K) hf).symm.trans ((Category.assoc f _ _).trans
        ((congrArg (f ≫ ·) pullback.condition.symm).trans (Category.assoc _ _ _).symm)))))
  haveI hC : ∀ i : (FinSubfieldAux.FinIF k K)ᵒᵖ, CompactSpace ↥(Dg.obj i) :=
    fun i => FinSubfieldAux.compactSpace_pullback_gF k K X fX i.unop
  haveI hQ : ∀ i : (FinSubfieldAux.FinIF k K)ᵒᵖ, QuasiSeparatedSpace ↥(Dg.obj i) :=
    fun i => FinSubfieldAux.quasiSeparatedSpace_pullback_gF k K X fX i.unop
  obtain ⟨i, g₀, hg₀a, hg₀f⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation Dg tg fY cg hc a ha
  obtain ⟨L⟩ := i

  have hw : g₀ ≫ fY = pullback.snd fX (gF k K L) ≫ gF k K L := by
    rw [hg₀f]
    exact pullback.condition
  let g : pullback fX (gF k K L) ⟶ pullback fY (gF k K L) := pullback.lift g₀ (pullback.snd fX (gF k K L)) hw
  refine ⟨L.1, L.2, g, toK_comp_gF k K L, pullback.lift_snd _ _ _, ?_⟩
  have hπ : cg.π.app (op L) ≫ g₀ = a := hg₀a
  dsimp only [cg, FinSubfieldAux.c] at hπ
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.assoc, pullback.lift_fst]
    exact hπ.symm
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc, hf, pullback.lift_snd]

end S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic
end P2MW




set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

namespace SchemeSpread

private noncomputable abbrev _root_.SchemeSpread.ι (F K : Type u) [CommRing F] [CommRing K] [Algebra F K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F) :=
  Spec.map (CommRingCat.ofHom (algebraMap F K))

p2m_export "SchemeSpread" "ι"
section Tower

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

theorem ι_comp (L : IntermediateField F K) : ι L K ≫ ι F L = ι F K := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq F L K]

scoped instance surjective_ι : Surjective (ι F K) := by
  refine ⟨fun x => ?_⟩
  haveI : Subsingleton ↥(Spec (CommRingCat.of F)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum F))
  exact ⟨(⊥ : PrimeSpectrum K), Subsingleton.elim _ _⟩

example (L : IntermediateField F K) (L' : IntermediateField L K)
    (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of L')) : X₀ ⟶ Spec (CommRingCat.of (L'.restrictScalars F)) := f₀

example (L : IntermediateField F K) (L' : IntermediateField L K) : ι (L'.restrictScalars F) K = ι L' K := rfl

theorem finiteDimensional_restrictScalars (L : IntermediateField F K) (L' : IntermediateField L K)
    [FiniteDimensional F L] [FiniteDimensional L L'] : FiniteDimensional F (L'.restrictScalars F) := by
  have : FiniteDimensional F L' := FiniteDimensional.trans F L L'
  exact this

end Tower

structure Model (F K : Type u) [Field F] [Field K] [Algebra F K] (Z : Scheme.{u}) (fZ : Z ⟶ Spec (CommRingCat.of K)) where
  X₀ : Scheme.{u}
  f₀ : X₀ ⟶ Spec (CommRingCat.of F)
  qc : CompactSpace X₀
  qs : QuasiSeparatedSpace X₀
  lft : LocallyOfFiniteType f₀
  g : Z ⟶ X₀
  pb : IsPullback g fZ f₀ (ι F K)

namespace Model

variable {F K : Type u} [Field F] [Field K] [Algebra F K] {Z : Scheme.{u}} {fZ : Z ⟶ Spec (CommRingCat.of K)}

section BaseChange

variable (m : Model F K Z fZ) (L : IntermediateField F K)

theorem w_baseChange : m.g ≫ m.f₀ = (fZ ≫ ι L K) ≫ ι F L := by
  rw [Category.assoc, ι_comp]; exact m.pb.w

noncomputable def gL : Z ⟶ pullback m.f₀ (ι F L) :=
  pullback.lift m.g (fZ ≫ ι L K) (m.w_baseChange L)

@[reassoc (attr := simp)]
theorem gL_fst : m.gL L ≫ pullback.fst m.f₀ (ι F L) = m.g := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem gL_snd : m.gL L ≫ pullback.snd m.f₀ (ι F L) = fZ ≫ ι L K := pullback.lift_snd _ _ _

theorem isPullback_gL : IsPullback (m.gL L) fZ (pullback.snd m.f₀ (ι F L)) (ι L K) :=
  IsPullback.of_right (by simpa only [gL_fst, ι_comp] using m.pb) (m.gL_snd L) (IsPullback.of_hasPullback _ _)

@[reducible] noncomputable def baseChange : Model L K Z fZ where
  X₀ := pullback m.f₀ (ι F L)
  f₀ := pullback.snd m.f₀ (ι F L)
  qc := by
    haveI := m.qc
    haveI : IsAffineHom (ι F L) := inferInstance
    infer_instance
  qs := by
    haveI := m.qs
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst m.f₀ (ι F L))
  lft := by haveI := m.lft; infer_instance
  g := m.gL L
  pb := m.isPullback_gL L

@[scoped simp] theorem baseChange_X₀ : (m.baseChange L).X₀ = pullback m.f₀ (ι F L) := rfl
@[scoped simp] theorem baseChange_f₀ : (m.baseChange L).f₀ = pullback.snd m.f₀ (ι F L) := rfl
@[scoped simp] theorem baseChange_g : (m.baseChange L).g = m.gL L := rfl

theorem gL_preimage (W : m.X₀.Opens) :
    m.gL L ⁻¹ᵁ (pullback.fst m.f₀ (ι F L) ⁻¹ᵁ W) = m.g ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, gL_fst]

theorem baseChange_g_preimage (W : m.X₀.Opens) :
    (m.baseChange L).g ⁻¹ᵁ (pullback.fst m.f₀ (ι F L) ⁻¹ᵁ W) = m.g ⁻¹ᵁ W :=
  m.gL_preimage L W

end BaseChange

end Model
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

section Inputs

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
  {Z : Scheme.{u}} {fZ : Z ⟶ Spec (CommRingCat.of K)}

theorem exists_open_descends (m : Model F K Z fZ) (U : Z.Opens) (hU : IsCompact (U : Set Z)) :
    ∃ (L : IntermediateField F K) (_ : FiniteDimensional F L) (V : (m.baseChange L).X₀.Opens),
      IsCompact (V : Set (m.baseChange L).X₀) ∧ (m.baseChange L).g ⁻¹ᵁ V = U := by
  let e := m.pb.isoPullback
  have hU' : IsCompact ((e.inv ⁻¹ᵁ U : (pullback m.f₀ (ι F K)).Opens) : Set ↥(pullback m.f₀ (ι F K))) :=
    QuasiCompact.isCompact_preimage (f := e.inv) (U : Set Z) U.isOpen hU
  obtain ⟨L, hL, hι, V, hVc, hV⟩ :=
    P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_preimage_pullback_map_eq_of_isCompact_of_isAlgebraic.solution
      F K m.X₀ m.f₀ (e.inv ⁻¹ᵁ U) hU'
  refine ⟨L, hL, V, hVc, ?_⟩
  have hg : (m.baseChange L).g = e.hom ≫ pullback.map m.f₀ (ι F K) m.f₀ (ι F L) (𝟙 m.X₀) (ι L K) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]; simp [e]
    · rw [Category.assoc, pullback.lift_snd]; simp [e]
  rw [hg, Scheme.Hom.comp_preimage, hV, ← Scheme.Hom.comp_preimage, Iso.hom_inv_id, Scheme.Hom.id_preimage]

theorem exists_iso_descends (m n : Model F K Z fZ) :
    ∃ (L : IntermediateField F K) (_ : FiniteDimensional F L) (e₀ : (m.baseChange L).X₀ ≅ (n.baseChange L).X₀),
      e₀.hom ≫ (n.baseChange L).f₀ = (m.baseChange L).f₀ ∧ (n.baseChange L).g = (m.baseChange L).g ≫ e₀.hom := by
  haveI := m.qc; haveI := m.qs; haveI := m.lft; haveI := n.qc; haveI := n.qs; haveI := n.lft
  let eX := m.pb.isoPullback
  let eY := n.pb.isoPullback
  let e : pullback m.f₀ (ι F K) ≅ pullback n.f₀ (ι F K) := eX.symm ≪≫ eY
  have he : e.hom ≫ pullback.snd n.f₀ (ι F K) = pullback.snd m.f₀ (ι F K) := by
    simp [e, eX, eY]
  obtain ⟨L, hL, e₀, hι, h1, h2⟩ :=
    P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.solution
      F K m.X₀ n.X₀ m.f₀ n.f₀ e he
  refine ⟨L, hL, e₀, h1, ?_⟩
  have hgm : (m.baseChange L).g = eX.hom ≫ pullback.map m.f₀ (ι F K) m.f₀ (ι F L) (𝟙 m.X₀) (ι L K) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]; simp [eX]
    · rw [Category.assoc, pullback.lift_snd]; simp [eX]
  have hgn : (n.baseChange L).g = eY.hom ≫ pullback.map n.f₀ (ι F K) n.f₀ (ι F L) (𝟙 n.X₀) (ι L K) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]; simp [eY]
    · rw [Category.assoc, pullback.lift_snd]; simp [eY]
  have : eY.hom = eX.hom ≫ e.hom := by simp [e]
  rw [hgn, this, Category.assoc, h2, hgm, Category.assoc]

end Inputs
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

namespace Model

variable {F K : Type u} [Field F] [Field K] [Algebra F K] {Z : Scheme.{u}} {fZ : Z ⟶ Spec (CommRingCat.of K)}
  (m : Model F K Z fZ) {L L' : IntermediateField F K}

noncomputable abbrev incl (h : L ≤ L') : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of L) :=
  Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)

theorem incl_comp_ι (h : L ≤ L') : incl h ≫ ι F L = ι F L' := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem ι_comp_incl (h : L ≤ L') : ι L' K ≫ incl h = ι L K := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

scoped instance isAffineHom_incl (h : L ≤ L') : IsAffineHom (incl (F := F) (K := K) h) := inferInstance

noncomputable def transition (h : L ≤ L') : (m.baseChange L').X₀ ⟶ (m.baseChange L).X₀ :=
  pullback.map m.f₀ (ι F L') m.f₀ (ι F L) (𝟙 _) (incl h) (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, incl_comp_ι])

@[reassoc (attr := simp)]
theorem transition_fst (h : L ≤ L') :
    m.transition h ≫ pullback.fst m.f₀ (ι F L) = pullback.fst m.f₀ (ι F L') := by
  rw [transition, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
theorem transition_snd (h : L ≤ L') :
    m.transition h ≫ pullback.snd m.f₀ (ι F L) = pullback.snd m.f₀ (ι F L') ≫ incl h := by
  rw [transition, pullback.lift_snd]

@[reassoc (attr := simp)]
theorem gL_transition (h : L ≤ L') : m.gL L' ≫ m.transition h = m.gL L := by
  apply pullback.hom_ext
  · rw [Category.assoc, transition_fst, gL_fst, gL_fst]
  · rw [Category.assoc, transition_snd, gL_snd_assoc, gL_snd, ι_comp_incl]

theorem isPullback_transition (h : L ≤ L') :
    IsPullback (m.transition h) (pullback.snd m.f₀ (ι F L')) (pullback.snd m.f₀ (ι F L)) (incl h) :=
  IsPullback.of_right (by simpa only [transition_fst, incl_comp_ι] using (IsPullback.of_hasPullback m.f₀ (ι F L')))
    (m.transition_snd h) (IsPullback.of_hasPullback _ _)

scoped instance quasiCompact_transition (h : L ≤ L') : QuasiCompact (m.transition h) :=
  MorphismProperty.of_isPullback (m.isPullback_transition h).flip inferInstance

end Model
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

section TwoOpens

variable {X : Scheme.{u}} (U V : X.Opens)

theorem range_ι_preimage_ι : Set.range ((U.ι ⁻¹ᵁ V).ι ≫ U.ι) = (U : Set X) ∩ (V : Set X) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨((U.ι ⁻¹ᵁ V).ι y).2, y.2⟩
  · rintro ⟨hU, hV⟩
    exact ⟨⟨⟨x, hU⟩, hV⟩, rfl⟩

noncomputable def crossing : (U.ι ⁻¹ᵁ V).toScheme ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι ((U.ι ⁻¹ᵁ V).ι ≫ U.ι) (by
    rw [range_ι_preimage_ι, Scheme.Opens.range_ι]
    exact Set.inter_subset_right)

@[reassoc (attr := simp)]
theorem crossing_ι : crossing U V ≫ V.ι = (U.ι ⁻¹ᵁ V).ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _

scoped instance isOpenImmersion_crossing : IsOpenImmersion (crossing U V) := by
  haveI : IsOpenImmersion (crossing U V ≫ V.ι) := by rw [crossing_ι]; infer_instance
  exact IsOpenImmersion.of_comp (crossing U V) V.ι

theorem opensRange_crossing : (crossing U V).opensRange = V.ι ⁻¹ᵁ U := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change V.ι (crossing U V y) ∈ U
    rw [← Scheme.Hom.comp_apply, crossing_ι]
    exact ((U.ι ⁻¹ᵁ V).ι y).2
  · intro hx
    refine ⟨⟨⟨V.ι x, hx⟩, x.2⟩, ?_⟩
    apply V.ι.injective
    rw [← Scheme.Hom.comp_apply, crossing_ι]
    rfl

theorem isPullback_crossing : IsPullback (U.ι ⁻¹ᵁ V).ι (crossing U V) U.ι V.ι :=
  (IsOpenImmersion.isPullback (crossing U V) (U.ι ⁻¹ᵁ V).ι V.ι U.ι (crossing_ι U V).symm
    (by rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι])).flip

theorem isCompact_ι_preimage [QuasiSeparatedSpace X] (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X)) :
    IsCompact ((U.ι ⁻¹ᵁ V : U.toScheme.Opens) : Set U) := by
  have h : IsCompact ((U : Set X) ∩ V) := QuasiSeparatedSpace.inter_isCompact _ _ U.isOpen hU V.isOpen hV
  rw [U.ι.isOpenEmbedding.isInducing.isCompact_iff]
  convert h
  rw [← range_ι_preimage_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]

end TwoOpens
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

section Phases

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
  {X : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of K)} (U V : X.Opens)

theorem phase1 [QuasiSeparatedSpace X] (hUc : IsCompact (U : Set X)) (hVc : IsCompact (V : Set X))
    (mU : Model F K U (U.ι ≫ fX)) (mV : Model F K V (V.ι ≫ fX)) :
    ∃ (L : IntermediateField F K) (_ : FiniteDimensional F L)
      (mU' : Model L K U (U.ι ≫ fX)) (mV' : Model L K V (V.ι ≫ fX))
      (WU : mU'.X₀.Opens) (WV : mV'.X₀.Opens),
      IsCompact (WU : Set mU'.X₀) ∧ IsCompact (WV : Set mV'.X₀) ∧
      mU'.g ⁻¹ᵁ WU = U.ι ⁻¹ᵁ V ∧ mV'.g ⁻¹ᵁ WV = V.ι ⁻¹ᵁ U := by
  obtain ⟨L₁, hL₁, WU₁, hWU₁c, hWU₁⟩ := exists_open_descends mU (U.ι ⁻¹ᵁ V) (isCompact_ι_preimage U V hUc hVc)
  obtain ⟨L₂, hL₂, WV₁, hWV₁c, hWV₁⟩ := exists_open_descends mV (V.ι ⁻¹ᵁ U) (isCompact_ι_preimage V U hVc hUc)
  haveI := hL₁
  haveI := hL₂
  refine ⟨L₁ ⊔ L₂, inferInstance, mU.baseChange (L₁ ⊔ L₂), mV.baseChange (L₁ ⊔ L₂),
    mU.transition le_sup_left ⁻¹ᵁ WU₁, mV.transition le_sup_right ⁻¹ᵁ WV₁, ?_, ?_, ?_, ?_⟩
  · exact QuasiCompact.isCompact_preimage (f := mU.transition le_sup_left) _ WU₁.isOpen hWU₁c
  · exact QuasiCompact.isCompact_preimage (f := mV.transition le_sup_right) _ WV₁.isOpen hWV₁c
  · rw [← hWU₁, Model.baseChange_g, Model.baseChange_g, ← Scheme.Hom.comp_preimage, Model.gL_transition]
  · rw [← hWV₁, Model.baseChange_g, Model.baseChange_g, ← Scheme.Hom.comp_preimage, Model.gL_transition]

noncomputable def modelCapLeft [QuasiSeparatedSpace X] (mU : Model F K U (U.ι ≫ fX)) (WU : mU.X₀.Opens)
    (hWUc : IsCompact (WU : Set mU.X₀)) (hWU : mU.g ⁻¹ᵁ WU = U.ι ⁻¹ᵁ V) :
    Model F K (U.ι ⁻¹ᵁ V) ((U.ι ⁻¹ᵁ V).ι ≫ U.ι ≫ fX) where
  X₀ := WU
  f₀ := WU.ι ≫ mU.f₀
  qc := isCompact_iff_compactSpace.mp hWUc
  qs := by haveI := mU.qs; exact WU.ι.isOpenEmbedding.quasiSeparatedSpace
  lft := by haveI := mU.lft; infer_instance
  g := mU.g.resLE WU (U.ι ⁻¹ᵁ V) (by rw [hWU])
  pb := by
    have sq : IsPullback (mU.g.resLE WU (U.ι ⁻¹ᵁ V) (by rw [hWU])) (U.ι ⁻¹ᵁ V).ι WU.ι mU.g :=
      IsOpenImmersion.isPullback _ _ _ _ (by rw [Scheme.Hom.resLE_comp_ι])
        (by rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, hWU])
    exact sq.paste_vert mU.pb

omit [Algebra.IsAlgebraic F K] in
theorem range_crossing_comp_subset (mV : Model F K V (V.ι ≫ fX)) (WV : mV.X₀.Opens)
    (hWV : mV.g ⁻¹ᵁ WV = V.ι ⁻¹ᵁ U) : Set.range (crossing U V ≫ mV.g) ⊆ Set.range WV.ι := by
  rintro _ ⟨y, rfl⟩
  have hy : crossing U V y ∈ mV.g ⁻¹ᵁ WV := by rw [hWV, ← opensRange_crossing]; exact ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact hy

noncomputable def modelCapRight [QuasiSeparatedSpace X] (mV : Model F K V (V.ι ≫ fX)) (WV : mV.X₀.Opens)
    (hWVc : IsCompact (WV : Set mV.X₀)) (hWV : mV.g ⁻¹ᵁ WV = V.ι ⁻¹ᵁ U) :
    Model F K (U.ι ⁻¹ᵁ V) ((U.ι ⁻¹ᵁ V).ι ≫ U.ι ≫ fX) where
  X₀ := WV
  f₀ := WV.ι ≫ mV.f₀
  qc := isCompact_iff_compactSpace.mp hWVc
  qs := by haveI := mV.qs; exact WV.ι.isOpenEmbedding.quasiSeparatedSpace
  lft := by haveI := mV.lft; infer_instance
  g := IsOpenImmersion.lift WV.ι (crossing U V ≫ mV.g) (range_crossing_comp_subset U V mV WV hWV)
  pb := by
    have sq : IsPullback (IsOpenImmersion.lift WV.ι (crossing U V ≫ mV.g) (range_crossing_comp_subset U V mV WV hWV))
        (crossing U V) WV.ι mV.g :=
      IsOpenImmersion.isPullback _ _ _ _ (by rw [IsOpenImmersion.lift_fac])
        (by rw [Scheme.Opens.opensRange_ι, opensRange_crossing, hWV])
    have := sq.paste_vert mV.pb
    rwa [crossing_ι_assoc] at this

theorem phase2 [QuasiSeparatedSpace X] (mU : Model F K U (U.ι ≫ fX)) (mV : Model F K V (V.ι ≫ fX))
    (WU : mU.X₀.Opens) (WV : mV.X₀.Opens) (hWUc : IsCompact (WU : Set mU.X₀)) (hWVc : IsCompact (WV : Set mV.X₀))
    (hWU : mU.g ⁻¹ᵁ WU = U.ι ⁻¹ᵁ V) (hWV : mV.g ⁻¹ᵁ WV = V.ι ⁻¹ᵁ U) :
    ∃ (L : IntermediateField F K) (_ : FiniteDimensional F L)
      (W₀ : Scheme.{u}) (iU : W₀ ⟶ (mU.baseChange L).X₀) (iV : W₀ ⟶ (mV.baseChange L).X₀)
      (_ : IsOpenImmersion iU) (_ : IsOpenImmersion iV) (gW : (U.ι ⁻¹ᵁ V).toScheme ⟶ W₀),
      iU ≫ (mU.baseChange L).f₀ = iV ≫ (mV.baseChange L).f₀ ∧
      (mU.baseChange L).g ⁻¹ᵁ iU.opensRange ≤ U.ι ⁻¹ᵁ V ∧
      (mV.baseChange L).g ⁻¹ᵁ iV.opensRange ≤ V.ι ⁻¹ᵁ U ∧
      gW ≫ iU = (U.ι ⁻¹ᵁ V).ι ≫ (mU.baseChange L).g ∧
      gW ≫ iV = crossing U V ≫ (mV.baseChange L).g := by
  let mWU := modelCapLeft U V mU WU hWUc hWU
  let mWV := modelCapRight U V mV WV hWVc hWV
  obtain ⟨L, hL, e₀, he₀f, he₀g⟩ := exists_iso_descends mWU mWV

  let jU : (mWU.baseChange L).X₀ ⟶ (mU.baseChange L).X₀ :=
    pullback.map mWU.f₀ (ι F L) mU.f₀ (ι F L) WU.ι (𝟙 _) (𝟙 _) ((Category.comp_id _).trans rfl)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  let jV : (mWV.baseChange L).X₀ ⟶ (mV.baseChange L).X₀ :=
    pullback.map mWV.f₀ (ι F L) mV.f₀ (ι F L) WV.ι (𝟙 _) (𝟙 _) ((Category.comp_id _).trans rfl)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  haveI hWUι : IsOpenImmersion (WU.ι : mWU.X₀ ⟶ mU.X₀) := inferInstanceAs (IsOpenImmersion WU.ι)
  haveI hWVι : IsOpenImmersion (WV.ι : mWV.X₀ ⟶ mV.X₀) := inferInstanceAs (IsOpenImmersion WV.ι)
  have hjU : IsOpenImmersion jU :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) hWUι inferInstance rfl (Category.id_comp _).symm
  have hjV : IsOpenImmersion jV :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) hWVι inferInstance rfl (Category.id_comp _).symm
  have jU_fst : jU ≫ pullback.fst mU.f₀ (ι F L) = pullback.fst mWU.f₀ (ι F L) ≫ WU.ι := pullback.lift_fst _ _ _
  have jU_snd : jU ≫ pullback.snd mU.f₀ (ι F L) = pullback.snd mWU.f₀ (ι F L) :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have jV_fst : jV ≫ pullback.fst mV.f₀ (ι F L) = pullback.fst mWV.f₀ (ι F L) ≫ WV.ι := pullback.lift_fst _ _ _
  have jV_snd : jV ≫ pullback.snd mV.f₀ (ι F L) = pullback.snd mWV.f₀ (ι F L) :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  haveI : IsOpenImmersion (e₀.hom ≫ jV) := by haveI := hjV; infer_instance
  refine ⟨L, hL, (mWU.baseChange L).X₀, jU, e₀.hom ≫ jV, hjU, inferInstance, (mWU.baseChange L).g, ?_, ?_, ?_, ?_, ?_⟩
  ·
    change jU ≫ pullback.snd mU.f₀ (ι F L) = (e₀.hom ≫ jV) ≫ pullback.snd mV.f₀ (ι F L)
    rw [jU_snd, Category.assoc, jV_snd]
    exact he₀f.symm
  ·
    intro x hx
    obtain ⟨w, hw⟩ := hx
    have : (mU.baseChange L).g x ∈ pullback.fst mU.f₀ (ι F L) ⁻¹ᵁ WU := by
      change pullback.fst mU.f₀ (ι F L) ((mU.baseChange L).g x) ∈ WU
      have e1 : (jU ≫ pullback.fst mU.f₀ (ι F L)) w = (pullback.fst mWU.f₀ (ι F L) ≫ WU.ι) w := by rw [jU_fst]
      simp only [Scheme.Hom.comp_apply] at e1
      rw [← hw, e1]
      exact (pullback.fst mWU.f₀ (ι F L) w).2
    rw [← hWU, ← mU.baseChange_g_preimage L]
    exact this
  ·
    intro x hx
    obtain ⟨w, hw⟩ := hx
    have : (mV.baseChange L).g x ∈ pullback.fst mV.f₀ (ι F L) ⁻¹ᵁ WV := by
      change pullback.fst mV.f₀ (ι F L) ((mV.baseChange L).g x) ∈ WV
      have e1 : ((e₀.hom ≫ jV) ≫ pullback.fst mV.f₀ (ι F L)) w = (e₀.hom ≫ pullback.fst mWV.f₀ (ι F L) ≫ WV.ι) w := by
        rw [Category.assoc, jV_fst]
      rw [← hw]
      simp only [Scheme.Hom.comp_apply] at e1 ⊢
      rw [e1]
      exact (pullback.fst mWV.f₀ (ι F L) (e₀.hom w)).2
    rw [← hWV, ← mV.baseChange_g_preimage L]
    exact this
  ·
    apply pullback.hom_ext
    · rw [Category.assoc, jU_fst, Category.assoc, Model.baseChange_g, Model.baseChange_g, Model.gL_fst_assoc,
        Model.gL_fst]
      exact Scheme.Hom.resLE_comp_ι _ _
    · rw [Category.assoc, jU_snd, Category.assoc, Model.baseChange_g, Model.baseChange_g, Model.gL_snd, Model.gL_snd,
        Category.assoc]
  ·
    have hg : (mWU.baseChange L).g ≫ e₀.hom = (mWV.baseChange L).g := he₀g.symm
    rw [← Category.assoc, hg]
    apply pullback.hom_ext
    · rw [Category.assoc, jV_fst, Category.assoc, Model.baseChange_g, Model.baseChange_g, Model.gL_fst_assoc,
        Model.gL_fst]
      exact IsOpenImmersion.lift_fac WV.ι (crossing U V ≫ mV.g) (range_crossing_comp_subset U V mV WV hWV)
    · rw [Category.assoc, jV_snd, Category.assoc, Model.baseChange_g, Model.baseChange_g, Model.gL_snd, Model.gL_snd]
      simp only [Category.assoc, crossing_ι_assoc]

end Phases
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

section Pushout

variable {W A B : Scheme.{u}} (iU : W ⟶ A) (iV : W ⟶ B) [IsOpenImmersion iU] [IsOpenImmersion iV]

scoped instance span_map_isOpenImmersion {i j : WalkingSpan} (u : i ⟶ j) : IsOpenImmersion ((span iU iV).map u) := by
  rcases u with _ | (_ | _)
  · change IsOpenImmersion ((span iU iV).map (𝟙 _)); rw [CategoryTheory.Functor.map_id]; infer_instance
  · change IsOpenImmersion iU; infer_instance
  · change IsOpenImmersion iV; infer_instance

scoped instance hasPushout_of_isOpenImmersion : HasPushout iU iV := inferInstance

scoped instance isOpenImmersion_inl : IsOpenImmersion (pushout.inl iU iV) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span iU iV) WalkingSpan.left))

scoped instance isOpenImmersion_inr : IsOpenImmersion (pushout.inr iU iV) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span iU iV) WalkingSpan.right))

theorem exists_of_inl_eq_inr (a : A) (b : B) (h : pushout.inl iU iV a = pushout.inr iU iV b) :
    ∃ w, iU w = a ∧ iV w = b := by
  obtain ⟨k, fi, fj, x, hx1, hx2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span iU iV)).mp h
  rcases k with _ | (_ | _)
  · rcases fi with _ | _; rcases fj with _ | _; exact ⟨x, hx1, hx2⟩
  · rcases fj with _ | _
  · rcases fi with _ | _

theorem inl_or_inr (x : ↥(pushout iU iV)) : (∃ a, pushout.inl iU iV a = x) ∨ ∃ b, pushout.inr iU iV b = x := by
  obtain ⟨k, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span iU iV) x
  rcases k with _ | (_ | _)
  · left
    refine ⟨iU y, ?_⟩
    rw [← hy, ← colimit.w (span iU iV) WalkingSpan.Hom.fst, Scheme.Hom.comp_apply]
    rfl
  · left; exact ⟨y, hy⟩
  · right; exact ⟨y, hy⟩

noncomputable def pushoutCover : (pushout iU iV).OpenCover :=
  Scheme.Cover.mkOfCovers (J := Bool) (fun b => bif b then A else B)
    (fun b => match b with
      | true => pushout.inl iU iV
      | false => pushout.inr iU iV)
    (fun x => by
      rcases inl_or_inr iU iV x with ⟨a, ha⟩ | ⟨b, hb⟩
      · exact ⟨true, a, ha⟩
      · exact ⟨false, b, hb⟩)
    (by
      rintro (_ | _)
      · exact isOpenImmersion_inr iU iV
      · exact isOpenImmersion_inl iU iV)

end Pushout
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

theorem quasiSeparatedSpace_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [Surjective f]
    [QuasiSeparatedSpace X] : QuasiSeparatedSpace Y := by
  refine ⟨fun A B hAo hAc hBo hBc => ?_⟩
  have h := QuasiSeparatedSpace.inter_isCompact (f ⁻¹' A) (f ⁻¹' B) (hAo.preimage f.continuous)
    (QuasiCompact.isCompact_preimage _ hAo hAc) (hBo.preimage f.continuous) (QuasiCompact.isCompact_preimage _ hBo hBc)
  have : A ∩ B = f '' (f ⁻¹' A ∩ f ⁻¹' B) := by
    rw [← Set.preimage_inter, Set.image_preimage_eq _ f.surjective]
  rw [this]
  exact h.image f.continuous

theorem compactSpace_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [CompactSpace X] : CompactSpace Y := by
  refine ⟨?_⟩
  rw [← Set.range_eq_univ.mpr f.surjective]
  exact isCompact_range f.continuous

section Phase3

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {X : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of K)} (U V : X.Opens)

theorem phase3 [CompactSpace X] [QuasiSeparatedSpace X] (hUV : U ⊔ V = ⊤)
    (mU : Model F K U (U.ι ≫ fX)) (mV : Model F K V (V.ι ≫ fX))
    (W₀ : Scheme.{u}) (iU : W₀ ⟶ mU.X₀) (iV : W₀ ⟶ mV.X₀) [IsOpenImmersion iU] [IsOpenImmersion iV]
    (gW : (U.ι ⁻¹ᵁ V).toScheme ⟶ W₀) (hf : iU ≫ mU.f₀ = iV ≫ mV.f₀)
    (hrU : mU.g ⁻¹ᵁ iU.opensRange ≤ U.ι ⁻¹ᵁ V) (hrV : mV.g ⁻¹ᵁ iV.opensRange ≤ V.ι ⁻¹ᵁ U)
    (hgU : gW ≫ iU = (U.ι ⁻¹ᵁ V).ι ≫ mU.g) (hgV : gW ≫ iV = crossing U V ≫ mV.g) :
    Nonempty (Model F K X fX) := by
  haveI := mU.qc; haveI := mU.qs; haveI := mU.lft; haveI := mV.qc; haveI := mV.qs; haveI := mV.lft

  let X₀ : Scheme.{u} := pushout iU iV
  let inl : mU.X₀ ⟶ X₀ := pushout.inl iU iV
  let inr : mV.X₀ ⟶ X₀ := pushout.inr iU iV
  let f₀ : X₀ ⟶ Spec (CommRingCat.of F) := pushout.desc mU.f₀ mV.f₀ hf
  have inl_f₀ : inl ≫ f₀ = mU.f₀ := pushout.inl_desc _ _ _
  have inr_f₀ : inr ≫ f₀ = mV.f₀ := pushout.inr_desc _ _ _
  have key : (U.ι ⁻¹ᵁ V).ι ≫ mU.g ≫ inl = crossing U V ≫ mV.g ≫ inr := by
    rw [← Category.assoc, ← hgU, Category.assoc, pushout.condition, ← Category.assoc, hgV, Category.assoc]

  let 𝒱 : X.OpenCover := X.openCoverOfIsOpenCover (fun b : Bool => bif b then U else V) (by
    change (⨆ b : Bool, (bif b then U else V)) = ⊤
    rw [← sup_eq_iSup]; exact hUV)
  let piece : ∀ b : Bool, (𝒱.X b ⟶ X₀) := fun b => match b with
    | true => mU.g ≫ inl
    | false => mV.g ≫ inr
  have hcompat : ∀ b c : Bool, pullback.fst (𝒱.f b) (𝒱.f c) ≫ piece b = pullback.snd (𝒱.f b) (𝒱.f c) ≫ piece c := by
    rintro (_ | _) (_ | _)
    · change pullback.fst V.ι V.ι ≫ mV.g ≫ inr = pullback.snd V.ι V.ι ≫ mV.g ≫ inr
      rw [fst_eq_snd_of_mono_eq]
    · change pullback.fst V.ι U.ι ≫ mV.g ≫ inr = pullback.snd V.ι U.ι ≫ mU.g ≫ inl
      have sq := (isPullback_crossing U V).flip
      rw [← cancel_epi sq.isoPullback.hom, sq.isoPullback_hom_fst_assoc, sq.isoPullback_hom_snd_assoc]
      exact key.symm
    · change pullback.fst U.ι V.ι ≫ mU.g ≫ inl = pullback.snd U.ι V.ι ≫ mV.g ≫ inr
      have sq := isPullback_crossing U V
      rw [← cancel_epi sq.isoPullback.hom, sq.isoPullback_hom_fst_assoc, sq.isoPullback_hom_snd_assoc]
      exact key
    · change pullback.fst U.ι U.ι ≫ mU.g ≫ inl = pullback.snd U.ι U.ι ≫ mU.g ≫ inl
      rw [fst_eq_snd_of_mono_eq]
  let g : X ⟶ X₀ := 𝒱.glueMorphisms piece hcompat
  have gU : U.ι ≫ g = mU.g ≫ inl := 𝒱.ι_glueMorphisms piece hcompat true
  have gV : V.ι ≫ g = mV.g ≫ inr := 𝒱.ι_glueMorphisms piece hcompat false
  have gU_apply : ∀ x : U, g (U.ι x) = inl (mU.g x) := fun x => by
    rw [← Scheme.Hom.comp_apply, gU, Scheme.Hom.comp_apply]
  have gV_apply : ∀ x : V, g (V.ι x) = inr (mV.g x) := fun x => by
    rw [← Scheme.Hom.comp_apply, gV, Scheme.Hom.comp_apply]

  have hpreU : g ⁻¹ᵁ inl.opensRange = U := by
    ext x
    constructor
    · rintro ⟨a, ha⟩
      have hx : x ∈ U ⊔ V := by rw [hUV]; trivial
      rcases TopologicalSpace.Opens.mem_sup.mp hx with hxU | hxV
      · exact hxU
      · have e1 : g x = inr (mV.g ⟨x, hxV⟩) := gV_apply ⟨x, hxV⟩
        obtain ⟨w, -, hw2⟩ := exists_of_inl_eq_inr iU iV a (mV.g ⟨x, hxV⟩) (ha.trans e1)
        exact hrV (show (⟨x, hxV⟩ : V) ∈ mV.g ⁻¹ᵁ iV.opensRange from ⟨w, hw2⟩)
    · intro hxU
      exact ⟨mU.g ⟨x, hxU⟩, (gU_apply ⟨x, hxU⟩).symm⟩
  have hpreV : g ⁻¹ᵁ inr.opensRange = V := by
    ext x
    constructor
    · rintro ⟨b, hb⟩
      have hx : x ∈ U ⊔ V := by rw [hUV]; trivial
      rcases TopologicalSpace.Opens.mem_sup.mp hx with hxU | hxV
      · have e1 : g x = inl (mU.g ⟨x, hxU⟩) := gU_apply ⟨x, hxU⟩
        obtain ⟨w, hw1, -⟩ := exists_of_inl_eq_inr iU iV (mU.g ⟨x, hxU⟩) b (e1.symm.trans hb.symm)
        exact hrU (show (⟨x, hxU⟩ : U) ∈ mU.g ⁻¹ᵁ iU.opensRange from ⟨w, hw1⟩)
      · exact hxV
    · intro hxV
      exact ⟨mV.g ⟨x, hxV⟩, (gV_apply ⟨x, hxV⟩).symm⟩

  have sqU : IsPullback mU.g U.ι inl g :=
    IsOpenImmersion.isPullback _ _ _ _ gU (by rw [hpreU, Scheme.Opens.opensRange_ι])
  have sqV : IsPullback mV.g V.ι inr g :=
    IsOpenImmersion.isPullback _ _ _ _ gV (by rw [hpreV, Scheme.Opens.opensRange_ι])

  have H : IsPullback g fX f₀ (ι F K) := by
    refine Scheme.isPullback_of_openCover g fX f₀ (ι F K) (pushoutCover iU iV) ?_
    rintro (_ | _)
    · change IsPullback (pullback.snd g inr) (pullback.fst g inr ≫ fX) (inr ≫ f₀) (ι F K)
      rw [inr_f₀]
      refine mV.pb.of_iso sqV.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
      · rw [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_snd]
      · rw [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_fst_assoc]
    · change IsPullback (pullback.snd g inl) (pullback.fst g inl ≫ fX) (inl ≫ f₀) (ι F K)
      rw [inl_f₀]
      refine mU.pb.of_iso sqU.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
      · rw [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_snd]
      · rw [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_fst_assoc]

  haveI : Surjective g := MorphismProperty.of_isPullback H.flip inferInstance
  haveI : QuasiCompact g := MorphismProperty.of_isPullback H.flip inferInstance
  haveI hlft : LocallyOfFiniteType f₀ := by
    refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) (pushoutCover iU iV) ?_
    rintro (_ | _)
    · change LocallyOfFiniteType (inr ≫ f₀); rw [inr_f₀]; infer_instance
    · change LocallyOfFiniteType (inl ≫ f₀); rw [inl_f₀]; infer_instance
  exact ⟨{ X₀ := X₀, f₀ := f₀, qc := compactSpace_of_surjective g, qs := quasiSeparatedSpace_of_surjective g,
           lft := hlft, g := g, pb := H }⟩

end Phase3
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

section Core

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
  {X : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of K)} (U V : X.Opens)

theorem glue_core [CompactSpace X] [QuasiSeparatedSpace X] (hUV : U ⊔ V = ⊤)
    (hUc : IsCompact (U : Set X)) (hVc : IsCompact (V : Set X))
    (mU : Model F K U (U.ι ≫ fX)) (mV : Model F K V (V.ι ≫ fX)) :
    ∃ (L : IntermediateField F K) (_ : FiniteDimensional F L), Nonempty (Model L K X fX) := by
  obtain ⟨L₁, hL₁, mU₁, mV₁, WU, WV, hWUc, hWVc, hWU, hWV⟩ := phase1 U V hUc hVc mU mV
  haveI := hL₁
  haveI : Algebra.IsAlgebraic L₁ K := Algebra.IsAlgebraic.tower_top (K := F) L₁
  obtain ⟨L₂, hL₂, W₀, iU, iV, hiU, hiV, gW, hf, hrU, hrV, hgU, hgV⟩ :=
    phase2 U V mU₁ mV₁ WU WV hWUc hWVc hWU hWV
  haveI := hL₂
  haveI := hiU
  haveI := hiV
  obtain ⟨m⟩ := phase3 U V hUV _ _ W₀ iU iV gW hf hrU hrV hgU hgV
  exact ⟨L₂.restrictScalars F, finiteDimensional_restrictScalars L₁ L₂, ⟨m⟩⟩

end Core
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

structure Datum (k K : Type u) [Field k] [Field K] [Algebra k K] (X : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of K)) where
  E : IntermediateField k K
  fd : FiniteDimensional k E
  X₀ : Scheme.{u}
  f₀ : X₀ ⟶ Spec (CommRingCat.of E)
  qc : CompactSpace X₀
  qs : QuasiSeparatedSpace X₀
  lft : LocallyOfFiniteType f₀
  g : X ⟶ X₀
  pb : IsPullback g fX f₀ (ι E K)

namespace Datum

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of K)}

def toModel (d : Datum k K X fX) : Model d.E K X fX :=
  { X₀ := d.X₀, f₀ := d.f₀, qc := d.qc, qs := d.qs, lft := d.lft, g := d.g, pb := d.pb }

def ofModel (E : IntermediateField k K) (hE : FiniteDimensional k E) (m : Model E K X fX) : Datum k K X fX :=
  { E := E, fd := hE, X₀ := m.X₀, f₀ := m.f₀, qc := m.qc, qs := m.qs, lft := m.lft, g := m.g, pb := m.pb }

theorem ι_comp_inclusion {E E' : IntermediateField k K} (h : E ≤ E') :
    ι E' K ≫ Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) = ι E K := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

noncomputable def relevel (d : Datum k K X fX) (E' : IntermediateField k K) (h : d.E ≤ E')
    (hE' : FiniteDimensional k E') : Datum k K X fX := by
  let j : Spec (CommRingCat.of E') ⟶ Spec (CommRingCat.of d.E) :=
    Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)
  haveI := d.lft
  haveI := d.qc
  haveI := d.qs
  have w : d.g ≫ d.f₀ = (fX ≫ ι E' K) ≫ j := by
    rw [Category.assoc, ι_comp_inclusion h]
    exact d.pb.w
  refine
    { E := E'
      fd := hE'
      X₀ := pullback d.f₀ j
      f₀ := pullback.snd d.f₀ j
      qc := ?_
      qs := ?_
      lft := inferInstance
      g := pullback.lift d.g (fX ≫ ι E' K) w
      pb := ?_ }
  · haveI : IsAffineHom j := inferInstance
    infer_instance
  · exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst d.f₀ j)
  · refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback d.f₀ j)
    rw [pullback.lift_fst, ι_comp_inclusion h]
    exact d.pb

end Datum
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

section Affine

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]

theorem affine_descends (X : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [LocallyOfFiniteType fX] :
    Nonempty (Datum k K X fX) := by
  classical

  let R : CommRingCat.{u} := Γ(X, ⊤)
  let φ : CommRingCat.of K ⟶ R := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ fX.appTop
  have hfX : fX = X.isoSpec.hom ≫ Spec.map φ := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  have hlft : LocallyOfFiniteType (Spec.map φ) := by
    have : Spec.map φ = X.isoSpec.inv ≫ fX := by rw [hfX, Iso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  have hft : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hlft
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hft
  obtain ⟨L, hL, A₀, _, _, hA₀, ⟨e⟩⟩ :=
    Algebra.exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic k K R

  let X₀ : Scheme.{u} := Spec (CommRingCat.of A₀)
  let f₀ : X₀ ⟶ Spec (CommRingCat.of L) := Spec.map (CommRingCat.ofHom (algebraMap L A₀))
  haveI : LocallyOfFiniteType f₀ :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr (RingHom.finiteType_algebraMap.mpr hA₀)

  have sq : IsPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := L) (A := K) (B := A₀)).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := L) (A := K) (B := A₀))))
      f₀ (ι L K) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ (pullbackSpecIso L K A₀).symm ?_ ?_ |>.flip
    · rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      change algebraMap K (K ⊗[L] A₀) (algebraMap L K x) = (Algebra.TensorProduct.includeRight (R := L) (A := K) (B := A₀))
        (algebraMap L A₀ x)
      rw [AlgHom.commutes]
      exact (IsScalarTower.algebraMap_apply L K (K ⊗[L] A₀) x).symm
    · exact pullbackSpecIso_inv_fst L K A₀
    · exact pullbackSpecIso_inv_snd L K A₀

  let u : X ⟶ Spec (CommRingCat.of (K ⊗[L] A₀)) :=
    X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom)
  haveI : IsIso (Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom)) := by
    change IsIso (Scheme.Spec.map (e.toRingEquiv.toCommRingCatIso.hom.op))
    infer_instance
  haveI : IsIso u := IsIso.comp_isIso
  have hu : u ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := L) (A := K) (B := A₀))) = fX := by
    rw [hfX, Category.assoc, ← Spec.map_comp]
    congr 2
    ext x
    change e (algebraMap K (K ⊗[L] A₀) x) = φ.hom x
    rw [AlgEquiv.commutes]
    rfl
  let g : X ⟶ X₀ := u ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := L) (A := K) (B := A₀)).toRingHom)
  have pb : IsPullback g fX f₀ (ι L K) := by
    refine IsPullback.of_iso sq (asIso u).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [g]
    · simp [← hu]
    · simp
    · simp
  exact ⟨{ E := L, fd := hL, X₀ := X₀, f₀ := f₀, qc := inferInstance, qs := inferInstance, lft := inferInstance,
           g := g, pb := pb }⟩

end Affine
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

section Induction

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]

def GlueHyp : Prop :=
  ∀ (X : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of K)) [CompactSpace X] [QuasiSeparatedSpace X]
    [LocallyOfFiniteType fX] (U V : X.Opens), U ⊔ V = ⊤ → IsCompact (U : Set X) → IsCompact (V : Set X) →
    Nonempty (Datum k K U.toScheme (U.ι ≫ fX)) → Nonempty (Datum k K V.toScheme (V.ι ≫ fX)) →
    Nonempty (Datum k K X fX)

variable {k K}

theorem glueHyp : GlueHyp k K := by
  intro X fX _ _ _ U V hUV hUc hVc hU hV
  obtain ⟨dU⟩ := hU
  obtain ⟨dV⟩ := hV
  haveI := dU.fd
  haveI := dV.fd
  obtain ⟨E, hUE, hVE, hE⟩ : ∃ E : IntermediateField k K, dU.E ≤ E ∧ dV.E ≤ E ∧ FiniteDimensional k E :=
    ⟨dU.E ⊔ dV.E, le_sup_left, le_sup_right, IntermediateField.finiteDimensional_sup dU.E dV.E⟩
  haveI := hE
  haveI : Algebra.IsAlgebraic E K := Algebra.IsAlgebraic.tower_top (K := k) E
  have mU : Model E K U (U.ι ≫ fX) := (dU.relevel E hUE hE).toModel
  have mV : Model E K V (V.ι ≫ fX) := (dV.relevel E hVE hE).toModel
  obtain ⟨L, hL, ⟨m⟩⟩ := glue_core U V hUV hUc hVc mU mV
  exact ⟨Datum.ofModel (L.restrictScalars k) (finiteDimensional_restrictScalars E L) m⟩

theorem descends_of_finite_affine_cover (hG : GlueHyp k K) :
    ∀ (n : ℕ) (X : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of K)) [CompactSpace X] [QuasiSeparatedSpace X]
      [LocallyOfFiniteType fX] (U : Fin n → X.Opens), (∀ i, IsAffineOpen (U i)) → ⨆ i, U i = ⊤ →
      Nonempty (Datum k K X fX) := by
  intro n
  induction n with
  | zero =>
    intro X fX _ _ _ U hU hcov
    have hbot : (⊤ : X.Opens) = ⊥ := by rw [← hcov]; simp
    haveI : IsEmpty X := ⟨fun x => by
      have : x ∈ (⊤ : X.Opens) := trivial
      rw [hbot] at this
      exact this⟩
    haveI : IsAffine X := isAffine_of_isEmpty
    exact affine_descends X fX
  | succ n ih =>
    intro X fX _ _ _ U hU hcov

    let U' : X.Opens := U (Fin.last n)
    let V' : X.Opens := ⨆ i : Fin n, U (Fin.castSucc i)
    have hUV : U' ⊔ V' = ⊤ := by
      apply top_le_iff.mp
      rw [← hcov]
      refine iSup_le fun i => ?_
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact le_sup_of_le_right (le_iSup (fun j : Fin n => U (Fin.castSucc j)) j)
      · exact le_sup_left
    have hU'c : IsCompact (U' : Set X) := (hU (Fin.last n)).isCompact
    have hV'c : IsCompact (V' : Set X) := by
      simp only [V', TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
        TopologicalSpace.Opens.coe_mk]
      exact isCompact_iUnion fun i => (hU _).isCompact

    have hU' : Nonempty (Datum k K U'.toScheme (U'.ι ≫ fX)) := by
      haveI : IsAffine U'.toScheme := hU (Fin.last n)
      exact affine_descends _ _

    have hV' : Nonempty (Datum k K V'.toScheme (V'.ι ≫ fX)) := by
      haveI : CompactSpace V'.toScheme := isCompact_iff_compactSpace.mp hV'c
      haveI : QuasiSeparatedSpace V'.toScheme := V'.ι.isOpenEmbedding.quasiSeparatedSpace
      refine ih V'.toScheme (V'.ι ≫ fX) (fun i => V'.ι ⁻¹ᵁ U (Fin.castSucc i)) (fun i => ?_) ?_
      · refine (hU _).preimage_of_isOpenImmersion V'.ι ?_
        rw [Scheme.Opens.opensRange_ι]
        exact le_iSup (fun j : Fin n => U (Fin.castSucc j)) i
      · rw [← Scheme.Hom.preimage_iSup]
        exact Scheme.Opens.ι_preimage_self V'
    exact hG X fX U' V' hUV hU'c hV'c hU' hV'

theorem descends (X : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of K))
    [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType fX] : Nonempty (Datum k K X fX) := by
  classical
  let 𝒰 := X.affineCover.finiteSubcover
  let eqv := Fintype.equivFin 𝒰.I₀
  exact descends_of_finite_affine_cover glueHyp (Fintype.card 𝒰.I₀) X fX
    (fun i => (𝒰.f (eqv.symm i)).opensRange) (fun i => isAffineOpen_opensRange _) (by
      apply top_le_iff.mp
      rw [← 𝒰.iSup_opensRange]
      exact iSup_le fun j => le_iSup_of_le (eqv j) (by
        change (𝒰.f j).opensRange ≤ (𝒰.f (eqv.symm (eqv j))).opensRange
        rw [Equiv.symm_apply_apply]))

end Induction
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model"

end SchemeSpread
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread.Model P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in

theorem solution
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of K))
    [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType fX] :
    ∃ (L : IntermediateField k K) (_ : FiniteDimensional k L)
      (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of L)) (_ : CompactSpace X₀) (_ : QuasiSeparatedSpace X₀)
      (_ : LocallyOfFiniteType f₀) (g : X ⟶ X₀),
      IsPullback g fX f₀ (Spec.map (CommRingCat.ofHom (algebraMap L K))) := by
  obtain ⟨d⟩ := SchemeSpread.descends (k := k) (K := K) X fX
  exact ⟨d.E, d.fd, d.X₀, d.f₀, d.qc, d.qs, d.lft, d.g, d.pb⟩

end S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic
end P2MW

namespace PhilipponSchemeFieldDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem exists_finite_model
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of K))
    [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType fX] :
    ∃ (L : IntermediateField k K) (_ : FiniteDimensional k L)
      (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of L))
      (_ : CompactSpace X₀) (_ : QuasiSeparatedSpace X₀)
      (_ : LocallyOfFiniteType f₀) (g : X ⟶ X₀),
      IsPullback g fX f₀ (Spec.map (CommRingCat.ofHom (algebraMap L K))) := by
  exact P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.solution k K X fX

end PhilipponSchemeFieldDescent


set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponRelativeFieldDescent
open P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic.SchemeSpread

/-- Descent of a finite-type scheme and its morphism to a fixed finite-type ground-field
scheme, with an actual cartesian square and exact recovery of the morphism. -/
theorem exists_relative_finite_model
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (Y : Scheme.{u}) (fY : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace Y] [QuasiSeparatedSpace Y] [LocallyOfFiniteType fY]
    (X : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of K))
    [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType fX]
    (φ : X ⟶ Y)
    (hφ : φ ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of E))
      (_ : CompactSpace X₀) (_ : QuasiSeparatedSpace X₀) (_ : LocallyOfFiniteType f₀)
      (g : X ⟶ X₀) (φ₀ : X₀ ⟶ Y),
      IsPullback g fX f₀ (Spec.map (CommRingCat.ofHom (algebraMap E K))) ∧
      φ₀ ≫ fY = f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) ∧
      g ≫ φ₀ = φ := by
  classical
  obtain ⟨d⟩ := descends (k := k) (K := K) X fX
  let E := d.E
  let m : Model E K X fX := d.toModel
  letI : FiniteDimensional k E := d.fd
  letI : Algebra.IsAlgebraic E K := Algebra.IsAlgebraic.tower_top (K := k) E
  let YK : Scheme.{u} := pullback fY (ι k K)
  let fYK : YK ⟶ Spec (CommRingCat.of K) := pullback.snd fY (ι k K)
  let YE : Scheme.{u} := pullback fY (ι k E)
  let fYE : YE ⟶ Spec (CommRingCat.of E) := pullback.snd fY (ι k E)
  have wY : pullback.fst fY (ι k K) ≫ fY = (fYK ≫ ι E K) ≫ ι k E := by
    rw [Category.assoc, ι_comp]
    exact pullback.condition
  let rY : YK ⟶ YE := pullback.lift (pullback.fst fY (ι k K))
    (fYK ≫ ι E K) wY
  have hrY : IsPullback rY fYK fYE (ι E K) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst, ι_comp]
    exact IsPullback.of_hasPullback _ _
  let n : Model E K YK fYK :=
    { X₀ := YE
      f₀ := fYE
      qc := by
        haveI : IsAffineHom (ι k E) := inferInstance
        infer_instance
      qs := quasiSeparatedSpace_of_quasiSeparated (pullback.fst fY (ι k E))
      lft := inferInstance
      g := rY
      pb := hrY }
  let φK : X ⟶ YK := pullback.lift φ fX hφ
  let eX := m.pb.isoPullback
  let eY := n.pb.isoPullback
  let φ' : pullback m.f₀ (ι E K) ⟶ pullback n.f₀ (ι E K) :=
    eX.inv ≫ φK ≫ eY.hom
  have hφ' : φ' ≫ pullback.snd n.f₀ (ι E K) = pullback.snd m.f₀ (ι E K) := by
    simp only [φ', eY, Category.assoc, n.pb.isoPullback_hom_snd]
    change eX.inv ≫ (φK ≫ fYK) = pullback.snd m.f₀ (ι E K)
    rw [show φK ≫ fYK = fX from pullback.lift_snd _ _ _]
    rw [Iso.inv_comp_eq, m.pb.isoPullback_hom_snd]
  letI := m.qc
  letI := m.qs
  letI := n.lft
  obtain ⟨L, hL, a, hι, ha, hsq⟩ :=
    P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic.solution
      E K m.X₀ n.X₀ m.f₀ n.f₀ φ' hφ'
  letI := hL
  let mL := m.baseChange L
  let nL := n.baseChange L
  have hm : mL.g = eX.hom ≫
      pullback.map m.f₀ (ι E K) m.f₀ (ι E L) (𝟙 m.X₀) (ι L K) (𝟙 _)
        (by simp) (by rw [Category.comp_id, hι]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      simp [eX, mL]
    · rw [Category.assoc, pullback.lift_snd]
      simp [eX, mL]
  have hn : nL.g = eY.hom ≫
      pullback.map n.f₀ (ι E K) n.f₀ (ι E L) (𝟙 n.X₀) (ι L K) (𝟙 _)
        (by simp) (by rw [Category.comp_id, hι]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      simp [eY, nL]
    · rw [Category.assoc, pullback.lift_snd]
      simp [eY, nL]
  have hrec : mL.g ≫ a = φK ≫ nL.g := by
    rw [hm, Category.assoc, ← hsq, ← Category.assoc]
    have he : eX.hom ≫ φ' = φK ≫ eY.hom := by simp [φ']
    rw [he, Category.assoc, ← hn]
  let b : nL.X₀ ⟶ Y := pullback.fst n.f₀ (ι E L) ≫ pullback.fst fY (ι k E)
  have hb : b ≫ fY = nL.f₀ ≫ ι k (L.restrictScalars k) := by
    change (pullback.fst n.f₀ (ι E L) ≫ pullback.fst fY (ι k E)) ≫ fY = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (pullback.fst n.f₀ (ι E L) ≫ n.f₀) ≫ ι k E = _
    rw [pullback.condition, Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let φ₀ : mL.X₀ ⟶ Y := a ≫ b
  have hbase : φ₀ ≫ fY = mL.f₀ ≫ ι k (L.restrictScalars k) := by
    dsimp only [φ₀]
    rw [Category.assoc, hb, ← Category.assoc]
    exact congrArg (fun z => z ≫ ι k (L.restrictScalars k)) ha
  have hrecover : mL.g ≫ φ₀ = φ := by
    dsimp only [φ₀]
    rw [← Category.assoc, hrec, Category.assoc]
    change φK ≫ (nL.g ≫ (pullback.fst n.f₀ (ι E L) ≫ pullback.fst fY (ι k E))) = φ
    rw [← Category.assoc nL.g, n.gL_fst]
    change φK ≫ (rY ≫ pullback.fst fY (ι k E)) = φ
    rw [pullback.lift_fst, pullback.lift_fst]
  exact ⟨L.restrictScalars k, finiteDimensional_restrictScalars E L, mL.X₀, mL.f₀,
    mL.qc, mL.qs, mL.lft, mL.g, φ₀, mL.pb, hbase, hrecover⟩

end PhilipponRelativeFieldDescent

theorem solution
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (Y : Scheme.{u}) (fY : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace Y] [QuasiSeparatedSpace Y] [LocallyOfFiniteType fY]
    (X : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of K))
    [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType fX]
    (φ : X ⟶ Y)
    (hφ : φ ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of E))
      (_ : CompactSpace X₀) (_ : QuasiSeparatedSpace X₀) (_ : LocallyOfFiniteType f₀)
      (g : X ⟶ X₀) (φ₀ : X₀ ⟶ Y),
      IsPullback g fX f₀ (Spec.map (CommRingCat.ofHom (algebraMap E K))) ∧
      φ₀ ≫ fY = f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) ∧
      g ≫ φ₀ = φ := by
  exact PhilipponRelativeFieldDescent.exists_relative_finite_model k K Y fY X fX φ hφ
