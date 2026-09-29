-- Prove2me | solution 1 for AlgebraicGeometry.exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f2405849-36ab-534a-b009-bfce4e1395c6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic

set_option autoImplicit false

open scoped IntermediateField

namespace AlgExtSpread

namespace FinSubfield

variable {k K : Type} [Field k] [Field K] [Algebra k K]

abbrev FinIF (k K : Type) [Field k] [Field K] [Algebra k K] := {L : IntermediateField k K // FiniteDimensional k L}

scoped instance (L : FinIF k K) : FiniteDimensional k L.1 := L.2

noncomputable def adj [Algebra.IsAlgebraic k K] (x : K) : FinIF k K :=
  ⟨k⟮x⟯, IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩

theorem mem_adj [Algebra.IsAlgebraic k K] (x : K) : x ∈ (adj (k := k) x).1 :=
  IntermediateField.mem_adjoin_simple_self k x

noncomputable def sup2 (L L' : FinIF k K) : FinIF k K :=
  ⟨L.1 ⊔ L'.1, IntermediateField.finiteDimensional_sup L.1 L'.1⟩

theorem existsUnique_ringHom_forall_comp_eq [Algebra.IsAlgebraic k K]
    (R : Type) [CommRing R] (φ : ∀ L : FinIF k K, L.1 →+* R)
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
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.AlgExtSpread.FinSubfield"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

section Aux

variable (k K : Type) [Field k] [Field K] [Algebra k K] (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of k))

private abbrev _root_.AlgExtSpread.FinIF := FinSubfield.FinIF k K

p2m_export "AlgExtSpread" "FinIF"

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

noncomputable def D : (FinIF k K)ᵒᵖ ⥤ Scheme.{0} where
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

noncomputable def ringOf {W : Scheme.{0}} {B : CommRingCat.{0}} (g : W ⟶ Spec B) : B ⟶ Γ(W, ⊤) :=
  (Scheme.ΓSpecIso B).inv ≫ g.appTop

noncomputable def toSpec {W : Scheme.{0}} {B : CommRingCat.{0}} (φ : B ⟶ Γ(W, ⊤)) : W ⟶ Spec B :=
  ΓSpec.adjunction.homEquiv W (op B) φ.op

theorem ringOf_toSpec {W : Scheme.{0}} {B : CommRingCat.{0}} (φ : B ⟶ Γ(W, ⊤)) : ringOf (toSpec φ) = φ :=
  ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ

theorem ext_ringOf {W : Scheme.{0}} {B : CommRingCat.{0}} {g₁ g₂ : W ⟶ Spec B} (h : ringOf g₁ = ringOf g₂) : g₁ = g₂ := by
  apply ext_of_isAffine
  simpa [ringOf, Iso.cancel_iso_inv_left] using h

theorem toSpec_ringOf {W : Scheme.{0}} {B : CommRingCat.{0}} (g : W ⟶ Spec B) : toSpec (ringOf g) = g :=
  ext_ringOf (ringOf_toSpec _)

theorem ringOf_comp_specMap {W : Scheme.{0}} {B B' : CommRingCat.{0}} (g : W ⟶ Spec B) (u : B' ⟶ B) :
    ringOf (g ≫ Spec.map u) = u ≫ ringOf g := by
  simp only [ringOf, Scheme.Hom.comp_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

theorem ringOf_precomp {W W' : Scheme.{0}} {B : CommRingCat.{0}} (m : W' ⟶ W) (g : W ⟶ Spec B) :
    ringOf (m ≫ g) = ringOf g ≫ m.appTop := by
  simp only [ringOf, Scheme.Hom.comp_appTop, Category.assoc]

end RingOf
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.AlgExtSpread.FinSubfield"

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.AlgExtSpread.FinSubfield"

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.AlgExtSpread.FinSubfield"

end Aux
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.AlgExtSpread.FinSubfield"

section API

variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable {X : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of k)}

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

theorem hom_extL {L : FinIF k K} {W : Scheme.{0}} {a b : W ⟶ (D k K X fX).obj (op L)}
    (h₁ : a ≫ fstL fX L = b ≫ fstL fX L) (h₂ : a ≫ sndL fX L = b ≫ sndL fX L) : a = b :=
  pullback.hom_ext h₁ h₂

theorem conditionL (L : FinIF k K) : fstL fX L ≫ fX = sndL fX L ≫ gF k K L := pullback.condition

noncomputable def liftL (fX : X ⟶ Spec (CommRingCat.of k)) (L : FinIF k K) {W : Scheme.{0}} (a : W ⟶ X)
    (b : W ⟶ Spec (CommRingCat.of L.1)) (w : a ≫ fX = b ≫ gF k K L) : W ⟶ (D k K X fX).obj (op L) :=
  pullback.lift a b w

theorem liftL_fstL (L : FinIF k K) {W : Scheme.{0}} (a : W ⟶ X) (b : W ⟶ Spec (CommRingCat.of L.1))
    (w : a ≫ fX = b ≫ gF k K L) : liftL fX L a b w ≫ fstL fX L = a :=
  pullback.lift_fst _ _ _

theorem liftL_sndL (L : FinIF k K) {W : Scheme.{0}} (a : W ⟶ X) (b : W ⟶ Spec (CommRingCat.of L.1))
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
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.AlgExtSpread.FinSubfield"

section IsoSpread

variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable {X Y : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of k)}

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.AlgExtSpread.FinSubfield"

end AlgExtSpread
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.AlgExtSpread.FinSubfield P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic.AlgExtSpread"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite AlgExtSpread in
theorem solution
    (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X Y : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
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
export P2MW.S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_iso_hom_comp_pullback_map_eq_of_isAlgebraic (solution)
