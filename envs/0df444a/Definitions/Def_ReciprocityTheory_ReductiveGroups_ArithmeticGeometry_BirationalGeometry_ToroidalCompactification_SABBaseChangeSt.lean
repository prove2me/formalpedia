-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:59:09.589873+00:00
-- url     : https://prove2.me/theorems/b535a50a-bb20-49b8-af0d-7db34dcc8153
-- title:
--   SABBase Change St
-- statement:
--   Definitions and structural lemmas for SABBase Change St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SABBaseChangeSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
section Transport
variable {K : Type} [Field K] {G₁ G₂ : Over (Spec (CommRingCat.of K))} [GrpObj G₁] [GrpObj G₂]
omit [GrpObj G₁] [GrpObj G₂] in
lemma isIso_inv_left (e : G₁ ≅ G₂) : IsIso e.inv.left :=
  Functor.map_isIso (Over.forget _) e.inv
def torusExtOfIso (e : G₁ ≅ G₂) [IsMonHom e.hom] (T : TorusExtension G₁) : TorusExtension G₂ :=
  letI := T.grpB
  haveI := T.q_hom
  haveI := T.i_hom
  { X := T.X
    addCommGroup := T.addCommGroup
    free := T.free
    finite := T.finite
    B := T.B
    grpB := T.grpB
    isAbelian := T.isAbelian
    q := e.inv ≫ T.q
    q_hom := inferInstance
    q_flat := by rw [Over.comp_left]; have := T.q_flat; have := isIso_inv_left e; infer_instance
    q_surjective := by rw [Over.comp_left]; have := T.q_surjective; have := isIso_inv_left e; infer_instance
    q_quasiCompact := by rw [Over.comp_left]; have := T.q_quasiCompact; have := isIso_inv_left e; infer_instance
    i := T.i ≫ e.hom
    i_hom := inferInstance
    isKernel := by
      refine IsPullback.of_iso T.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp }
end Transport
section Pull
variable {T S S' : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G]
def pullCompMon : (Over.pullback (p ≫ f)).mapMon.obj (Mon.mk G) ≅
    (Over.pullback p).mapMon.obj ((Over.pullback f).mapMon.obj (Mon.mk G)) :=
  (Functor.mapMonNatIso (Over.pullbackComp p f) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)
def pullCompIso : (Over.pullback (p ≫ f)).obj G ≅ (Over.pullback p).obj ((Over.pullback f).obj G) :=
  (Mon.forget _).mapIso (pullCompMon p f G)
instance : IsMonHom (pullCompIso p f G).hom := by
  show IsMonHom (pullCompMon p f G).hom.hom
  infer_instance
theorem IsSemiAbelian.pullback (h : IsSemiAbelian G) : IsSemiAbelian ((Over.pullback f).obj G) where
  comm := by have := h.comm; infer_instance
  smooth := by have := h.smooth; show Smooth (pullback.snd G.hom f); infer_instance
  separated := by have := h.separated; show IsSeparated (pullback.snd G.hom f); infer_instance
  quasiCompact := by have := h.quasiCompact; show QuasiCompact (pullback.snd G.hom f); infer_instance
  geomConnected := by have := h.geomConnected; show GeometricallyConnected (pullback.snd G.hom f); infer_instance
  fibres := fun Ω _ _ q => by
    obtain ⟨E⟩ := h.fibres Ω (q ≫ f)
    exact ⟨torusExtOfIso (pullCompIso q f G) E⟩
def OAct.pullback [IsCommMonObj G] {O : Type} [CommRing O] (a : OAct O G) : OAct O ((Over.pullback f).obj G) where
  act x := (Over.pullback f).map (a.act x)
  hom x := by have := a.hom x; infer_instance
  one := by rw [a.one, CategoryTheory.Functor.map_id]
  mul x y := by rw [a.mul, CategoryTheory.Functor.map_comp]
  add x y := by rw [a.add]; exact CategoryTheory.Functor.map_mul _ _ _
end Pull
def SABBaseChangeSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t : SAB H S)
    (PP' : RigLB ((Over.pullback f).obj t.G)),
    (∃ w : LB.Iso PP'.L (t.PP.L.pull (pullback.fst t.G.hom f)), w.IsGen) →
    ∃ (semi : IsSemiAbelian ((Over.pullback f).obj t.G)) (act : OAct (𝓞 E) ((Over.pullback f).obj t.G))
      (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric)
      (adj : ∀ a, LBIso (cubeLB _ ![fst _ _ ≫ act.act a, snd _ _] PP'.L)
        (cubeLB _ ![fst _ _, snd _ _ ≫ act.act (H.bar a)] PP'.L))
      (prim : LBIso PP'.L (cubeLB _ ![𝟙 _, act.act H.w0] PP'.L)),
      Nonempty (SABMap ⟨(Over.pullback f).obj t.G, semi, act, PP', cub, sym, adj, prim⟩ t f)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


