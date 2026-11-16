-- Prove2me | Definitions.Def_RPLib_S4_EtShStalkFV
-- name    : RPLib_S4_EtShStalkFV
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:41:50.529236+00:00
-- url     : https://prove2.me/theorems/7b5eda70-763d-4722-9f10-74e21282ca2c
-- title:
--   The stalk of $F_V$ is $V$, with the Galois action through $\rho$
-- statement:
--   In the setting of the sheaf $F_V$ of a representation $\rho$ of the group $G$ of a Galois cover $\pi : Y = \mathrm{Spec}\,B \to X$: for a geometric point $\bar t$ of $Y$ the stalk of $F_V$ at $\pi \circ \bar t$ is $V$ (by restriction to $Y$ and $F_V|_Y \cong V_Y$), with the inverse sending $v$ to the germ of an explicit section over $Y$. An automorphism $\tau$ of $\mathrm{Spec}\,\Omega$ over $X$ determines a unique $g \in G$ with $\bar t \circ \tau = g_Y \circ \bar t$ (trivial inertia), multiplicatively in $\tau$, and $\tau$ acts on the stalk $V$ by $\rho(g)$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. Grothendieck, Revetements etales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Expose V; J. S. Milne, Etale Cohomology, Princeton University Press (1980)

import Mathlib
import Definitions.Def_RPLib_S4_EtShFVRes
import Definitions.Def_RPLib_S4_EtShStalkRes
import Definitions.Def_RPLib_S4_EtShFaith
import Definitions.Def_RPLib_S4_EtShGalCont

/-!
# S4-EtSheaves, part O10d-2(iv-b): the stalk of `F_V` is `V`, with the Galois action through `ρ`

For a geometric point `t` of `Y = Spec B`, the stalk of `F_V` at `t ≫ π` is `V` (`stalkFV`: restriction to `Y`
(`resFibIso`), `F_V|_Y ≅ V_X|_Y` (`resIso`), constant stalks). Its inverse sends `v` to the germ of the section
`unitFV v` of `F_V` over `Y` (`stalkFV_inv`). The element `g ∈ G` acting on `Y` over `X` moves `unitFV v` to
`unitFV (ρ g v)` (`map_actE_unitFV`), so an automorphism `τ` of `Spec Ω` over `X` with `τ ≫ t = t ≫ g_Y` acts on the
stalk by `ρ g` (`stalkAut_stalkFV_inv`). Every such `τ` determines a unique `g` (`existsUnique_act`, trivial inertia),
`actOf`, multiplicative in `τ` (`actOf_comp`), and `τ` acts on the stalk by `ρ (actOf τ)` (`stalkAut_stalkFV`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] {C : GalCover A} (Λ : Type) [CommRing Λ] {V : Type}
  [AddCommGroup V] [Module Λ V] (ρ : Representation Λ C.G V)

/-- **The stalk of `F_V` at `t ≫ π` is `V`.** -/
def stalkFV (t : GeomPt (SY C)) : ((t.map (pr C)).stalkF Λ).obj (FV C Λ ρ) ≅ ModuleCat.of Λ V :=
  (resFibIso (pr C) t Λ (FV C Λ ρ)).symm ≪≫ (t.stalkF Λ).mapIso (resIso Λ ρ) ≪≫
    resFibIso (pr C) t Λ (VX A Λ V) ≪≫ constStalkIso Λ (t.map (pr C)) (ModuleCat.of Λ V)

theorem resIso_inv_app (T : (SY C).Etale) (z : (VX A Λ V).obj.obj (op (tx T))) :
    ((resIso Λ ρ).inv.hom.app (op T)).hom z = (eT Λ ρ T).symm z := rfl

/-- The section of `F_V` over `Y` corresponding to `v` (constant on `Y`). -/
def unitFV (v : V) : (FV C Λ ρ).obj.obj (op (tx (etId (SY C)))) :=
  (eT Λ ρ (etId (SY C))).symm ((constUnit (ModuleCat.of Λ V) (tx (etId (SY C)))).hom v)

/-- **`stalkFV⁻¹ v` is the germ of `unitFV v`.** -/
theorem stalkFV_inv (t : GeomPt (SY C)) (v : V) :
    (stalkFV Λ ρ t).inv.hom v = (t.map (pr C)).point.toPresheafFiber (tx (etId (SY C)))
      (liftX (pr C) t t.top) (FV C Λ ρ).obj (unitFV Λ ρ v) := by
  let z : (VX A Λ V).obj.obj (op (tx (etId (SY C)))) := (constUnit (ModuleCat.of Λ V) (tx (etId (SY C)))).hom v
  have h1 : (constStalkIso Λ (t.map (pr C)) (ModuleCat.of Λ V)).inv.hom v =
      (t.map (pr C)).point.toPresheafFiber (tx (etId (SY C))) (liftX (pr C) t t.top) (VX A Λ V).obj z :=
    (congrArg (fun φ => φ.hom v)
      (constUnit_germ (t.map (pr C)) (ModuleCat.of Λ V) (tx (etId (SY C))) (liftX (pr C) t t.top))).symm
  have h2 := resFibIso_inv_germ (pr C) t Λ (VX A Λ V) (etId (SY C)) t.top z
  have h3 : ((t.stalkF Λ).map (resIso Λ ρ).inv).hom
      (t.point.toPresheafFiber (etId (SY C)) t.top ((res (pr C) Λ).obj (VX A Λ V)).obj z) =
      t.point.toPresheafFiber (etId (SY C)) t.top ((res (pr C) Λ).obj (FV C Λ ρ)).obj (unitFV Λ ρ v) :=
    congrArg (fun φ => φ.hom z)
      (t.point.toPresheafFiber_naturality (resIso Λ ρ).inv.hom (etId (SY C)) t.top)
  have h4 := resFib_germ (pr C) t Λ (FV C Λ ρ) (etId (SY C)) t.top (unitFV Λ ρ v)
  calc (stalkFV Λ ρ t).inv.hom v
      = (resFib (pr C) t Λ (FV C Λ ρ)).hom (((t.stalkF Λ).map (resIso Λ ρ).inv).hom
          ((resFibIso (pr C) t Λ (VX A Λ V)).inv.hom
            ((constStalkIso Λ (t.map (pr C)) (ModuleCat.of Λ V)).inv.hom v))) := rfl
    _ = (resFib (pr C) t Λ (FV C Λ ρ)).hom (((t.stalkF Λ).map (resIso Λ ρ).inv).hom
          (t.point.toPresheafFiber (etId (SY C)) t.top ((res (pr C) Λ).obj (VX A Λ V)).obj z)) := by
        rw [h1, h2]
    _ = (resFib (pr C) t Λ (FV C Λ ρ)).hom
          (t.point.toPresheafFiber (etId (SY C)) t.top ((res (pr C) Λ).obj (FV C Λ ρ)).obj (unitFV Λ ρ v)) := by
        rw [h3]
    _ = _ := h4

/-- `g ∈ G` acting on `Y`, as an endomorphism of `Y` over `X`. -/
def actE (g : C.G) : tx (etId (SY C)) ⟶ tx (etId (SY C)) :=
  MorphismProperty.Over.homMk (act C g) (by
    change act C g ≫ 𝟙 _ ≫ pr C = 𝟙 _ ≫ pr C
    rw [Category.id_comp, act_pr]) trivial

theorem secL_mL (g : C.G) :
    secL (etId (SY C)) 1 ≫ pullback.lift (pullback.fst ((etId (SY C)).hom ≫ pr C) (pr C) ≫ act C g)
      (pullback.snd ((etId (SY C)).hom ≫ pr C) (pr C)) (by
        have h1 : act C g ≫ (etId (SY C)).hom ≫ pr C = (etId (SY C)).hom ≫ pr C := by
          change act C g ≫ 𝟙 _ ≫ pr C = 𝟙 _ ≫ pr C
          rw [Category.id_comp, act_pr]
        exact (Category.assoc _ _ _).trans ((congrArg
          (fun k => pullback.fst ((etId (SY C)).hom ≫ pr C) (pr C) ≫ k) h1).trans pullback.condition)) =
      act C g ≫ secL (etId (SY C)) g⁻¹ := by
  have key : (etId (SY C)).hom ≫ act C 1 = act C g ≫ (etId (SY C)).hom ≫ act C g⁻¹ := by
    change 𝟙 _ ≫ act C 1 = act C g ≫ 𝟙 _ ≫ act C g⁻¹
    rw [Category.id_comp, Category.id_comp, act_mul, mul_inv_cancel]
  refine pullback.hom_ext (f := (etId (SY C)).hom ≫ pr C) (g := pr C) ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (fun k => secL (etId (SY C)) 1 ≫ k)
      (pullback.lift_fst _ _ _)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ act C g) (secL_fst (etId (SY C)) 1)).trans ((Category.id_comp _).trans
      ((Category.comp_id _).symm.trans ((congrArg (fun k => act C g ≫ k) (secL_fst (etId (SY C)) g⁻¹)).symm.trans
      (Category.assoc _ _ _).symm))))))
  · exact (Category.assoc _ _ _).trans ((congrArg (fun k => secL (etId (SY C)) 1 ≫ k)
      (pullback.lift_snd _ _ _)).trans ((secL_snd (etId (SY C)) 1).trans (key.trans
      ((congrArg (fun k => act C g ≫ k) (secL_snd (etId (SY C)) g⁻¹)).symm.trans (Category.assoc _ _ _).symm))))

/-- **`ι 1 ≫ (g × 1) = g ≫ ι g⁻¹`** on `Y ×_X Y`. -/
theorem sec_actE (g : C.G) :
    sec (etId (SY C)) 1 ≫ (etComp (pr C)).map ((etPull (pr C)).map (actE g)) = actE g ≫ sec (etId (SY C)) g⁻¹ :=
  MorphismProperty.Over.Hom.ext (secL_mL g)

theorem eT_map_actE (g : C.G) (s : (FV C Λ ρ).obj.obj (op (tx (etId (SY C))))) :
    eT Λ ρ (etId (SY C)) (((FV C Λ ρ).obj.map (actE g).op).hom s) =
      ((VX A Λ V).obj.map (actE g).op).hom
        (((th C Λ ρ g⁻¹).hom.app (op (tx (etId (SY C))))).hom (eT Λ ρ (etId (SY C)) s)) := by
  let s1 : (VX A Λ V).obj.obj (op (tp (etId (SY C)))) := s.1
  have hm : ((VX A Λ V).obj.map (sec (etId (SY C)) g⁻¹).op).hom s1 =
      ((th C Λ ρ g⁻¹).hom.app (op (tx (etId (SY C))))).hom
        (((VX A Λ V).obj.map (sec (etId (SY C)) 1).op).hom s1) := by
    have h := (mem_FV_iff Λ ρ (etId (SY C)) s1).1 s.2 g⁻¹ 1
    rwa [one_mul] at h
  change ((VX A Λ V).obj.map (sec (etId (SY C)) 1).op).hom (((VX A Λ V).obj.map
      ((etComp (pr C)).map ((etPull (pr C)).map (actE g))).op).hom s1) =
    ((VX A Λ V).obj.map (actE g).op).hom (((th C Λ ρ g⁻¹).hom.app (op (tx (etId (SY C))))).hom
      (((VX A Λ V).obj.map (sec (etId (SY C)) 1).op).hom s1))
  exact (map_map_apply (VX A Λ V) ((etComp (pr C)).map ((etPull (pr C)).map (actE g))) (sec (etId (SY C)) 1) s1).trans
    ((congrArg (fun f => ((VX A Λ V).obj.map f.op).hom s1) (sec_actE g)).trans
      ((map_map_apply (VX A Λ V) (sec (etId (SY C)) g⁻¹) (actE g) s1).symm.trans
        (congrArg ((VX A Λ V).obj.map (actE g).op).hom hm)))

theorem th_constUnit (σ : C.G) (U : (SX A).Etale) (v : V) :
    ((th C Λ ρ σ).hom.app (op U)).hom ((constUnit (ModuleCat.of Λ V) U).hom v) =
      (constUnit (ModuleCat.of Λ V) U).hom (ρ σ⁻¹ v) :=
  (congrArg (fun η => (η.app (op U)).hom v) (toSheafify_naturality (SX A).smallEtaleTopology
    ((Functor.const ((SX A).Etale)ᵒᵖ).map (ModuleCat.ofHom (ρ σ⁻¹))))).symm

theorem map_constUnit {U U' : (SX A).Etale} (f : U ⟶ U') (w : V) :
    ((VX A Λ V).obj.map f.op).hom ((constUnit (ModuleCat.of Λ V) U').hom w) =
      (constUnit (ModuleCat.of Λ V) U).hom w :=
  (congrArg (fun φ => φ.hom w)
    ((toSheafify (SX A).smallEtaleTopology (constPre (ModuleCat.of Λ V))).naturality f.op)).symm

/-- **`g` moves `unitFV v` to `unitFV (ρ g v)`.** -/
theorem map_actE_unitFV (g : C.G) (v : V) :
    ((FV C Λ ρ).obj.map (actE g).op).hom (unitFV Λ ρ v) = unitFV Λ ρ (ρ g v) := by
  refine (eT Λ ρ (etId (SY C))).injective ((eT_map_actE Λ ρ g _).trans ?_)
  rw [unitFV, unitFV, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, th_constUnit, inv_inv,
    map_constUnit]

/-- **Equivariance**: `τ` with `τ ≫ t = t ≫ g_Y` acts on the stalk of `F_V` by `ρ g`. -/
theorem stalkAut_stalkFV_inv (t : GeomPt (SY C)) (g : C.G)
    (τ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of t.Ω))
    (hτ : τ ≫ (t.map (pr C)).pt = (t.map (pr C)).pt) (hl : τ ≫ t.pt = t.pt ≫ act C g) (v : V) :
    (((t.map (pr C)).stalkAut Λ τ hτ).app (FV C Λ ρ)).hom ((stalkFV Λ ρ t).inv.hom v) =
      (stalkFV Λ ρ t).inv.hom (ρ g v) := by
  rw [stalkFV_inv, stalkFV_inv, GeomPt.stalkAut_toPresheafFiber]
  have ha : ((t.map (pr C)).autHom τ hτ).hom.app (tx (etId (SY C))) (liftX (pr C) t t.top) =
      (t.map (pr C)).point.fiber.map (actE g) (liftX (pr C) t t.top) := Over.OverMorphism.ext hl
  rw [ha, ← map_actE_unitFV]
  exact (congrArg (fun φ => φ.hom (unitFV Λ ρ v))
    ((t.map (pr C)).point.toPresheafFiber_w (actE g) (liftX (pr C) t t.top) (FV C Λ ρ).obj)).symm

/-- **An automorphism of `Spec Ω` over `X` moves a lift to `Y` by a unique `g ∈ G`.** -/
theorem existsUnique_act {Ω : Type} [Field Ω] (l : Spec (CommRingCat.of Ω) ⟶ SY C)
    (τ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of Ω)) (hτ : τ ≫ l ≫ pr C = l ≫ pr C) :
    ∃! g : C.G, τ ≫ l = l ≫ act C g := by
  obtain ⟨γ, rfl⟩ : ∃ γ, Spec.map γ = l := ⟨_, Spec.map_preimage l⟩
  obtain ⟨β, rfl⟩ : ∃ β, Spec.map β = τ := ⟨_, Spec.map_preimage τ⟩
  have key : ∀ g : C.G, Spec.map β ≫ Spec.map γ = Spec.map γ ≫ act C g ↔
      γ ≫ β = CommRingCat.ofHom (rh C g) ≫ γ := by
    intro g
    rw [act, ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  have hA : γ.hom.comp (algebraMap A C.B) = (γ ≫ β).hom.comp (algebraMap A C.B) := by
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap A C.B) ≫ γ ≫ β) =
        Spec.map (CommRingCat.ofHom (algebraMap A C.B) ≫ γ) := by
      simpa only [Spec.map_comp, Category.assoc] using hτ
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective h1)).symm
  obtain ⟨σ, hσ⟩ := exists_eq_comp C γ.hom (γ ≫ β).hom hA
  have hσ' : γ ≫ β = CommRingCat.ofHom (rh C σ) ≫ γ := CommRingCat.hom_ext hσ
  refine ⟨σ, (key σ).2 hσ', fun g hg => ?_⟩
  exact eq_of_comp_eq C γ.hom (congrArg CommRingCat.Hom.hom (((key g).1 hg).symm.trans hσ'))

/-- The element of `G` by which `τ` (over `X`) moves the lift `t`. -/
def actOf (t : GeomPt (SY C)) (τ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of t.Ω))
    (hτ : τ ≫ (t.map (pr C)).pt = (t.map (pr C)).pt) : C.G :=
  (existsUnique_act t.pt τ hτ).exists.choose

theorem actOf_spec (t : GeomPt (SY C)) (τ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of t.Ω))
    (hτ : τ ≫ (t.map (pr C)).pt = (t.map (pr C)).pt) : τ ≫ t.pt = t.pt ≫ act C (actOf t τ hτ) :=
  (existsUnique_act t.pt τ hτ).exists.choose_spec

theorem actOf_comp (t : GeomPt (SY C)) {τ₁ τ₂ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of t.Ω)}
    (h₁ : τ₁ ≫ (t.map (pr C)).pt = (t.map (pr C)).pt) (h₂ : τ₂ ≫ (t.map (pr C)).pt = (t.map (pr C)).pt)
    (h : (τ₁ ≫ τ₂) ≫ (t.map (pr C)).pt = (t.map (pr C)).pt) :
    actOf t (τ₁ ≫ τ₂) h = actOf t τ₁ h₁ * actOf t τ₂ h₂ :=
  (existsUnique_act t.pt (τ₁ ≫ τ₂) h).unique (actOf_spec t _ h) (by
    show (τ₁ ≫ τ₂) ≫ t.pt = t.pt ≫ act C (actOf t τ₁ h₁ * actOf t τ₂ h₂)
    rw [Category.assoc, actOf_spec t τ₂ h₂, ← Category.assoc, actOf_spec t τ₁ h₁, Category.assoc, act_mul])

/-- **`τ` acts on the stalk of `F_V` at `t ≫ π` by `ρ (actOf τ)`.** -/
theorem stalkAut_stalkFV (t : GeomPt (SY C)) (τ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of t.Ω))
    (hτ : τ ≫ (t.map (pr C)).pt = (t.map (pr C)).pt) (v : V) :
    (((t.map (pr C)).stalkAut Λ τ hτ).app (FV C Λ ρ)).hom ((stalkFV Λ ρ t).inv.hom v) =
      (stalkFV Λ ρ t).inv.hom (ρ (actOf t τ hτ) v) :=
  stalkAut_stalkFV_inv Λ ρ t (actOf t τ hτ) τ hτ (actOf_spec t τ hτ) v

end RamanujanPetersson.EtSheaves.TorSec


