-- Prove2me | Definitions.Def_RPLib_S4_EtShGalFV
-- name    : RPLib_S4_EtShGalFV
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:45:56.002501+00:00
-- url     : https://prove2.me/theorems/f5c2e1e4-48f3-4d66-86e3-f9759aaac778
-- title:
--   The Galois representation on the stalks of $F_V$
-- statement:
--   In the setting of the sheaf $F_V$ of a representation $\rho$ of the group $G$ of a Galois cover $Y = \mathrm{Spec}\,B \to X = \mathrm{Spec}\,A$: every geometric point $\bar s$ of $X$ lifts to $Y$; for a lift the stalk $(F_V)_{\bar s}$ is $V$, and an automorphism $\tau$ of $\mathrm{Spec}\,\Omega$ over $X$ moves the lift by a unique element of $G$ and acts on the stalk by $\rho$ of it. At $\bar x$ this gives a homomorphism $\mathrm{Gal}(\kappa(x)^{\mathrm{sep}}/\kappa(x)) \to G$ with open kernel, and the Galois representation on $(F_V)_{\bar x}$ is $\rho$ composed with it.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. Grothendieck, Revetements etales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Expose V; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter I, Section 5

import Mathlib
import Definitions.Def_RPLib_S4_EtShStalkFV

/-!
# S4-EtSheaves, part O10d-2(iv-c): the Galois representation on `(F_V)_x̄` is `ρ ∘ galFV`

Every geometric point `s` of `X = Spec A` lifts to `Y = Spec B` (`exists_lift`); for a lift `l`, the stalk of `F_V`
at `s` is `V` (`stalkFVAt`), an automorphism `τ` of `Spec Ω` over `X` moves `l` by a unique `actOfL τ ∈ G`
(`actOfL_eq_iff`, multiplicative: `actOfL_comp`) and acts on the stalk by `ρ (actOfL τ)` (`stalkAut_stalkFVAt`).
At `x̄ = geomPtAt x` this gives a hom `galFV : Gal(κ(x)^sep/κ(x)) →* G` with open kernel (`isOpen_ker_galFV`, via
the regular representation and discreteness of stalks), and the Galois representation on `(F_V)_x̄` is
`ρ ∘ galFV` (`galRep_FV`, `stalkFVAt_galRep`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] {C : GalCover A}

/-- The geometric point of `Y` given by a lift `l` of a geometric point `s` of `X`. -/
def liftPt (s : GeomPt (SX A)) (l : Spec (CommRingCat.of s.Ω) ⟶ SY C) : GeomPt (SY C) where
  Ω := s.Ω
  pt := l

theorem liftPt_map (s : GeomPt (SX A)) (l : Spec (CommRingCat.of s.Ω) ⟶ SY C) (hl : l ≫ pr C = s.pt) :
    (liftPt s l).map (pr C) = s := by
  show GeomPt.mk s.Ω (l ≫ pr C) = s
  rw [hl]

/-- **Every geometric point of `X` lifts to `Y`.** -/
theorem exists_lift (s : GeomPt (SX A)) : ∃ l : Spec (CommRingCat.of s.Ω) ⟶ SY C, l ≫ pr C = s.pt := by
  obtain ⟨y, hy⟩ := pr_surjective C s.center
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (pr C) s.pt y hy
  exact ⟨l, hl⟩

section Act

variable (s : GeomPt (SX A)) (l : Spec (CommRingCat.of s.Ω) ⟶ SY C)

theorem liftPt_comp (hl : l ≫ pr C = s.pt) (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (hτ : τ ≫ s.pt = s.pt) :
    τ ≫ ((liftPt s l).map (pr C)).pt = ((liftPt s l).map (pr C)).pt :=
  (by rw [hl]; exact hτ : τ ≫ l ≫ pr C = l ≫ pr C)

/-- The element of `G` by which `τ` (over `X`) moves the lift `l`. -/
def actOfL (hl : l ≫ pr C = s.pt) (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (hτ : τ ≫ s.pt = s.pt) : C.G :=
  actOf (liftPt s l) τ (liftPt_comp s l hl τ hτ)

theorem actOfL_spec (hl : l ≫ pr C = s.pt) (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (hτ : τ ≫ s.pt = s.pt) :
    τ ≫ l = l ≫ act C (actOfL s l hl τ hτ) :=
  actOf_spec (liftPt s l) τ (liftPt_comp s l hl τ hτ)

theorem actOfL_eq_iff (hl : l ≫ pr C = s.pt) (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (hτ : τ ≫ s.pt = s.pt)
    (g : C.G) : actOfL s l hl τ hτ = g ↔ τ ≫ l = l ≫ act C g :=
  ⟨fun h => h ▸ actOfL_spec s l hl τ hτ,
    fun h => (existsUnique_act l τ (liftPt_comp s l hl τ hτ)).unique (actOfL_spec s l hl τ hτ) h⟩

theorem actOfL_id (hl : l ≫ pr C = s.pt) (h : 𝟙 _ ≫ s.pt = s.pt) : actOfL s l hl (𝟙 _) h = 1 :=
  (actOfL_eq_iff s l hl _ h 1).2 (by rw [act_one, Category.id_comp, Category.comp_id])

theorem actOfL_comp (hl : l ≫ pr C = s.pt) {τ₁ τ₂ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)}
    (h₁ : τ₁ ≫ s.pt = s.pt) (h₂ : τ₂ ≫ s.pt = s.pt) (h : (τ₁ ≫ τ₂) ≫ s.pt = s.pt) :
    actOfL s l hl (τ₁ ≫ τ₂) h = actOfL s l hl τ₁ h₁ * actOfL s l hl τ₂ h₂ :=
  (actOfL_eq_iff s l hl _ h _).2 (by
    rw [Category.assoc, actOfL_spec s l hl τ₂ h₂, ← Category.assoc, actOfL_spec s l hl τ₁ h₁, Category.assoc,
      act_mul])

end Act

/-- **The Galois group of `κ(x)` acting through `G`**: `σ ↦` the element moving the lift `l` of `x̄`. -/
def galFV (x : SX A) (l : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ SY C) (hl : l ≫ pr C = (geomPtAt x).pt) :
    Gal x →* C.G where
  toFun σ := actOfL (geomPtAt x) l hl (galSpec x σ) (galSpec_comp x σ)
  map_one' := (actOfL_eq_iff _ l hl _ _ 1).2
    (((congrArg (fun φ : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ Spec (CommRingCat.of (geomPtAt x).Ω) => φ ≫ l)
      (galSpec_one x)).trans (Category.id_comp l)).trans
      ((Category.comp_id l).symm.trans (congrArg (fun φ => l ≫ φ) (act_one C).symm)))
  map_mul' σ τ := (actOfL_eq_iff _ l hl _ _ _).2 (by
    refine (congrArg (fun φ : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ Spec (CommRingCat.of (geomPtAt x).Ω) =>
      φ ≫ l) (galSpec_mul x σ τ)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun φ => galSpec x σ ≫ φ) (actOfL_spec _ l hl _ (galSpec_comp x τ))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun φ => φ ≫ act C _) (actOfL_spec _ l hl _ (galSpec_comp x σ))).trans ?_
    exact (Category.assoc _ _ _).trans (congrArg (fun φ => l ≫ φ) (act_mul C _ _)))

theorem galFV_spec (x : SX A) (l : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ SY C)
    (hl : l ≫ pr C = (geomPtAt x).pt) (σ : Gal x) : galSpec x σ ≫ l = l ≫ act C (galFV x l hl σ) :=
  actOfL_spec _ l hl _ (galSpec_comp x σ)

variable (Λ : Type) [CommRing Λ] {V : Type} [AddCommGroup V] [Module Λ V] (ρ : Representation Λ C.G V)

/-- **The stalk of `F_V` at a geometric point `s` of `X` with a lift `l` to `Y` is `V`.** -/
def stalkFVAt (s : GeomPt (SX A)) (l : Spec (CommRingCat.of s.Ω) ⟶ SY C) (hl : l ≫ pr C = s.pt) :
    (s.stalkF Λ).obj (FV C Λ ρ) ≅ ModuleCat.of Λ V :=
  eqToIso (congrArg (fun p : GeomPt (SX A) => (p.stalkF Λ).obj (FV C Λ ρ)) (liftPt_map s l hl).symm) ≪≫
    stalkFV Λ ρ (liftPt s l)

theorem stalkAut_stalkFVAt_mk (Ω : Type) [Field Ω] [IsSepClosed Ω] (pt : Spec (CommRingCat.of Ω) ⟶ SX A)
    (l : Spec (CommRingCat.of Ω) ⟶ SY C) (hl : l ≫ pr C = pt)
    (τ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of Ω)) (hτ : τ ≫ pt = pt) (v : V) :
    (((GeomPt.mk Ω pt).stalkAut Λ τ hτ).app (FV C Λ ρ)).hom ((stalkFVAt Λ ρ (GeomPt.mk Ω pt) l hl).inv.hom v) =
      (stalkFVAt Λ ρ (GeomPt.mk Ω pt) l hl).inv.hom (ρ (actOfL (GeomPt.mk Ω pt) l hl τ hτ) v) := by
  subst hl
  exact stalkAut_stalkFV Λ ρ (liftPt (GeomPt.mk Ω (l ≫ pr C)) l) τ hτ v

/-- **Equivariance at any geometric point**: `τ` over `X` acts on `(F_V)_s` by `ρ (actOfL τ)`. -/
theorem stalkAut_stalkFVAt (s : GeomPt (SX A)) (l : Spec (CommRingCat.of s.Ω) ⟶ SY C) (hl : l ≫ pr C = s.pt)
    (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (hτ : τ ≫ s.pt = s.pt) (v : V) :
    ((s.stalkAut Λ τ hτ).app (FV C Λ ρ)).hom ((stalkFVAt Λ ρ s l hl).inv.hom v) =
      (stalkFVAt Λ ρ s l hl).inv.hom (ρ (actOfL s l hl τ hτ) v) :=
  stalkAut_stalkFVAt_mk Λ ρ s.Ω s.pt l hl τ hτ v

/-- **The Galois representation on `(F_V)_x̄` is `ρ ∘ galFV`** (inverse form). -/
theorem galRep_FV (x : SX A) (l : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ SY C)
    (hl : l ≫ pr C = (geomPtAt x).pt) (σ : Gal x) (v : V) :
    galRep Λ (FV C Λ ρ) x σ ((stalkFVAt Λ ρ (geomPtAt x) l hl).inv.hom v) =
      (stalkFVAt Λ ρ (geomPtAt x) l hl).inv.hom (ρ (galFV x l hl σ) v) :=
  stalkAut_stalkFVAt Λ ρ (geomPtAt x) l hl (galSpec x σ) (galSpec_comp x σ) v

theorem iso_inv_hom_apply {M N : ModuleCat Λ} (e : M ≅ N) (u : N) : e.hom.hom (e.inv.hom u) = u :=
  congrArg (fun φ => φ.hom u) e.inv_hom_id

theorem iso_hom_inv_apply {M N : ModuleCat Λ} (e : M ≅ N) (w : M) : e.inv.hom (e.hom.hom w) = w :=
  congrArg (fun φ => φ.hom w) e.hom_inv_id

theorem iso_conj {M N : ModuleCat Λ} (e : M ≅ N) (f : M → M) (g : N → N)
    (h : ∀ u, f (e.inv.hom u) = e.inv.hom (g u)) (w : M) : e.hom.hom (f w) = g (e.hom.hom w) := by
  calc e.hom.hom (f w) = e.hom.hom (f (e.inv.hom (e.hom.hom w))) := by rw [iso_hom_inv_apply Λ e w]
    _ = e.hom.hom (e.inv.hom (g (e.hom.hom w))) := by rw [h]
    _ = g (e.hom.hom w) := iso_inv_hom_apply Λ e _

/-- **The Galois representation on `(F_V)_x̄` is `ρ ∘ galFV`**: `e (σ • w) = ρ (galFV σ) (e w)`. -/
theorem stalkFVAt_galRep (x : SX A) (l : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ SY C)
    (hl : l ≫ pr C = (geomPtAt x).pt) (σ : Gal x) (w : stalk Λ (FV C Λ ρ) x) :
    (stalkFVAt Λ ρ (geomPtAt x) l hl).hom.hom (galRep Λ (FV C Λ ρ) x σ w) =
      ρ (galFV x l hl σ) ((stalkFVAt Λ ρ (geomPtAt x) l hl).hom.hom w) :=
  iso_conj Λ (stalkFVAt Λ ρ (geomPtAt x) l hl) (galRep Λ (FV C Λ ρ) x σ) (ρ (galFV x l hl σ))
    (galRep_FV Λ ρ x l hl σ) w

/-- **`galFV` is continuous**: its kernel is open (stalks of `F_{ℤ[G]}` are discrete Galois modules). -/
theorem isOpen_ker_galFV (x : SX A) (l : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ SY C)
    (hl : l ≫ pr C = (geomPtAt x).pt) : IsOpen ((galFV x l hl).ker : Set (Gal x)) := by
  classical
  let e := stalkFVAt ℤ (Representation.ofMulAction ℤ C.G C.G) (geomPtAt x) l hl
  obtain ⟨H, hH, hfix⟩ := exists_open_fix ℤ (FV C ℤ (Representation.ofMulAction ℤ C.G C.G)) x (e.inv.hom (MonoidAlgebra.single (1 : C.G) (1 : ℤ)))
  refine Subgroup.isOpen_mono (fun σ hσ => ?_) hH
  have h1 : e.inv.hom ((Representation.ofMulAction ℤ C.G C.G) (galFV x l hl σ) (MonoidAlgebra.single (1 : C.G) (1 : ℤ))) = e.inv.hom (MonoidAlgebra.single (1 : C.G) (1 : ℤ)) :=
    (galRep_FV ℤ (Representation.ofMulAction ℤ C.G C.G) x l hl σ _).symm.trans (hfix σ hσ)
  have h2 : (Representation.ofMulAction ℤ C.G C.G) (galFV x l hl σ) (MonoidAlgebra.single (1 : C.G) (1 : ℤ)) = MonoidAlgebra.single (1 : C.G) (1 : ℤ) :=
    (iso_inv_hom_apply ℤ e _).symm.trans ((congrArg e.hom.hom h1).trans (iso_inv_hom_apply ℤ e _))
  rw [Representation.ofMulAction_single, MonoidAlgebra.single_left_inj one_ne_zero, smul_eq_mul, mul_one] at h2
  exact (MonoidHom.mem_ker).2 h2

end RamanujanPetersson.EtSheaves.TorSec


