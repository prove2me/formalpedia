-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_levelLifts_pi_of_forall_exists_levelLifts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/be9c780e-7f1f-5dad-9763-333e8fec7911

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_monoidHom_pt_comp_eq_act_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_thetaPt_eq_of_pt_eq_of_forall_act_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_mul_act
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_ofScalar_act
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_levelLifts_pi_of_forall_exists_levelLifts
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_levelLifts_pi_of_forall_exists_levelLifts.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_levelLifts_pi_of_forall_exists_levelLifts.AlgebraicGeometry.Polarisation"
open scoped BigOperators

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.Hom.app_smul Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.Hom.comp_appTop Scheme.Modules.pullbackCongr Spec.map_id Scheme.Modules Scheme.Modules.pullbackComp Scheme.ΓSpecIso PolarisedAbelianScheme Scheme.Modules.pullbackLocalSection Scheme.Modules.pullbackLocalSection_smul existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal PolarisedAbelianScheme.thetaPt_eq_of_pt_eq_of_forall_act_eq"
namespace Polarisation
p2m_export "AlgebraicGeometry.Polarisation" "ThetaPt.mul_pt ThetaPt.ofUnit ThetaPt.ofScalar ThetaPt.ofScalar_pt ThetaPt baseScalar ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one ThetaPt.exists_monoidHom_pt_comp_eq_act_eq_of_isPullback ThetaPt.mul_act ThetaPt.ofScalar_act"
namespace TA
p2m_open "AlgebraicGeometry.Polarisation AlgebraicGeometry"

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
  (𝓛 : A.Modules) {R R' : Type} [CommRing R] [CommRing R']
  (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (t' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S))
  (ψ : R →+* R') (hr : Spec.map (CommRingCat.ofHom ψ) ≫ t = t')

def b : pullback f t' ⟶ pullback f t :=
  pullback.lift (pullback.fst f t' ≫ 𝟙 A) (pullback.snd f t' ≫ Spec.map (CommRingCat.ofHom ψ)) (by
    rw [Category.assoc, Category.id_comp, pullback.condition, Category.assoc, hr])

theorem b_fst : b f t t' ψ hr ≫ pullback.fst f t = pullback.fst f t' ≫ 𝟙 A := pullback.lift_fst _ _ _

theorem b_fst' : b f t t' ψ hr ≫ pullback.fst f t = pullback.fst f t' := by rw [b_fst, Category.comp_id]

theorem b_snd : b f t t' ψ hr ≫ pullback.snd f t = pullback.snd f t' ≫ Spec.map (CommRingCat.ofHom ψ) :=
  pullback.lift_snd _ _ _

def c : (Scheme.Modules.pullback (b f t t' ψ hr)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅
    (Scheme.Modules.pullback (pullback.fst f t')).obj 𝓛 :=
  (Scheme.Modules.pullbackComp (b f t t' ψ hr) _).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr (b_fst' f t t' ψ hr)).app 𝓛

theorem isPullback_id : IsPullback (𝟙 A) f f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
  rw [CommRingCat.ofHom_id, Spec.map_id]
  exact IsPullback.id_horiz f

theorem mul_congr_base {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (x y : SchemeHomOver t₁ f) :
    (L.mul t₁ x y).1 = (L.mul t₂ ⟨x.1, h ▸ x.2⟩ ⟨y.1, h ▸ y.2⟩).1 := by
  subst h; rfl

theorem hmul_id {T : Scheme.{0}} (t'' : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t'' f) :
    (L.mul t'' x y).1 ≫ 𝟙 A =
      (L.mul (t'' ≫ Spec.map (CommRingCat.ofHom (RingHom.id S)))
        ⟨x.1 ≫ 𝟙 A, by rw [Category.assoc, (isPullback_id f).w, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ 𝟙 A, by rw [Category.assoc, (isPullback_id f).w, ← Category.assoc, y.2]⟩).1 := by
  have ht : t'' = t'' ≫ Spec.map (CommRingCat.ofHom (RingHom.id S)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  rw [Category.comp_id, mul_congr_base f L ht x y]
  congr 2 <;> exact Subtype.ext (Category.comp_id _).symm

include hr in
theorem hr' : Spec.map (CommRingCat.ofHom ψ) ≫ t = t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id S)) := by
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, hr]

theorem exists_monoidHom_transport :
    ∃ β : ThetaPt f L 𝓛 t →* ThetaPt f L 𝓛 t',
      (∀ θ, (β θ).pt.1 = Spec.map (CommRingCat.ofHom ψ) ≫ θ.pt.1) ∧
      (∀ θ (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)),
        (β θ).act ((c f 𝓛 t t' ψ hr).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b f t t' ψ hr) s :
            Γ((Scheme.Modules.pullback (b f t t' ψ hr)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) =
          (c f 𝓛 t t' ψ hr).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b f t t' ψ hr) (θ.act s) :
            Γ((Scheme.Modules.pullback (b f t t' ψ hr)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) ∧
      (∀ v : Rˣ, β (ThetaPt.ofScalar v) = ThetaPt.ofScalar (Units.map (ψ : R →* R') v)) ∧
      (∀ w : Γ(pullback f t, ⊤)ˣ,
        β (ThetaPt.ofUnit w) = ThetaPt.ofUnit (Units.map ((b f t t' ψ hr).appTop.hom : _ →* _) w)) := by
  obtain ⟨β, h1, h2, h3, h4⟩ := ThetaPt.exists_monoidHom_pt_comp_eq_act_eq_of_isPullback (RingHom.id S) L L (𝟙 A)
    (isPullback_id f) (fun t'' x y => hmul_id f L t'' x y) 𝓛 𝓛 t t' ψ (hr' t t' ψ hr)
    (b f t t' ψ hr) (b_fst f t t' ψ hr) (b_snd f t t' ψ hr) (c f 𝓛 t t' ψ hr)
  refine ⟨β, fun θ => ?_, h2, h3, h4⟩
  have := h1 θ
  rwa [Category.comp_id] at this

theorem hr_algebraMap (R R' : Type) [CommRing R] [CommRing R'] [Algebra S R] [Algebra S R'] [Algebra R R']
    [IsScalarTower S R R'] :
    Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ Spec.map (CommRingCat.ofHom (algebraMap S R)) =
      Spec.map (CommRingCat.ofHom (algebraMap S R')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

end AlgebraicGeometry.Polarisation.TA

namespace TN
namespace B4

section PiRing

variable {P : Type} [Fintype P] [DecidableEq P] (Rp : P → Type) [∀ p, CommRing (Rp p)]

def stdIdem (p : P) : (∀ q, Rp q) := Pi.single p 1

theorem stdIdem_same (p : P) : stdIdem Rp p p = 1 := Pi.single_eq_same _ _

theorem stdIdem_ne {p q : P} (h : q ≠ p) : stdIdem Rp p q = 0 := Pi.single_eq_of_ne h _

theorem stdIdem_mul_apply (p : P) (x : ∀ q, Rp q) (q : P) :
    (stdIdem Rp p * x) q = if q = p then x q else 0 := by
  rw [Pi.mul_apply]
  by_cases hq : q = p
  · subst hq; rw [stdIdem_same, one_mul, if_pos rfl]
  · rw [stdIdem_ne Rp hq, zero_mul, if_neg hq]

theorem isIdempotentElem_stdIdem (p : P) : IsIdempotentElem (stdIdem Rp p) := by
  change stdIdem Rp p * stdIdem Rp p = stdIdem Rp p
  funext q
  rw [stdIdem_mul_apply]
  by_cases hq : q = p
  · rw [if_pos hq]
  · rw [if_neg hq, stdIdem_ne Rp hq]

theorem sum_stdIdem : ∑ p, stdIdem Rp p = 1 := by
  funext q
  rw [Finset.sum_apply, Finset.sum_eq_single q]
  · rw [stdIdem_same]; rfl
  · intro p _ hp; exact stdIdem_ne Rp (Ne.symm hp)
  · intro h; exact absurd (Finset.mem_univ q) h

theorem stdIdem_mul_stdIdem (p p' : P) (h : p ≠ p') : stdIdem Rp p * stdIdem Rp p' = 0 := by
  funext q
  rw [stdIdem_mul_apply, Pi.zero_apply]
  by_cases hq : q = p
  · rw [if_pos hq]; subst hq; exact stdIdem_ne Rp h
  · rw [if_neg hq]

theorem eval_stdIdem_pow (p : P) (x : ∀ q, Rp q) : (stdIdem Rp p * x) p = x p := by
  rw [stdIdem_mul_apply, if_pos rfl]

theorem isLocalization_eval (p : P) :
    letI : Algebra (∀ q, Rp q) (Rp p) := (Pi.evalRingHom Rp p).toAlgebra
    IsLocalization.Away (stdIdem Rp p) (Rp p) := by
  letI : Algebra (∀ q, Rp q) (Rp p) := (Pi.evalRingHom Rp p).toAlgebra
  refine IsLocalization.away_of_isIdempotentElem_of_mul (isIdempotentElem_stdIdem Rp p) (fun x y => ?_)
    (fun y => ⟨Pi.single p y, by change (Pi.single p y : ∀ q, Rp q) p = y; simp⟩)
  change x p = y p ↔ stdIdem Rp p * x = stdIdem Rp p * y
  constructor
  · intro h
    funext q
    rw [stdIdem_mul_apply, stdIdem_mul_apply]
    by_cases hq : q = p
    · subst hq; rw [if_pos rfl, if_pos rfl, h]
    · rw [if_neg hq, if_neg hq]
  · intro h
    have := congrFun h p
    rwa [eval_stdIdem_pow, eval_stdIdem_pow] at this

end PiRing

theorem exists_ringHom_factor_to_away {P : Type} [Fintype P] [DecidableEq P] (Rp : P → Type) [∀ p, CommRing (Rp p)] (p : P) :
    ∃ ψ : Rp p →+* Localization.Away (stdIdem Rp p),
      ∀ a : (∀ q, Rp q), ψ (a p) = algebraMap (∀ q, Rp q) (Localization.Away (stdIdem Rp p)) a := by
  letI : Algebra (∀ q, Rp q) (Rp p) := (Pi.evalRingHom Rp p).toAlgebra
  haveI := isLocalization_eval Rp p
  refine ⟨(IsLocalization.algEquiv (Submonoid.powers (stdIdem Rp p)) (Rp p) (Localization.Away (stdIdem Rp p))).toRingHom,
    fun a => ?_⟩
  have : a p = algebraMap (∀ q, Rp q) (Rp p) a := rfl
  rw [this]
  exact (IsLocalization.algEquiv (Submonoid.powers (stdIdem Rp p)) (Rp p) (Localization.Away (stdIdem Rp p))).commutes a

section Chart
variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (𝓛 : A.Modules)
  {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (t' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S))
  (b : pullback f t' ⟶ pullback f t)
  (hb₂ : b ≫ pullback.snd f t = pullback.snd f t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
  (c : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅
    (Scheme.Modules.pullback (pullback.fst f t')).obj 𝓛)

include hb₂ in
theorem app_baseScalar (r : R) : b.app ⊤ (baseScalar f t r) = baseScalar f t' (algebraMap R R' r) := by
  have nat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R R'))
  have h2 : (Spec.map (CommRingCat.ofHom (algebraMap R R'))).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv (algebraMap R R' r) := by
    have e1 := CommRingCat.comp_apply (Scheme.ΓSpecIso (CommRingCat.of R)).inv
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))).appTop r
    have e2 := CommRingCat.comp_apply (CommRingCat.ofHom (algebraMap R R')) (Scheme.ΓSpecIso (CommRingCat.of R')).inv r
    rw [← nat] at e1
    rw [← e1, e2]
    rfl
  change ((pullback.snd f t).appTop ≫ b.appTop) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) =
    (pullback.snd f t').appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv (algebraMap R R' r))
  rw [← Scheme.Hom.comp_appTop, hb₂, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h2]

include hb₂ in
theorem chart_smul (r : R) (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)) :
    c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection b (baseScalar f t r • s) :
        Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤)) =
      baseScalar f t' (algebraMap R R' r) • c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection b s :
        Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤)) := by
  rw [Scheme.Modules.pullbackLocalSection_smul]
  erw [Scheme.Modules.Hom.app_smul]
  rw [app_baseScalar f t t' b hb₂]

end Chart

end TN.B4

end

open TN.B4 in
set_option maxHeartbeats 6400000 in
theorem solution
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)]
    {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {m : ℕ} (Rp : Fin m → Type) [∀ p, CommRing (Rp p)] (φ : ∀ p, S →+* Rp p) (ζ : ∀ p, (Rp p)ˣ)
    (hL : ∀ p : Fin m,
      ∃ (lift : ((i : Fin g) → ZMod (δ i)) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (φ p))))
        (dualLift : (((i : Fin g) → ZMod (δ i)) →+ ZMod d) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (φ p)))),
        lift 0 = 1 ∧ (∀ h h' : ((i : Fin g) → ZMod (δ i)), lift (h + h') = lift h * lift h') ∧
        dualLift 0 = 1 ∧ (∀ c c' : ((i : Fin g) → ZMod (δ i)) →+ ZMod d, dualLift (c + c') = dualLift c * dualLift c') ∧
        (∀ (c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d) (h : ((i : Fin g) → ZMod (δ i))),
          dualLift c * lift h = ThetaPt.ofScalar (ζ p ^ (c h).val) * (lift h * dualLift c))) :
    ∃ (lift : ((i : Fin g) → ZMod (δ i)) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (RingHom.pi φ))))
        (dualLift : (((i : Fin g) → ZMod (δ i)) →+ ZMod d) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (RingHom.pi φ)))),
        lift 0 = 1 ∧ (∀ h h' : ((i : Fin g) → ZMod (δ i)), lift (h + h') = lift h * lift h') ∧
        dualLift 0 = 1 ∧ (∀ c c' : ((i : Fin g) → ZMod (δ i)) →+ ZMod d, dualLift (c + c') = dualLift c * dualLift c') ∧
        (∀ (c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d) (h : ((i : Fin g) → ZMod (δ i))),
          dualLift c * lift h = ThetaPt.ofScalar (MulEquiv.piUnits.symm ζ ^ (c h).val) * (lift h * dualLift c)) := by
  classical

  set t : Spec (CommRingCat.of ((p : Fin m) → Rp p)) ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (RingHom.pi φ)) with ht
  let ε : Fin m → ((p : Fin m) → Rp p) := stdIdem Rp
  have hε : ∀ j, IsIdempotentElem (ε j) := isIdempotentElem_stdIdem Rp
  have hsum : ∑ j, ε j = 1 := sum_stdIdem Rp
  have horth : ∀ j l, j ≠ l → ε j * ε l = 0 := fun j l h => stdIdem_mul_stdIdem Rp j l h

  have hψ := fun p => exists_ringHom_factor_to_away Rp p
  choose ψ hψ using hψ
  have hψcomp : ∀ p, (algebraMap ((q : Fin m) → Rp q) (Localization.Away (ε p))).comp (RingHom.pi φ) = (ψ p).comp (φ p) := by
    intro p; ext s; show algebraMap _ _ (RingHom.pi φ s) = ψ p (φ p s); rw [← hψ]; rfl
  have hr : ∀ p, Spec.map (CommRingCat.ofHom (ψ p)) ≫ Spec.map (CommRingCat.ofHom (φ p)) =
      Spec.map (CommRingCat.ofHom (algebraMap ((q : Fin m) → Rp q) (Localization.Away (ε p)))) ≫ t := by
    intro p
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hψcomp]

  obtain ⟨b, hb₁, hb₂, c, -⟩ : ∃ (b : ∀ j, pullback u.f (Spec.map (CommRingCat.ofHom (algebraMap ((q : Fin m) → Rp q)
        (Localization.Away (ε j)))) ≫ t) ⟶ pullback u.f t)
      (_ : ∀ j, b j ≫ pullback.fst u.f t = pullback.fst u.f _)
      (_ : ∀ j, b j ≫ pullback.snd u.f t = pullback.snd u.f _ ≫
        Spec.map (CommRingCat.ofHom (algebraMap ((q : Fin m) → Rp q) (Localization.Away (ε j)))))
      (c : ∀ j, (Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol) ≅
        (Scheme.Modules.pullback (pullback.fst u.f _)).obj u.pol), True :=
    ⟨fun j => TA.b u.f t _ _ rfl, fun j => TA.b_fst' u.f t _ _ rfl, fun j => TA.b_snd u.f t _ _ rfl,
      fun j => TA.c u.f u.pol t _ _ rfl, trivial⟩
  obtain ⟨bb, hbb₁, hbb₂, cc, -⟩ : ∃ (bb : ∀ p, pullback u.f (Spec.map (CommRingCat.ofHom (algebraMap ((q : Fin m) → Rp q)
        (Localization.Away (ε p)))) ≫ t) ⟶ pullback u.f (Spec.map (CommRingCat.ofHom (φ p))))
      (_ : ∀ p, bb p ≫ pullback.fst u.f _ = pullback.fst u.f _)
      (_ : ∀ p, bb p ≫ pullback.snd u.f _ = pullback.snd u.f _ ≫ Spec.map (CommRingCat.ofHom (ψ p)))
      (cc : ∀ p, (Scheme.Modules.pullback (bb p)).obj ((Scheme.Modules.pullback (pullback.fst u.f
          (Spec.map (CommRingCat.ofHom (φ p))))).obj u.pol) ≅
        (Scheme.Modules.pullback (pullback.fst u.f _)).obj u.pol), True :=
    ⟨fun p => TA.b u.f _ _ (ψ p) (hr p), fun p => TA.b_fst' u.f _ _ (ψ p) (hr p), fun p => TA.b_snd u.f _ _ (ψ p) (hr p),
      fun p => TA.c u.f u.pol _ _ (ψ p) (hr p), trivial⟩

  have glue := fun θ' => ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one u.f u.L u.pol t ε hε hsum horth
    b hb₁ hb₂ c θ'
  choose G hGpt hGact hGuniq using glue

  have trans := fun p => ThetaPt.exists_monoidHom_pt_comp_eq_act_eq_of_isPullback (RingHom.id S) u.L u.L (𝟙 u.A)
    (TA.isPullback_id u.f) (fun t'' x y => TA.hmul_id u.f u.L t'' x y) u.pol u.pol (Spec.map (CommRingCat.ofHom (φ p))) _
    (ψ p) (TA.hr' _ _ _ (hr p)) (bb p) (by rw [hbb₁, Category.comp_id]) (hbb₂ p) (cc p)
  choose β hβpt hβact hβsc hβu using trans

  have G_mul : ∀ θ' θ'', G (θ' * θ'') = G θ' * G θ'' := by
    intro θ' θ''
    apply PolarisedAbelianScheme.thetaPt_eq_of_pt_eq_of_forall_act_eq u t
    · apply Subtype.ext
      refine (existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal ε hε hsum horth
        (fun j => ((θ' * θ'') j).pt.1)).unique (fun j => (hGpt (θ' * θ'') j).symm) (fun j => ?_)
      rw [ThetaPt.mul_pt, Pi.mul_apply, ThetaPt.mul_pt, ← GoodReductionJacobian.schemeHomOverComp_coe _ rfl (u.L.mul t _ _),
        u.L.mul_natural t _ _ rfl]
      congr 2 <;> exact Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe]; exact (hGpt _ j).symm)
    · intro s
      rw [ThetaPt.mul_act]
      apply hGuniq (θ' * θ'') s
      intro j
      rw [Pi.mul_apply, ThetaPt.mul_act, hGact θ'' j s, hGact θ' j]
  have G_one : G 1 = 1 := by
    have h := G_mul 1 1
    rw [one_mul] at h
    exact mul_left_cancel (h.symm.trans (mul_one (G 1)).symm)

  have G_scalar : ∀ v : ((p : Fin m) → Rp p)ˣ,
      G (fun j => ThetaPt.ofScalar (Units.map (algebraMap ((q : Fin m) → Rp q) (Localization.Away (ε j)) : _ →* _) v)) =
        ThetaPt.ofScalar v := by
    intro v
    set fam : ∀ j, ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (algebraMap ((q : Fin m) → Rp q)
        (Localization.Away (ε j)))) ≫ t) :=
      fun j => ThetaPt.ofScalar (Units.map (algebraMap ((q : Fin m) → Rp q) (Localization.Away (ε j)) : _ →* _) v) with hfam
    apply PolarisedAbelianScheme.thetaPt_eq_of_pt_eq_of_forall_act_eq u t
    · apply Subtype.ext
      refine (existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal ε hε hsum horth
        (fun j => (fam j).pt.1)).unique (fun j => (hGpt fam j).symm) (fun j => ?_)
      rw [ThetaPt.ofScalar_pt, ← GoodReductionJacobian.schemeHomOverComp_coe _ rfl (u.L.one t), u.L.one_natural t _ _ rfl]
      show (u.L.one _).1 = (ThetaPt.ofScalar _ : ThetaPt u.f u.L u.pol _).pt.1
      rw [ThetaPt.ofScalar_pt]
    · intro s
      rw [ThetaPt.ofScalar_act]
      apply hGuniq fam s
      intro j
      show (ThetaPt.ofScalar _ : ThetaPt u.f u.L u.pol _).act _ = _
      rw [ThetaPt.ofScalar_act, Units.coe_map, MonoidHom.coe_coe, chart_smul u.f u.pol t _ (b j) (hb₂ j) (c j)]

  choose lf dl hl0 hlmul hd0 hdmul hHeis using hL
  refine ⟨fun h => G (fun p => β p (lf p h)), fun c' => G (fun p => β p (dl p c')), ?_, ?_, ?_, ?_, ?_⟩
  · show G (fun p => β p (lf p 0)) = 1
    rw [← G_one]; congr 1; funext p; rw [hl0, map_one]; rfl
  · intro h h'
    show G (fun p => β p (lf p (h + h'))) = G (fun p => β p (lf p h)) * G (fun p => β p (lf p h'))
    rw [← G_mul]; congr 1; funext p; rw [hlmul, map_mul]; rfl
  · show G (fun p => β p (dl p 0)) = 1
    rw [← G_one]; congr 1; funext p; rw [hd0, map_one]; rfl
  · intro c₁ c₂
    show G (fun p => β p (dl p (c₁ + c₂))) = G (fun p => β p (dl p c₁)) * G (fun p => β p (dl p c₂))
    rw [← G_mul]; congr 1; funext p; rw [hdmul, map_mul]; rfl
  · intro c' h
    show G (fun p => β p (dl p c')) * G (fun p => β p (lf p h)) =
      ThetaPt.ofScalar (MulEquiv.piUnits.symm ζ ^ (c' h).val) * (G (fun p => β p (lf p h)) * G (fun p => β p (dl p c')))
    have key : (fun p => β p (dl p c')) * (fun p => β p (lf p h)) =
        (fun j => ThetaPt.ofScalar (Units.map (algebraMap ((q : Fin m) → Rp q) (Localization.Away (ε j)) : _ →* _)
          (MulEquiv.piUnits.symm ζ ^ (c' h).val))) * ((fun p => β p (lf p h)) * (fun p => β p (dl p c'))) := by
      funext p
      simp only [Pi.mul_apply]
      rw [← map_mul, hHeis, map_mul, map_mul, hβsc]
      congr 2
      ext
      simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val, map_pow]
      rw [← hψ p]
      rfl
    rw [← G_mul, key, G_mul, G_mul, G_scalar]

end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_levelLifts_pi_of_forall_exists_levelLifts
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_levelLifts_pi_of_forall_exists_levelLifts (solution)
