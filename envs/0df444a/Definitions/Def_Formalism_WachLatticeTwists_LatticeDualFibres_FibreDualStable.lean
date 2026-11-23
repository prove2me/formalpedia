-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
-- name    : Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:50.445076+00:00
-- url     : https://prove2.me/theorems/09e18b39-3e17-4748-807a-85a2f3e79ed3
-- title:
--   Fibre Dual Stable
-- statement:
--   Definitions and structural lemmas for Fibre Dual Stable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/FibreDualStable.lean

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_StatDualFibreLattice
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_MapHOneCommSquare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
open ReciprocityTheory.Gal
noncomputable section
namespace Formalism.RepresentationBoundsCohomology.LOC
section Basic
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
def twist {G : Type u} [Group G] (ε : G →* Oˣ) (M : Type u) [AddCommGroup M] [Module O M] :
    Representation O G M where
  toFun g := ((ε g : Oˣ) : O) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by
    ext
    simp [mul_smul]
    exact smul_comm _ _ _
@[simp] theorem twist_apply {G : Type u} [Group G] (ε : G →* Oˣ) (M : Type u) [AddCommGroup M]
    [Module O M] (g : G) (m : M) : twist ε M g m = ((ε g : Oˣ) : O) • m := rfl
def pairKO {V V' : Type u} [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module O V']
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V) :
    (V ⧸ T) →ₗ[O] (dualLat b T) →ₗ[O] KO O :=
  Submodule.liftQ T ((b.compl₂ (dualLat b T).subtype).compr₂ (toKO O)) (by
    intro x hx
    rw [LinearMap.mem_ker]
    ext f
    exact (Submodule.Quotient.mk_eq_zero _).2 (f.2 x hx))
@[simp] theorem pairKO_mk {V V' : Type u} [AddCommGroup V] [Module O V] [AddCommGroup V']
    [Module O V'] (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V) (x : V)
    (f : dualLat b T) : pairKO b T (Submodule.Quotient.mk x) f = toKO O (b x f) := rfl
variable {G : Type u} [Group G]
theorem dualLat_stable {V V' : Type u} [AddCommGroup V] [Module O V] [AddCommGroup V']
    [Module O V'] {ε : G →* Oˣ} {ρ : Representation O G V} {ρ' : Representation O G V'}
    {b : V →ₗ[O] V' →ₗ[O] FractionRing O} {T : Submodule O V} (hT : StableUnder ρ T)
    (hb : EquivPair ε ρ ρ' b) : StableUnder ρ' (dualLat b T) := by
  intro g f hf x hx
  have hx' : ρ g⁻¹ x ∈ T := hT g⁻¹ x hx
  have ex : x = ρ g (ρ g⁻¹ x) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  show b x (ρ' g f) ∈ (1 : Submodule O (FractionRing O))
  rw [ex, hb]
  exact Submodule.smul_mem _ _ (hf _ hx')
theorem fibre_stable {VY VT : Type u} [AddCommGroup VY] [Module O VY] [AddCommGroup VT]
    [Module O VT] {ρY : Representation O G VY} {ρT : Representation O G VT} {Y : Submodule O VY}
    {T : Submodule O VT} {φ : Y →ₗ[O] VT ⧸ T} (hY : StableUnder ρY Y)
    (hφ : EquivToQuot ρY ρT Y T φ) : StableUnder (ρY.prod ρT) (fibre Y T φ) := by
  rintro g ⟨y, t⟩ ⟨hy, hyt⟩
  exact (show ∃ h : ρY g y ∈ Y, φ ⟨ρY g y, h⟩ = Submodule.Quotient.mk (ρT g t) from
    ⟨hY g y hy, hφ g ⟨y, hy⟩ (hY g y hy) t hyt⟩)
theorem fibreDual_stable {VY VT VY' VT' : Type u} [AddCommGroup VY] [Module O VY]
    [AddCommGroup VT] [Module O VT] [AddCommGroup VY'] [Module O VY'] [AddCommGroup VT']
    [Module O VT'] {ε : G →* Oˣ} {ρY : Representation O G VY} {ρT : Representation O G VT}
    {ρY' : Representation O G VY'} {ρT' : Representation O G VT'}
    {bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O} {bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O}
    {Y : Submodule O VY} {T : Submodule O VT} {φ : Y →ₗ[O] VT ⧸ T}
    (hY : StableUnder ρY Y) (hT : StableUnder ρT T) (hφ : EquivToQuot ρY ρT Y T φ)
    (hbY : EquivPair ε ρY ρY' bY) (hbT : EquivPair ε ρT ρT' bT) :
    StableUnder (ρT'.prod ρY') (fibreDual bY bT Y T φ) := by
  rintro g ⟨f', y'⟩ ⟨hf', hp'⟩
  refine (show ρT' g f' ∈ dualLat bT T ∧ ∀ (y : Y) (x : VT), φ y = Submodule.Quotient.mk x →
      bY y (ρY' g y') - bT x (ρT' g f') ∈ (1 : Submodule O (FractionRing O)) from
    ⟨dualLat_stable hT hbT g f' hf', ?_⟩)
  intro y x hyx
  have hy0 : ρY g⁻¹ (y : VY) ∈ Y := hY g⁻¹ _ y.2
  have h0 := hp' ⟨_, hy0⟩ (ρT g⁻¹ x) (hφ g⁻¹ y hy0 x hyx)
  have ey : (y : VY) = ρY g (ρY g⁻¹ (y : VY)) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have ex : x = ρT g (ρT g⁻¹ x) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [ey, ex, hbY, hbT, ← smul_sub]
  exact Submodule.smul_mem _ _ h0
end Basic
section Top
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]
  [ContinuousSMul O (FractionRing O)]
theorem toKO_cont : Continuous (toKO O) := continuous_quot_mk
theorem toKO_equiv {G : Type u} [Group G] (ε : G →* Oˣ) (g : G) (m : FractionRing O) :
    toKO O (twist ε (FractionRing O) g m) = twist ε (KO O) g (toKO O m) := by
  rw [twist_apply, twist_apply, map_smul]
theorem sub_contAction {G V : Type u} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module O V]
    [TopologicalSpace V] {ρ : Representation O G V} (h : ContAction ρ) (L : Submodule O V)
    (hL : StableUnder ρ L) : ContAction (ρ.subrepresentation L hL) := by
  have hc : Continuous (fun p : G × L => ρ p.1 (p.2 : V)) :=
    h.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  exact Continuous.subtype_mk hc _
theorem pairKO_cont {V V' : Type u} [AddCommGroup V] [Module O V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [AddCommGroup V'] [Module O V'] [TopologicalSpace V']
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (hb : Continuous fun p : V × V' => b p.1 p.2)
    (T : Submodule O V) : Continuous fun p : (V ⧸ T) × dualLat b T => pairKO b T p.1 p.2 := by
  have hm : IsOpenQuotientMap T.mkQ := by
    first
    | exact Submodule.isOpenQuotientMap_mkQ T
    | exact QuotientAddGroup.isOpenQuotientMap_mk
    | exact QuotientAddGroup.isOpenQuotientMap_mk (N := T.toAddSubgroup)
  have hq : IsOpenQuotientMap (Prod.map T.mkQ (id : dualLat b T → dualLat b T)) :=
    hm.prodMap IsOpenQuotientMap.id
  rw [hq.isQuotientMap.continuous_iff]
  exact toKO_cont.comp (hb.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
end Top
structure LatData (O G VT VT' : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] where
  ε : G →* Oˣ
  ρT : Representation O G VT
  ρT' : Representation O G VT'
  bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O
  T : Submodule O VT
  stT : StableUnder ρT T
  eqT : EquivPair ε ρT ρT' bT
  contT' : ContAction ρT'
  contbT : Continuous fun p : VT × VT' => bT p.1 p.2

  inv : H2 (twist ε (KO O)) →ₗ[O] KO O

  invF : H2 (twist ε (FractionRing O)) →ₗ[O] FractionRing O
namespace LatData
variable {O G VT VT' : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] (D : LatData O G VT VT')
def InvCompat : Prop :=
  ∀ z, D.inv (mapH2 (twist D.ε (FractionRing O)) (twist D.ε (KO O)) (toKO O) toKO_cont
    (toKO_equiv D.ε) z) = toKO O (D.invF z)
abbrev T' : Submodule O VT' := dualLat D.bT D.T
theorem stT' : StableUnder D.ρT' D.T' := dualLat_stable D.stT D.eqT
def ρA : Representation O G (VT ⧸ D.T) := D.ρT.quotient D.T D.stT
def ρTl' : Representation O G D.T' := D.ρT'.subrepresentation D.T' D.stT'
def ρA' : Representation O G (VT' ⧸ D.T') := D.ρT'.quotient D.T' D.stT'
def q : H1 D.ρT →ₗ[O] H1 D.ρA :=
  mapH1 D.ρT D.ρA D.T.mkQ continuous_quot_mk (fun _ _ => rfl)
def j' : H1 D.ρTl' →ₗ[O] H1 D.ρT' :=
  mapH1 D.ρTl' D.ρT' D.T'.subtype continuous_subtype_val (fun _ _ => rfl)
theorem pairKO_equiv (g : G) (x : VT ⧸ D.T) (f : D.T') :
    pairKO D.bT D.T (D.ρA g x) (D.ρTl' g f) = twist D.ε (KO O) g (pairKO D.bT D.T x f) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    show toKO O (D.bT (D.ρT g x) (D.ρT' g f)) = twist D.ε (KO O) g (toKO O (D.bT x f))
    rw [D.eqT, twist_apply, map_smul]
def pr : H1 D.ρA →ₗ[O] H1 D.ρTl' →ₗ[O] KO O :=
  (cupProductH1H1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T)
    D.pairKO_equiv (sub_contAction D.contT' _ D.stT')).compr₂ D.inv
end LatData
structure PushData {O G VT VT' : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] (D : LatData O G VT VT') where
  VY : Type u
  VY' : Type u
  [gY : AddCommGroup VY] [mY : Module O VY] [tY : TopologicalSpace VY]
  [tgY : IsTopologicalAddGroup VY] [csY : ContinuousSMul O VY]
  [gY' : AddCommGroup VY'] [mY' : Module O VY'] [tY' : TopologicalSpace VY']
  [tgY' : IsTopologicalAddGroup VY'] [csY' : ContinuousSMul O VY']
  ρY : Representation O G VY
  ρY' : Representation O G VY'
  bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O
  Y : Submodule O VY
  stY : StableUnder ρY Y
  eqY : EquivPair D.ε ρY ρY' bY
  contY' : ContAction ρY'
  contbY : Continuous fun p : VY × VY' => bY p.1 p.2
  φ : Y →ₗ[O] VT ⧸ D.T
  eqφ : EquivToQuot ρY D.ρT Y D.T φ
  contφ : Continuous φ

  HfVY : Submodule O (H1 ρY)

  HfVY' : Submodule O (H1 ρY')

  HfVL : Submodule O (H1 (ρY.prod D.ρT))

  HfVLb : Submodule O (H1 (D.ρT'.prod ρY'))
attribute [instance] PushData.gY PushData.mY PushData.tY PushData.tgY PushData.csY
  PushData.gY' PushData.mY' PushData.tY' PushData.tgY' PushData.csY'
namespace PushData
variable {O G VT VT' : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] {D : LatData O G VT VT'} (E : PushData D)
def ρYl : Representation O G E.Y := E.ρY.subrepresentation E.Y E.stY
abbrev L : Submodule O (E.VY × VT) := fibre E.Y D.T E.φ
def ρL : Representation O G E.L :=
  (E.ρY.prod D.ρT).subrepresentation E.L (fibre_stable E.stY E.eqφ)
abbrev Lb : Submodule O (VT' × E.VY') := fibreDual E.bY D.bT E.Y D.T E.φ
def ρLb : Representation O G E.Lb :=
  (D.ρT'.prod E.ρY').subrepresentation E.Lb (fibreDual_stable E.stY D.stT E.eqφ E.eqY D.eqT)
def prL : E.L →ₗ[O] E.Y :=
  LinearMap.codRestrict E.Y (LinearMap.fst O E.VY VT ∘ₗ E.L.subtype) (fun p => p.2.1)
def prLb : E.Lb →ₗ[O] D.T' :=
  LinearMap.codRestrict D.T' (LinearMap.fst O VT' E.VY' ∘ₗ E.Lb.subtype) (fun p => p.2.1)
theorem φ_equiv (g : G) (y : E.Y) : E.φ (E.ρYl g y) = D.ρA g (E.φ y) := by
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective _ (E.φ y)
  have h := E.eqφ g y (E.stY g y y.2) x hx.symm
  show E.φ ⟨E.ρY g y, E.stY g y y.2⟩ = D.ρA g (E.φ y)
  rw [h, ← hx]
  try rfl
def φs : H1 E.ρYl →ₗ[O] H1 D.ρA := mapH1 E.ρYl D.ρA E.φ E.contφ E.φ_equiv
def jY : H1 E.ρYl →ₗ[O] H1 E.ρY :=
  mapH1 E.ρYl E.ρY E.Y.subtype continuous_subtype_val (fun _ _ => rfl)
def toDirect : DirectPush O (H1 D.ρA) (H1 D.ρT) D.q where
  HY := H1 E.ρYl
  HVY := H1 E.ρY
  HL := H1 E.ρL
  HVL := H1 (E.ρY.prod D.ρT)
  jY := E.jY
  jL := mapH1 E.ρL (E.ρY.prod D.ρT) E.L.subtype continuous_subtype_val (fun _ _ => rfl)
  p1 := mapH1 E.ρL E.ρYl E.prL
    (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _) (fun _ _ => rfl)
  p2 := mapH1 (E.ρY.prod D.ρT) D.ρT (LinearMap.snd O E.VY VT) continuous_snd (fun _ _ => rfl)
  φs := E.φs
  comm := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      refine congrArg (Submodule.Quotient.mk) ?_
      exact Subtype.ext (funext fun g => (x.1 g).2.2)
  HfVY := E.HfVY
  HfVL := E.HfVL
def prF : H1 E.ρY →ₗ[O] H1 E.ρY' →ₗ[O] FractionRing O :=
  (cupProductH1H1 E.ρY E.ρY' (twist D.ε (FractionRing O)) E.bY E.contbY E.eqY E.contY').compr₂ D.invF
def toDual (hc : D.InvCompat) : DualPush O (H1 D.ρA) (H1 D.ρTl') D.pr where
  HY := H1 E.ρYl
  HVY := H1 E.ρY
  HVY' := H1 E.ρY'
  HLb := H1 E.ρLb
  HVLb := H1 (D.ρT'.prod E.ρY')
  jY := E.jY
  jLb := mapH1 E.ρLb (D.ρT'.prod E.ρY') E.Lb.subtype continuous_subtype_val (fun _ _ => rfl)
  p1 := mapH1 E.ρLb D.ρTl' E.prLb
    (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _) (fun _ _ => rfl)
  p2 := mapH1 (D.ρT'.prod E.ρY') E.ρY' (LinearMap.snd O VT' E.VY') continuous_snd (fun _ _ => rfl)
  φs := E.φs
  prF := E.prF
  cup := by
    intro y x
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        rw [LatData.pr, PushData.prF, LinearMap.compr₂_apply, LinearMap.compr₂_apply,
          ← hc]
        refine congrArg D.inv (congrArg (Submodule.Quotient.mk) ?_)
        refine Subtype.ext (funext fun p => ?_)
        obtain ⟨g, k⟩ := p
        obtain ⟨x0, hx0⟩ := Submodule.mkQ_surjective _ (E.φ (y.1 g))
        have hm := (E.ρLb g (x.1 k)).2.2 (y.1 g) x0 hx0.symm
        show pairKO D.bT D.T (E.φ (y.1 g)) (D.ρTl' g (E.prLb (x.1 k))) =
          toKO O (E.bY (y.1 g) (E.ρY' g (x.1 k).1.2))
        rw [← hx0]
        show toKO O (D.bT x0 (D.ρT' g (x.1 k).1.1)) = _
        symm
        rw [← sub_eq_zero, ← map_sub]
        exact (Submodule.Quotient.mk_eq_zero _).2 hm
  HfVY := E.HfVY
  HfVY' := E.HfVY'
  HfVLb := E.HfVLb
end PushData
def StatPropLocCont : Prop :=
  ∀ (O G VT VT' : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    (D : LatData O G VT VT') (HfV : Submodule O (H1 D.ρT)) (HfV' : Submodule O (H1 D.ρT'))
    (ℓ e' : ℕ) (ι₁ ι₂ : Type u) (P : ι₁ → PushData D) (Q : ι₂ → PushData D),
    IsLatticeIn D.T → PerfectRight D.bT → Module.Finite O (H1 D.ρTl') → ∀ hc : D.InvCompat,
    HfV.map D.q = annih D.pr (HfV'.comap D.j') →
    (∀ i, (P i).toDirect.Fun HfV ∧ (P i).toDirect.Lift ℓ e') →
    (∀ i, ((Q i).toDual hc).Fun ∧ ((Q i).toDual hc).Orth ∧
      ((Q i).toDual hc).Lift (HfV'.comap D.j') ℓ e') →
    (∀ i, ∀ y ∈ (P i).HfVY.comap (P i).jY, ((ℓ : O) ^ e') • (P i).φs y ∈ HfV.map D.q) ∧
    (∀ i, ∀ y ∈ (Q i).HfVY.comap (Q i).jY, ((ℓ : O) ^ e') • (Q i).φs y ∈ HfV.map D.q) ∧
    Module.length O
      (((⨆ i, ((P i).HfVY.comap (P i).jY).map (P i).φs) ⊔
          (⨆ i, ((Q i).HfVY.comap (Q i).jY).map (Q i).φs) : Submodule O (H1 D.ρA)) ⧸
        (HfV.map D.q).comap ((⨆ i, ((P i).HfVY.comap (P i).jY).map (P i).φs) ⊔
          (⨆ i, ((Q i).HfVY.comap (Q i).jY).map (Q i).φs) : Submodule O (H1 D.ρA)).subtype) ≤
      ((Module.finrank O ↥(HfV'.comap D.j') + Module.finrank O D.T : ℕ) : ℕ∞) *
        ((e' : ℕ∞) * eO O ℓ)
end Formalism.RepresentationBoundsCohomology.LOC


