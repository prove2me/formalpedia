-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PrimitiveExponentPullback
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_PrimitiveExponentPullback
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:13.851104+00:00
-- url     : https://prove2.me/theorems/3c3ad0f3-f5a8-424f-84f3-ef7f13dea77e
-- title:
--   Primitive Exponent Pullback
-- statement:
--   Definitions and structural lemmas for Primitive Exponent Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PrimitiveExponentPullback.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HostConjugateIdeal
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Level_Dvd_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback
open GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal
section Mumford
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]
abbrev LamK : Type := ULift.{0} (Finset (Fin 2))
def lamPt {T : Over S} (x z : T ⟶ G) : LamK → (T.left ⟶ G.left) :=
  fun I => (psum G ![x, z] I.down).left
def lamExp : LamK → ℤ := fun I => (-1) ^ (2 - I.down.card)
def lamAt (L : LB G.left) {T : Over S} (x z : T ⟶ G) : LB T.left :=
  LB.LinComb L (lamPt G x z) lamExp
def adjPt (a b : G ⟶ G) : LamK ⊕ LamK → ((G ⊗ G).left ⟶ G.left) :=
  Sum.elim (lamPt G (fst G G) (snd G G ≫ b)) (lamPt G (fst G G ≫ a) (snd G G))
def adjExp : LamK ⊕ LamK → ℤ := Sum.elim lamExp (fun I => -lamExp I)
def IsAdjointPair (L : LB G.left) (a b : G ⟶ G) : Prop :=
  ∃ t : LB.Gen (LB.LinComb L (adjPt G a b) adjExp), t.IsGen ∧
    LB.Gen.Corr L _ _ _ _
      (LB.pullGen L (adjPt G a b) adjExp t (lift (pzero G G) (𝟙 G)).left) (LB.oneGen L) ∧
    LB.Gen.Corr L _ _ _ _
      (LB.pullGen L (adjPt G a b) adjExp t (lift (𝟙 G) (pzero G G)).left) (LB.oneGen L)
def primPt (w : G ⟶ G) : PUnit.{1} ⊕ LamK → (G.left ⟶ G.left) :=
  Sum.elim (fun _ => 𝟙 G.left) (lamPt G (𝟙 G) w)
def primExp : PUnit.{1} ⊕ LamK → ℤ := Sum.elim (fun _ => 1) (fun I => -lamExp I)
def IsPrimitiveFor (L : RigLB G) (w : G ⟶ G) : Prop :=
  ∃ t : LB.Gen (LB.LinComb L.L (primPt G w) primExp), t.IsGen ∧
    LB.Gen.Corr L.L _ _ (fun _ : PUnit.{1} => eSec G) (fun _ => 1)
      (LB.pullGen L.L (primPt G w) primExp t (eSec G)) L.rig
end Mumford
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
structure Triple (H : Host E) (S : Scheme.{0}) where

  G : Over S
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semiAbelian : IsSemiAbelian G

  iota : OAct (𝓞 E) G

  L : RigLB G

  cube : CubicalStr G L
  symm : L.IsSymmetric
  adjoint : ∀ a : 𝓞 E, IsAdjointPair G L.L (iota.act a) (iota.act (conjO E a))
  primitive : IsPrimitiveFor G L (iota.act H.w₀)
attribute [instance] Triple.grp Triple.comm
namespace Triple
variable {H : Host E} {S S' : Scheme.{0}}
def P (t : Triple H S) : LB (t.G ⊗ t.G).left := abelian₂ t.G t.L.L
structure Pull (t' : Triple H S') (t : Triple H S) (f : S' ⟶ S) where

  φ : t'.G.left ⟶ t.G.left
  isGrpPullback : IsGrpPullback t'.G t.G f φ
  act_comm : ∀ a : 𝓞 E, (t'.iota.act a).left ≫ φ = φ ≫ (t.iota.act a).left
  bundle : ∃ m : CubeMap t'.G t.G, m.F = φ ∧ m.e = f ∧ m.IsPullCubical t'.cube t.cube
structure PullIso (t' : Triple H S') (t : Triple H S) (f : S' ⟶ S) where

  m : CubeMap t'.G t.G
  base : m.e = f
  isGrpPullback : IsGrpPullback t'.G t.G f m.F
  act_comm : ∀ a : 𝓞 E, (t'.iota.act a).left ≫ m.F = m.F ≫ (t.iota.act a).left

  w : LB.Iso t'.L.L (t.L.L.pull m.F)
  isGen : w.IsGen
  rig : LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1))
    t'.L.rig (m.rigPull t.L.L t.L.rig)
  cube : LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cube.t
    (m.thetaPull t.L.L t.cube.t)
def PullIso.toPull {t' : Triple H S'} {t : Triple H S} {f : S' ⟶ S} (p : PullIso t' t f) :
    Pull t' t f :=
  ⟨p.m.F, p.isGrpPullback, p.act_comm, p.m, rfl, p.base, p.w, p.isGen, p.rig, p.cube⟩
theorem res_eq_one {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) {x : Γ(X, U)ˣ} (hx : x = 1) :
    res h x = 1 := by rw [hx, map_one]
theorem pullU_eq_one {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) {x : Γ(X, U)ˣ} (hx : x = 1) :
    pullU f U x = 1 := by rw [hx, map_one]
theorem mul_eq_one_of_both {M : Type} [Monoid M] {x y : M} (hx : x = 1) (hy : y = 1) :
    x * y = 1 := by rw [hx, hy, _root_.one_mul]
theorem zpow_eq_one_of {M : Type} [Group M] {x : M} (hx : x = 1) (n : ℤ) : x ^ n = 1 := by
  rw [hx, one_zpow]
theorem isGen_one {X : Scheme.{0}} (L : LB X) (hg : ∀ i j, L.g i j = 1) :
    (⟨fun _ => 1⟩ : LB.Gen L).IsGen := fun i j => by
  rw [hg, res_eq_one _ rfl, res_eq_one _ rfl, _root_.one_mul]
theorem linComb_g_one {X Y : Scheme.{0}} (L : LB X) (hg : ∀ i j, L.g i j = 1) {K : Type}
    [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i j) : (LB.LinComb L φ ε).g i j = 1 :=
  Finset.prod_eq_one fun _ _ =>
    zpow_eq_one_of (res_eq_one _ (pullU_eq_one _ _ (hg _ _))) _
theorem linCombIso_one {X Y : Scheme.{0}} (L M : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p) :
    (LB.linCombIso (L := L) (M := M) ⟨fun _ => 1⟩ φ ε).s p = 1 := by
  unfold LB.linCombIso
  refine Finset.prod_eq_one fun k _ => ?_
  refine zpow_eq_one_of ?_ _
  refine res_eq_one _ ?_
  exact map_one (pullU (φ k) (M.U (p.1 k) ⊓ L.U (p.2 k)))
theorem corr_one {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ j, t.s j = 1) (h' : ∀ j, t'.s j = 1) : LB.Gen.Corr L φ ε φ' ε' t t' :=
  fun j j' _ _ _ => (res_eq_one _ (h j)).trans (res_eq_one _ (h' j')).symm
def trivLB (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
def trivRig (G : Over S) [GrpObj G] [IsCommMonObj G] : RigLB G where
  L := trivLB G.left
  rig := ⟨fun _ => 1⟩
  isLB := ⟨by simp [trivLB], fun _ => res_eq_one _ rfl, fun _ _ _ =>
    (mul_eq_one_of_both (res_eq_one _ rfl) (res_eq_one _ rfl)).trans (res_eq_one _ rfl).symm⟩
  rigGen := isGen_one _ (linComb_g_one _ (fun _ _ => rfl) _ _)
def ofTrivial (H : Host E) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : IsSemiAbelian G)
    (act : OAct (𝓞 E) G) : Triple H S where
  G := G
  semiAbelian := h
  iota := act
  L := trivRig G
  cube :=
    { t := ⟨fun _ => 1⟩
      isGen := isGen_one _ (linComb_g_one _ (fun _ _ => rfl) _ _)
      face := fun _ => corr_one _ (fun _ => res_eq_one _ (pullU_eq_one _ _ rfl)) fun _ => rfl
      cubeSymmetric_swap_first := corr_one _ (fun _ => rfl) fun _ => res_eq_one _ (pullU_eq_one _ _ rfl)
      cubeSymmetric_swap_last := corr_one _ (fun _ => rfl) fun _ => res_eq_one _ (pullU_eq_one _ _ rfl)
      cocycle := corr_one _
        (fun _ => mul_eq_one_of_both (res_eq_one _ (res_eq_one _ (pullU_eq_one _ _ rfl)))
          (res_eq_one _ (res_eq_one _ (pullU_eq_one _ _ rfl))))
        (fun _ => mul_eq_one_of_both (res_eq_one _ (res_eq_one _ (pullU_eq_one _ _ rfl)))
          (res_eq_one _ (res_eq_one _ (pullU_eq_one _ _ rfl)))) }
  symm := ⟨by
      rw [Category.id_comp, eSec, ← Over.comp_left]; simp,
    ⟨fun _ => 1⟩, isGen_one _ (fun _ _ => mul_eq_one_of_both
      (res_eq_one _ (linComb_g_one _ (fun _ _ => rfl) _ _ _ _))
      (inv_eq_one.mpr (res_eq_one _ rfl))),
    fun _ => (res_eq_one _ (res_eq_one _ (pullU_eq_one _ _ rfl))).trans
      (Eq.symm <| mul_eq_one_of_both (linCombIso_one _ _ _ _ _) (res_eq_one _ rfl))⟩
  adjoint := fun _ => ⟨⟨fun _ => 1⟩, isGen_one _ (linComb_g_one _ (fun _ _ => rfl) _ _),
    corr_one _ (fun _ => res_eq_one _ (pullU_eq_one _ _ rfl)) fun _ => rfl,
    corr_one _ (fun _ => res_eq_one _ (pullU_eq_one _ _ rfl)) fun _ => rfl⟩
  primitive := ⟨⟨fun _ => 1⟩, isGen_one _ (linComb_g_one _ (fun _ _ => rfl) _ _),
    corr_one _ (fun _ => res_eq_one _ (pullU_eq_one _ _ rfl)) fun _ => rfl⟩
end Triple
end GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback


