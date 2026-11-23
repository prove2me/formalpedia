-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_StatDualFibreLattice
-- name    : Formalism_WachLatticeTwists_LatticeDualFibres_StatDualFibreLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:00.655578+00:00
-- url     : https://prove2.me/theorems/ee74ba56-d31a-4abb-adf0-f9db69d44c7a
-- title:
--   Stat Dual Fibre Lattice
-- statement:
--   Definitions and structural lemmas for Stat Dual Fibre Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/StatDualFibreLattice.lean

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO)
noncomputable section
namespace Formalism.RepresentationBoundsCohomology.LOC
section Lat
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
def IsLatticeIn {V : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] (L : Submodule O V) : Prop :=
  L.FG ∧ Submodule.span (FractionRing O) (L : Set V) = ⊤
def StableUnder {G V : Type u} [Group G] [AddCommGroup V] [Module O V] (ρ : Representation O G V)
    (L : Submodule O V) : Prop := ∀ g, ∀ x ∈ L, ρ g x ∈ L
def EquivToQuot {G VY VT : Type u} [Group G] [AddCommGroup VY] [Module O VY] [AddCommGroup VT]
    [Module O VT] (ρY : Representation O G VY) (ρT : Representation O G VT) (Y : Submodule O VY)
    (T : Submodule O VT) (φ : Y →ₗ[O] VT ⧸ T) : Prop :=
  ∀ (g : G) (y : Y) (hy : ρY g y ∈ Y) (x : VT), φ y = Submodule.Quotient.mk x →
    φ ⟨ρY g y, hy⟩ = Submodule.Quotient.mk (ρT g x)
def fibre {VY VT : Type u} [AddCommGroup VY] [Module O VY] [AddCommGroup VT] [Module O VT]
    (Y : Submodule O VY) (T : Submodule O VT) (φ : Y →ₗ[O] VT ⧸ T) : Submodule O (VY × VT) where
  carrier := {p | ∃ h : p.1 ∈ Y, φ ⟨p.1, h⟩ = Submodule.Quotient.mk p.2}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Y.add_mem ha hb, ?_⟩
    have : (⟨(a + b).1, Y.add_mem ha hb⟩ : Y) = ⟨a.1, ha⟩ + ⟨b.1, hb⟩ := rfl
    rw [this, map_add, ha', hb']; rfl
  zero_mem' := ⟨Y.zero_mem, by
    have : (⟨(0 : VY × VT).1, Y.zero_mem⟩ : Y) = 0 := rfl
    rw [this, map_zero]; rfl⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨Y.smul_mem c ha, ?_⟩
    have : (⟨(c • a).1, Y.smul_mem c ha⟩ : Y) = c • ⟨a.1, ha⟩ := rfl
    rw [this, map_smul, ha']; rfl
def dualLat {V V' : Type u} [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module O V']
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V) : Submodule O V' where
  carrier := {f | ∀ x ∈ T, b x f ∈ (1 : Submodule O (FractionRing O))}
  add_mem' := by
    intro f g hf hg x hx
    rw [map_add]; exact Submodule.add_mem _ (hf x hx) (hg x hx)
  zero_mem' := by
    intro x _
    rw [map_zero]; exact Submodule.zero_mem _
  smul_mem' := by
    intro c f hf x hx
    rw [map_smul]; exact Submodule.smul_mem _ c (hf x hx)
def fibreDual {VY VT VY' VT' : Type u} [AddCommGroup VY] [Module O VY] [AddCommGroup VT]
    [Module O VT] [AddCommGroup VY'] [Module O VY'] [AddCommGroup VT'] [Module O VT']
    (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O) (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O)
    (Y : Submodule O VY) (T : Submodule O VT) (φ : Y →ₗ[O] VT ⧸ T) :
    Submodule O (VT' × VY') where
  carrier := {p | p.1 ∈ dualLat bT T ∧ ∀ (y : Y) (x : VT), φ y = Submodule.Quotient.mk x →
    bY y p.2 - bT x p.1 ∈ (1 : Submodule O (FractionRing O))}
  add_mem' := by
    rintro p r ⟨hp, hp'⟩ ⟨hr, hr'⟩
    refine ⟨Submodule.add_mem _ hp hr, fun y x h => ?_⟩
    have : bY y (p + r).2 - bT x (p + r).1 = (bY y p.2 - bT x p.1) + (bY y r.2 - bT x r.1) := by
      simp only [Prod.snd_add, Prod.fst_add, map_add]; ring
    rw [this]; exact Submodule.add_mem _ (hp' y x h) (hr' y x h)
  zero_mem' := ⟨Submodule.zero_mem _, fun y x _ => by
    simp only [Prod.snd_zero, Prod.fst_zero, map_zero, sub_zero]; exact Submodule.zero_mem _⟩
  smul_mem' := by
    rintro c p ⟨hp, hp'⟩
    refine ⟨Submodule.smul_mem _ c hp, fun y x h => ?_⟩
    have : bY y (c • p).2 - bT x (c • p).1 = c • (bY y p.2 - bT x p.1) := by
      simp only [Prod.smul_snd, Prod.smul_fst, map_smul, smul_sub]
    rw [this]; exact Submodule.smul_mem _ c (hp' y x h)
def PerfectRight {V V' : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V']
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) : Prop :=
  ∀ ψ : V →ₗ[FractionRing O] FractionRing O, ∃! f : V', ∀ x, b x f = ψ x
def EquivPair {G V V' : Type u} [Group G] [AddCommGroup V] [Module O V] [AddCommGroup V']
    [Module O V'] (ε : G →* Oˣ) (ρ : Representation O G V) (ρ' : Representation O G V')
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) : Prop :=
  ∀ g x f, b (ρ g x) (ρ' g f) = (ε g : O) • b x f
end Lat
def StatImageKilled : Prop :=
  ∀ (O VY VT : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup VY] [Module O VY] [AddCommGroup VT] [Module O VT] [Module (FractionRing O) VT]
    [IsScalarTower O (FractionRing O) VT] (Y : Submodule O VY) (T : Submodule O VT)
    (φ : Y →ₗ[O] VT ⧸ T) (ϖ : O), Irreducible ϖ → Y.FG → IsLatticeIn T →
    ∃ a : ℕ, ∀ y, (ϖ ^ a) • φ y = 0
def StatFibreLattice : Prop :=
  ∀ (O G VY VT : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Group G]
    [AddCommGroup VY] [Module O VY] [Module (FractionRing O) VY]
    [IsScalarTower O (FractionRing O) VY]
    [AddCommGroup VT] [Module O VT] [Module (FractionRing O) VT]
    [IsScalarTower O (FractionRing O) VT]
    (ρY : Representation O G VY) (ρT : Representation O G VT) (Y : Submodule O VY)
    (T : Submodule O VT) (φ : Y →ₗ[O] VT ⧸ T),
    IsLatticeIn Y → IsLatticeIn T → StableUnder ρY Y → StableUnder ρT T → EquivToQuot ρY ρT Y T φ →
    IsLatticeIn (fibre Y T φ) ∧
    (∀ g, ∀ p ∈ fibre Y T φ, (ρY g p.1, ρT g p.2) ∈ fibre Y T φ) ∧
    (∀ x ∈ T, ((0 : VY), x) ∈ fibre Y T φ) ∧
    (∀ y ∈ Y, ∃ x, (y, x) ∈ fibre Y T φ)
def StatDualLattice : Prop :=
  ∀ (O G V V' : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Group G]
    [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
    [AddCommGroup V'] [Module O V'] [Module (FractionRing O) V']
    [IsScalarTower O (FractionRing O) V']
    (ε : G →* Oˣ) (ρ : Representation O G V) (ρ' : Representation O G V')
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V),
    IsLatticeIn T → StableUnder ρ T → PerfectRight b → EquivPair ε ρ ρ' b →
    IsLatticeIn (dualLat b T) ∧ Module.finrank O (dualLat b T) = Module.finrank O T ∧
    StableUnder ρ' (dualLat b T) ∧ dualLat b.flip (dualLat b T) = T
def StatDualFibreLattice : Prop :=
  ∀ (O G VY VT VY' VT' : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Group G]
    [AddCommGroup VY] [Module O VY] [Module (FractionRing O) VY]
    [IsScalarTower O (FractionRing O) VY]
    [AddCommGroup VT] [Module O VT] [Module (FractionRing O) VT]
    [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VY'] [Module O VY'] [Module (FractionRing O) VY']
    [IsScalarTower O (FractionRing O) VY']
    [AddCommGroup VT'] [Module O VT'] [Module (FractionRing O) VT']
    [IsScalarTower O (FractionRing O) VT']
    (ε : G →* Oˣ) (ρY : Representation O G VY) (ρT : Representation O G VT)
    (ρY' : Representation O G VY') (ρT' : Representation O G VT')
    (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O) (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O)
    (Y : Submodule O VY) (T : Submodule O VT) (φ : Y →ₗ[O] VT ⧸ T),
    IsLatticeIn Y → IsLatticeIn T → StableUnder ρY Y → StableUnder ρT T → EquivToQuot ρY ρT Y T φ →
    PerfectRight bY → PerfectRight bT → EquivPair ε ρY ρY' bY → EquivPair ε ρT ρT' bT →
    IsLatticeIn (fibreDual bY bT Y T φ) ∧
    (∀ g, ∀ p ∈ fibreDual bY bT Y T φ, (ρT' g p.1, ρY' g p.2) ∈ fibreDual bY bT Y T φ) ∧
    (∀ f ∈ dualLat bT T, ∃ g, (f, g) ∈ fibreDual bY bT Y T φ)
def StatQuotEmbeds : Prop :=
  ∀ (O V : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
    (T : Submodule O V), IsLatticeIn T →
    Module.finrank O T = Module.finrank (FractionRing O) V ∧
    ∃ e : (V ⧸ T) →ₗ[O] (Fin (Module.finrank O T) → KO O), Function.Injective e
end Formalism.RepresentationBoundsCohomology.LOC


