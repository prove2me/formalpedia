-- Prove2me | Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
-- name    : Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:21:22.473926+00:00
-- url     : https://prove2.me/theorems/5cd085fb-53f5-4233-9870-c48fc3c71aae
-- title:
--   Loc Coh
-- statement:
--   Definitions and structural lemmas for Loc Coh, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/LocCoh.lean

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_ReciprocityTheory_BasicDefinitions_AdRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.N
open Formalism.WeaklyAdmissibleFiltrations Module
section Core
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
def IsDR {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) : Prop :=
  finrank LL ↥(DdR PD ρ) = finrank Qp K * finrank LL V
def cycLL (LL : Type) [Field LL] [Algebra Qp LL] : G →* LLˣ :=
  (Units.map (algebraMap Qp LL : Qp →* LL)).comp PD.χ
def GoodO [TopologicalSpace Qp] (LL O : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] : Prop :=
  (∃ hO : IsDomain O, @IsDiscreteValuationRing O _ hO ∧ IsFractionRing O LL) ∧
    FiniteDimensional Qp LL ∧ IsModuleTopology Qp LL ∧ IsTopologicalRing LL ∧
    IsOpen (Set.range (algebraMap O LL))
end Core
structure GRep (G : Type) [Group G] [TopologicalSpace G] (Qp LL O : Type) [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] where
  V : Type
  [acg : AddCommGroup V]
  [modLL : Module LL V]
  [modQp : Module Qp V]
  [towQp : IsScalarTower Qp LL V]
  [modO : Module O V]
  [towO : IsScalarTower O LL V]
  [fd : FiniteDimensional LL V]
  [top : TopologicalSpace V]
  [mtop : IsModuleTopology LL V]
  [cadd : ContinuousAdd V]
  [csmul : ContinuousConstSMul LL V]
  ρ : Representation LL G V
  cont : ∀ x, Continuous fun g => ρ g x
attribute [instance] GRep.acg GRep.modLL GRep.modQp GRep.towQp GRep.modO GRep.towO GRep.fd GRep.top
  GRep.mtop GRep.cadd GRep.csmul
section Rep
variable {G : Type} [Group G] {LL : Type} [Field LL]
def IsTwistRep (χ : G →* LLˣ) {V V' : Type} [AddCommGroup V] [Module LL V] [AddCommGroup V']
    [Module LL V'] (ρ : Representation LL G V) (ρ' : Representation LL G V') : Prop :=
  ∃ e : V ≃ₗ[LL] V', ∀ g x, ρ' g (e x) = ((χ g : LLˣ) : LL) • e (ρ g x)
end Rep
section Dual
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V']
def IsDual1 (ρ : Representation LL G V) (ρ' : Representation LL G V') (P : V →ₗ[LL] V' →ₗ[LL] LL) :
    Prop :=
  (∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y) ∧
    (∀ x, (∀ y, P x y = 0) → x = 0) ∧ (∀ y, (∀ x, P x y = 0) → y = 0) ∧
    finrank LL V = finrank LL V'
def IsDualLat1 {ρ : Representation LL G V} {ρ' : Representation LL G V'} (L : Lattice (O := O) ρ)
    (L' : Lattice (O := O) ρ') (P : V →ₗ[LL] V' →ₗ[LL] LL) : Prop :=
  IsDual1 PD ρ ρ' P ∧ ∀ y, y ∈ L'.T ↔ ∀ x ∈ L.T, ∃ a : O, P x y = algebraMap O LL a
end Dual
section Coch
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V}
def repD (L : Lattice (O := O) ρ) : Representation O G (V ⧸ L.T) where
  toFun g := L.T.mapQ L.T ((ρ g).restrictScalars O) (fun x hx => L.stable g x hx)
  map_one' := by
    apply Submodule.linearMap_qext
    ext x
    simp
  map_mul' g h := by
    apply Submodule.linearMap_qext
    ext x
    simp [Module.End.mul_apply]
    rfl
def liftD (L : Lattice (O := O) ρ) (c : V ⧸ L.T) : V :=
  (Submodule.Quotient.mk_surjective L.T c).choose
end Coch
section Cup
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
def cupL (ρ' : Representation LL G V') (P : V →ₗ[LL] V' →ₗ[LL] LL) (a : G → V) (b : G → V') :
    G × G → LL :=
  fun x => P (a x.1) (ρ' x.1 (b x.2))
def cupLD {ρ' : Representation LL G V'} (L' : Lattice (O := O) ρ') (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (d : G → V) (c : G → V' ⧸ L'.T) : G × G → LL :=
  fun x => P (d x.1) (ρ' x.1 (liftD L' (c x.2)))
def CobL [TopologicalSpace LL] (z : G × G → LL) : Prop :=
  ∃ f : G → LL, Continuous f ∧ ReciprocityTheory.Def.d1 (charRep (cycLL PD LL)) f = z
def CobO (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (z : G × G → LL) : Prop :=
  (fun x => (Submodule.Quotient.mk (z x) : LL ⧸ L1.T)) ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤
end Cup
section Main
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
def bkACore : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR PD A.ρ → IsDual1 PD A.ρ A'.ρ P →
    (∀ a ∈ continuousCocycles A.ρ, (a ∈ finiteCocycles PD A.ρ ↔ ∀ b ∈ finiteCocycles PD A'.ρ, CobL PD (cupL A'.ρ P a b))) ∧
    (∀ b ∈ continuousCocycles A'.ρ, (b ∈ finiteCocycles PD A'.ρ ↔ ∀ a ∈ finiteCocycles PD A.ρ, CobL PD (cupL A'.ρ P a b)))
def bkBCore : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ L1 : Lattice (O := O) (charRep (cycLL PD LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) →
  ∀ (A A' : GRep G Qp LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ)
    (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR PD A.ρ → IsDualLat1 PD LA LA' P →
    (∀ c ∈ divisibleCocycles LA', (c ∈ HfD PD LA' ↔ ∀ d ∈ latticeFiniteCocycles PD LA, CobO PD L1 (cupLD LA' P d c))) ∧
    (∀ d ∈ latticeCocycles LA, (d ∈ latticeFiniteCocycles PD LA ↔
      ∀ c ∈ divisibleCocycles LA', c ∈ HfD PD LA' → CobO PD L1 (cupLD LA' P d c)))
def LocalTateTopDegree : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ L1 : Lattice (O := O) (charRep (cycLL PD LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) →
    Nonempty (ReciprocityTheory.Def.H2 (repD L1) ⊤ ≃ₗ[O] (LL ⧸ L1.T))
def cycIntCore : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∃ L1 : Lattice (O := O) (charRep (cycLL PD LL)), L1.T = LinearMap.range (Algebra.linearMap O LL)
def TateFiniteness (_PD : PeriodData G Qp K₀ K B BdR) : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (A : GRep G Qp LL O) (LA : Lattice (O := O) A.ρ), Module.Finite O (LatticeCohomology LA)
def drDualCore : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR PD A.ρ →
    IsDual1 PD A.ρ A'.ρ P → IsDR PD A'.ρ
end Main
end Formalism.MainNotions.N


