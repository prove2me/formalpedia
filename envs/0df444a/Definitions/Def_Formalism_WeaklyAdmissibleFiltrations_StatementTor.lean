-- Prove2me | Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
-- name    : Formalism_WeaklyAdmissibleFiltrations_StatementTor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:45:25.549996+00:00
-- url     : https://prove2.me/theorems/d0e779cc-defb-43b1-890e-83529e9fe89d
-- title:
--   Statement Tor
-- statement:
--   Definitions and structural lemmas for Statement Tor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/StatementTor.lean

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.WeaklyAdmissibleFiltrations
open Module TensorProduct
section Tor
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
    {ρ : Representation LL G V}
def actT (L : Lattice (O := O) ρ) (g : G) : ↥L.T →ₗ[O] ↥L.T :=
  ((ρ g).restrictScalars O).restrict (L.stable g)
def StableSub (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) : Prop :=
  ∀ g, ∀ x ∈ I, actT L g x ∈ I
def actQ (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (g : G) :
    (↥L.T ⧸ I) →ₗ[O] (↥L.T ⧸ I) :=
  I.mapQ I (actT L g) (fun x hx => hI g x hx)
def quotientCocycles [TopologicalSpace G] (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) :
    Submodule O (G → ↥L.T ⧸ I) where
  carrier := {c | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + actQ L I hI g (c h)}
  zero_mem' := ⟨IsLocallyConstant.const 0, fun g h => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨ha.add hb, fun g h => ?_⟩
    simp only [Pi.add_apply, ha', hb', map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨ha.comp (c • ·), fun g h => ?_⟩
    simp only [Pi.smul_apply, ha', map_smul, smul_add]
def BQ (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) :
    Submodule O (G → ↥L.T ⧸ I) :=
  LinearMap.range (LinearMap.pi fun g => actQ L I hI g - LinearMap.id)
abbrev QuotientCohomology [TopologicalSpace G] (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T)
    (hI : StableSub L I) : Type :=
  ↥(quotientCocycles L I hI) ⧸ (BQ L I hI).comap (quotientCocycles L I hI).subtype
variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
def evT (L : Lattice (O := O) ρ) (g : G) : ↥(latticeCocycles L) →ₗ[O] ↥L.T where
  toFun c := ⟨(c : G → V) g, c.2.2 g (Set.mem_univ g)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def redT (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) : ↥(latticeCocycles L) →ₗ[O] (G → ↥L.T ⧸ I) :=
  LinearMap.pi fun g => I.mkQ ∘ₗ evT L g
def HfQ (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) :
    Submodule O (G → ↥L.T ⧸ I) :=
  ((latticeFiniteCocycles PD L).comap (latticeCocycles L).subtype).map (redT L I) ⊔ BQ L I hI
def quotientFiniteCohomology (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) :
    Submodule O (QuotientCohomology L I hI) :=
  ((HfQ PD L I hI).comap (quotientCocycles L I hI).subtype).map (Submodule.mkQ _)
end Tor
section TorMore
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
    {ρ : Representation LL G V} [TopologicalSpace G]
def Z1urQ (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (J : Subgroup G) :
    Submodule O (G → ↥L.T ⧸ I) where
  carrier := {c | c ∈ quotientCocycles L I hI ∧ ∃ x, ∀ g ∈ J, c g = actQ L I hI g x - x}
  zero_mem' := ⟨(quotientCocycles L I hI).zero_mem, 0, fun g _ => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, x, hx⟩ ⟨hb, y, hy⟩
    refine ⟨(quotientCocycles L I hI).add_mem ha hb, x + y, fun g hg => ?_⟩
    simp only [Pi.add_apply, hx g hg, hy g hg, map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, x, hx⟩
    refine ⟨(quotientCocycles L I hI).smul_mem c ha, c • x, fun g hg => ?_⟩
    simp only [Pi.smul_apply, hx g hg, map_smul, smul_sub]
def actD (L : Lattice (O := O) ρ) (g : G) : (V ⧸ L.T) →ₗ[O] (V ⧸ L.T) :=
  L.T.mapQ L.T ((ρ g).restrictScalars O) (fun x hx => L.stable g x hx)
def divisibleCocycles (L : Lattice (O := O) ρ) : Submodule O (G → V ⧸ L.T) where
  carrier := {c | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + actD L g (c h)}
  zero_mem' := ⟨IsLocallyConstant.const 0, fun g h => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨ha.add hb, fun g h => ?_⟩
    simp only [Pi.add_apply, ha', hb', map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨ha.comp (c • ·), fun g h => ?_⟩
    simp only [Pi.smul_apply, ha', map_smul, smul_add]
def BD (L : Lattice (O := O) ρ) : Submodule O (G → V ⧸ L.T) :=
  LinearMap.range (LinearMap.pi fun g => actD L g - LinearMap.id)
abbrev DivisibleCohomology (L : Lattice (O := O) ρ) : Type := ↥(divisibleCocycles L) ⧸ (BD L).comap (divisibleCocycles L).subtype
variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
def HfD (L : Lattice (O := O) ρ) : Submodule O (G → V ⧸ L.T) :=
  ((finiteCocycles PD ρ).restrictScalars O).map (LinearMap.compLeft L.T.mkQ G) ⊔ BD L
def divisibleFiniteCohomology (L : Lattice (O := O) ρ) : Submodule O (DivisibleCohomology L) :=
  ((HfD PD L).comap (divisibleCocycles L).subtype).map (Submodule.mkQ _)
def divisibleFiniteCohomologyLength (L : Lattice (O := O) ρ) : ℕ∞ := Module.length O ↥(divisibleFiniteCohomology PD L)
end TorMore
end Formalism.WeaklyAdmissibleFiltrations


