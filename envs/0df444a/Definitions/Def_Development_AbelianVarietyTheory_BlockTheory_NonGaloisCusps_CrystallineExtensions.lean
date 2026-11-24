-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineExtensions
-- name    : Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineExtensions
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T19:17:21.835858+00:00
-- url     : https://prove2.me/theorems/1bb7ebbd-0b41-4c91-888f-32ac43929a34
-- title:
--   Crystalline Extensions
-- statement:
--   Definitions and structural lemmas for Crystalline Extensions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/CrystallineExtensions.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
section Ext
variable {G : Type} [Group G] {LL : Type} [Field LL] {V W : Type} [AddCommGroup V] [Module LL V]
  [AddCommGroup W] [Module LL W]
def IsExt (ρ : Representation LL G V) (ρ' : Representation LL G W) (i : V →ₗ[LL] W) (p : W →ₗ[LL] LL) : Prop :=
  Function.Injective i ∧ Function.Exact i p ∧ Function.Surjective p ∧
    (∀ g x, i (ρ g x) = ρ' g (i x)) ∧ ∀ g y, p (ρ' g y) = p y
def IsCocycleOf (ρ' : Representation LL G W) (i : V →ₗ[LL] W) (p : W →ₗ[LL] LL) (c : G → V) : Prop :=
  ∃ e : W, p e = 1 ∧ ∀ g, ρ' g e = e + i (c g)
variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
def extRep (ρ : Representation LL G V) (c : ↥(continuousCocycles ρ)) : Representation LL G (V × LL) where
  toFun g := ((ρ g).coprod (LinearMap.toSpanSingleton LL V ((c : G → V) g))).prod (LinearMap.snd LL V LL)
  map_one' := by
    have h : (c : G → V) 1 = 0 := by simpa using c.2.2 1 1
    refine LinearMap.ext fun x => ?_
    simp [h]
  map_mul' g k := by
    refine LinearMap.ext fun x => ?_
    simp [c.2.2 g k]
    abel
end Ext
section Per
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
def H1fSubmodule {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL G V) :
    Submodule LL (H1V ρ) :=
  ((finiteCocycles PD ρ).comap (continuousCocycles ρ).subtype).map (Submodule.mkQ _)
def ExtCrysAt [TopologicalSpace LL] {n : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] [IsModuleTopology LL V]
    (ρ : Representation LL G V), (∀ x, Continuous fun g => ρ g x) → IsCrys PD ρ →
  ∀ (W : Type) [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    (ρ' : Representation LL G W) (i : V →ₗ[LL] W) (p : W →ₗ[LL] LL), IsExt ρ ρ' i p →
  ∀ c : ↥(continuousCocycles ρ), IsCocycleOf ρ' i p (c : G → V) →
    (IsCrys PD ρ' ↔ (Submodule.Quotient.mk c : H1V ρ) ∈ H1fSubmodule PD ρ) ∧
    (IsCrys PD ρ' → ∀ (j : ZMod n) (U : Multiset ℤ),
      AdmLoc.HasJumps PD ρ (emb j) U → AdmLoc.HasJumps PD ρ' (emb j) (U + {0}))
end Per
def ExtCrys {l : ℕ} [Fact l.Prime] (P : LocPrime l) : Prop :=
  ∀ (K LL : Loc.FinExt l) (n : ℕ) (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (lam : ↥(Loc.OL LL)),
    AdmLoc.Standing P K LL emb lam → ExtCrysAt (P.PD K) emb
end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions


