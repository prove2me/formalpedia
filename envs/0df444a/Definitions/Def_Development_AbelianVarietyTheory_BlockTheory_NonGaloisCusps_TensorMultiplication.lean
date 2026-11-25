-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
-- name    : Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:07:13.566722+00:00
-- url     : https://prove2.me/theorems/c9cdf476-0225-4bf7-bdd6-6e3738c013b5
-- title:
--   Tensor Multiplication
-- statement:
--   Definitions and structural lemmas for Tensor Multiplication, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/TensorMultiplication.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorMultiplication
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
section Generic
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
section Maps
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
theorem actVB_mulVB (ρ : Representation LL G V) (g : G) (c : K₀) (x : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (K₀ := K₀) (LL := LL) c x) = mulVB (K₀ := K₀) (LL := LL) c (actVB PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, mulVB]
  | add a b ha hb => simp only [map_add, ha, hb]
omit [IsScalarTower Qp K₀ B] in

theorem comm_smul [SMulCommClass Qp K₀ B] (c : K₀) (x : B ⊗[Qp] V) :
    TensorProduct.comm Qp B V (c • x) =
      mulVB (K₀ := K₀) (LL := LL) c (TensorProduct.comm Qp B V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v => simp [mulVB, TensorProduct.smul_tmul', Algebra.smul_def]
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
def DcrisK (ρ : Representation LL G V) : Submodule K₀ (B ⊗[Qp] V) where
  carrier := {x | TensorProduct.comm Qp B V x ∈ Dcris PD ρ}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    exact (Dcris PD ρ).add_mem ha hb
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    rw [comm_smul (LL := LL), actVB_mulVB, hx g]
def compMap (ρ : Representation LL G V) : B ⊗[K₀] ↥(DcrisK PD ρ) →ₗ[B] B ⊗[Qp] V :=
  LinearMap.liftBaseChange B (DcrisK PD ρ).subtype
variable (B) in

def mapVB (f : V →ₗ[LL] V') : V ⊗[Qp] B →ₗ[LL] V' ⊗[Qp] B :=
  AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)
def Equivariant (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V') : Prop :=
  ∀ g x, f (ρ g x) = ρ' g (f x)
variable (Qp B LL V V') in

def mulTens : (V ⊗[Qp] B) ⊗[LL] (V' ⊗[Qp] B) →ₗ[LL] (V ⊗[LL] V') ⊗[Qp] B :=
  (AlgebraTensorModule.map (LinearMap.id : V ⊗[LL] V' →ₗ[LL] V ⊗[LL] V') (LinearMap.mul' Qp B)).comp
    (AlgebraTensorModule.tensorTensorTensorComm Qp Qp LL LL V B V' B).toLinearMap
def mulDcris (ρ : Representation LL G V) (ρ' : Representation LL G V') :
    ↥(Dcris PD ρ) ⊗[LL] ↥(Dcris PD ρ') →ₗ[LL] (V ⊗[LL] V') ⊗[Qp] B :=
  (mulTens Qp B LL V V').comp (TensorProduct.map (Dcris PD ρ).subtype (Dcris PD ρ').subtype)
def balK (ρ : Representation LL G V) (ρ' : Representation LL G V') :
    Submodule LL (↥(Dcris PD ρ) ⊗[LL] ↥(Dcris PD ρ')) :=
  Submodule.span LL {z | ∃ (c : K₀) (x cx : ↥(Dcris PD ρ)) (y cy : ↥(Dcris PD ρ')),
    (cx : V ⊗[Qp] B) = mulVB (K₀ := K₀) (LL := LL) c (x : V ⊗[Qp] B) ∧
    (cy : V' ⊗[Qp] B) = mulVB (K₀ := K₀) (LL := LL) c (y : V' ⊗[Qp] B) ∧
    z = cx ⊗ₜ[LL] y - x ⊗ₜ[LL] cy}
end Maps
def InvB : Prop := ∀ b : B, (∀ g, PD.actB g b = b) ↔ ∃ c : K₀, algebraMap K₀ B c = b
variable (LL : Type) [Field LL] [Algebra Qp LL]
def DcrisFinite : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V), FiniteDimensional LL ↥(Dcris PD ρ)
def Comparison : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V),
    IsCrys PD ρ → Function.Bijective (compMap PD ρ)
def CrysSub : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V') (f : V' →ₗ[LL] V),
    Equivariant ρ' ρ f → Function.Injective f → IsCrys PD ρ → IsCrys PD ρ'
def CrysQuot : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V') (f : V →ₗ[LL] V'),
    Equivariant ρ ρ' f → Function.Surjective f → IsCrys PD ρ → IsCrys PD ρ'
def CrysSum : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V'),
    IsCrys PD ρ → IsCrys PD ρ' → IsCrys PD (ρ.prod ρ')
def CrysTensor : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V'),
    IsCrys PD ρ → IsCrys PD ρ' → IsCrys PD (ρ.tprod ρ')
def CrysDual : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V),
    IsCrys PD ρ → IsCrys PD ρ.dual
def DcrisExact : Prop :=
  ∀ (V₀ : Type) [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]
    [FiniteDimensional LL V₀] (ρ₀ : Representation LL G V₀)
    (V₁ : Type) [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    [FiniteDimensional LL V₁] (ρ₁ : Representation LL G V₁)
    (V₂ : Type) [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
    [FiniteDimensional LL V₂] (ρ₂ : Representation LL G V₂)
    (f : V₀ →ₗ[LL] V₁) (g : V₁ →ₗ[LL] V₂),
    Equivariant ρ₀ ρ₁ f → Equivariant ρ₁ ρ₂ g →
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    IsCrys PD ρ₀ → IsCrys PD ρ₁ → IsCrys PD ρ₂ →
    (∀ x ∈ Dcris PD ρ₀, mapVB B f x = 0 → x = 0) ∧
      (Dcris PD ρ₀).map (mapVB B f) = Dcris PD ρ₁ ⊓ LinearMap.ker (mapVB B g) ∧
      (Dcris PD ρ₁).map (mapVB B g) = Dcris PD ρ₂
def DcrisTensor : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V'),
    IsCrys PD ρ → IsCrys PD ρ' →
    LinearMap.range (mulDcris PD ρ ρ') = Dcris PD (ρ.tprod ρ') ∧
      LinearMap.ker (mulDcris PD ρ ρ') = balK PD ρ ρ'
def LetterDim : Prop :=
  Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀ →
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V), IsCrys PD ρ →
    ∀ τ₀ : K₀ →ₐ[Qp] LL, finrank LL ↥(DcrisL PD ρ τ₀) = finrank LL V
def FormalismAt : Prop :=
  InvB PD ∧ (DcrisFinite PD LL ∧ FontaineLe PD LL) ∧ Comparison PD LL ∧
    CrysSub PD LL ∧ CrysQuot PD LL ∧ CrysSum PD LL ∧ CrysTensor PD LL ∧ CrysDual PD LL ∧
    DcrisExact PD LL ∧ DcrisTensor PD LL ∧ LetterDim PD LL
end Generic
def FontaineFormalism (l : ℕ) [Fact l.Prime] (P : LocPrime l) : Prop :=
  ∀ K LL : FinExt l, FormalismAt (P.PD K) ↥LL.1
example (l : ℕ) [Fact l.Prime] (P : LocPrime l) (h : FontaineFormalism l P) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys (P.PD K) T.ρ) :
    Function.Bijective (compMap (P.PD K) T.ρ) ∧ IsCrys (P.PD K) T.ρ.dual :=
  ⟨(h K LL).2.2.1 T.V T.ρ hT, (h K LL).2.2.2.2.2.2.2.1 T.V T.ρ hT⟩
end GlobalTheory.IndefiniteRowSideFullHecke.TensorMultiplication


