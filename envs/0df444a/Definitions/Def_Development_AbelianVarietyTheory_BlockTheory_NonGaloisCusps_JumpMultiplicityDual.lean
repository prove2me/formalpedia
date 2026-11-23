-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_JumpMultiplicityDual
-- name    : Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_JumpMultiplicityDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:47:55.403813+00:00
-- url     : https://prove2.me/theorems/af1c7678-249c-461e-acac-cd2c1f2d7baf
-- title:
--   Jump Multiplicity Dual
-- statement:
--   Definitions and structural lemmas for Jump Multiplicity Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/JumpMultiplicityDual.lean

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct
section Core
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
section Ops
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
def mulPeriod (b : BdR) : V ⊗[Qp] BdR →ₗ[LL] V ⊗[Qp] BdR :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp b)
example (c : K) : mulPeriod (Qp := Qp) (LL := LL) (V := V) (algebraMap K BdR c) =
    mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) c := rfl
def mapdR {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (f : V →ₗ[LL] V') : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR :=
  AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)
def tdR : BdRˣ := (PD.t_unit.map PD.ι).unit
example : ((tdR PD : BdRˣ) : BdR) = PD.ι PD.t := rfl
variable (ρ : Representation LL G V)
def filDdR (a : ℤ) : Submodule LL (V ⊗[Qp] BdR) := DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a
def jumpMult (τ : K →ₐ[Qp] LL) (a : ℤ) : ℕ :=
  Module.finrank LL (↥(FildR PD ρ τ a) ⧸ (FildR PD ρ τ (a + 1)).comap (FildR PD ρ τ a).subtype)
def resEmb (K₀ : Type) [Field K₀] [Algebra Qp K₀] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (τ : K →ₐ[Qp] LL) : K₀ →ₐ[Qp] LL :=
  τ.comp (IsScalarTower.toAlgHom Qp K₀ K)
end Ops
variable [TopologicalSpace G] (LL O : Type) [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
  [TopologicalSpace LL]
def CrysDeRhamCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → IsDR PD T.ρ
def SpanCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
    DdR PD T.ρ = ⨆ c : K, ((Dcris PD T.ρ).map (ιV PD (LL := LL) (V := T.V))).map
      (mulVdR (Qp := Qp) (LL := LL) (V := T.V) (BdR := BdR) c)
def BaseChangeInjCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
    ∀ (m : ℕ) (c : Fin m → K), LinearIndependent K₀ c →
      ∀ x : Fin m → T.V ⊗[Qp] B, (∀ j, x j ∈ Dcris PD T.ρ) →
        ∑ j, mulVdR (Qp := Qp) (LL := LL) (V := T.V) (BdR := BdR) (c j)
          (ιV PD (LL := LL) (V := T.V) (x j)) = 0 → ∀ j, x j = 0
def ComponentCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ τ : K →ₐ[Qp] LL,
    ∃ e : ↥(DcrisL PD T.ρ (resEmb K₀ τ)) ≃ₗ[LL] ↥(DdRE PD T.ρ τ),
      ∀ x : ↥(DcrisL PD T.ρ (resEmb K₀ τ)),
        ιV PD (LL := LL) (V := T.V) (x : T.V ⊗[Qp] B) - (e x : T.V ⊗[Qp] BdR) ∈
          ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ'
def OntoCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
    (Dcris PD T.ρ).map (ιV PD (LL := LL) (V := T.V)) = DdR PD T.ρ
def ComparisonInjCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsDR PD T.ρ →
    ∀ (m : ℕ) (x : Fin m → T.V ⊗[Qp] BdR), (∀ j, x j ∈ DdR PD T.ρ) →
      (∀ c : Fin m → K,
        ∑ j, mulVdR (Qp := Qp) (LL := LL) (V := T.V) (BdR := BdR) (c j) (x j) = 0 → ∀ j, c j = 0) →
      ∀ b : Fin m → BdR,
        ∑ j, mulPeriod (Qp := Qp) (LL := LL) (V := T.V) (b j) (x j) = 0 → ∀ j, b j = 0
def FilteredCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsDR PD T.ρ → ∀ n : ℤ,
    FilV PD (LL := LL) (V := T.V) n =
      ⨆ (a : ℤ) (b : BdR) (_ : b ∈ PD.Fil (n - a)),
        (filDdR PD T.ρ a).map (mulPeriod (Qp := Qp) (LL := LL) (V := T.V) b)
def LatticeCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsDR PD T.ρ →
    FilV PD (LL := LL) (V := T.V) 0 =
      ⨆ (a : ℤ) (b : BdR) (_ : b ∈ PD.Fil 0),
        (filDdR PD T.ρ a).map
          (mulPeriod (Qp := Qp) (LL := LL) (V := T.V) (((tdR PD ^ (-a) : BdRˣ) : BdR) * b))
def StrictCore : Prop :=
  ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (f : T₀.V →ₗ[LL] T₁.V) (g : T₁.V →ₗ[LL] T₂.V),
    (∀ s x, f (T₀.ρ s x) = T₁.ρ s (f x)) → (∀ s x, g (T₁.ρ s x) = T₂.ρ s (g x)) →
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    IsDR PD T₀.ρ → IsDR PD T₁.ρ → IsDR PD T₂.ρ →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      (∀ x ∈ FildR PD T₀.ρ τ a, mapdR (Qp := Qp) (BdR := BdR) f x = 0 → x = 0) ∧
      (FildR PD T₀.ρ τ a).map (mapdR (Qp := Qp) (BdR := BdR) f) =
        FildR PD T₁.ρ τ a ⊓ LinearMap.ker (mapdR (Qp := Qp) (BdR := BdR) g) ∧
      (FildR PD T₁.ρ τ a).map (mapdR (Qp := Qp) (BdR := BdR) g) = FildR PD T₂.ρ τ a
def DualCore : Prop :=
  ∀ (T T' : LocLat G Qp LL O) (β : T.V →ₗ[LL] T'.V →ₗ[LL] LL),
    (∀ s x y, β (T.ρ s x) (T'.ρ s y) = β x y) → Function.Bijective β.flip → IsDR PD T.ρ →
    IsDR PD T'.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      (IsJumpV PD T'.ρ τ a ↔ IsJumpV PD T.ρ τ (-a)) ∧
      jumpMult PD T'.ρ τ a = jumpMult PD T.ρ τ (-a)
def TensorCore : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O) (e : T.V ⊗[LL] T'.V ≃ₗ[LL] T''.V),
    (∀ s x y, T''.ρ s (e (x ⊗ₜ[LL] y)) = e (T.ρ s x ⊗ₜ[LL] T'.ρ s y)) →
    IsDR PD T.ρ → IsDR PD T'.ρ →
    IsDR PD T''.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (c : ℤ),
      (IsJumpV PD T''.ρ τ c ↔ ∃ a b : ℤ, IsJumpV PD T.ρ τ a ∧ IsJumpV PD T'.ρ τ b ∧ c = a + b) ∧
      (Function.support fun a : ℤ => jumpMult PD T.ρ τ a * jumpMult PD T'.ρ τ (c - a)).Finite ∧
      jumpMult PD T''.ρ τ c = ∑ᶠ a : ℤ, jumpMult PD T.ρ τ a * jumpMult PD T'.ρ τ (c - a)
def TwistCore : Prop :=
  ∀ T T' : LocLat G Qp LL O, IsTwistRep (cycLL PD LL) T.ρ T'.ρ → IsDR PD T.ρ →
    IsDR PD T'.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      (IsJumpV PD T'.ρ τ (a - 1) ↔ IsJumpV PD T.ρ τ a) ∧
      jumpMult PD T'.ρ τ (a - 1) = jumpMult PD T.ρ τ a
end Core
section Local
variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)
def CrysDeRham : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → CrysDeRhamCore (P.PD K) ↥LL.1 ↥(OL LL)
def DeRhamSpan : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → SpanCore (P.PD K) ↥LL.1 ↥(OL LL)
def BaseChangeInj : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → BaseChangeInjCore (P.PD K) ↥LL.1 ↥(OL LL)
def ComponentIso : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ComponentCore (P.PD K) ↥LL.1 ↥(OL LL)
def UnramifiedOnto : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → K0 K = K.1 →
    OntoCore (P.PD K) ↥LL.1 ↥(OL LL)
def ComparisonInj : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ComparisonInjCore (P.PD K) ↥LL.1 ↥(OL LL)
def ComparisonFiltered : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → FilteredCore (P.PD K) ↥LL.1 ↥(OL LL)
def PlusLattice : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → LatticeCore (P.PD K) ↥LL.1 ↥(OL LL)
def Strictness : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → StrictCore (P.PD K) ↥LL.1 ↥(OL LL)
def DualJumps : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → DualCore (P.PD K) ↥LL.1 ↥(OL LL)
def TensorJumps : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → TensorCore (P.PD K) ↥LL.1 ↥(OL LL)
def TwistJumps : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → TwistCore (P.PD K) ↥LL.1 ↥(OL LL)
def PotCrysDeRham : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL →
    ∀ (K' : FinExt l) (h : K.1 ≤ K'.1) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
      IsCrys (P.PD K') (T.ρ.comp (Subgroup.inclusion (GK_le h))) → IsDR (P.PD K) T.ρ
def DeRhamComparison : Prop :=
  CrysDeRham l P ∧ DeRhamSpan l P ∧ BaseChangeInj l P ∧ ComponentIso l P ∧ UnramifiedOnto l P ∧
    ComparisonInj l P ∧ ComparisonFiltered l P ∧ PlusLattice l P ∧ Strictness l P ∧
    DualJumps l P ∧ TensorJumps l P ∧ TwistJumps l P ∧ PotCrysDeRham l P
end Local
end GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual


