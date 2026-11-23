-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_DualExactSequence
-- name    : Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_DualExactSequence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:54.255667+00:00
-- url     : https://prove2.me/theorems/bce294fd-a8fd-46f1-a151-681891f4207f
-- title:
--   Dual Exact Sequence
-- statement:
--   Definitions and structural lemmas for Dual Exact Sequence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/DualExactSequence.lean

import Mathlib
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
variable {l : ℕ} [Fact l.Prime]
abbrev Lat (K LL : FinExt l) : Type 1 := LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)
abbrev Emb (K LL : FinExt l) : Type := ↥K.1 →ₐ[ℚ_[l]] ↥LL.1
def embeddingRestrictMaxUnramified {K LL : FinExt l} (τ : Emb K LL) : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1 :=
  τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)
section Objects
variable (P : LocPrime l) {K LL : FinExt l}
abbrev iota (T : Lat K LL) : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.BdR :=
  ιV (P.PD K) (LL := ↥LL.1) (V := T.V)
abbrev filV (T : Lat K LL) (a : ℤ) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) :=
  FilV (P.PD K) (LL := ↥LL.1) (V := T.V) a
abbrev mulK (T : Lat K LL) (c : ↥K.1) :
    T.V ⊗[ℚ_[l]] P.R.BdR →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.BdR :=
  mulVdR (Qp := ℚ_[l]) (K := ↥K.1) (BdR := P.R.BdR) (LL := ↥LL.1) (V := T.V) c
def filD (T : Lat K LL) (a : ℤ) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) :=
  DdR (P.PD K) T.ρ ⊓ filV P T a
def tdR (K : FinExt l) : P.R.BdRˣ := ((P.PD K).t_unit.map (P.PD K).ι).unit
def offComp (T : Lat K LL) (τ : Emb K LL) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) :=
  Submodule.span ↥LL.1 {z | ∃ (c : ↥K.1), ∃ y ∈ DdR (P.PD K) T.ρ, z = mulK P T c y - τ c • y}
def mapdR {T T' : Lat K LL} (f : T.V →ₗ[↥LL.1] T'.V) :
    T.V ⊗[ℚ_[l]] P.R.BdR →ₗ[↥LL.1] T'.V ⊗[ℚ_[l]] P.R.BdR :=
  AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR)
end Objects
section Shapes
variable {K LL : FinExt l}
def IsSES {T₀ T₁ T₂ : Lat K LL} (f : T₀.V →ₗ[↥LL.1] T₁.V) (g : T₁.V →ₗ[↥LL.1] T₂.V) : Prop :=
  (∀ σ x, f (T₀.ρ σ x) = T₁.ρ σ (f x)) ∧ (∀ σ x, g (T₁.ρ σ x) = T₂.ρ σ (g x)) ∧
    Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g
def IsDualRep {T T' : Lat K LL} (β : T.V →ₗ[↥LL.1] T'.V →ₗ[↥LL.1] ↥LL.1) : Prop :=
  (∀ σ x y, β (T.ρ σ x) (T'.ρ σ y) = β x y) ∧ Function.Bijective β.flip
def IsTensorRep {T₁ T₂ T₃ : Lat K LL} (e : T₁.V ⊗[↥LL.1] T₂.V ≃ₗ[↥LL.1] T₃.V) : Prop :=
  ∀ σ x y, T₃.ρ σ (e (x ⊗ₜ[↥LL.1] y)) = e (T₁.ρ σ x ⊗ₜ[↥LL.1] T₂.ρ σ y)
def SubSES (P : LocPrime l) {T₀ T₁ T₂ : Lat K LL} (f : T₀.V →ₗ[↥LL.1] T₁.V)
    (g : T₁.V →ₗ[↥LL.1] T₂.V) (A₀ : Submodule ↥LL.1 (T₀.V ⊗[ℚ_[l]] P.R.BdR))
    (A₁ : Submodule ↥LL.1 (T₁.V ⊗[ℚ_[l]] P.R.BdR))
    (A₂ : Submodule ↥LL.1 (T₂.V ⊗[ℚ_[l]] P.R.BdR)) : Prop :=
  (∀ x ∈ A₀, mapdR P f x = 0 → x = 0) ∧
    (∀ y, (∃ x ∈ A₀, mapdR P f x = y) ↔ (y ∈ A₁ ∧ mapdR P g y = 0)) ∧
    (∀ z, (∃ y ∈ A₁, mapdR P g y = z) ↔ z ∈ A₂)
end Shapes
section At
variable (P : LocPrime l) (K LL : FinExt l)
def CrysDeRhamAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ → IsDR (P.PD K) T.ρ
def DdRSpanAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ →
    DdR (P.PD K) T.ρ = Submodule.span ↥LL.1
      {z | ∃ (c : ↥K.1), ∃ x ∈ Dcris (P.PD K) T.ρ, z = mulK P T c (iota P T x)}
def DdRInjAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ →
    ∀ (m : ℕ) (c : Fin m → ↥K.1) (x : Fin m → T.V ⊗[ℚ_[l]] P.R.B),
      LinearIndependent ↥(K0 K) c → (∀ i, x i ∈ Dcris (P.PD K) T.ρ) →
      ∑ i, mulK P T (c i) (iota P T (x i)) = 0 → ∀ i, x i = 0
def ComponentIsoAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ → ∀ τ : Emb K LL,
    ∃ e : ↥(DcrisL (P.PD K) T.ρ (embeddingRestrictMaxUnramified τ)) ≃ₗ[↥LL.1] ↥(DdRE (P.PD K) T.ρ τ),
      ∀ x : ↥(DcrisL (P.PD K) T.ρ (embeddingRestrictMaxUnramified τ)), iota P T (x : T.V ⊗[ℚ_[l]] P.R.B) - (e x : T.V ⊗[ℚ_[l]] P.R.BdR) ∈ offComp P T τ
def UnramOntoAt : Prop :=
  K.1 ≤ MaximalUnramifiedExtension l → ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ →
    (Dcris (P.PD K) T.ρ).map (iota P T) = DdR (P.PD K) T.ρ
def FilZeroAt : Prop :=
  ∀ T : Lat K LL, IsDR (P.PD K) T.ρ →
    filV P T 0 = Submodule.span ↥LL.1
      {z | ∃ (a : ℤ), ∃ b ∈ (P.PD K).Fil 0, ∃ d ∈ filD P T a,
        z = mulVR T (((tdR P K ^ (-a) : P.R.BdRˣ) : P.R.BdR) * b) d}
def StrictAt : Prop :=
  ∀ (T₀ T₁ T₂ : Lat K LL) (f : T₀.V →ₗ[↥LL.1] T₁.V) (g : T₁.V →ₗ[↥LL.1] T₂.V), IsSES f g →
    IsDR (P.PD K) T₀.ρ → IsDR (P.PD K) T₁.ρ → IsDR (P.PD K) T₂.ρ →
    ∀ (τ : Emb K LL) (a : ℤ), SubSES P f g
      (FildR (P.PD K) T₀.ρ τ a) (FildR (P.PD K) T₁.ρ τ a) (FildR (P.PD K) T₂.ρ τ a)
def DualJumpsAt : Prop :=
  ∀ (T T' : Lat K LL) (β : T.V →ₗ[↥LL.1] T'.V →ₗ[↥LL.1] ↥LL.1), IsDualRep β →
    IsDR (P.PD K) T.ρ →
    IsDR (P.PD K) T'.ρ ∧ ∀ (τ : Emb K LL) (a : ℤ),
      (IsJumpV (P.PD K) T'.ρ τ a ↔ IsJumpV (P.PD K) T.ρ τ (-a)) ∧
        multV (P.PD K) T'.ρ τ a = multV (P.PD K) T.ρ τ (-a)
def TensorJumpsAt : Prop :=
  ∀ (T₁ T₂ T₃ : Lat K LL) (e : T₁.V ⊗[↥LL.1] T₂.V ≃ₗ[↥LL.1] T₃.V), IsTensorRep e →
    IsDR (P.PD K) T₁.ρ → IsDR (P.PD K) T₂.ρ →
    IsDR (P.PD K) T₃.ρ ∧ ∀ (τ : Emb K LL) (c : ℤ),
      (IsJumpV (P.PD K) T₃.ρ τ c ↔
        ∃ a b : ℤ, IsJumpV (P.PD K) T₁.ρ τ a ∧ IsJumpV (P.PD K) T₂.ρ τ b ∧ a + b = c) ∧
      ∀ S : Finset ℤ, JumpsInV (P.PD K) T₁.ρ τ (S : Set ℤ) →
        multV (P.PD K) T₃.ρ τ c =
          ∑ a ∈ S, multV (P.PD K) T₁.ρ τ a * multV (P.PD K) T₂.ρ τ (c - a)
def TwistJumpsAt : Prop :=
  ∀ T T' : Lat K LL, IsTwistRep (cycLL (P.PD K) ↥LL.1) T.ρ T'.ρ → IsDR (P.PD K) T.ρ →
    IsDR (P.PD K) T'.ρ ∧ ∀ (τ : Emb K LL) (a : ℤ),
      (IsJumpV (P.PD K) T'.ρ τ (a - 1) ↔ IsJumpV (P.PD K) T.ρ τ a) ∧
        multV (P.PD K) T'.ρ τ (a - 1) = multV (P.PD K) T.ρ τ a
def PotCrysDeRhamAt : Prop :=
  ∀ (T : Lat K LL) (K' : FinExt l) (hK : K.1 ≤ K'.1),
    IsCrys (P.PD K') (T.ρ.comp (Subgroup.inclusion (GK_le hK))) → IsDR (P.PD K) T.ρ
def FilteredIsoAt : Prop :=
  ∀ T : Lat K LL, IsDR (P.PD K) T.ρ →
    (∀ (m : ℕ) (b : Fin m → P.R.BdR) (d : Fin m → T.V ⊗[ℚ_[l]] P.R.BdR),
      LinearIndependent ↥K.1 b → (∀ i, d i ∈ DdR (P.PD K) T.ρ) →
      ∑ i, mulVR T (b i) (d i) = 0 → ∀ i, d i = 0) ∧
    Submodule.span ↥LL.1 {z | ∃ (b : P.R.BdR), ∃ d ∈ DdR (P.PD K) T.ρ, z = mulVR T b d} = ⊤ ∧
    ∀ n : ℤ, filV P T n = Submodule.span ↥LL.1
      {z | ∃ (a : ℤ), ∃ b ∈ (P.PD K).Fil (n - a), ∃ d ∈ filD P T a, z = mulVR T b d}
def StrictWholeAt : Prop :=
  ∀ (T₀ T₁ T₂ : Lat K LL) (f : T₀.V →ₗ[↥LL.1] T₁.V) (g : T₁.V →ₗ[↥LL.1] T₂.V), IsSES f g →
    IsDR (P.PD K) T₀.ρ → IsDR (P.PD K) T₁.ρ → IsDR (P.PD K) T₂.ρ →
    ∀ a : ℤ, SubSES P f g (filD P T₀ a) (filD P T₁ a) (filD P T₂ a)
def GradedHodgeTateAt : Prop :=
  ∀ T : Lat K LL, IsDR (P.PD K) T.ρ → ∀ (a : ℤ), ∀ x ∈ filV P T a,
    (∀ σ, actVdR (P.PD K) T.ρ σ x - x ∈ filV P T (a + 1)) →
    ∃ d ∈ filD P T a, x - d ∈ filV P T (a + 1)
end At
def OverGood (C : FinExt l → FinExt l → Prop) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → C K LL
section Good
variable (l) (P : LocPrime l)
def CrysDeRham : Prop := OverGood (CrysDeRhamAt P)
def DdRSpan : Prop := OverGood (DdRSpanAt P)
def DdRInj : Prop := OverGood (DdRInjAt P)
def ComponentIso : Prop := OverGood (ComponentIsoAt P)
def UnramOnto : Prop := OverGood (UnramOntoAt P)
def FilZero : Prop := OverGood (FilZeroAt P)
def Strict : Prop := OverGood (StrictAt P)
def DualJumps : Prop := OverGood (DualJumpsAt P)
def TensorJumps : Prop := OverGood (TensorJumpsAt P)
def TwistJumps : Prop := OverGood (TwistJumpsAt P)
def PotCrysDeRham : Prop := OverGood (PotCrysDeRhamAt P)
def FilteredIso : Prop := OverGood (FilteredIsoAt P)
def StrictWhole : Prop := OverGood (StrictWholeAt P)
def GradedHodgeTate : Prop := OverGood (GradedHodgeTateAt P)
def DeRhamComparison : Prop :=
  CrysDeRham l P ∧ DdRSpan l P ∧ ComponentIso l P ∧ UnramOnto l P ∧ FilZero l P ∧ Strict l P ∧
    DualJumps l P ∧ TensorJumps l P ∧ TwistJumps l P ∧ PotCrysDeRham l P
def DeRhamComparisonFull : Prop :=
  DeRhamComparison l P ∧ DdRInj l P ∧ FilteredIso l P ∧ StrictWhole l P ∧ GradedHodgeTate l P
def DeRhamComparisonAllFields : Prop :=
  ∀ K LL : FinExt l, CrysDeRhamAt P K LL ∧ DdRSpanAt P K LL ∧ ComponentIsoAt P K LL ∧
    UnramOntoAt P K LL ∧ FilZeroAt P K LL ∧ StrictAt P K LL ∧ DualJumpsAt P K LL ∧
    TensorJumpsAt P K LL ∧ TwistJumpsAt P K LL ∧ PotCrysDeRhamAt P K LL ∧ DdRInjAt P K LL ∧
    FilteredIsoAt P K LL ∧ StrictWholeAt P K LL ∧ GradedHodgeTateAt P K LL
end Good
example (P : LocPrime l) {K LL : FinExt l} (T : Lat K LL) (τ : Emb K LL) (a : ℤ) :
    FildR (P.PD K) T.ρ τ a ≤ filD P T a :=
  inf_le_inf_right _ inf_le_left
example (P : LocPrime l) {K LL : FinExt l} (T : Lat K LL) :
    (Dcris (P.PD K) T.ρ).map (iota P T) ≤ DdR (P.PD K) T.ρ := by
  rintro _ ⟨x, hx, rfl⟩
  have key : ∀ g y, actVdR (P.PD K) T.ρ g (iota P T y) = iota P T (actVB (P.PD K) T.ρ g y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVdR, actVB, ιV, (P.PD K).ι_comm]
    | add a b ha hb => simp only [map_add, ha, hb]
  simp only [Dcris, DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hx ⊢
  intro g
  rw [key, hx]
end GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence


