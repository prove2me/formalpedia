-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:53:21.888142+00:00
-- url     : https://prove2.me/theorems/49df837f-de16-4f69-936b-60280476ccfe
-- title:
--   Not Full Bot
-- statement:
--   Definitions and structural lemmas for Not Full Bot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NotFullBot.lean

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
namespace GlobalTheory.NL
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
section Generic
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
def conv {M : Type} [AddCommGroup M] [Module LL M] (e : PowerSeries LL) (f : ℤ → M) : ℤ → M :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j e • f (k - j)
def latSpan {M ι : Type} [AddCommGroup M] [Module LL M] (ex : ι → ℤ → M) : Submodule LL (ℤ → M) :=
  Submodule.span LL {f | ∃ (e : PowerSeries LL) (x : ι), f = conv e (ex x)}
def Full {M : Type} [AddCommGroup M] [Module LL M] (D : Submodule LL M) (Λ : Submodule LL (ℤ → M)) : Prop :=
  ∃ m : ℕ, ∀ f : ℤ → M, (∀ k, f k ∈ D) → (∀ k < (m : ℤ), f k = 0) → f ∈ Λ
def Std {M : Type} [AddCommGroup M] [Module LL M] (D : Submodule LL M) (Λ : Submodule LL (ℤ → M)) : Prop :=
  ∀ f : ℤ → M, f ∈ Λ ↔ (∀ k, f k ∈ D) ∧ ∀ k < (0 : ℤ), f k = 0
def Graded {M : Type} [AddCommGroup M] [Module LL M] (Λ : Submodule LL (ℤ → M)) : Prop :=
  ∀ f : ℤ → M, f ∈ Λ ↔ (∃ m : ℤ, ∀ k < m, f k = 0) ∧ ∀ k, Pi.single k (f k) ∈ Λ
variable (PD) in

def FilAt (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (a : ℤ) : Submodule LL (T.V ⊗[Qp] BdR) :=
  FildR PD T.ρ τ a ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ'
def van (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) (k : ℕ) : Ideal (LetA O n) :=
  (Ideal.span {(PowerSeries.X : PowerSeries LL) ^ k}).comap (W.lev i ζ)
end Generic
section Concrete
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}
abbrev Lt (K LL : FinExt l) : Type 1 := LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)
abbrev Let (K : FinExt l) : Type := ZMod (Module.finrank ℚ_[l] ↥(K0 K))
abbrev AA (K LL : FinExt l) : Type := LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))
abbrev Di (H : LocHW l P) (h : Good K s LL) (T : Lt K LL) (i : Let K) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.B) :=
  DcrisL (P.PD K) T.ρ ((H.W K s LL h).emb i)
def ex (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (i : Let K) (ζ : ↥LL.1)
    (x : ↥((H.W K s LL h).N T)) : ℤ → T.V ⊗[ℚ_[l]] P.R.B :=
  (C.C K s LL h).tie.levB T i ζ x
def Lat (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (i : Let K) (ζ : ↥LL.1) :
    Submodule ↥LL.1 (ℤ → T.V ⊗[ℚ_[l]] P.R.B) :=
  latSpan (ex C h T i ζ)
def Pt (H : LocHW l P) (h : Good K s LL) (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) : Prop :=
  ∃ τs : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h i ζ τs ∧
    ∀ (x : ↥K.1) (y : ↥(Ks K s)), (y : Om l) = (x : Om l) → τ x = τs y
def Comp (H : LocHW l P) (h : Good K s LL) (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) : Prop :=
  (∀ c : ↥(K0 K), ι ((H.W K s LL h).emb i c) = algebraMap ↥(K0 K) P.R.BdR c) ∧
    ι ζ = algebraMap (Om l) P.R.BdR (P.ζQ s) ∧ ∀ c : ↥K.1, ι (τ c) = algebraMap ↥K.1 P.R.BdR c
def tS (P : LocPrime l) (s : ℕ) : P.R.BdR := (((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB
end Concrete
end GlobalTheory.NL


