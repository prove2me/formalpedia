-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_GradedSeries
-- name    : Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_GradedSeries
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:52:47.295599+00:00
-- url     : https://prove2.me/theorems/79be9cda-6a9a-4b55-853d-871dc61ceb83
-- title:
--   Graded Series
-- statement:
--   Definitions and structural lemmas for Graded Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/GradedSeries.lean

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
section Series
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]
def IsLaurent (u : ℤ → M) : Prop := ∃ m : ℤ, ∀ k < m, u k = 0
def serMul (f : PowerSeries L) (u : ℤ → M) : ℤ → M :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j f • u (k - (j : ℤ))
variable (L) in

def serSpan (S : Set (ℤ → M)) : Submodule L (ℤ → M) :=
  Submodule.span L {w | ∃ (f : PowerSeries L) (u : ℤ → M), u ∈ S ∧ IsLaurent u ∧ w = serMul f u}
def shiftSer (a : ℤ) (F : Submodule L M) : Submodule L (ℤ → M) where
  carrier := {u | (∀ k < -a, u k = 0) ∧ ∀ k, u k ∈ F}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => F.zero_mem⟩
  add_mem' := by
    rintro u w ⟨hu, hu'⟩ ⟨hw, hw'⟩
    exact ⟨fun k hk => by simp [hu k hk, hw k hk], fun k => F.add_mem (hu' k) (hw' k)⟩
  smul_mem' := by
    rintro c u ⟨hu, hu'⟩
    exact ⟨fun k hk => by simp [hu k hk], fun k => F.smul_mem c (hu' k)⟩
def gradedSer (F : ℤ → Submodule L M) : Submodule L (ℤ → M) := ⨆ a : ℤ, shiftSer a (F a)
example (a : ℤ) (F : Submodule L M) (d : M) (hd : d ∈ F) :
    (Pi.single (-a) d : ℤ → M) ∈ shiftSer a F := by
  refine ⟨fun k hk => Pi.single_eq_of_ne (ne_of_lt hk) _, fun k => ?_⟩
  by_cases h : k = -a
  · subst h; simpa using hd
  · simp [Pi.single_eq_of_ne h]
end Series
section Generic
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
def Dlet (i : ZMod n) : Submodule LL (T.V ⊗[Qp] B) := DcrisL PD T.ρ (W.emb i)
def FilLet (i : ZMod n) (τ : K →ₐ[Qp] LL) (a : ℤ) : Submodule LL (T.V ⊗[Qp] B) :=
  Dlet W T i ⊓
    (FildR PD T.ρ τ a ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ').comap
      (ιV PD (LL := LL) (V := T.V))
def toDR (F : Submodule LL (T.V ⊗[Qp] B)) : Submodule LL (T.V ⊗[Qp] BdR) :=
  F.map (ιV PD (LL := LL) (V := T.V))
def Nlev (i : ZMod n) (ζ : LL) : Submodule LL (ℤ → T.V ⊗[Qp] BdR) :=
  serSpan LL (Set.range (W.levN T i ζ))
def IsExpansion (i : ZMod n) (ζ : LL) (y : W.DD T) (u : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  IsLaurent u ∧ ∃ (m : ℕ) (hy : W.Q ^ m • y ∈ W.N T),
    serMul (W.lev i ζ (W.Q ^ m)) u = W.levN T i ζ ⟨W.Q ^ m • y, hy⟩
def phiNlev (i : ZMod n) (ζ : LL) : Submodule LL (ℤ → T.V ⊗[Qp] BdR) :=
  serSpan LL {u | ∃ y ∈ W.N T, IsExpansion W T i ζ (W.φD T y) u}
variable (PD) in

def phiSer (j : ℕ) (u : ℤ → T.V ⊗[Qp] B) : ℤ → T.V ⊗[Qp] BdR :=
  fun k => ιV PD (LL := LL) (V := T.V)
    ((((PD.p : LL) ^ j) ^ k) • ((φVB PD (LL := LL) (V := T.V)) ^ j) (u k))
end Generic
section Statement
variable {l : ℕ} [Fact l.Prime]
def resEmb {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1) : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 :=
  τ.comp (IntermediateField.inclusion h.2.2.1)
def LatticeAtLevels (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) (C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1),
      (∀ j : ℕ, j < s → IsPrimitiveRoot ζ (l ^ j) →
        Nlev (H.W K s LL h) T i ζ =
          shiftSer 0 (toDR (PD := P.PD K) T (Dlet (H.W K s LL h) T i))) ∧
      (∀ τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h i ζ τ →
        phiNlev (H.W K s LL h) T i ζ =
            shiftSer 0 (toDR (PD := P.PD K) T (Dlet (H.W K s LL h) T i)) ∧
          Nlev (H.W K s LL h) T i ζ =
            gradedSer fun a =>
              toDR (PD := P.PD K) T (FilLet (H.W K s LL h) T i (resEmb h τ) a)) ∧
      (∀ j : ℕ, 1 ≤ j → IsPrimitiveRoot ζ (l ^ (s + j)) →
        Nlev (H.W K s LL h) T i ζ =
            serSpan ↥LL.1 (phiSer (P.PD K) T j ''
              (serSpan ↥LL.1 (Set.range
                ((C.C K s LL h).tie.levB T (i - (j : ZMod _)) (ζ ^ (l ^ j)))) :
                  Set (ℤ → T.V ⊗[ℚ_[l]] P.R.B))) ∧
          ∀ τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h (i - (j : ZMod _)) (ζ ^ (l ^ j)) τ →
            Nlev (H.W K s LL h) T i ζ =
              gradedSer fun a =>
                toDR (PD := P.PD K) T
                  ((FilLet (H.W K s LL h) T (i - (j : ZMod _)) (resEmb h τ) a).map
                    ((φVB (P.PD K) (LL := ↥LL.1) (V := T.V)) ^ j)))
end Statement
end GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries


