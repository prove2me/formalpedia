-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_PointRingCommRing
-- name    : Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_PointRingCommRing
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:52:37.921448+00:00
-- url     : https://prove2.me/theorems/e5538eb2-c63b-5b5e-8402-822c271b2a9f
-- title:
--   Point Ring Comm Ring
-- statement:
--   Definitions and structural lemmas for Point Ring Comm Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/PointRingCommRing.lean

import Mathlib
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
section Generic
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
def LiesOver (W : LocWach PD LL O v n) (τ : K →ₐ[Qp] LL) (i : ZMod n) : Prop :=
  ∀ c : K₀, τ (algebraMap K₀ K c) = W.emb i c
def JumpsOverLetters (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) : Prop :=
  ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), LiesOver W τ i →
    JumpsInV PD T.ρ τ (Set.Icc (-(M i : ℤ)) (h i : ℤ))
def phiPullLetter (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) :
    Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) (W.φD T '' (W.Nl T (i - 1) : Set (W.DD T)))
def InLetterAwayQ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (y : W.DD T) : Prop :=
  ∃ k : ℕ, W.Q ^ k • y ∈ W.Nl T i
def PointRing (_W : LocWach PD LL O v n) (_i : ZMod n) (_ζ : LL) : Type := PowerSeries LL
instance PointRing.commRing (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) :
    CommRing (PointRing W i ζ) :=
  inferInstanceAs (CommRing (PowerSeries LL))
instance PointRing.algebra (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) :
    Algebra (LetA O n) (PointRing W i ζ) :=
  RingHom.toAlgebra (R := LetA O n) (S := PointRing W i ζ) (W.lev i ζ).toRingHom
example (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) (a : LetA O n) :
    algebraMap (LetA O n) (PointRing W i ζ) a = W.lev i ζ a := rfl
abbrev CompletedAt (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) : Type :=
  PointRing W i ζ ⊗[LetA O n] ↥(W.Nl T i)
def InCompletedAt (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL)
    (y : W.DD T) : Prop :=
  ∃ (k : ℕ) (hk : W.Q ^ k • y ∈ W.Nl T i) (w : CompletedAt W T i ζ),
    (1 : PointRing W i ζ) ⊗ₜ[LetA O n] (⟨W.Q ^ k • y, hk⟩ : ↥(W.Nl T i)) = W.Q ^ k • w
example (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (y : W.DD T)
    (hy : y ∈ W.Nl T i) : InCompletedAt W T i ζ y :=
  ⟨0, by simpa using hy, (1 : PointRing W i ζ) ⊗ₜ[LetA O n] ⟨W.Q ^ 0 • y, by simpa using hy⟩,
    by simp⟩
def HeightBounds (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) : Prop :=
  ∀ i : ZMod n,
    (∀ y ∈ phiPullLetter W T i, W.Q ^ M i • y ∈ W.Nl T i) ∧
    (∀ y ∈ W.Nl T i, W.Q ^ h i • y ∈ phiPullLetter W T i)
def RootTest (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Prop :=
  ∀ (i : ZMod n) (y : W.DD T), InLetterAwayQ W T i y →
    (y ∈ W.Nl T i ↔ ∀ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ W.s) → InCompletedAt W T i ζ y)
variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
def latticeAinf (inclR : RA →ₐ[O] RW) (T : LocLat G Qp LL O) : Submodule O (TW RW T) :=
  LinearMap.range (TWincl inclR T)
def wachAinf (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) : Submodule O (TW RW T) :=
  Submodule.span O {z | ∃ (a : RA) (x : W.DD T), x ∈ W.N T ∧ z = inclR a • E.jD T x}
def Sandwich (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (M h : ℕ) : Prop :=
  (∀ z ∈ latticeAinf inclR T, inclR (E.io W.X) ^ h • z ∈ wachAinf E T) ∧
  (∀ z ∈ wachAinf E T, inclR (E.io W.X) ^ M • z ∈ latticeAinf inclR T)
end Generic
open TensorProduct in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing.letters_neZero {l : ℕ} [Fact l.Prime] (K : _root_.Formalism.BasicNotions.Loc.FinExt l) :
    NeZero (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) := by
  haveI : FiniteDimensional ℚ_[l] ↥(K : IntermediateField ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l)) := K.2
  have hle : _root_.Formalism.BasicNotions.Loc.K0 K ≤ (K : IntermediateField ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l)) := by
    unfold _root_.Formalism.BasicNotions.Loc.K0; exact inf_le_left
  haveI : FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  exact ⟨Module.finrank_pos.ne'⟩
def letterMax {l : ℕ} [Fact l.Prime] (K : FinExt l)
    (f : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) : ℕ :=
  haveI := letters_neZero K
  Finset.univ.sup f
def HeightsFromJumps (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) (_C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    ∀ Mi hi : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ,
      JumpsOverLetters (H.W K s LL h) T Mi hi →
        HeightBounds (H.W K s LL h) T Mi hi ∧
        RootTest (H.W K s LL h) T ∧
        Sandwich (F.E K s LL h).tie T (letterMax K Mi) (letterMax K hi)
end GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing


