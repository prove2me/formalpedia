-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_WachModuleUniqueness
-- name    : Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_WachModuleUniqueness
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:53:00.894707+00:00
-- url     : https://prove2.me/theorems/136a3438-efab-5ff2-9ff1-33e81c05edd9
-- title:
--   Wach Module Uniqueness
-- statement:
--   Definitions and structural lemmas for Wach Module Uniqueness, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/WachModuleUniqueness.lean

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.WachModuleUniqueness
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
def invSub {A D : Type} [CommRing A] [AddCommGroup D] [Module A D] (a : A) (M : Submodule A D) :
    Submodule A D where
  carrier := {x | ∃ k : ℕ, a ^ k • x ∈ M}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨k, hk⟩ ⟨m, hm⟩
    refine ⟨k + m, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]; exact M.smul_mem _ hk
    · rw [pow_add, mul_smul]; exact M.smul_mem _ hm
  smul_mem' := by
    rintro c x ⟨k, hk⟩
    exact ⟨k, by rw [smul_comm]; exact M.smul_mem _ hk⟩
section Generic
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
def BasisCond (N₁ : Submodule (LetA O n) (W.DD T)) : Prop :=
  ∃ (ι : Type) (b : Module.Basis ι (LetA O n) ↥N₁) (c : Module.Basis ι W.EE (W.DD T)),
    ∀ j, c j = (b j : W.DD T)
def GammaStable (N₁ : Submodule (LetA O n) (W.DD T)) : Prop :=
  W.γ T '' (N₁ : Set (W.DD T)) = (N₁ : Set (W.DD T))
def GammaTrivModπ (N₁ : Submodule (LetA O n) (W.DD T)) : Prop :=
  ∀ x ∈ N₁, ∃ y ∈ N₁, W.γ T x - x = (letπ : LetA O n) • y
def phiSpan (N₁ : Submodule (LetA O n) (W.DD T)) : Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) (W.φD T '' (N₁ : Set (W.DD T)))
def PhiIsoAwayQ (N₁ : Submodule (LetA O n) (W.DD T)) : Prop :=
  invSub W.Q (phiSpan W T N₁) = invSub W.Q N₁
example : GammaStable W T (W.N T) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact W.N_Γ T _ x hx
  · intro x hx
    refine ⟨W.γD T W.gam⁻¹ x, W.N_Γ T _ x hx, ?_⟩
    change W.γD T W.gam (W.γD T W.gam⁻¹ x) = x
    rw [← W.γD_mul, mul_inv_cancel, W.γD_one]
example : GammaTrivModπ W T (W.N T) := fun x hx => W.N_π T W.gam x hx
example : PhiIsoAwayQ W T (W.N T) := by
  apply le_antisymm
  · rintro x ⟨k, hk⟩
    have h : phiSpan W T (W.N T) ≤ invSub W.Q (W.N T) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      exact W.N_φ T y hy
    obtain ⟨m, hm⟩ := h hk
    exact ⟨m + k, by rw [pow_add, mul_smul]; exact hm⟩
  · rintro x ⟨k, hk⟩
    obtain ⟨m, hm⟩ := W.N_φinv T _ hk
    exact ⟨m + k, by rw [pow_add, mul_smul]; exact hm⟩
end Generic
def WachUnique (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) (_C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    ∀ N₁ : Submodule (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ((H.W K s LL h).DD T),
      BasisCond (H.W K s LL h) T N₁ →
      GammaStable (H.W K s LL h) T N₁ →
      GammaTrivModπ (H.W K s LL h) T N₁ →
      PhiIsoAwayQ (H.W K s LL h) T N₁ →
      N₁ = (H.W K s LL h).N T
end GlobalTheory.IndefiniteRowSideFullHecke.WachModuleUniqueness


