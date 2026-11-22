-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
-- name    : Formalism_HarderNarasimhan_DegSupermodZ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:52:18.914262+00:00
-- url     : https://prove2.me/theorems/a74ba72c-24e4-4c3c-ab37-5074f30890e4
-- title:
--   Deg Supermod Z
-- statement:
--   Definitions and structural lemmas for Deg Supermod Z, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/DegSupermodZ.lean

import Definitions.Def_Formalism_HarderNarasimhan_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
namespace Formalism.HN
def DegSupermodZ : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L A B : Submodule ℤ E), DiscreteTopology L → A ≤ L → B ≤ L →
    Formalism.F.rk (A ⊔ B) + Formalism.F.rk (A ⊓ B) = Formalism.F.rk A + Formalism.F.rk B ∧
    Formalism.F.deg A + Formalism.F.deg B ≤ Formalism.F.deg (A ⊔ B) + Formalism.F.deg (A ⊓ B)
def SatR : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L N : Submodule R V),
    IsLat ρ L → N ≤ L →
    ∃ N' : Submodule R V, N ≤ N' ∧ N' ≤ L ∧ zl ρ N' = Formalism.F.satur (zl ρ L) (zl ρ N)
def FinSup : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L : Submodule R V)
    (S : Set (Submodule R V)), IsLat ρ L → (∀ N ∈ S, N ≤ L) →
    ∃ t : Finset (Submodule R V), (↑t : Set (Submodule R V)) ⊆ S ∧ sSup S = t.sup id
def SatBasic : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L : Submodule R V),
    IsLat ρ L →
    (∀ N : Submodule R V, N ≤ L → IsLat ρ N) ∧
    (∀ A B : Submodule R V, A ≤ B → B ≤ L → rk ρ A ≤ rk ρ B ∧ (rk ρ A = rk ρ B → deg ρ A ≤ deg ρ B)) ∧
    (∀ S N : Submodule R V, IsSat ρ L S → S ≤ N → N ≤ L → rk ρ N = rk ρ S → N = S) ∧
    (∀ N : Submodule R V, N ≤ L → (rk ρ N = 0 ↔ N = ⊥)) ∧
    deg ρ (⊥ : Submodule R V) = 0 ∧ IsSat ρ L ⊥ ∧ IsSat ρ L L ∧
    (∀ S : Submodule R V, IsSat ρ L S →
      Formalism.F.rk (Formalism.F.quot (zl ρ L) (zl ρ S)) = rk ρ L - rk ρ S ∧
      rk ρ S ≤ rk ρ L ∧
      Formalism.F.deg (Formalism.F.quot (zl ρ L) (zl ρ S)) = deg ρ L - deg ρ S)
def RatioMax : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L S : Submodule R V),
    IsLat ρ L → IsSat ρ L S → S ≠ L →
    ∃ N : Submodule R V, S < N ∧ IsSat ρ L N ∧
      ∀ N' : Submodule R V, S < N' → N' ≤ L →
        (deg ρ N' - deg ρ S) * ((rk ρ N : ℝ) - rk ρ S) ≤
          (deg ρ N - deg ρ S) * ((rk ρ N' : ℝ) - rk ρ S)
end Formalism.HN


