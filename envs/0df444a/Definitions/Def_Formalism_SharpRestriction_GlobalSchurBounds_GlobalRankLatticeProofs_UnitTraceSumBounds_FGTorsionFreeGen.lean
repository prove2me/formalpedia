-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_FGTorsionFreeGen
-- name    : Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_FGTorsionFreeGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:28.675024+00:00
-- url     : https://prove2.me/theorems/33938e83-3bc1-415e-a0d8-3bf39d3a2b3a
-- title:
--   FGTorsion Free Gen
-- statement:
--   Definitions and structural lemmas for FGTorsion Free Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/UnitTraceSumBounds/FGTorsionFreeGen.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.MainNotions.Ext.CutC
open NumberField
def stdLat (R K : Type) [CommRing R] [Field K] [Algebra R K] (r : ℕ) : Submodule R (Fin r → K) :=
  Submodule.span R (Set.range fun i : Fin r => (Pi.single i (1 : K) : Fin r → K))
def vecK (R K : Type) [CommRing R] [Field K] [Algebra R K] {r : ℕ} (x : Fin r → R) : Fin r → K :=
  fun i => algebraMap R K (x i)
def supLat (R K : Type) [CommRing R] [Field K] [Algebra R K] (ϖ : R) {r : ℕ} (x : Fin r → R) :
    Submodule R (Fin r → K) :=
  stdLat R K r ⊔ Submodule.span R {(algebraMap R K ϖ)⁻¹ • vecK R K x}
def SupLatLine : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R), Irreducible ϖ → ∀ r : ℕ,
    (∀ x : Fin r → R, (∃ i, ¬ ϖ ∣ x i) →
      IsSimpleModule R ((supLat R K ϖ x) ⧸ (stdLat R K r).comap (supLat R K ϖ x).subtype)) ∧
    (∀ x y : Fin r → R, (∃ i, ¬ ϖ ∣ x i) → (∃ i, ¬ ϖ ∣ y i) →
      (supLat R K ϖ x = supLat R K ϖ y ↔ ∃ c : R, IsUnit c ∧ ∀ i, ϖ ∣ x i - c * y i)) ∧
    (∀ M : Submodule R (Fin r → K), stdLat R K r ≤ M →
      IsSimpleModule R (M ⧸ (stdLat R K r).comap M.subtype) →
      ∃ x : Fin r → R, (∃ i, ¬ ϖ ∣ x i) ∧ M = supLat R K ϖ x)
def FGTorsionFreeGen : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [NoZeroSMulDivisors R M],
    ∃ s : Finset M, s.card ≤ Module.finrank R M + 1 ∧ Submodule.span R (s : Set M) = ⊤
def IndexMatNorm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (A : Matrix (Fin r) (Fin r) (𝓞 E)), A.det ≠ 0 →
    Nat.card ((Fin r → 𝓞 E) ⧸ LinearMap.range A.mulVecLin) = (Algebra.norm ℤ A.det).natAbs
def IndexMulLattice : Prop :=
  ∀ (E Y : Type) [Field E] [NumberField E] [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite (𝓞 E) Y] [NoZeroSMulDivisors (𝓞 E) Y] (M : ℕ), 1 ≤ M →
    Nat.card (Y ⧸ LinearMap.range ((M : 𝓞 E) • LinearMap.id : Y →ₗ[𝓞 E] Y)) = M ^ (Module.finrank ℚ E * Module.finrank (𝓞 E) Y)
def DualIndex : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (B : LinearMap.BilinForm ℚ V),
    B.Nondegenerate → ∀ L₀ L : Submodule ℤ V, L₀ ≤ L → L.FG →
    Submodule.span ℚ (L₀ : Set V) = ⊤ →
    Nat.card ((B.dualSubmodule L₀) ⧸ (B.dualSubmodule L).comap (B.dualSubmodule L₀).subtype) =
      Nat.card (L ⧸ L₀.comap L.subtype)
end Formalism.MainNotions.Ext.CutC


