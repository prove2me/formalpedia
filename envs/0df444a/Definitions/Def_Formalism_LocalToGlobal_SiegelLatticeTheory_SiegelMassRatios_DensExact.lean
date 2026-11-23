-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:08:48.695929+00:00
-- url     : https://prove2.me/theorems/c8ddd841-49b2-43fd-8eda-dda44c1c3135
-- title:
--   Dens Exact
-- statement:
--   Definitions and structural lemmas for Dens Exact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/DensExact.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.L2.SG.DensExact
def densProd (q : ℕ) (η : ℝ) (n m c : ℕ) : ℝ :=
  ∏ i ∈ Icc (n + 1 - (m + c)) n, (1 - η ^ i * ((q : ℝ) ^ i)⁻¹)
def countInert (K L : Type) [Fintype K] [Field L] (n m : ℕ) (Ph : Matrix (Fin n) (Fin n) L)
    (Gm : Matrix (Fin m) (Fin m) L) : ℕ :=
  {X : Fin m → Fin n → L | LinearIndependent L X ∧
      ∀ i j, ∑ k, ∑ l, X i k * Ph k l * X j l ^ Fintype.card K = Gm i j}.ncard
def countSplit (K : Type) [Field K] (n m : ℕ) (Ph : Matrix (Fin n) (Fin n) K)
    (Gm : Matrix (Fin m) (Fin m) K) : ℕ :=
  {XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) | LinearIndependent K XY.1 ∧
      LinearIndependent K XY.2 ∧ ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph k l * XY.2 j l = Gm i j}.ncard
def DensExactInert : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (n m : ℕ) (Ph : Matrix (Fin n) (Fin n) L) (Gm : Matrix (Fin m) (Fin m) L),
      IsUnit Ph.det → (∀ k l, Ph l k = Ph k l ^ Fintype.card K) →
      (∀ i j, Gm j i = Gm i j ^ Fintype.card K) →
      (countInert K L n m Ph Gm : ℝ) /
          ((Fintype.card K : ℝ) ^ (2 * n * m) / (Fintype.card K : ℝ) ^ (m ^ 2)) =
        densProd (Fintype.card K) (-1) n m (m - Gm.rank)
def DensExactSplit : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (n m : ℕ) (Ph : Matrix (Fin n) (Fin n) K)
    (Gm : Matrix (Fin m) (Fin m) K), IsUnit Ph.det →
      (countSplit K n m Ph Gm : ℝ) /
          ((Fintype.card K : ℝ) ^ (2 * n * m) / (Fintype.card K : ℝ) ^ (m ^ 2)) =
        densProd (Fintype.card K) 1 n m (m - Gm.rank)
def DensExact : Prop := DensExactInert ∧ DensExactSplit
def DensInertDisplay : Prop :=
  ∀ (q n m c : ℕ), 0 < q → c ≤ m → m + c ≤ n →
    (∏ j ∈ Icc (n - m + c + 1) n, (1 - ((-(q : ℝ)) ^ j)⁻¹)) *
        (∏ i ∈ range c, ((1 - (-1 : ℝ) ^ (n - m + c - 2 * i) * ((q : ℝ) ^ (n - m + c - 2 * i))⁻¹) *
          (1 + (-1 : ℝ) ^ (n - m + c - 2 * i) * ((q : ℝ) ^ (n - m + c - 2 * i - 1))⁻¹))) =
      densProd q (-1) n m c
def DensSplitDisplay : Prop :=
  ∀ (q n m c : ℕ), 0 < q → m + c ≤ n →
    (∏ i ∈ range m, (1 - ((q : ℝ) ^ (n - i))⁻¹)) *
        (∏ i ∈ range c, (1 - ((q : ℝ) ^ (n - m - i))⁻¹)) =
      densProd q 1 n m c
end Formalism.L2.SG.DensExact


