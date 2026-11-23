-- Prove2me | Definitions.Def_ReciprocityTheory_ReducedBases_ExistsBoundedBasis
-- name    : ReciprocityTheory_ReducedBases_ExistsBoundedBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:51.839823+00:00
-- url     : https://prove2.me/theorems/7720dee9-8d50-4b8c-9eee-0a7b2855c367
-- title:
--   Exists Bounded Basis
-- statement:
--   Definitions and structural lemmas for Exists Bounded Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/ExistsBoundedBasis.lean

import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ReducedBases.T2
open ReciprocityTheory.ReducedBases Matrix
def C1 (d : ℕ) : ℝ := (d : ℝ) * (3 / 2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) / 2 - 1)
def BilinBoundedBasis {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) : Prop :=
  ∀ (i : Fin d) (μ : Fin d → ℤ), |polar A (e i) μ| ≤ (d : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2) * polar A μ μ
def CoordBoundedOnMin {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) : Prop :=
  ∀ (N : ℤ), 1 ≤ N → ∀ α : Fin d → ℤ, IsMinInClass (Q A) N α →
    ∀ i : Fin d, |((e.repr α i : ℤ) : ℝ)| ≤ C1 d * (N : ℝ)
def ExistsBoundedBasis : Prop :=
  ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ), A.PosDef →
    ∃ e : Module.Basis (Fin d) ℤ (Fin d → ℤ), BilinBoundedBasis A e ∧ CoordBoundedOnMin A e
end ReciprocityTheory.ReducedBases.T2
end


