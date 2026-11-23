-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:53.519029+00:00
-- url     : https://prove2.me/theorems/293a3e57-f071-4926-9ee5-c3875637cefc
-- title:
--   Skew Adjoint Casimir Spectral
-- statement:
--   Definitions and structural lemmas for Skew Adjoint Casimir Spectral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace GlobalTheory.CompanionTheory.AnalyticWord
variable {V H : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type}
def word (Z : ι → Module.End ℂ V) (l : List ι) : Module.End ℂ V := (l.map Z).prod
def bnd [Finite ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V) {m : ℕ} (y : Fin m → V) (k : ℕ) : ℝ :=
  (((List.finite_length_eq ι k).toFinset ×ˢ (univ : Finset (Fin m))).sup
    fun p => ‖j (word Z p.1 (y p.2))‖₊ : NNReal)
section Bnd
variable [Finite ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V) {m : ℕ} (y : Fin m → V)
end Bnd
section Main
variable [Fintype ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V) {m : ℕ} (y : Fin m → V)
  (S Ω : Module.End ℂ V) (K : Finset ι) (c : ι → ι → ι → ℂ) (d o : Fin m → Fin m → ℂ)
def c0 : ℝ := 2 * ∑ i, ∑ κ ∈ K, ∑ n, ‖c κ i n‖
def tot (a : Fin m → Fin m → ℂ) : ℝ := ∑ e, ∑ f, ‖a e f‖
end Main
end GlobalTheory.CompanionTheory.AnalyticWord


