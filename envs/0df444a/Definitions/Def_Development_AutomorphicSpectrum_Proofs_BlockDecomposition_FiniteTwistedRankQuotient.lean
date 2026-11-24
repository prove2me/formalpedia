-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:34:41.306518+00:00
-- url     : https://prove2.me/theorems/7d3bbd0d-503d-45d6-882a-c2a30c93dfde
-- title:
--   Finite Twisted Rank Quotient
-- statement:
--   Definitions and structural lemmas for Finite Twisted Rank Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteTwistedRankQuotient.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
noncomputable section
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
section Matrices
variable {k a c d : Type} [Field k] [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
end Matrices
section Orbit
variable {H X : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace X] [MulAction H X]
abbrev orb (N : Subgroup H) (x₀ : X) : Set X := (fun n : H => n • x₀) '' (N : Set H)
def IsLevel (K N : Subgroup H) : Prop :=
  IsOpen (N : Set H) ∧ N ≤ K ∧ ∀ κ ∈ K, ∀ n ∈ N, κ * n * κ⁻¹ ∈ N
def Reached (ρ : Representation ℂ H (SB X)) (K : Subgroup H) (x₀ : X) (f : SB X) : Prop :=
  ∃ N : Subgroup H, IsLevel K N ∧ ∃ v : SB X, (∀ x, v.1 x = (orb N x₀).indicator (fun _ => (1 : ℂ)) x) ∧
    f ∈ Submodule.span ℂ (Set.range fun g : H => ρ g v)
variable [T2Space X] [ContinuousSMul H X]
end Orbit
section Stratum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a c : Type} [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
@[reducible] def rMul (κ : ℕ) : MulAction (GL a k) (RankIn k a c {κ}) where
  smul g x := rAct {κ} x g⁻¹
  one_smul x := by
    show rAct {κ} x 1⁻¹ = x
    rw [inv_one, rAct_one]
  mul_smul g h x := by
    show rAct {κ} x (g * h)⁻¹ = rAct {κ} (rAct {κ} x h⁻¹) g⁻¹
    rw [_root_.mul_inv_rev, rAct_mul]
end Stratum
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank


