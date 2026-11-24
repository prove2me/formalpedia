-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:06.348751+00:00
-- url     : https://prove2.me/theorems/9159f907-73a7-40fd-b8bf-d771e479c0d1
-- title:
--   Statements Diag R
-- statement:
--   Definitions and structural lemmas for Statements Diag R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsDiagR.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
abbrev ProjectiveLineBundle.Diag {D : ℕ} (S : ProjectiveLineBundle D) : Ideal (MRing S.WIdx) :=
  T.wwIdeal S.x S.δ S.e S.φ (S.a 0) (S.a 0)
section Statements
def DiagDiv.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.DiagDivStatement (Φ := Φ) B e φ δ
def DiagPullI.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ (D : ℕ) (S : ProjectiveLineBundle D) (X : HermLine S.YIdx) (X₀ X₁ : HermLine S.WIdx)
    (L : Fin D → HermLine S.WIdx),
    IsSmoothHerm X → IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ → IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ →
    (∀ j, IsSmoothHerm (L j)) →
    I T.WBlk S.WIdx S.Diag (D + 1) (Fin.snoc L X₀) = I T.WBlk S.WIdx S.Diag (D + 1) (Fin.snoc L X₁)
def ZeroSetNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (s : MRing ι)
    (a : K → ℕ) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g₁ g₂ : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsMultiHomog s a → s ∉ P →
    (∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) s) ≠ 0 → g₁ z = g₂ z) →
    ptsIntegral P φ g₁ = ptsIntegral P φ g₂
end Statements
section Inhabit
end Inhabit
end
end GroundTheory.Heights₂.Heights.Inter


