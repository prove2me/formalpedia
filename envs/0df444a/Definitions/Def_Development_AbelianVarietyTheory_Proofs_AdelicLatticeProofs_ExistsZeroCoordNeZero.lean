-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:43.729794+00:00
-- url     : https://prove2.me/theorems/c79527aa-737f-4a4f-be0f-403977ac2962
-- title:
--   Exists Zero Coord Ne Zero
-- statement:
--   Definitions and structural lemmas for Exists Zero Coord Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroCoordNeZero.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
namespace GlobalTheory.LocalQuad
namespace HermClass
section Congr
variable {E : Type*} [Field E] {c : E →+* E} {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]
def Congr (c : E →+* E) (G G' : Matrix n n E) : Prop :=
  ∃ P : Matrix n n E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map c
end Congr
def Isotropy : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (a : ι → F),
    5 ≤ Fintype.card ι → (∀ i, a i ≠ 0) → (∀ σ : F →+* ℝ, ∃ i j, σ (a i) < 0 ∧ 0 < σ (a j)) →
    ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable def posCount (τ : E →+* ℂ) {r : ℕ} (g : Fin r → E) : ℕ :=
  (Finset.univ.filter fun k => 0 < (τ (g k)).re).card
end HermClass
end GlobalTheory.LocalQuad


