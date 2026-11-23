-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:37.111546+00:00
-- url     : https://prove2.me/theorems/9239d1f3-acc4-44dd-95cc-87cc672aa435
-- title:
--   Positive Span Matrices
-- statement:
--   Definitions and structural lemmas for Positive Span Matrices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PositiveSpanMatrices.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
def kap {n p : ℕ} (hp : p ≤ n) (a : Fin (n - p)) : Fin n := ⟨p + a, by have := a.isLt; omega⟩
def ext0 {M : Type*} [AddCommMonoid M] {n : ℕ} (F : Fin n → M) (i : ℕ) : M :=
  if h : i < n then F ⟨i, h⟩ else 0
section Ortho
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
abbrev Spos (x : Frame X.Ψ r) (τ : X.Ψ) : Submodule ℂ (Fin r → ℂ) :=
  Submodule.span ℂ (Set.range fun b : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le b))
def Pos (x : Frame X.Ψ r) (τ : X.Ψ) (y : Fin r → ℂ) : ℝ :=
  ∑ b : Fin X.p0, ‖hermC τ.1 X.Gm y (col (mat x τ) (Fin.castLE X.p0_le b))‖ ^ 2
def Neg (x : Frame X.Ψ r) (τ : X.Ψ) (y : Fin r → ℂ) : ℝ :=
  ∑ a : Fin (r - X.p0), ‖hermC τ.1 X.Gm y (col (mat x τ) (kap X.p0_le a))‖ ^ 2
end Ortho
end
end ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices


