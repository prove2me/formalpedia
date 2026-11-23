-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_AdmissibleHermitianColumns
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_AdmissibleHermitianColumns
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:29.666796+00:00
-- url     : https://prove2.me/theorems/7254fe0c-fe68-433e-b14c-e0cc66231c7d
-- title:
--   Admissible Hermitian Columns
-- statement:
--   Definitions and structural lemmas for Admissible Hermitian Columns, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/AdmissibleHermitianColumns.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
section gram
variable (X : Data E r)
def hv (ξ : Fin r → E) (τ : X.Ψ) (M : Matrix (Fin r) (Fin r) ℂ) : Fin r → ℂ :=
  fun a => hermC τ.1 X.Gm (col M a) (Data.emb τ.1 ξ)
def rk1 (ξ : Fin r → E) (τ : X.Ψ) (M : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  vecMulVec (hv X ξ τ M) (fun b => conj (hv X ξ τ M b))
def admissibleImaginary (ξ : Fin r → E) (x : Frame X.Ψ r) : Set (X.Ψ → ℝ) :=
  {y | ∀ τ : X.Ψ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i *
    (lminor (gram τ.1 X.Gm (mat x τ) + ((2 * X.c τ * y τ : ℝ) : ℂ) • rk1 X ξ τ (mat x τ)) i).re}
end gram
section affine
end affine
section adm
variable (X : Data E r)
end adm
end ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns


