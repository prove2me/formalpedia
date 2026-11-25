-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MahlerCompactness
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MahlerCompactness
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T13:53:14.193528+00:00
-- url     : https://prove2.me/theorems/d2bdf83b-9173-507a-9a79-b37a0155870e
-- title:
--   Mahler Compactness
-- statement:
--   Definitions and structural lemmas for Mahler Compactness, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MahlerCompactness.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.FlagMahler
open ReciprocityTheory.ChartRestriction.G.FD NumberField Module
open Matrix hiding col gram
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
section
open Complex
def Kset (R : ℝ) : Set (Frame X.Ψ r) :=
  {w | ∀ τ : X.Ψ, gram τ.1 X.Gm (mat w τ) = diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ∧
    ∀ a c, ‖w τ a c‖ ≤ R}
end
noncomputable def bound {ι : Type} [Fintype ι] (C : ℝ) (g : Basis ι ℤ X.Λ) (s : GL (Fin r) E) : ℝ :=
  ∑ τ : X.Ψ, ∑ l : Fin r, ∑ k : Fin r, ‖(X.Gm.map τ.1)⁻¹ k l‖ *
    ∑ i, ‖(((RealPlaceEmbeddings.qb X g).repr ((s : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single k 1) i : ℚ) : ℂ)‖ *
      (1 + |C| / X.c τ)
end GlobalTheory.FlagMahler


