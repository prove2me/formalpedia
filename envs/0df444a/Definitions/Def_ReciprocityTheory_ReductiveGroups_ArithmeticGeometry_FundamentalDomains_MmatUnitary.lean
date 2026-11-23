-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatUnitary
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatUnitary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:05.918215+00:00
-- url     : https://prove2.me/theorems/de3edac4-114d-4447-8c79-dac1c6e9d731
-- title:
--   Mmat Unitary
-- statement:
--   Definitions and structural lemmas for Mmat Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MmatUnitary.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpSpanRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (p : ℕ) (f g : Fin n → Fin r → ℂ)
def eps (k : Fin n) : ℂ := if (k : ℕ) < p then 1 else -1
def Mmat : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => (if a = b then 1 else 0) +
    ∑ k, (eps p k * (g k - f k) a) * ∑ m, τ (G b m) * conj (f k m)
variable (hG : ∀ a b, cc (G a b) = G b a)
  (hf : ∀ k l, hermC τ G (f k) (f l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
include hG hf
end
end ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices


