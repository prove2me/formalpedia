-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:38.145548+00:00
-- url     : https://prove2.me/theorems/dabdbf45-0949-4eda-ad7c-11f5375b487c
-- title:
--   Positive Minor Units
-- statement:
--   Definitions and structural lemmas for Positive Minor Units, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PositiveMinorUnits.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
def famN (x : Matrix (Fin r) (Fin r) ℂ) (i : ℕ) (hi : i ≤ r) : Fin i → Fin r → ℂ :=
  fun a => col x (Fin.castLE hi a)
def pN (x : Matrix (Fin r) (Fin r) ℂ) (e : Fin r → ℂ) (i : ℕ) : Fin r → ℂ :=
  if h : i ≤ r then pv τ G (famN x i h) e else 0
def mN (x : Matrix (Fin r) (Fin r) ℂ) (e : Fin r → ℂ) (i : ℕ) : ℝ :=
  (hermC τ G (pN τ G x e i) (pN τ G x e i)).re
section Frame
variable {τ G} (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (p0 : ℕ) (hp0 : p0 ≤ r)
  (x : Matrix (Fin r) (Fin r) ℂ) (hx : x.det ≠ 0)
  (hsg : ∀ i (h : i ≤ r), 0 < psgn p0 i * (gramF τ G (famN x i h)).det.re)
  (e : Fin r → ℂ) (he : hermC τ G e e = 0)
include hsg
include hG
end Frame
end
end ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits


