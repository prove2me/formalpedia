-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:22.312039+00:00
-- url     : https://prove2.me/theorems/528ba9c8-bab5-44c2-9764-595c0aa2ac2e
-- title:
--   Gram Determinant Real
-- statement:
--   Definitions and structural lemmas for Gram Determinant Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
def hL (v : Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun u := hermC τ G u v
  map_add' u u' := by simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a u := by
    simp only [hermC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]
def gramF {n : ℕ} (f : Fin n → Fin r → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => hermC τ G (f a) (f b)
section Proj
variable {n : ℕ} (f : Fin n → Fin r → ℂ) (e : Fin r → ℂ)
def cv : Fin n → ℂ := fun a => hermC τ G e (f a)
def yv : Fin n → ℂ := Matrix.vecMul (cv τ G f e) (gramF τ G f)⁻¹
def pv : Fin r → ℂ := ∑ b, yv τ G f e b • f b
def mt : ℂ := ∑ a, ∑ b, cv τ G f e a * (gramF τ G f)⁻¹ a b * conj (cv τ G f e b)
end Proj
section StepDef
variable {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ)
def dv : Fin r → ℂ := pv τ G f e - pv τ G (fun a : Fin n => f a.castSucc) e
end StepDef
variable {τ G} (hG : ∀ a b, τ (G b a) = conj (τ (G a b)))
include hG
section Step
variable {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ)
end Step
end
end ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal


