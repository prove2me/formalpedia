-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:33.996718+00:00
-- url     : https://prove2.me/theorems/9b0bfe43-1fc4-4f76-924a-13cad87bc984
-- title:
--   Unipotent On Hyperbolic Complement
-- statement:
--   Definitions and structural lemmas for Unipotent On Hyperbolic Complement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable section
section herm
variable {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
def hL (y : Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun v := hermC τ G v y
  map_add' u v := hC_add_left τ G u v y
  map_smul' c v := by
    simp only [smul_eq_mul, RingHom.id_apply]
    exact hC_smul_left τ G c v y
def rz (φ : (Fin r → ℂ) →ₗ[ℂ] ℂ) : Fin r → ℂ :=
  fun b => conj (((G.map τ)⁻¹).mulVec (fun a => φ (fun j => if a = j then 1 else 0)) b)
end herm
namespace Data
variable {r : ℕ} (X : Data E r)
def Jp (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) : Fin r → ℂ := (2 : ℂ) • X.ppos x τ v - v
section perTau
variable (x : Frame X.Ψ r) (τ : X.Ψ) (e : Fin r → ℂ) (δ : (Fin r → ℂ) →ₗ[ℂ] ℂ)
def d2q : ℂ := X.Hf x τ e e
def d2b : (Fin r → ℂ) →ₗ[ℂ] ℂ := (X.d2q x τ e)⁻¹ • hL τ.1 X.Gm e
def d2a : (Fin r → ℂ) →ₗ[ℂ] ℂ := (X.d2q x τ e)⁻¹ • hL τ.1 X.Gm (X.Jp x τ e)
def d2pi : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
  LinearMap.id - (X.d2a x τ e).smulRight e - (X.d2b x τ e).smulRight (X.Jp x τ e)
def d2z : Fin r → ℂ := rz τ.1 X.Gm ((X.d2q x τ e) • (δ ∘ₗ X.d2pi x τ e))
def d2nL : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
  LinearMap.id + (δ ∘ₗ X.d2pi x τ e - (δ (X.d2z x τ e δ) / 2) • X.d2b x τ e).smulRight e -
    (X.d2b x τ e).smulRight (X.d2z x τ e δ)
def d2n : Matrix (Fin r) (Fin r) ℂ := LinearMap.toMatrix' (X.d2nL x τ e δ)
variable {x τ e}
variable (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0) (hq : X.d2q x τ e ≠ 0)
include hx he hq
end perTau
end Data
end
end ReciprocityTheory.ChartRestriction.G.FD


