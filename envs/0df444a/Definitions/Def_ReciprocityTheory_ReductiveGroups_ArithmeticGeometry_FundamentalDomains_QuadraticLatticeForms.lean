-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticLatticeForms
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticLatticeForms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:49.258794+00:00
-- url     : https://prove2.me/theorems/347a98fa-6e07-40e4-ba2f-85bdc61110d6
-- title:
--   Quadratic Lattice Forms
-- statement:
--   Definitions and structural lemmas for Quadratic Lattice Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/QuadraticLatticeForms.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_DetToMatrixSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace QuadraticLatticeForms
open Matrix NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
noncomputable def ip (u w : X.Ψ → Fin r → ℂ) : ℝ := ∑ τ, X.c τ * (∑ a, u τ a * conj (w τ a)).re
theorem ip_add_left (u u' w : X.Ψ → Fin r → ℂ) : ip X (u + u') w = ip X u w + ip X u' w := by
  simp only [ip, Pi.add_apply, add_mul, Finset.sum_add_distrib, Complex.add_re, mul_add]
theorem ip_add_right (u w w' : X.Ψ → Fin r → ℂ) : ip X u (w + w') = ip X u w + ip X u w' := by
  simp only [ip, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, Complex.add_re]
theorem ip_smul_left (k : ℝ) (u w : X.Ψ → Fin r → ℂ) : ip X (k • u) w = k * ip X u w := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h : (∑ a, (k • u) τ a * conj (w τ a)) = (k : ℂ) * ∑ a, u τ a * conj (w τ a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, Complex.real_smul]
    ring
  rw [h, Complex.re_ofReal_mul]
  ring
theorem ip_smul_right (k : ℝ) (u w : X.Ψ → Fin r → ℂ) : ip X u (k • w) = k * ip X u w := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h : (∑ a, u τ a * conj ((k • w) τ a)) = (k : ℂ) * ∑ a, u τ a * conj (w τ a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    ring
  rw [h, Complex.re_ofReal_mul]
  ring
noncomputable def ipB : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (ip X) (ip_add_left X) (ip_smul_left X) (ip_add_right X) (ip_smul_right X)
noncomputable def Ly (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) :
    (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) where
  toFun u τ := (y τ)⁻¹ *ᵥ u τ
  map_add' u w := by funext τ; simp [Matrix.mulVec_add]
  map_smul' k u := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply]
    funext a
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm, Complex.real_smul]
noncomputable def Sg : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) where
  toFun u τ a := ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * u τ a
  map_add' u w := by funext τ a; simp [mul_add]
  map_smul' k u := by funext τ a; simp [Complex.real_smul]; ring
noncomputable def Qy (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) : ℝ :=
  ∑ τ, X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 v) a‖ ^ 2
variable {ι : Type} [Fintype ι] [DecidableEq ι]
noncomputable def Am (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (g : Basis ι ℤ X.Λ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ip X (Ly X y (X.embV (g i : Fin r → E))) (Ly X y (X.embV (g j : Fin r → E)))
noncomputable def Bm (g : Basis ι ℤ X.Λ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∑ τ, X.c τ * (τ.1 (herm X.Gm (g i : Fin r → E) (g j : Fin r → E))).re
end QuadraticLatticeForms
end ReciprocityTheory.ChartRestriction.G.FD


