-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsBoundOrthonormalFrame
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsBoundOrthonormalFrame
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:18:31.752221+00:00
-- url     : https://prove2.me/theorems/5e22bcdc-0ea6-422d-a71c-dea81f866b21
-- title:
--   Exists Bound Orthonormal Frame
-- statement:
--   Definitions and structural lemmas for Exists Bound Orthonormal Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsBoundOrthonormalFrame.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeightedSupDriftOnOrthonormalFrames
import Theorems.Thm_GlobalTheory_FlagMahler_Qy_smul_le
import Theorems.Thm_GlobalTheory_FlagMahler_col_map_eq
import Theorems.Thm_GlobalTheory_FlagMahler_comb_bound
import Theorems.Thm_GlobalTheory_FlagMahler_comp_le_Qy
import Theorems.Thm_GlobalTheory_FlagMahler_finite_int_sq
import Theorems.Thm_GlobalTheory_FlagMahler_inv_lact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianLatticeMaps_phi_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianLatticeMaps_phi_phi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_Am_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_Ly_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_Ly_surjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_ipB_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_quad_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealPlaceEmbeddings_linIndR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealPlaceEmbeddings_qb_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealPlaceEmbeddings_span_embV
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


set_option autoImplicit false
namespace GlobalTheory.MixedSignature
open ReciprocityTheory.ChartRestriction.G.FD NumberField Module Complex
open Matrix hiding col gram
open scoped ComplexConjugate
open QuadraticLatticeForms (ip ipB ipB_apply Ly Am Qy Ly_injective Ly_surjective quad_int Am_posDef)
open HermitianLatticeMaps (phi phi_f phi_zsum phi_mem phi_phi smul_coe coe_expand mulQ mulQ_apply)
open GlobalTheory.FlagMahler (col_map_eq inv_lact comp_le_Qy comb_bound Qy_smul_le finite_int_sq)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ}
noncomputable def signInv (p : X.Ψ → ℕ) : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) where
  toFun u τ a := ((sgn (p τ) (a : ℕ) : ℝ) : ℂ) * u τ a
  map_add' u w := by funext τ a; simp [mul_add]
  map_smul' k u := by funext τ a; simp [Complex.real_smul]; ring
def Normal (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ : X.Ψ, (y τ).det ≠ 0 ∧ gram τ.1 G (y τ) = diagonal fun a : Fin r => ((sgn (p τ) (a : ℕ) : ℝ) : ℂ)
section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
noncomputable def traceGram (G : Matrix (Fin r) (Fin r) E) (g : Basis ι ℤ X.Λ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∑ τ, X.c τ * (τ.1 (herm G (g i : Fin r → E) (g j : Fin r → E))).re
noncomputable def frameBasis {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : Normal X G p y) (g : Basis ι ℤ X.Λ) :
    Basis ι ℝ (X.Ψ → Fin r → ℂ) :=
  (Basis.mk (RealPlaceEmbeddings.linIndR X g) (RealPlaceEmbeddings.span_embV X g).ge).map
    (LinearEquiv.ofBijective (Ly X y) ⟨Ly_injective X y fun τ => (hy τ).1,
      Ly_surjective X y fun τ => (hy τ).1⟩)
noncomputable def basisType (G : Matrix (Fin r) (Fin r) E) (f : Basis ι ℤ X.Λ) :
    (ι → ι → E) × (Free.ChooseBasisIndex ℤ (𝓞 E) → ι → ι → ℤ) :=
  (fun i j => herm G (f i : Fin r → E) (f j : Fin r → E),
    fun k i j => f.repr (RingOfIntegers.basis E k • f i) j)
noncomputable def hermLeft (G : Matrix (Fin r) (Fin r) E) (y : Fin r → E) : (Fin r → E) →ₗ[ℚ] E where
  toFun x := herm G x y
  map_add' x x' := by simp [herm, add_mul, Finset.sum_add_distrib]
  map_smul' q x := by
    simp only [herm, Pi.smul_apply, Rat.smul_def, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
noncomputable def hermRight (G : Matrix (Fin r) (Fin r) E) (x : Fin r → E) : (Fin r → E) →ₗ[ℚ] E where
  toFun y := herm G x y
  map_add' y y' := by simp [herm, cc, mul_add, Finset.sum_add_distrib]
  map_smul' q y := by
    simp only [herm, cc, Pi.smul_apply, Rat.smul_def, RingHom.id_apply, Finset.mul_sum, map_mul,
      map_ratCast]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
variable {f f' : Basis ι ℤ X.Λ}
theorem transfer_integralBasis (h : basisType X G f = basisType X G f') (k : Free.ChooseBasisIndex ℤ (𝓞 E)) (i : ι) :
    phi X f f' ((RingOfIntegers.basis E k : E) • (f i : Fin r → E)) =
      (RingOfIntegers.basis E k : E) • (f' i : Fin r → E) := by
  have h2 : ∀ j, f.repr (RingOfIntegers.basis E k • f i) j = f'.repr (RingOfIntegers.basis E k • f' i) j :=
    fun j => congrFun (congrFun (congrFun (congrArg Prod.snd h) k) i) j
  rw [← smul_coe, ← smul_coe, coe_expand X f, coe_expand X f', phi_zsum]
  simp only [h2]
theorem transfer_smul (h : basisType X G f = basisType X G f') (α : E) (v : Fin r → E) :
    phi X f f' (α • v) = α • phi X f f' v := by
  have hk : ∀ k, (phi X f f').comp (mulQ (RingOfIntegers.basis E k : E)) =
      (mulQ (RingOfIntegers.basis E k : E)).comp (phi X f f') := by
    intro k
    refine (RealPlaceEmbeddings.qb X f).ext fun i => ?_
    simp only [LinearMap.comp_apply, mulQ_apply, RealPlaceEmbeddings.qb_apply]
    rw [transfer_integralBasis X h k i, phi_f]
  have hα : α = ∑ k, (integralBasis E).repr α k • (RingOfIntegers.basis E k : E) := by
    conv_lhs => rw [← (integralBasis E).sum_repr α]
    simp [integralBasis_apply]
  rw [hα, Finset.sum_smul, Finset.sum_smul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_assoc, smul_assoc, map_smul]
  congr 1
  exact LinearMap.congr_fun (hk k) v
noncomputable def transferE (h : basisType X G f = basisType X G f') : (Fin r → E) →ₗ[E] (Fin r → E) where
  toFun := phi X f f'
  map_add' := map_add _
  map_smul' := transfer_smul X h
end
noncomputable def bound (G : Matrix (Fin r) (Fin r) E) {ι : Type} [Fintype ι] (C : ℝ) (g : Basis ι ℤ X.Λ) : ℝ :=
  ∑ τ : X.Ψ, ∑ l : Fin r, ∑ k : Fin r, ‖(G.map τ.1)⁻¹ k l‖ *
    ∑ i, ‖(((RealPlaceEmbeddings.qb X g).repr (Pi.single k 1) i : ℚ) : ℂ)‖ *
      (1 + |C| / X.c τ)
end GlobalTheory.MixedSignature


