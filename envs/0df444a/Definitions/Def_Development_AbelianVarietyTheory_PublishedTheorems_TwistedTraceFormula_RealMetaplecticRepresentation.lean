-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:49.972379+00:00
-- url     : https://prove2.me/theorems/7ae60624-007f-4695-af1e-d31504f14451
-- title:
--   Real Metaplectic Representation
-- statement:
--   Definitions and structural lemmas for Real Metaplectic Representation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff
namespace GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
abbrev L2 (l : Type) [Fintype l] : Type := Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ l))
abbrev Sch (l : Type) [Fintype l] : Type := 𝓢(EuclideanSpace ℝ l, ℂ)
def pPart (w : l ⊕ l → ℝ) : EuclideanSpace ℝ l := WithLp.toLp 2 fun i => w (Sum.inl i)
def qPart (w : l ⊕ l → ℝ) : EuclideanSpace ℝ l := WithLp.toLp 2 fun i => w (Sum.inr i)
def sympl (w w' : l ⊕ l → ℝ) : ℝ := ⟪pPart w, qPart w'⟫ - ⟪qPart w, pPart w'⟫
def phase (w : l ⊕ l → ℝ) (x : EuclideanSpace ℝ l) : ℂ :=
  exp (((2 * π * ⟪qPart w, x⟫ + π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * I)
def rhoFun (w : l ⊕ l → ℝ) (f : EuclideanSpace ℝ l → ℂ) : EuclideanSpace ℝ l → ℂ :=
  fun x => phase w x * f (x + pPart w)
omit [Fintype l] in
theorem pPart_add (w w' : l ⊕ l → ℝ) : pPart (w + w') = pPart w + pPart w' := rfl
omit [Fintype l] in
theorem qPart_add (w w' : l ⊕ l → ℝ) : qPart (w + w') = qPart w + qPart w' := rfl
theorem norm_phase (w : l ⊕ l → ℝ) (x : EuclideanSpace ℝ l) : ‖phase w x‖ = 1 :=
  norm_exp_ofReal_mul_I _
theorem continuous_phase (w : l ⊕ l → ℝ) : Continuous (phase w) := by
  unfold phase
  fun_prop
theorem rhoFun_rhoFun (w w' : l ⊕ l → ℝ) (f : EuclideanSpace ℝ l → ℂ) :
    rhoFun w (rhoFun w' f) = exp (((π * sympl w w' : ℝ) : ℂ) * I) • rhoFun (w + w') f := by
  funext x
  simp only [rhoFun, phase, Pi.smul_apply, smul_eq_mul, pPart_add, qPart_add, ← mul_assoc, ← Complex.exp_add,
    add_assoc x]
  congr 2
  rw [← add_mul, ← add_mul, ← ofReal_add, ← ofReal_add]
  congr 2
  simp only [sympl, inner_add_left, inner_add_right, real_inner_comm (pPart w) (qPart w'),
    real_inner_comm (qPart w) (pPart w')]
  ring
theorem rhoFun_zero (f : EuclideanSpace ℝ l → ℂ) : rhoFun 0 f = f := by
  funext x
  have h1 : pPart (0 : l ⊕ l → ℝ) = 0 := rfl
  have h2 : qPart (0 : l ⊕ l → ℝ) = 0 := rfl
  simp [rhoFun, phase, h1, h2]
theorem rhoFun_congr (w : l ⊕ l → ℝ) {f g : EuclideanSpace ℝ l → ℂ} (h : f =ᵐ[volume] g) :
    rhoFun w f =ᵐ[volume] rhoFun w g := by
  filter_upwards [(measurePreserving_add_right volume (pPart w)).quasiMeasurePreserving.ae_eq_comp h] with x hx
  simp only [rhoFun]
  rw [show f (x + pPart w) = g (x + pPart w) from hx]
theorem eLpNorm_rhoFun (w : l ⊕ l → ℝ) (f : L2 l) : eLpNorm (rhoFun w f) 2 volume = eLpNorm f 2 volume := by
  rw [← eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f) (measurePreserving_add_right volume (pPart w))]
  refine eLpNorm_congr_norm_ae (.of_forall fun x => ?_)
  simp [rhoFun, norm_phase]
theorem memLp_rhoFun (w : l ⊕ l → ℝ) (f : L2 l) : MemLp (rhoFun w f) 2 volume :=
  ⟨(continuous_phase w).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable f).comp_measurePreserving (measurePreserving_add_right volume (pPart w))),
    by rw [eLpNorm_rhoFun]; exact Lp.eLpNorm_lt_top f⟩
def rhoIsometry (w : l ⊕ l → ℝ) : L2 l →ₗᵢ[ℂ] L2 l where
  toFun f := (memLp_rhoFun w f).toLp
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ((rhoFun_congr w (Lp.coeFn_add f g)).trans (.of_forall fun x => ?_))
    simp [rhoFun, mul_add]
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ((rhoFun_congr w (Lp.coeFn_smul c f)).trans (.of_forall fun x => ?_))
    simp [rhoFun, mul_left_comm]
  norm_map' f := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Lp.norm_toLp, eLpNorm_rhoFun, Lp.norm_def]
theorem coeFn_rhoIsometry (w : l ⊕ l → ℝ) (f : L2 l) : rhoIsometry w f =ᵐ[volume] rhoFun w f :=
  (memLp_rhoFun w f).coeFn_toLp
theorem rhoIsometry_rhoIsometry (w w' : l ⊕ l → ℝ) (f : L2 l) :
    rhoIsometry w (rhoIsometry w' f) = exp (((π * sympl w w' : ℝ) : ℂ) * I) • rhoIsometry (w + w') f := by
  refine Lp.ext ((coeFn_rhoIsometry _ _).trans ((rhoFun_congr w (coeFn_rhoIsometry _ _)).trans ?_))
  rw [rhoFun_rhoFun]
  filter_upwards [Lp.coeFn_smul (exp (((π * sympl w w' : ℝ) : ℂ) * I)) (rhoIsometry (w + w') f),
    coeFn_rhoIsometry (w + w') f] with x h1 h2
  rw [h1, Pi.smul_apply, Pi.smul_apply, h2]
theorem rhoIsometry_zero (f : L2 l) : rhoIsometry 0 f = f :=
  Lp.ext ((coeFn_rhoIsometry _ _).trans (by rw [rhoFun_zero]))
def rho (w : l ⊕ l → ℝ) : L2 l ≃ₗᵢ[ℂ] L2 l :=
  LinearIsometryEquiv.ofSurjective (rhoIsometry w) fun f =>
    ⟨(exp (((π * sympl w (-w) : ℝ) : ℂ) * I))⁻¹ • rhoIsometry (-w) f, by
      rw [map_smul, rhoIsometry_rhoIsometry, add_neg_cancel, rhoIsometry_zero, inv_smul_smul₀ (exp_ne_zero _)]⟩
def dRho (w : l ⊕ l → ℝ) : Sch l →L[ℂ] Sch l :=
  lineDerivOpCLM ℂ (Sch l) (pPart w) +
    (2 * π * I : ℂ) • smulLeftCLM ℂ fun x : EuclideanSpace ℝ l => ((⟪qPart w, x⟫ : ℝ) : ℂ)
variable [DecidableEq l]
def quad (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) : Sch l →L[ℂ] Sch l :=
  (4 * π * I : ℂ)⁻¹ • ∑ a, ∑ b, (((X * Matrix.J l ℝ) a b / 2 : ℝ) : ℂ) •
    (dRho (Pi.single a 1) * dRho (Pi.single b 1) + dRho (Pi.single b 1) * dRho (Pi.single a 1))
end GlobalTheory.RealWeil
namespace GlobalTheory.Published
open GlobalTheory.RealWeil
def RealMetaplecticRepresentation : Prop :=
  ∀ (l : Type) [Fintype l] [DecidableEq l] [Nonempty l],
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G)
      (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)),
      (IsCoveringMap pr ∧ Function.Surjective pr ∧
        ∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧
      (∀ f : L2 l, Continuous fun g => om g f) ∧
      (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
        om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧
      (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧
      (∀ (k : ℕ) (γ : (Fin k → ℝ) → G), Continuous γ →
        (∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b) →
        ∀ f : Sch l, ContDiff ℝ ∞ fun t => om (γ t) (f.toLp 2)) ∧
      (∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∃ γ : ℝ → G, Continuous γ ∧ γ 0 = 1 ∧ (∀ s t, γ (s + t) = γ s * γ t) ∧
        (∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) ∧
        ∀ f : Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2)) ((quad X f).toLp 2) 0)
end GlobalTheory.Published
end


