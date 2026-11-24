-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:28:04.390173+00:00
-- url     : https://prove2.me/theorems/882e6ebd-70c8-4bf3-8f5f-137b1a3e80ba
-- title:
--   Orbital Integral Ae Convergence Continuity
-- statement:
--   Definitions and structural lemmas for Orbital Integral Ae Convergence Continuity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section common
variable {k r : ℕ}
theorem sf {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance
def invM (x : Mt k r) : Mt k r := ((Matrix.of x : Mat k r)⁻¹ : Mat k r)
def mulM (x y : Mt k r) : Mt k r := Matrix.of x * Matrix.of y
end common
section setting
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
theorem sfG (D : RealPlaceData k r Wp Wq) : SigmaFinite D.μG := by
  exact sf D.haarG
theorem sfW (D : RealPlaceData k r Wp Wq) : SigmaFinite D.μW := by
  first | exact sf D.haarW | exact sf D.haarU | exact sf D.haarUW
theorem sfN (D : RealPlaceData k r Wp Wq) : SigmaFinite D.μN := by
  first | exact sf D.haarN | exact sf D.haarNN
theorem sfW' (D : RealPlaceData k r Wp Wq) : SigmaFinite D.μW' := by
  first | exact sf D.haarW' | exact sf D.haarU' | exact sf D.haarUW'
attribute [local instance] sfG sfW sfN sfW'
theorem sfSS (D : RealPlaceData k r Wp Wq) : SigmaFinite D.μSS := by
  show SigmaFinite ((D.μW.prod D.μN).prod (D.μW'.prod D.μN))
  infer_instance
attribute [local instance] sfSS
def Q0 (D : RealPlaceData k r Wp Wq) : Set ((Fin r → ℂ) × ℂ) :=
  {q | (∀ a, q.1 a ≠ 0) ∧ Tz k r D.z * Tz k r D.z' < Complex.normSq q.2}
def gqF (D : RealPlaceData k r Wp Wq) (q : (Fin r → ℂ) × ℂ) : Mt k r := gq D q
def gqM (D : RealPlaceData k r Wp Wq) (q : (Fin r → ℂ) × ℂ) : Mt k r :=
  (Q0 D).indicator (gqF D) q
theorem measurable_bcWeight (T T' : ℝ) : Measurable (bcWeight k r T T') := by
  show Measurable fun p : (Fin r → ℂ) × ℂ => if T * T' ≤ Complex.normSq p.2 then
    (∏ a : Fin r, ‖p.1 a‖ ^ (2 * (Mdim k r a - 2))) * (Complex.normSq p.2 - T * T') ^ (k - 1) else 0
  have hn : Measurable fun p : (Fin r → ℂ) × ℂ => Complex.normSq p.2 :=
    Complex.continuous_normSq.measurable.comp measurable_snd
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le measurable_const hn
  · first
      | exact (Finset.measurable_prod _ fun a _ => ((measurable_pi_apply a).comp measurable_fst).norm.pow_const _).mul
          ((hn.sub_const _).pow_const _)
      | fun_prop
      | measurability
end setting
section fd
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS
theorem properFD (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] :
    ProperSpace W := by
  infer_instance
attribute [local instance] properFD
def piM (D : RealPlaceData k r Wp Wq) : Mt k r → (Wp →L[ℂ] Wp) :=
  {x : Mt k r | Matrix.of x ∈ UWset k r D.z}.indicator fun x => D.π (Matrix.of x)
def piM' (D : RealPlaceData k r Wp Wq) : Mt k r → (Wq →L[ℂ] Wq) :=
  {x : Mt k r | Matrix.of x ∈ UWset k r D.z'}.indicator fun x => D.π' (Matrix.of x)
def FM (F : Mat k r → (Wq →L[ℂ] Wp)) : Mt k r → (Wq →L[ℂ] Wp) :=
  {x : Mt k r | Matrix.of x ∈ GV k r}.indicator fun x => F (Matrix.of x)
def sgsM (p : SS k r) (x : Mt k r) : Mt k r := sgs p (Matrix.of x)
def RM (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) (x : Mt k r) : Wq →L[ℂ] Wp :=
  (piM D p.1.1).comp ((FM F (sgsM p x)).comp (piM' D (invM p.2.1)))
def hsL : (Wq →L[ℂ] Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  LinearMap.toContinuousLinearMap
    { toFun := hsVec
      map_add' := fun A B => by ext i; simp [hsVec]
      map_smul' := fun a A => by ext i; simp [hsVec] }
def JM (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (τ : ℝ × ℝ) (q : (Fin r → ℂ) × ℂ) :
    Wq →L[ℂ] Wp := ∫ p, xiTau D τ p • RM D F p (gqM D q) ∂D.μSS
def KM (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) (x : Mt k r) : ℂ :=
  hsInner (RM D F p x) (FM F x)
def Om (D : RealPlaceData k r Wp Wq) (w₁ w₂ : ℝ → ℝ) (p : SS k r) : ℂ :=
  om w₁ (lam k r D.z (Matrix.of p.1.2)) * om w₂ (-lam k r D.z' (Matrix.of p.2.2))
def PhiM (D : RealPlaceData k r Wp Wq) (a : ((Fin r → ℂ) × ℂ) × SS k r) : Mt k r := sgsM a.2 (gqM D a.1)
def nuQ (D : RealPlaceData k r Wp Wq) : Measure ((Fin r → ℂ) × ℂ) :=
  volume.withDensity fun q => ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q)
def GM (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (w₁ w₂ : ℝ → ℝ) (x : Mt k r) : ℂ :=
  ∫ p, Om D w₁ w₂ p * KM D F p x ∂D.μSS
def tr (p' p : SS k r) : SS k r :=
  ((lmulM (Matrix.of p'.1.1) p.1.1, lmulM (Matrix.of p'.1.2) (conjM (Matrix.of p'.1.1) p.1.2)),
   (lmulM (Matrix.of p'.2.1) p.2.1, lmulM (Matrix.of p'.2.2) (conjM (Matrix.of p'.2.1) p.2.2)))
end fd
section dil
variable {k r : ℕ}
def d_dg (k r : ℕ) (t : ℝ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then ((t ^ (r - i.val) : ℝ) : ℂ)
    else if i.val ≤ r + k then 1 else (((t ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ)
theorem d_aDil_eq (t : ℝ) : aDil k r t = Matrix.diagonal (d_dg k r t) := rfl
theorem d_isUnit_aDil (t : ℝ) (ht : t ≠ 0) : IsUnit (aDil k r t).det := by
  rw [d_aDil_eq, Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  unfold d_dg
  split_ifs <;> simp [ht]
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
def d_dilE (t : ℝ × ℝ) (h1 : t.1 ≠ 0) (h2 : t.2 ≠ 0) : SS k r ≃ᵐ SS k r :=
  ((MeasurableEquiv.refl _).prodCongr (BesselUnitaryEquiv.conjE (aDil k r t.1) (d_isUnit_aDil t.1 h1))).prodCongr
    ((MeasurableEquiv.refl _).prodCongr (BesselUnitaryEquiv.conjE (aDil k r t.2) (d_isUnit_aDil t.2 h2)))
def d_S (r : ℕ) (s : ℝ) (q : (Fin r → ℂ) × ℂ) : (Fin r → ℂ) × ℂ :=
  (fun a => ((s ^ (r - a.val) : ℝ) : ℂ) * q.1 a, q.2)
def halfDimensionBlockSummand (k r : ℕ) : ℕ := ∑ a : Fin r, (r - a.val) * (2 * (Mdim k r a - 2))
def halfDimensionRankTwoSummand (r : ℕ) : ℕ := ∑ a : Fin r, (r - a.val) * 2
end dil
section jc
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
def jc_E (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (q : (Fin r → ℂ) × ℂ) : ℝ≥0∞ :=
  ∫⁻ p, ‖FM F (sgsM p (gqM D q))‖ₑ ∂D.μSS
end jc
section alg
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
end alg
section u12
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
set_option maxHeartbeats 800000 in

theorem sfNu (D : RealPlaceData k r Wp Wq) : SigmaFinite (nuQ D) := by
  unfold nuQ
  first
    | exact SigmaFinite.withDensity_ofReal _
    | exact SigmaFinite.withDensity_ofReal (measurable_bcWeight _ _)
    | infer_instance
def u_fX (z : Fin (2 * r + k + 1) → ℂ) (Ξ : Mat k r → NNReal) (p : Mt k r × Mt k r) : ℝ≥0∞ :=
  Ξ (Matrix.of p.2 * Matrix.of p.1) * ENNReal.ofReal ((1 + |lam k r z (Matrix.of p.2)|) ^ (-(2 : ℝ)))
end u12
section abstractFubini
end abstractFubini
section u3
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
end u3
section abstractFinal
end abstractFinal
section u4
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
attribute [local instance] sfNu
end u4
end Formalism.FourierDecayAlt.P.B7
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


