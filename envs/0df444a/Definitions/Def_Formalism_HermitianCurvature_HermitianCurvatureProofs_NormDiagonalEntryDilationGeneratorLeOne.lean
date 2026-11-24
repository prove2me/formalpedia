-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:28:17.763047+00:00
-- url     : https://prove2.me/theorems/47201628-c8f7-4afe-bf7f-53a408e40212
-- title:
--   Norm Diagonal Entry Dilation Generator Le One
-- statement:
--   Definitions and structural lemmas for Norm Diagonal Entry Dilation Generator Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
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
namespace Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def X0 (k r : ℕ) : Mat k r := Matrix.diagonal fun i =>
  if i.val < r then ((((r - i.val : ℕ) : ℝ) / ((r : ℝ) + 1) : ℝ) : ℂ)
  else if i.val ≤ r + k then 0 else ((-(((i.val - (r + k) : ℕ) : ℝ) / ((r : ℝ) + 1)) : ℝ) : ℂ)
def rr (r : ℕ) : ℝ := (r : ℝ) + 1
section spaces
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def admitted (α c : ℝ) (f : Mat k r → E) : Prop :=
  ContinuousOn f (GV k r) ∧ ∀ g ∈ GV k r, gN g ^ α * ‖f g‖ ≤ c
def DR (f : Mat k r → E) : Prop :=
  ∀ g ∈ GV k r, HasDerivAt (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X0 k r))) (RdV (X0 k r) f g) 0
def DL (f : Mat k r → E) : Prop :=
  ∀ g ∈ GV k r, HasDerivAt (fun s : ℝ => f (NormedSpace.exp (-((s : ℂ) • X0 k r)) * g)) (LdV (X0 k r) f g) 0
abbrev Rr (f : Mat k r → E) : Mat k r → E := RdV (X0 k r) f
abbrev Ll (f : Mat k r → E) : Mat k r → E := LdV (X0 k r) f
def AdmW (α c : ℝ) (n m : ℕ) (f : Mat k r → E) : Prop :=
  (∀ j ≤ n, ∀ i ≤ m, admitted α c (Ll^[i] (Rr^[j] f))) ∧ (∀ j < n, DR (Rr^[j] f)) ∧
    ∀ j ≤ n, ∀ i < m, DL (Ll^[i] (Rr^[j] f))
end spaces
def gam (ρ : ℝ) (W : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun t => W t - iteratedDeriv 2 W t
  | 1 => fun t => 2 * ρ * deriv W t / t - ρ * W t / t ^ 2
  | _ => fun t => -(ρ ^ 2 * W t / t ^ 2)
section setting
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def Wd (D : RealPlaceData k r Wp Wq) (t : ℝ) : ℝ := D.χ t * t ^ kap k r
def QL (D : RealPlaceData k r Wp Wq) (p : SS k r) :
    ℕ → (Mat k r → (Wq →L[ℂ] Wp)) → (Mat k r → (Wq →L[ℂ] Wp)) → ℝ → ℝ → ℂ
  | 0, A, B => fun x y => Ph D A B (dilation₂ (x, y) p)
  | m + 1, A, B => fun x y => QL D p m (Ll A) B x y + QL D p m A (Ll B) x y
def QR (D : RealPlaceData k r Wp Wq) (p : SS k r) (m : ℕ) :
    ℕ → (Mat k r → (Wq →L[ℂ] Wp)) → (Mat k r → (Wq →L[ℂ] Wp)) → ℝ → ℝ → ℂ
  | 0, A, B => QL D p m A B
  | l + 1, A, B => fun x y => QR D p m l (Rr A) B x y + QR D p m l A (Rr B) x y
structure Hyp (D : RealPlaceData k r Wp Wq) (Ξ : Mat k r → NNReal) (α : ℝ) : Prop where
  α_nonneg : 0 ≤ α
  coef : CoefBound D Ξ α
  xi : XiInt D Ξ 2
  T0 : ∃ T : Wq →L[ℂ] Wp, ‖T‖ = 1
  dilN : DilN
  dilUW : DilUW
def XX (Ξ : Mat k r → NNReal) (p : SS k r) : ℝ :=
  (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) * (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ)
def Ef (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) (t : ℝ × ℝ) : ℂ :=
  ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
    ((gam (rr r) (Wd D) m t.1 * gam (rr r) (Wd D) l t.2 : ℝ) : ℂ) * QR D p m l F F' t.1 t.2
end setting
section basic
variable {k r : ℕ}
def dilationGeneratorDiagonal (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then ((((r - i.val : ℕ) : ℝ) / ((r : ℝ) + 1) : ℝ) : ℂ)
  else if i.val ≤ r + k then 0 else ((-(((i.val - (r + k) : ℕ) : ℝ) / ((r : ℝ) + 1)) : ℝ) : ℂ)
def hilbertSchmidtNormSq (g : Mat k r) : ℝ := ∑ i, ∑ j, Complex.normSq (g i j)
end basic
section basic
variable {k r : ℕ}
end basic
section setting
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
end setting
section calcG
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end calcG
section hs
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def Sd (D : RealPlaceData k r Wp Wq) (p : SS k r) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp (D.π (Matrix.of p.1.1))).comp
    ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (D.π' (Matrix.of p.2.1)⁻¹))
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
theorem continuous_right_multiplication_map (a : Mat k r) : Continuous (rmulF a) := by
  unfold rmulF
  exact continuous_id.matrix_mul continuous_const
def rightMulMeasurableEquiv (a : Mat k r) (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun := rmulF a
  invFun := rmulF a⁻¹
  left_inv x := by
    have : Matrix.of x * a * a⁻¹ = Matrix.of x := Matrix.mul_nonsing_inv_cancel_right _ _ ha
    exact this
  right_inv x := by
    have : Matrix.of x * a⁻¹ * a = Matrix.of x := Matrix.nonsing_inv_mul_cancel_right _ _ ha
    exact this
  measurable_toFun := (continuous_right_multiplication_map a).measurable
  measurable_invFun := (continuous_right_multiplication_map a⁻¹).measurable
def normProductOfPair (p : SS k r) : ℝ :=
  gN (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r) * gN (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r)⁻¹
end hs
section phd
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
end phd
section abs
def regularised_kernel_product (ρ : ℝ) (W : ℝ → ℝ) (q : ℕ → ℕ → ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  (W x : ℂ) * ((gam ρ W 0 y : ℂ) * q 0 0 x y + (gam ρ W 1 y : ℂ) * q 0 1 x y + (gam ρ W 2 y : ℂ) * q 0 2 x y)
end abs
section wd
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
end wd
section shared
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def phase (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (p : SS k r) (t : ℝ × ℝ) : ℝ :=
  τ.1 * t.1 * lam k r D.z (Matrix.of p.1.2) - τ.2 * t.2 * lam k r D.z' (Matrix.of p.2.2)
def wt (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (p : SS k r) : ℝ :=
  (1 + τ.1 ^ 2 * lam k r D.z (Matrix.of p.1.2) ^ 2)⁻¹ * (1 + τ.2 ^ 2 * lam k r D.z' (Matrix.of p.2.2) ^ 2)⁻¹
def LL (D : RealPlaceData k r Wp Wq) (p : SS k r) : ℝ :=
  (1 + |lam k r D.z (Matrix.of p.1.2)|) ^ (-2 : ℝ) * (1 + |lam k r D.z' (Matrix.of p.2.2)|) ^ (-2 : ℝ)
def Et (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (q : SS k r × (ℝ × ℝ)) : ℂ :=
  Set.indicator ({p | D.inSS p} ×ˢ Quad) (fun q => Ef D F F' q.1 q.2) q
def Bt (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (q : SS k r × (ℝ × ℝ)) : ℂ :=
  Set.indicator ({p | D.inSS p} ×ˢ Quad) (fun q => regBracket D F F' q.1 q.2.1 q.2.2) q
def Gt (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (τ : ℝ × ℝ) (p : SS k r) : ℂ :=
  (wt D τ p : ℂ) * ∫ t : ℝ × ℝ, Et D F F' (p, t) * Complex.exp (Complex.I * (phase D τ p t : ℂ))
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
end shared
section regbound
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
end regbound
section avg1
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
end avg1
section avg2pre
end avg2pre
section avg2
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
end avg2
section avg3
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
def fourierWeightedPhase (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (w₁ w₂ : ℝ → ℝ) (p : SS k r) : ℂ :=
  om w₁ (lam k r D.z (Matrix.of p.1.2)) * om w₂ (-lam k r D.z' (Matrix.of p.2.2)) * Ph D F F' p
end avg3
section avg4
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
def weightedPhaseJointIntegrand (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (w₁ w₂ : ℝ → ℝ)
    (q : SS k r × (ℝ × ℝ)) : ℂ :=
  Bt D F F' q * (om w₁ (q.2.1 * lam k r D.z (Matrix.of q.1.1.2)) *
    om w₂ (-(q.2.2 * lam k r D.z' (Matrix.of q.1.2.2))))
end avg4
section avg5
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
end avg5
section top
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
end top
end Formalism.FourierDecayAlt.P.B6
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


