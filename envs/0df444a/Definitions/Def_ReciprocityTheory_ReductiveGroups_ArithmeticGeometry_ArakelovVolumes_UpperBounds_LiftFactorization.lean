-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LiftFactorization
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LiftFactorization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:27.781796+00:00
-- url     : https://prove2.me/theorems/a51a025f-bc45-4459-a6e3-e66d62f522f1
-- title:
--   Lift Factorization
-- statement:
--   Definitions and structural lemmas for Lift Factorization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LiftFactorization.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexOrder
noncomputable section
def nD (f p q : ℕ) : ℕ := f * (p * q)
def Zof {f p q : ℕ} (v : V (nD f p q)) (k : Fin f) : Matrix (Fin p) (Fin q) ℂ :=
  Matrix.of fun a b => v (finProdFinEquiv (k, finProdFinEquiv (a, b)))
def Dset (f p q : ℕ) : Set (V (nD f p q)) :=
  {v | ∀ k, (1 - Zof v k * (Zof v k)ᴴ).PosDef}
def rh {f p q : ℕ} (v : V (nD f p q)) : ℝ :=
  -∑ k, Real.log (1 - Zof v k * (Zof v k)ᴴ).det.re
def zPart {f p q N' : ℕ} (v : V (nD f p q + N')) : V (nD f p q) :=
  WithLp.toLp 2 fun j => v (Fin.castAdd N' j)
def tPart {f p q N' : ℕ} (v : V (nD f p q + N')) : V N' :=
  WithLp.toLp 2 fun j => v (Fin.natAdd (nD f p q) j)
def OmSet (f p q N' : ℕ) : Set (V (nD f p q + N')) := {v | zPart v ∈ Dset f p q}
def eOm {f p q N' : ℕ} (v : V (nD f p q + N')) : ℝ :=
  rh (zPart v) + Real.log (1 + ‖tPart v‖ ^ 2)
def ExhaustStatement : Prop :=
  ∀ f p q N' : ℕ, ∃ S : EtaleStein (nD f p q + N') (OmSet f p q N'),
    S.z = Subtype.val ∧ S.e = fun y => eOm y.1
def RhGradStatement : Prop :=
  ∀ f p q : ℕ, ∀ v ∈ Dset f p q, ∀ ξ : Fin (nD f p q) → ℂ,
    Complex.normSq (∑ j, wd (nD f p q) j (fun w => ((rh w : ℝ) : ℂ)) v * ξ j) ≤
      ((f * min p q : ℕ) : ℝ) * (leviV (nD f p q) (fun w => ((rh w : ℝ) : ℂ)) v ξ).re
def PolyGrowthStatement : Prop :=
  ∀ (D m : ℕ) (P Q : MvPolynomial (Fin D) ℂ), Q ≠ 0 →
    (∃ C : ℝ, ∀ y : Fin D → ℂ, MvPolynomial.eval y Q ≠ 0 →
      ‖MvPolynomial.eval y P / MvPolynomial.eval y Q‖ ≤ C * (1 + ∑ i, ‖y i‖) ^ m) →
    ∃ R : MvPolynomial (Fin D) ℂ, R.totalDegree ≤ m ∧ P = R * Q
end
end ReciprocityTheory.ChartRestriction.G.AR.Up


