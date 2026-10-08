-- Prove2me | Definitions.Def_OAI_PiExponent_FormalInterpolationPackets
-- name    : OAI_PiExponent_FormalInterpolationPackets
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-07T19:39:53.988761+00:00
-- url     : https://prove2.me/theorems/93cdde3e-6e69-4221-b4dc-f037f29d324d
-- title:
--   Weighted formal logarithmic interpolation packets
-- statement:
--   Let $m$ be the number of logarithmic coordinates. A polynomial $P(Y,X_1,\ldots,X_m)$ has weighted degree at most $H$ when every monomial in its support satisfies
--
--   $$w_0 a_0+\sum_{i=1}^m w_i a_i\le H.$$
--
--   At a center $c\in\mathbb C^m$, its formal logarithmic jet is obtained by the substitutions
--
--   $$Y\mapsto1+t,\qquad X_i\mapsto c_i+u_i+\log(1+t).$$
--
--   For a fixed admissible family $d$, the packet map records the coefficients of these jets at all centers $j r$, with $0\le j<K$, and all exponents in the strict row simplex. It maps weighted polynomials to the same coefficient space as the actual interpolation matrix. The formal logarithm is the infinite power series, rather than the fixed polynomial truncation used by that matrix.
--
--   **Formalization Note.** The formal jet is transcribed from FormalLogJet. The polynomial support bound and coefficient packets use the existing matrix weights and row indices; this is the concrete coefficient version of the source's rational packet interface.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Jets/FormalLogJet.lean#L16-L18 and #L68-L72; Approximation/WeightedSliceDegree.lean, SupportBound; Approximation/AdmissibleMatrixInterpolation.lean, WeightedPolynomials and packetMap.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators
noncomputable section

namespace OAI.PiExponent.FormalInterpolation

-- FormalLogJet.liftSeries and formalJet in the pinned source.
def liftSeries (m : ℕ) : PowerSeries ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ :=
  (MvPowerSeries.finSuccEquiv ℂ m).symm.toRingHom.comp
    (PowerSeries.map MvPowerSeries.C)

def formalJet {m : ℕ} (c : Fin m → ℂ) :
    MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPowerSeries (Fin (m + 1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
    (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
      liftSeries m (PowerSeries.log ℂ)))

def WeightedPolynomial {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) (H : ℝ) :=
  {P : MvPolynomial (Fin (m + 1)) ℂ //
    ∀ a ∈ P.support,
      ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : ℝ) ≤ H}

def packetMap {nu : ℝ} (d : DeterminantContradiction.FixedData nu) (H : ℝ)
    (P : WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (DeterminantContradiction.finiteDenominators d)) H) :
    DeterminantContradiction.Row d H → ℂ :=
  fun ρ => MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)
    (formalJet (fun i => (ρ.1.val : ℂ) *
      MatrixArithmetic.rationalCenters
        (DeterminantContradiction.finiteNumerators d)
        (DeterminantContradiction.finiteDenominators d) i) P.val)

end OAI.PiExponent.FormalInterpolation


