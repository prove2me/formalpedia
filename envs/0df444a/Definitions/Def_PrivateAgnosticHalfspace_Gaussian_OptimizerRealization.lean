-- Prove2me | Definitions.Def_PrivateAgnosticHalfspace_Gaussian_OptimizerRealization
-- name    : PrivateAgnosticHalfspace_Gaussian_OptimizerRealization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:37:05.65676+00:00
-- url     : https://prove2.me/theorems/d5c7416e-f258-40ef-843f-302a73dbf324
-- title:
--   Canonical finite Gaussian regression law and its realization
-- statement:
--   This interface specifies the output law of the finite Gaussian regression optimizer used with clipped Hermite features.
--
--   For dimension $d$, degree $p$, sample size $n$, privacy parameters $\varepsilon,\delta$ and a deterministic dataset, choose an equivalence between Hermite multi-indices and $D_p$ coordinates that respects the public index ranking. When $D_p\le n$, the law is obtained by $n$ projected accelerated iterations with independent scalar Gaussian smoothing records and independent Gaussian vector noise. The smoothing radius is $1/n$, the vector noise scale is $8T\sqrt{\log(1/\delta)/n}/\varepsilon$, and the exact step sizes and recurrence are included in the definition. When $D_p>n$, the output is zero.
--
--   The realization predicate says that the coefficient-valued marginal of a probability-valued optimizer equals this explicit law for every deterministic dataset and all public parameters:
--
--   $$\operatorname{Law}(\operatorname{coeff}(O(S)))=Q_{d,p,n,\varepsilon,\delta,S}.$$
--
--   The predicate specifies the computation's mathematical distribution. Privacy, excess-loss bounds, measurable dependence and efficient program implementation are separate conclusions to prove. This separates a common algorithm specification from its statistical and operational verification.
-- source:
--   Racca, Sanyal and Singhal, Privacy for Free in Efficient Agnostic Halfspace Learning, held STOC 2027 submission #1006, October 2026, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1006.pdf, Algorithm 1, §2.1 equation (4), Appendix B Lemma B.4, and §2.2 arithmetic account. Derived finite Gaussian regression implementation; accelerated recurrence: Ghadimi and Lan, https://arxiv.org/abs/1310.3787v1, p.22 equation (3.36).

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression
import Definitions.Def_NonconvexAG_StochComposite_RSAG
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
/-- The explicit finite Gaussian regression law in a specified coefficient ordering. -/
noncomputable def orderedRegressionRawLaw (d p n : ℕ) (ε δ : ℝ)
    (e : Index d p ≃ Fin (featureDimension d p)) (S : Fin n → Example d) : Measure (Coeff d p) :=
  let I := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  let a := fun i => I (clipped d p (S i).1)
  let y := fun i => label (S i).2
  let T := radius d p
  let L := 2*T/((n : ℝ)⁻¹)
  let τ := 8*T*Real.sqrt (Real.log (1/δ)/n)/ε
  let σ := 20*T*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/(Real.sqrt n*ε)
  let β := min (1/(2*L)) (1/(σ*n*Real.sqrt n))
  let Ξ := (Fin n → ℝ) × Vec (featureDimension d p)
  let G := fun (v : Vec (featureDimension d p)) (q : Ξ) =>
    (n : ℝ)⁻¹ • (∑ i,
      (if 0 ≤ inner ℝ v (a i)-y i+(n : ℝ)⁻¹*‖a i‖*q.1 i then (1 : ℝ) else -1) • a i) + τ • q.2
  let out := NonconvexAG.StochComposite.xagSeq G
    (fun x z c => (max 1 ‖x-c • z‖)⁻¹ • (x-c • z))
    (fun k => 2/((k : ℝ)+1)) (fun _ => β) (fun k => (k : ℝ)*β/2) (fun _ => 1) 0
    (fun k (s : Fin (n+1) → Ξ) => if hk : k < n+1 then s ⟨k,hk⟩ else (0,0)) n
  if featureDimension d p ≤ n then
    (Measure.pi (fun _ : Fin (n+1) =>
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).prod (gaussian (featureDimension d p)))).map
      (fun s => I.symm (out s))
  else Measure.dirac 0
/-- A probability-valued optimizer realizes the public, ordered finite regression law. -/
def RealizesOrderedRegression (O : Optimizer) : Prop :=
  ∃ e : ∀ d p : ℕ, Index d p ≃ Fin (featureDimension d p),
    (∀ d p κ, (e d p κ).val=indexRank κ) ∧
    ∀ d p n ε δ S, (O d p n ε δ S : Measure (UnitBall d p)).map Subtype.val =
      orderedRegressionRawLaw d p n ε δ (e d p) S
end PrivateAgnosticHalfspace.Gaussian


