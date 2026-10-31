-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P62
-- name    : QAlgorithms_Papers_Independent_Intake100_P62
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T11:02:32.136981+00:00
-- url     : https://prove2.me/theorems/f6bd5a3d-ed21-48e7-8162-1b0e1b1b0d50
-- title:
--   Definitions for All inseparable two-mode Gaussian continuous variable states are distillable
-- statement:
--   The objects the formalized statements of *All inseparable two-mode Gaussian continuous variable states are distillable* (arXiv:quant-ph/0007061) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `TwoModeKernel`: PDF p.1: coefficient arrays on the completed two-mode space l2(N x N).
--   - `asFockKernel`: PDF p.2, (2)--(6): relabel two number indices as Fin 2 -> N, with no cutoff.
--   - `CenteredStandard`: PDF p.2, (5)--(6): centered standard form of this density, with physical covariance and convergent Weyl traces supplied by GaussianWithCovariance.
--   - `ParameterViolation`: PDF p.2, (9): the strict inseparability polynomial, not a definition of entanglement.
--   - `branchTrace`: PDF pp.1--3: sum of diagonal entries; used only on positive trace-class branches. Infinite sums are genuine traces on these inputs.
--   - `normalizeBranch`: PDF pp.1--3: normalized positive-success branch; only p>0 is used.
--   - `localFilterKernel`: PDF pp.1--3: coefficients of two actual local bounded Kraus maps on n independent copies, regrouped by party. Output dimension d is finite.
--   - `filteredCopies`: PDF pp.1--3: computed unnormalized successful LOCC history on actual copies. Bounded filters and nuclear input make the nested sums convergent.
--   - `fixedBellTargetOverlap`: PDF pp.2--3: squared overlap with the FIXED Phi_d=d^(-1/2) sum_i |i,i>. Distinct from Information100.P04.bellOverlap, which optimizes over PPT channels. Only d>=2 is used for distillation, so the denominator never vanishes.
--   - `HasFiniteOutputLOCCDistillation`: PDF pp.1,3--4: full-oscillator finite-output LOCC in refined-history form. Bridge50.P37.Distillable instead takes finite input types and an NPT-filter test. Rank is fixed before accuracy; copy number and positive success probability may depend on accuracy. Norm-bounded local maps are physical Kraus contractions.
--   - `reductionKernel`: PDF pp.1,3, (1): coefficients of (tr_B rho) tensor I - rho. The identity is bounded and is not asserted to be trace class.
--   - `reductionOperator`: PDF p.3: bounded reduction operator. Nuclear density inputs always have a bounded realization; the accepted realization's off-domain fallback is unused.
--   - `reductionExpectation`: PDF pp.1,3, (1): real reduction quadratic form on a genuine Hilbert vector.
--   - `bilateralNumberCutoff`: PDF p.3: bilateral NUMBER-BASIS projection to span{|0>,...,|N>}. This explicit coordinate specialization is distinct from Claimed50.P32's arbitrary-family, bundled trace-class compression interface. It is embedded back into the completed space; normalization is a separate operation.
--   - `squeezedLambdaWitness`: PDF p.3: finite, normalized two-mode squeezed vector in PAIR coordinates, parameterized by lambda=tanh(r). Next46.P45.squeezedVector instead takes r and returns Fin-2 coordinates; it cannot replace this interface without reindexing. Used only for 0<lambda<1, where the Hilbert-space series is norm convergent. There is no normalized lambda=1 vector or infinite-squeezing limit here.
--   - `regroupedTwoCopyKernel`: PDF p.4: coordinate adapter for the imported independent-copy operation, regrouped as (A1,A2):(B1,B2). Renew46.P39.twoCopies uses Fin-4 coordinates.
--   - `numberBranch`: PDF p.4: the computed branch of both total-number measurements giving N. All four row and column conditions are needed for operator compression.
--   - `finiteXor`: PDF pp.3--4: local XOR_(N+1) matrix on the actual finite truncation. The target receives (source+target) mod (N+1), with no zero modulus.
--   - `truncatedTwoCopies`: PDF p.4: bilaterally truncate BOTH copies before applying XOR.
--   - `afterXor`: PDF p.4: apply the bilocal finite XOR to the actual truncated two-copy state.
--   - `xorBranch`: PDF p.4: select target outcome EXACTLY N on each party and embed the remaining finite support in the full four-mode space, keeping both targets.
--   - `bilocalConjugation`: PDF p.4: tensor product coefficients of two full local unitaries.
-- source:
--   All inseparable two-mode Gaussian continuous variable states are distillable, arXiv:quant-ph/0007061v2, https://arxiv.org/abs/quant-ph/0007061v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P39

/-!
Giedke--Duan--Cirac--Zoller, arXiv:quant-ph/0007061v2, PDF pp.1--4.
Full oscillator densities, with no input cutoff. Interleaved quadratures,
[q,p]=i, vacuum covariance I. Gaussianity is a characteristic-function condition
on an actual positive trace-class state. General first moments and pure states
are allowed. The accepted W(v)=exp(i v.R) is the source D(-v), so the Gaussian
class and centered covariance coincide, and the first moment changes sign.

Distillability below uses refined successful LOCC histories: a history has one
bounded local Kraus contraction on each party. Conversely these two filters
are a legal two-outcome local experiment followed by communication. Refining
an arbitrarily accurate pure-target LOCC output into Kraus histories leaves at
least one positive-weight history with at least that fidelity. This existential
representation imposes no uniform lower success bound, rate or optical gate set.
It is not the finite-copy NPT criterion used in Support50.P39.IsDistillable.

Accepted short-name matches are not interchangeable interfaces: Claimed50.P39
IsGaussian is one-mode, Information100.P04 bellOverlap optimizes PPT channels,
and Bridge50.P37 Distillable requires finite input types. Gaussianity here uses
the imported GaussianWithCovariance directly. The distinct full-oscillator LOCC
predicate and fixed-target overlap have explicit names. bilateralNumberCutoff
specializes a bilateral number-basis cutoff, whereas Claimed50.P32 finiteCompression
takes an arbitrary finite Hilbert family and a bundled trace-class input.
squeezedLambdaWitness uses lambda in pair coordinates, whereas Next46.P45
squeezedVector uses squeezing r in Fin-2 coordinates. regroupedTwoCopyKernel
reuses the imported noisyResourceCopies with only a two-copy coordinate adapter.

Source corrections: (4)'s linear term is imaginary; the normalized squeezed
vector on p.3 has covariance cosh(2r), plus/minus sinh(2r); its finite-squeezing reduction
test gives (n-kx)(n+kp)<1, rather than printed (12). The p.3 witness belongs to
H tensor H. Compression is bilateral and normalized only at positive trace.
These corrections require independent moderation. Compilation is pending.
-/

noncomputable section

open scoped BigOperators ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P62

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsSeparable productCoeff)
open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex GaussianWithCovariance standardFormCovariance
   multimodeWeylTrace covarianceCharacteristicValue)
open QAlgorithms.Papers.Independent.Frontier30.P14
  (conjugateKernel partialRight boundedUnitaryConjugation)
open QAlgorithms.Papers.Independent.Bridge50.P18
  (HasCoefficients realizeCoefficients)
open QAlgorithms.Papers.Independent.Support50.P39 (noisyResourceCopies)

/-- PDF p.1: coefficient arrays on the completed two-mode space l2(N x N). -/
abbrev TwoModeKernel := Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ

/-- PDF p.2, (2)--(6): relabel two number indices as Fin 2 -> N, with no cutoff. -/
def asFockKernel (rho : TwoModeKernel) : Matrix (FockIndex 2) (FockIndex 2) ℂ :=
  fun i j => rho (i 0, i 1) (j 0, j 1)

/-- PDF p.2, (5)--(6): centered standard form of this density, with physical
covariance and convergent Weyl traces supplied by GaussianWithCovariance. -/
def CenteredStandard (rho : TwoModeKernel) (a b kx kp : ℝ) : Prop :=
  GaussianWithCovariance (asFockKernel rho) (standardFormCovariance a b kx kp) ∧
  ∀ v, multimodeWeylTrace (asFockKernel rho) v =
    covarianceCharacteristicValue (standardFormCovariance a b kx kp) 0 v

/-- PDF p.2, (9): the strict inseparability polynomial, not a definition of entanglement. -/
def ParameterViolation (a b kx kp : ℝ) : Prop :=
  (a*b-kx^2)*(a*b-kp^2)+1 < a^2+b^2-2*kx*kp

/-- PDF pp.1--3: sum of diagonal entries; used only on positive trace-class
branches. Infinite sums are genuine traces on these inputs. -/
def branchTrace {I : Type} (X : Matrix I I ℂ) : ℝ := ∑' i, (X i i).re

/-- PDF pp.1--3: normalized positive-success branch; only p>0 is used. -/
def normalizeBranch {I : Type} (X : Matrix I I ℂ) : Matrix I I ℂ :=
  ((branchTrace X : ℂ)⁻¹) • X

/-- PDF pp.1--3: coefficients of two actual local bounded Kraus maps on n
independent copies, regrouped by party. Output dimension d is finite. -/
def localFilterKernel {n d : ℕ}
    (F G : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin d)) :
    Matrix (Fin d × Fin d) ((Fin n → ℕ) × (Fin n → ℕ)) ℂ :=
  fun i j => F (lp.single 2 j.1 1) i.1 * G (lp.single 2 j.2 1) i.2

/-- PDF pp.1--3: computed unnormalized successful LOCC history on actual copies.
Bounded filters and nuclear input make the nested sums convergent. -/
def filteredCopies {n d : ℕ} (rho : TwoModeKernel)
    (F G : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin d)) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  conjugateKernel (localFilterKernel F G) (noisyResourceCopies rho n)

/-- PDF pp.2--3: squared overlap with the FIXED Phi_d=d^(-1/2) sum_i |i,i>.
Distinct from Information100.P04.bellOverlap, which optimizes over PPT channels.
Only d>=2 is used for distillation, so the denominator never vanishes. -/
def fixedBellTargetOverlap {d : ℕ} (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  (∑ i : Fin d, ∑ j : Fin d, X (i,i) (j,j)).re / (d : ℝ)

/-- PDF pp.1,3--4: full-oscillator finite-output LOCC in refined-history form.
Bridge50.P37.Distillable instead takes finite input types and an NPT-filter test.
Rank is fixed before accuracy; copy number and positive success probability may
depend on accuracy. Norm-bounded local maps are physical Kraus contractions. -/
def HasFiniteOutputLOCCDistillation (rho : TwoModeKernel) : Prop :=
  ∃ d : ℕ, 2 ≤ d ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∃ n : ℕ, 0 < n ∧
      ∃ F G : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin d),
        ‖F‖ ≤ 1 ∧ ‖G‖ ≤ 1 ∧
        0 < branchTrace (filteredCopies rho F G) ∧
        branchTrace (filteredCopies rho F G) ≤ 1 ∧
        IsDensity (normalizeBranch (filteredCopies rho F G)) ∧
        1-epsilon < fixedBellTargetOverlap (normalizeBranch (filteredCopies rho F G))

/-- PDF pp.1,3, (1): coefficients of (tr_B rho) tensor I - rho.
The identity is bounded and is not asserted to be trace class. -/
def reductionKernel (rho : TwoModeKernel) : TwoModeKernel :=
  fun i j => (if i.2 = j.2 then partialRight rho i.1 j.1 else 0) - rho i j

/-- PDF p.3: bounded reduction operator. Nuclear density inputs always have a
bounded realization; the accepted realization's off-domain fallback is unused. -/
def reductionOperator (rho : TwoModeKernel) :
    Hilbert (ℕ × ℕ) →L[ℂ] Hilbert (ℕ × ℕ) :=
  realizeCoefficients (reductionKernel rho)

/-- PDF pp.1,3, (1): real reduction quadratic form on a genuine Hilbert vector. -/
def reductionExpectation (rho : TwoModeKernel) (psi : Hilbert (ℕ × ℕ)) : ℝ :=
  (inner ℂ psi (reductionOperator rho psi)).re

/-- PDF p.3: bilateral NUMBER-BASIS projection to span{|0>,...,|N>}.
This explicit coordinate specialization is distinct from Claimed50.P32's
arbitrary-family, bundled trace-class compression interface. It is embedded back
into the completed space; normalization is a separate operation. -/
def bilateralNumberCutoff (N : ℕ) (rho : TwoModeKernel) : TwoModeKernel :=
  fun i j => if i.1 ≤ N ∧ i.2 ≤ N ∧ j.1 ≤ N ∧ j.2 ≤ N then rho i j else 0

/-- PDF p.3: finite, normalized two-mode squeezed vector in PAIR coordinates,
parameterized by lambda=tanh(r). Next46.P45.squeezedVector instead takes r and
returns Fin-2 coordinates; it cannot replace this interface without reindexing.
Used only for 0<lambda<1, where the Hilbert-space series is norm convergent.
There is no normalized lambda=1 vector or infinite-squeezing limit here. -/
def squeezedLambdaWitness (lambda : ℝ) : Hilbert (ℕ × ℕ) :=
  ∑' k : ℕ, ((Real.sqrt (1-lambda^2) * lambda^k : ℝ) : ℂ) •
    lp.single 2 (k,k) 1

/-- PDF p.4: coordinate adapter for the imported independent-copy operation,
regrouped as (A1,A2):(B1,B2). Renew46.P39.twoCopies uses Fin-4 coordinates. -/
def regroupedTwoCopyKernel (rho : TwoModeKernel) :
    Matrix ((ℕ × ℕ) × (ℕ × ℕ)) ((ℕ × ℕ) × (ℕ × ℕ)) ℂ :=
  fun i j => noisyResourceCopies rho 2
    (![i.1.1, i.1.2], ![i.2.1, i.2.2])
    (![j.1.1, j.1.2], ![j.2.1, j.2.2])

/-- PDF p.4: the computed branch of both total-number measurements giving N.
All four row and column conditions are needed for operator compression. -/
def numberBranch (N : ℕ) (rho : TwoModeKernel) :
    Matrix ((ℕ × ℕ) × (ℕ × ℕ)) ((ℕ × ℕ) × (ℕ × ℕ)) ℂ :=
  fun i j => if i.1.1+i.1.2=N ∧ i.2.1+i.2.2=N ∧
      j.1.1+j.1.2=N ∧ j.2.1+j.2.2=N then regroupedTwoCopyKernel rho i j else 0

/-- PDF pp.3--4: local XOR_(N+1) matrix on the actual finite truncation.
The target receives (source+target) mod (N+1), with no zero modulus. -/
def finiteXor (N : ℕ) :
    Matrix (Fin (N+1) × Fin (N+1)) (Fin (N+1) × Fin (N+1)) ℂ :=
  fun i j => if i.1=j.1 ∧ i.2.val=(j.2.val+j.1.val) % (N+1) then 1 else 0

/-- PDF p.4: bilaterally truncate BOTH copies before applying XOR. -/
def truncatedTwoCopies (N : ℕ) (rho : TwoModeKernel) :
    Matrix ((Fin (N+1) × Fin (N+1)) × (Fin (N+1) × Fin (N+1)))
      ((Fin (N+1) × Fin (N+1)) × (Fin (N+1) × Fin (N+1))) ℂ :=
  fun i j => regroupedTwoCopyKernel rho
    ((i.1.1.val,i.1.2.val),(i.2.1.val,i.2.2.val))
    ((j.1.1.val,j.1.2.val),(j.2.1.val,j.2.2.val))

/-- PDF p.4: apply the bilocal finite XOR to the actual truncated two-copy state. -/
def afterXor (N : ℕ) (rho : TwoModeKernel) :=
  let K := Matrix.kronecker (finiteXor N) (finiteXor N)
  K * truncatedTwoCopies N rho * K.conjTranspose

/-- PDF p.4: select target outcome EXACTLY N on each party and embed the
remaining finite support in the full four-mode space, keeping both targets. -/
def xorBranch (N : ℕ) (rho : TwoModeKernel) :
    Matrix ((ℕ × ℕ) × (ℕ × ℕ)) ((ℕ × ℕ) × (ℕ × ℕ)) ℂ :=
  fun i j => if h : i.1.1 ≤ N ∧ i.1.2=N ∧ i.2.1 ≤ N ∧ i.2.2=N ∧
      j.1.1 ≤ N ∧ j.1.2=N ∧ j.2.1 ≤ N ∧ j.2.2=N then
    afterXor N rho
      ((⟨i.1.1, by omega⟩,⟨N, by omega⟩),(⟨i.2.1, by omega⟩,⟨N, by omega⟩))
      ((⟨j.1.1, by omega⟩,⟨N, by omega⟩),(⟨j.2.1, by omega⟩,⟨N, by omega⟩))
    else 0

/-- PDF p.4: tensor product coefficients of two full local unitaries. -/
def bilocalConjugation
    (U V : Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ))
    (X : Matrix ((ℕ × ℕ) × (ℕ × ℕ)) ((ℕ × ℕ) × (ℕ × ℕ)) ℂ) :=
  conjugateKernel
    (productCoeff (QAlgorithms.Papers.Independent.Frontier30.P14.unitaryCoeff U)
      (QAlgorithms.Papers.Independent.Frontier30.P14.unitaryCoeff V)) X

/-- Sanity: the vacuum boundary saturates (9), so strict violation is false. -/
example : ¬ ParameterViolation 1 1 0 0 := by norm_num [ParameterViolation]

/-- Sanity: a single finite-output Bell basis state has unit overlap at d=1.
This rank is deliberately excluded from HasFiniteOutputLOCCDistillation. -/
example : fixedBellTargetOverlap (fun _ _ : Fin 1 × Fin 1 => (1 : ℂ)) = 1 := by
  norm_num [fixedBellTargetOverlap, Fin.sum_univ_succ]

/-- Sanity: a zero input has zero success trace; normalization cannot make it a state. -/
example : branchTrace (0 : TwoModeKernel) = 0 := by simp [branchTrace]

/-- Sanity: both local projections at N=0 retain precisely the joint vacuum entry. -/
example (rho : TwoModeKernel) : bilateralNumberCutoff 0 rho (0,0) (0,0) = rho (0,0) (0,0) := by
  simp [bilateralNumberCutoff]

end QAlgorithms.Papers.Independent.Intake100.P62


