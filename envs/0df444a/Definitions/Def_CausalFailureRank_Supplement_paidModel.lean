-- Prove2me | Definitions.Def_CausalFailureRank_Supplement_paidModel
-- name    : CausalFailureRank_Supplement_paidModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:52:06.806162+00:00
-- url     : https://prove2.me/theorems/ec7dc763-76b1-4ef6-b234-f2a94520f99d
-- title:
--   Homogeneous shared-pool current-payment model and equation (34) certificate
-- statement:
--   The Appendix D model has integers $K<N$, a shared pool of $K$ one-use tools that can correct every output, independent fair binary facts, and homogeneous binary-symmetric reviews. Each review has rational accuracy $1/2+\gamma$ and rational price $c$, where $c>0$ and $0<\gamma\le 1/4$; every physically executed correction has the same rational price $f\ge0$.
--
--   Both the native and cap-relaxed values use the stricter **current-payment** contract: an erroneous output is physically corrected and paid before the process advances. The cap-relaxed value removes only review and call limits. The free baseline changes only $f$ to zero.
--
--   The definition also gives all quantities of equation (34):
--
--   $$
--   R=\frac{1+2\gamma}{1-2\gamma},\quad p_m=(1+R^m)^{-1},\quad
--   Q=\max\left\{1,\left\lceil\frac{M+1}{\gamma}\right\rceil,
--   \left\lceil\frac{2E}{\gamma^2}\right\rceil\right\},
--   $$
--
--   with $t_0,B,\Lambda,\varepsilon,M,E$ defined by the exact minima in the paper. Resource qualification is precisely $Q_i\ge Q$ at every stage and $H\ge H_0+NQ+K$. The comparison scales are $D_f=aN\log(1+f/a)$ and $S_\delta=aN\log(1+N/\delta)$, where $a=c/(2\gamma h)$ and $h=\log R$.
--
--   **Formalization Note** The model reuses the published fixed-graph execution and value definitions. Inputs remain rational. Values and expected bills are in $[0,\infty]$, and the explicit algorithm interface records finite-state policies, exact rational test calibration, and operation/bit counts.
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), Appendix D, pp.23, 25, 30–33 (PDF pp.24, 26, 31–34), eqs. (28)–(34), (46)–(56)

import Mathlib
import Definitions.Def_CausalFailureRank_V

set_option autoImplicit false

open MeasureTheory

namespace CausalFailureRank
namespace Supplement

/-- The fair homogeneous shared-pool specialization of Appendix D. The statistical and price
inputs are rational, as required by the paper's explicit algorithm; the execution model itself is
the published fixed-graph `Instance`.

Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027
submission, version of 2026-11-03, sha256 721c8b0d…), Appendix D, p.23.

**Formalization Note.** `channelEquiv i` identifies each stage alphabet with `Bool`; `bsc` states
the two point masses of the BSC exactly. Every tool is compatible with every stage. The conditions
`K < N`, `c > 0`, `0 < γ ≤ 1/4`, and `f ≥ 0` are fields, so no malformed parameter instance
can enter an Appendix D theorem. -/
structure PaidModel (N K : ℕ) where
  I : Instance N K
  c : ℚ
  gamma : ℚ
  fee : ℚ
  N_pos : 0 < N
  K_lt_N : K < N
  c_pos : 0 < c
  gamma_pos : 0 < gamma
  gamma_le_quarter : gamma ≤ 1 / 4
  fee_nonneg : 0 ≤ fee
  compatibility : ∀ i, I.S i = Finset.univ
  fairPrior : ∀ i, I.prior i = 1 / 2
  channelEquiv : ∀ i, I.α i ≃ Bool
  bsc : ∀ i x y,
    I.P i x ((channelEquiv i).symm y) =
      ENNReal.ofReal (if y = x then (1 / 2 : ℝ) + gamma else (1 / 2 : ℝ) - gamma)
  reviewPrice : ∀ i, I.c i = c
  correctionPrice : ∀ i r, I.f i r = fee

/-- The same shared-pool instance with every physical correction free. This changes no fact,
channel, compatibility, review price, or native resource field. -/
def freeInstance {N K : ℕ} (M : PaidModel N K) : Instance N K :=
  { M.I with
    f := fun _ _ ↦ 0
    f_nonneg := fun _ _ ↦ le_rfl }

/-- No review or call limit. The `currentPay` correction rule remains unchanged. -/
def relaxedCaps (N : ℕ) : Caps N :=
  { Q := fun _ ↦ ⊤, H := ⊤ }

/-- `V_f^nat(δ)`: the value under the supplied native caps and the stricter current-payment
contract. -/
noncomputable def nativeValue {N K : ℕ} (M : PaidModel N K) (caps : Caps N) (δ : ℚ) : ENNReal :=
  V M.I .currentPay caps (δ : ℝ)

/-- `V_f^∞(δ)`: only review and call limits are relaxed; current payment and all correction
rights are retained. -/
noncomputable def relaxedValue {N K : ℕ} (M : PaidModel N K) (δ : ℚ) : ENNReal :=
  V M.I .currentPay (relaxedCaps N) (δ : ℝ)

/-- The native free-correction baseline `A = V_0^nat(δ)` with the same original quotas, call cap,
current-payment contract, and target risk. -/
noncomputable def nativeFreeValue {N K : ℕ} (M : PaidModel N K) (caps : Caps N)
    (δ : ℚ) : ENNReal :=
  V (freeInstance M) .currentPay caps (δ : ℝ)

/-- The cap-relaxed free-correction value `V_0^∞(δ)`. -/
noncomputable def relaxedFreeValue {N K : ℕ} (M : PaidModel N K) (δ : ℚ) : ENNReal :=
  V (freeInstance M) .currentPay (relaxedCaps N) (δ : ℝ)

/-- Expected review charge alone, used in the policy-by-policy paid overlay. -/
noncomputable def expectedObsBill {N K : ℕ} (I : Instance N K) (caps : Caps N)
    (p : Policy I) : ENNReal :=
  ∫⁻ x, obsBillFrom I .currentPay caps (p.act x.1) (initState I) x.2
    ∂(p.ν.prod (tapeLaw I))

/-- `H₀`, the number of normal calls in the base execution model. -/
def normalCallTotal {N K : ℕ} (M : PaidModel N K) : ℕ :=
  ∑ i, M.I.normalCalls i

/-- The likelihood ratio `R = (1+2γ)/(1-2γ)` in (34). -/
def likelihoodRatio {N K : ℕ} (M : PaidModel N K) : ℚ :=
  (1 + 2 * M.gamma) / (1 - 2 * M.gamma)

/-- The exact symmetric-boundary error `p_m = (1+R^m)^{-1}`. -/
def boundaryError {N K : ℕ} (M : PaidModel N K) (m : ℕ) : ℚ :=
  1 / (1 + likelihoodRatio M ^ m)

/-- The probability of a length-`Q` binary review word under truth `x`. This is rational because
Appendix D keeps the BSC parameter rational. -/
def bscWordProbability {N K Q : ℕ} (M : PaidModel N K) (x : Bool)
    (y : Fin Q → Bool) : ℚ :=
  ∏ j, if y j = x then (1 / 2 : ℚ) + M.gamma else (1 / 2 : ℚ) - M.gamma

/-- The least natural number satisfying a predicate; this is the paper's `min` convention. If the
set were empty Lean returns zero, so Theorems D.1/D.10 explicitly assert the defining predicates
for the selected certificate, ruling out the total-function junk value. -/
noncomputable def leastNat (P : ℕ → Prop) [DecidablePred P] : ℕ :=
  sInf {n | P n}

/-- Ceiling into natural numbers, expressed as the least natural upper bound. -/
noncomputable def ceilNat (x : ℚ) : ℕ :=
  leastNat fun n ↦ x ≤ n

/-- `t₀` of equation (34). -/
noncomputable def certT0 {N K : ℕ} (M : PaidModel N K) (δ : ℚ) : ℕ :=
  leastNat fun t ↦ 1 ≤ t ∧ Odd t ∧
    (1 - 4 * M.gamma ^ 2) ^ t ≤ (δ / (2 * N)) ^ 2

noncomputable def certB {N K : ℕ} (M : PaidModel N K) (δ : ℚ) : ℚ :=
  M.c * N * certT0 M δ

noncomputable def certLambda {N K : ℕ} (M : PaidModel N K) (δ : ℚ) : ℚ :=
  4 * certB M δ / δ

noncomputable def certEpsilon {N K : ℕ} (M : PaidModel N K) (δ : ℚ) : ℚ :=
  M.c / (3 * certLambda M δ)

/-- `M` of equation (34), not the shared-pool model. -/
noncomputable def certM {N K : ℕ} (M : PaidModel N K) (δ : ℚ) : ℕ :=
  leastNat fun m ↦ boundaryError M m ≤ M.c / certLambda M δ

/-- `E` of equation (34). -/
noncomputable def certE {N K : ℕ} (M : PaidModel N K) (δ : ℚ) : ℕ :=
  leastNat fun e ↦ 1 ≤ e ∧ (2 : ℚ) ^ (-((e : ℤ))) ≤ M.gamma * certEpsilon M δ

/-- The explicit native review certificate `Q(N,γ,δ)` of equation (34), independent of `f`. -/
noncomputable def certQ {N K : ℕ} (M : PaidModel N K) (δ : ℚ) : ℕ :=
  max 1 (max (ceilNat (((certM M δ + 1 : ℕ) : ℚ) / M.gamma))
    (ceilNat (2 * (certE M δ : ℚ) / M.gamma ^ 2)))

/-- The zero-variable-charge failure threshold `ζ_f` from (53). -/
noncomputable def zeroChargeFailure {N K : ℕ} (M : PaidModel N K) : ℚ :=
  if M.fee = 0 then
    ∑ j ∈ Finset.Icc (K + 1) N, (Nat.choose N j : ℚ) / (2 : ℚ) ^ N
  else
    1 - (2 : ℚ) ^ (-((N : ℕ) : ℤ))

/-- The positive-charge floor `b_f` used in the termination bound (54). -/
def positiveChargeFloor {N K : ℕ} (M : PaidModel N K) : ℚ :=
  if M.fee = 0 then M.c else min M.c M.fee

/-- The explicit bisection bound `J_bis` of (54), written without a real logarithm: it is the least
`j` for which `2^j` dominates `2Λδ / (b_f(ζ_f-δ))`. When the zero-charge policy is already safe,
the algorithm returns it before bisection and the bound is zero. -/
noncomputable def certJBis {N K : ℕ} (M : PaidModel N K) (δ : ℚ) : ℕ :=
  if zeroChargeFailure M ≤ δ then 0 else
    leastNat fun j ↦
      2 * certLambda M δ * δ ≤
        positiveChargeFloor M * (zeroChargeFailure M - δ) * (2 : ℚ) ^ j

/-- The least-number definition of `J_bis` is genuine in the branch where bisection is needed. -/
def BisectionBoundValid {N K : ℕ} (M : PaidModel N K) (δ : ℚ) : Prop :=
  zeroChargeFailure M ≤ δ ∨
    2 * certLambda M δ * δ ≤
      positiveChargeFloor M * (zeroChargeFailure M - δ) * (2 : ℚ) ^ certJBis M δ

/-- The selected minima in (34) are genuine and `Q` has the three displayed lower bounds. This is
a conclusion of the explicit construction, not an additional model assumption. -/
def CertificateValid {N K : ℕ} (M : PaidModel N K) (δ : ℚ) : Prop :=
  1 ≤ certT0 M δ ∧ Odd (certT0 M δ) ∧
  (1 - 4 * M.gamma ^ 2) ^ certT0 M δ ≤ (δ / (2 * N)) ^ 2 ∧
  boundaryError M (certM M δ) ≤ M.c / certLambda M δ ∧
  1 ≤ certE M δ ∧
  (2 : ℚ) ^ (-((certE M δ : ℕ) : ℤ)) ≤ M.gamma * certEpsilon M δ ∧
  1 ≤ certQ M δ ∧
  (certM M δ + 1 : ℚ) / M.gamma ≤ certQ M δ ∧
  2 * certE M δ / M.gamma ^ 2 ≤ certQ M δ

/-- Resource condition (29): every native stage admits `Q` reviews and the total cap admits the
normal calls, all `NQ` reviews, and at most `K` physical corrections. -/
def ResourceQualified {N K : ℕ} (M : PaidModel N K) (caps : Caps N) (δ : ℚ) : Prop :=
  (∀ i, (certQ M δ : ℕ∞) ≤ caps.Q i) ∧
    ((normalCallTotal M + N * certQ M δ + K : ℕ) : ℕ∞) ≤ caps.H

/-- `h = log((1+2γ)/(1-2γ))` and `a = c/(2γh)`. -/
noncomputable def scaleA {N K : ℕ} (M : PaidModel N K) : ℝ :=
  M.c / (2 * M.gamma * Real.log (likelihoodRatio M))

noncomputable def feeScale {N K : ℕ} (M : PaidModel N K) : ENNReal :=
  ENNReal.ofReal (scaleA M * N * Real.log (1 + M.fee / scaleA M))

noncomputable def noCorrectionScale {N K : ℕ} (M : PaidModel N K) (δ : ℚ) : ENNReal :=
  ENNReal.ofReal (scaleA M * N * Real.log (1 + N / (δ : ℝ)))

noncomputable def comparisonScale {N K : ℕ} (M : PaidModel N K) (caps : Caps N)
    (δ : ℚ) : ENNReal :=
  min (nativeFreeValue M caps δ + feeScale M) (noCorrectionScale M δ)

/-- A finite-state policy: after fixing its private seed, a finite state is initialized once and
updated from each visible event; the next action depends only on that state. -/
def IsFiniteStatePolicy {N K : ℕ} {I : Instance N K} (p : Policy I) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ init : p.Ω → σ, ∃ next : σ → Event I → σ,
    ∃ out : σ → Action N K,
      ∀ seed h, p.act seed h = out (h.foldl next (init seed))

/-- A randomized policy has rational law when every finite cylinder of its sampled complete
visible-history strategy has rational probability. This records the exact rational coins used by
the Appendix D implementation, rather than merely saying that its numerical inputs are rational. -/
def IsRationalPolicy {N K : ℕ} {I : Instance N K} (p : Policy I) : Prop :=
  ∀ (m : ℕ) (h : Fin m → History I) (a : Fin m → Action N K),
    ∃ r : ℚ, 0 ≤ r ∧
      p.ν {seed | ∀ j, p.act seed (h j) = a j} = ENNReal.ofReal r

/-- The rational bounded calibrated tests of (55)–(56). `cappedWriteTrue m y` is the probability
of writing `true` after the at-most-`Q` capped experiment, represented by its decision on the first
`Q` BSC coordinates. The two displayed finite sums require the same error `q_m` under either truth.
For every positive boundary index used by the penalty program, `q_m < p_m`, and rational blind
mixing restores the error exactly to `p_m`. -/
structure CalibrationData {N K : ℕ} (M : PaidModel N K) (δ : ℚ) where
  cappedWriteTrue : ℕ → (Fin (certQ M δ) → Bool) → ℚ
  write_probability : ∀ m y, 0 ≤ cappedWriteTrue m y ∧ cappedWriteTrue m y ≤ 1
  cappedError : ℕ → ℚ
  cappedMix : ℕ → ℚ
  error_if_false : ∀ m, 1 ≤ m → m ≤ certM M δ →
    cappedError m = ∑ y, bscWordProbability M false y * cappedWriteTrue m y
  error_if_true : ∀ m, 1 ≤ m → m ≤ certM M δ →
    cappedError m = ∑ y, bscWordProbability M true y * (1 - cappedWriteTrue m y)
  error_nonneg : ∀ m, 1 ≤ m → m ≤ certM M δ → 0 ≤ cappedError m
  error_lt : ∀ m, 1 ≤ m → m ≤ certM M δ → cappedError m < boundaryError M m
  mix_formula : ∀ m, 1 ≤ m → m ≤ certM M δ →
    cappedMix m = (1 / 2 - boundaryError M m) / (1 / 2 - cappedError m)
  mix_probability : ∀ m, 1 ≤ m → m ≤ certM M δ →
    0 ≤ cappedMix m ∧ cappedMix m ≤ 1
  calibrated : ∀ m, 1 ≤ m → m ≤ certM M δ →
    cappedMix m * cappedError m + (1 - cappedMix m) / 2 = boundaryError M m

/-- An initial mixture of at most two whole finite-state policies. The risk and expected bill are
the corresponding convex combinations; the local tests carry the exact bounded calibration data.
-/
def IsTwoPolicyOutput {N K : ℕ} (M : PaidModel N K) (caps : Caps N) (δ : ℚ)
    (tests : CalibrationData M δ) (p : Policy M.I) : Prop :=
  ∃ pL pU : Policy M.I, ∃ w : ℚ, 0 ≤ w ∧ w ≤ 1 ∧
    IsFiniteStatePolicy p ∧ IsFiniteStatePolicy pL ∧ IsFiniteStatePolicy pU ∧
    IsRationalPolicy p ∧ IsRationalPolicy pL ∧ IsRationalPolicy pU ∧
    (∀ (m : ℕ) (h : Fin m → History M.I) (a : Fin m → Action N K),
      p.ν {seed | ∀ j, p.act seed (h j) = a j} =
        ENNReal.ofReal w * pL.ν {seed | ∀ j, pL.act seed (h j) = a j} +
          ENNReal.ofReal (1 - w) * pU.ν {seed | ∀ j, pU.act seed (h j) = a j}) ∧
    failProb M.I .currentPay caps p =
      ENNReal.ofReal w * failProb M.I .currentPay caps pL +
        ENNReal.ofReal (1 - w) * failProb M.I .currentPay caps pU ∧
    expBill M.I .currentPay caps p =
      ENNReal.ofReal w * expBill M.I .currentPay caps pL +
        ENNReal.ofReal (1 - w) * expBill M.I .currentPay caps pU ∧
    (∀ m, 1 ≤ m → m ≤ certM M δ →
      tests.cappedError m < boundaryError M m ∧
      tests.cappedMix m * tests.cappedError m + (1 - tests.cappedMix m) / 2 =
        boundaryError M m) ∧
    ∀ seed sample n, (runFrom M.I .currentPay caps (p.act seed) (initState M.I) sample n).reviews ≤
      certQ M δ

/-- Explicit operation/storage counts for Appendix D.2.5. -/
structure AlgorithmComplexity where
  penaltySolves : ℕ
  penaltyRationalOps : ℕ
  storedRecords : ℕ
  calibrationRationalOps : ℕ
  menuInputBitLength : ℕ
  gammaInputBitLength : ℕ
  deltaInputBitLength : ℕ
  multiplierBitLength : ℕ
  probabilityBitLength : ℕ

/-- A single uniform algorithm taking only the rational public instance, native caps, and target
risk. In particular neither `A = V_0^nat(δ)` nor an optimal free policy is an input. Its rational
operation, storage, calibration, and bit counts are part of the same output interface. -/
structure RationalNativeAlgorithm where
  run : ∀ {N K : ℕ} (M : PaidModel N K), Caps N → ℚ → Policy M.I
  calibration : ∀ {N K : ℕ} (M : PaidModel N K), Caps N → (δ : ℚ) → CalibrationData M δ
  work : ∀ {N K : ℕ} (_M : PaidModel N K), Caps N → ℚ → AlgorithmComplexity

/-- The literal rational-operation, storage, calibration, and additive bit-length accounting in
Appendix D.2.5, in the displayed numerical parameters. -/
def AlgorithmComplexity.Correct {N K : ℕ} (M : PaidModel N K) (δ : ℚ)
    (work : AlgorithmComplexity) : Prop :=
  work.penaltySolves ≤ certJBis M δ + 2 ∧
  work.penaltyRationalOps =
    work.penaltySolves * N * (K + 1) * (certM M δ + 1) ∧
  work.storedRecords = N * (K + 1) ∧
  work.calibrationRationalOps = certQ M δ * (certM M δ + 1) ^ 2 ∧
  work.probabilityBitLength =
    (N + 1) * (certM M δ + 1) * (work.menuInputBitLength + 1) +
      certQ M δ * (work.gammaInputBitLength + 1) +
      work.deltaInputBitLength + work.multiplierBitLength + 1

/-- Upload-module interface for the homogeneous shared-pool current-payment model and its exact
resource/algorithm vocabulary. -/
abbrev paidModel (N K : ℕ) := PaidModel N K

end Supplement
end CausalFailureRank


