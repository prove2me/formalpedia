-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P52
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P52
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T05:49:39.593114+00:00
-- url     : https://prove2.me/theorems/382a7edf-16fa-415a-9671-b86753f34feb
-- title:
--   Definitions for Quantum Markov chains, sufficiency of quantum channels, and Renyi information measures
-- statement:
--   The objects the formalized statements of *Quantum Markov chains, sufficiency of quantum channels, and Renyi information measures* (arXiv:1501.05636) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsStrictChannel`: Section 3, PDF p.7: strictness on every positive definite input.
--   - `IsSufficient`: Definition 1, PDF p.3, including its extension to unnormalized operators: one common CPTP recovery must recover both members of the pair.
--   - `renyiKernel`: Equation (1.16), PDF p.4: the operator inside the trace after rho^alpha.
--   - `sandwichedKernel`: Equation (1.17), PDF p.4: the sandwiched reference kernel, before rho factors.
--   - `renyiReference`: Equations (3.23),(3.57), PDF pp.10,14: the computed reference R_alpha.
--   - `sandwichedReference`: Equations (3.24),(3.59), PDF pp.10,14: the computed reference S_alpha.
--   - `renyiDifference`: Equation (1.16), PDF p.4. The extended logarithm is -infinity at raw trace zero, so below order one the difference is +infinity, not zero.
--   - `deltaTilde`: Equations (1.17),(A.17), PDF pp.4,21: for the positive operator X inside the alpha-norm, alpha log ||X||_alpha = log Tr X^alpha. This retains the primary normalization, rather than the erroneous auxiliary prefactor in (A.19), p.22.
--   - `minRelative`: Equations (3.2),(3.8), PDF pp.7–8: -log of squared root fidelity. The square-root sandwich formula equals the squared trace norm in (3.2).
--   - `deltaMin`: Definition 16, equation (5.1), PDF p.17: actual Petz-recovered reference.
--   - `deltaMax`: Definition 16, equation (5.2), PDF p.17: Dmax as in primary (3.9), in bits.
--   - `conditionalSigma`: Equation (1.21), PDF p.5: sigma=rho_AC tensor I_B, in coordinates A x (C x B). The AC marginal is computed from this same rho; the physical middle register is C.
--   - `conditionalRenyiInformation`: Equations (1.14),(1.22), PDF pp.4–5, in the exact channel specialization (1.21).
--   - `conditionalRenyiTilde`: Equations (1.15),(1.23), PDF pp.4–5, with the same computed marginal reference.
--   - `conditionalPetzReference`: Equations (5.4),(5.7), PDF pp.17–18: the reference equals rho_AC^(1/2) rho_C^(-1/2) rho_BC rho_C^(-1/2) rho_AC^(1/2), with identities on complementary registers. It is constructed by (1.11),(1.21).
--   - `conditionalMinInformation`: Equation (5.7), PDF p.18: primary min-information definition.
--   - `conditionalMaxInformation`: Equation (5.4), PDF p.17: primary max-information definition, using 2^lambda from (3.9), rather than the inconsistent exp(lambda) in the alternative (5.5).
--   - `outputReference`: Appendix A, equation (A.1), PDF p.19: output-space reference P_alpha. Both outer N(sigma) exponents are (alpha-1)/2. No trace normalization is applied.
--   - `jointTrace`: Appendix A, equations (A.10)–(A.12), PDF p.20: power stays inside the trace.
-- source:
--   Quantum Markov chains, sufficiency of quantum channels, and Renyi information measures, arXiv:1501.05636v4, https://arxiv.org/abs/1501.05636v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P35

/-!
Datta–Wilde, arXiv:1501.05636v4. Finite nonzero physical registers throughout.
Information is in bits; operator logs in the exponential inequality are natural.
All real spectral powers, including exponent zero, vanish on the kernel.
Compilation is pending the requested batch handoff.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P52

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint petz marginalAB)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms.Papers.Independent.Renew46.P35 (HasMarkovBlocks)

/-- Section 3, PDF p.7: strictness on every positive definite input. -/
def IsStrictChannel {H K : Type} [Fintype H] [Fintype K] [DecidableEq H]
    (N : Superop H K) : Prop :=
  IsChannel N ∧ ∀ X : Mat H, X.PosDef → (N X).PosDef

/-- Definition 1, PDF p.3, including its extension to unnormalized operators:
one common CPTP recovery must recover both members of the pair. -/
def IsSufficient {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] (rho sigma : Mat H) (N : Superop H K) : Prop :=
  ∃ R : Superop K H, IsChannel R ∧ R (N rho) = rho ∧ R (N sigma) = sigma

/-- Equation (1.16), PDF p.4: the operator inside the trace after rho^alpha. -/
def renyiKernel {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] (a : ℝ) (rho sigma : Mat H)
    (N : Superop H K) : Mat H :=
  supportPower sigma ((1 - a) / 2) *
    channelAdjoint N (supportPower (N sigma) ((a - 1) / 2) *
      supportPower (N rho) (1 - a) * supportPower (N sigma) ((a - 1) / 2)) *
    supportPower sigma ((1 - a) / 2)

/-- Equation (1.17), PDF p.4: the sandwiched reference kernel, before rho factors. -/
def sandwichedKernel {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] (a : ℝ) (rho sigma : Mat H)
    (N : Superop H K) : Mat H :=
  supportPower sigma ((1 - a) / (2 * a)) *
    channelAdjoint N (supportPower (N sigma) ((a - 1) / (2 * a)) *
      supportPower (N rho) ((1 - a) / a) * supportPower (N sigma) ((a - 1) / (2 * a))) *
    supportPower sigma ((1 - a) / (2 * a))

/-- Equations (3.23),(3.57), PDF pp.10,14: the computed reference R_alpha. -/
def renyiReference {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] (a : ℝ) (rho sigma : Mat H)
    (N : Superop H K) : Mat H :=
  supportPower (renyiKernel a rho sigma N) (1 / (1 - a))

/-- Equations (3.24),(3.59), PDF pp.10,14: the computed reference S_alpha. -/
def sandwichedReference {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] (a : ℝ) (rho sigma : Mat H)
    (N : Superop H K) : Mat H :=
  supportPower (sandwichedKernel a rho sigma N) (a / (1 - a))

/-- Equation (1.16), PDF p.4. The extended logarithm is -infinity at raw trace
zero, so below order one the difference is +infinity, not zero. -/
def renyiDifference {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] (a : ℝ) (rho sigma : Mat H)
    (N : Superop H K) : EReal :=
  ((1 / (a - 1) : ℝ) : EReal) *
    elog (tr (supportPower rho a * renyiKernel a rho sigma N))

/-- Equations (1.17),(A.17), PDF pp.4,21: for the positive operator X inside
the alpha-norm, alpha log ||X||_alpha = log Tr X^alpha. This retains the primary
normalization, rather than the erroneous auxiliary prefactor in (A.19), p.22. -/
def deltaTilde {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] (a : ℝ) (rho sigma : Mat H)
    (N : Superop H K) : EReal :=
  ((1 / (a - 1) : ℝ) : EReal) * elog (tr (supportPower
    (supportPower rho (1 / 2) * sandwichedKernel a rho sigma N * supportPower rho (1 / 2)) a))

/-- Equations (3.2),(3.8), PDF pp.7–8: -log of squared root fidelity.
The square-root sandwich formula equals the squared trace norm in (3.2). -/
def minRelative {H : Type} [Fintype H] [DecidableEq H]
    (rho tau : Mat H) : EReal :=
  -elog (rootFidelity rho tau ^ 2)

/-- Definition 16, equation (5.1), PDF p.17: actual Petz-recovered reference. -/
def deltaMin {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] (rho sigma : Mat H) (N : Superop H K) : EReal :=
  minRelative rho (petz sigma N (N rho))

/-- Definition 16, equation (5.2), PDF p.17: Dmax as in primary (3.9), in bits. -/
def deltaMax {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] (rho sigma : Mat H) (N : Superop H K) : EReal :=
  maxRelative rho (petz sigma N (N rho))

/-- Equation (1.21), PDF p.5: sigma=rho_AC tensor I_B, in coordinates A x (C x B).
The AC marginal is computed from this same rho; the physical middle register is C. -/
def conditionalSigma {A C B : Type} [Fintype B] [DecidableEq B]
    (rho : Mat (A × (C × B))) : Mat (A × (C × B)) :=
  fun i j => if i.2.2 = j.2.2 then marginalAB rho (i.1, i.2.1) (j.1, j.2.1) else 0

/-- Equations (1.14),(1.22), PDF pp.4–5, in the exact channel specialization (1.21). -/
def conditionalRenyiInformation {A C B : Type} [Fintype A] [Fintype C] [Fintype B]
    [DecidableEq A] [DecidableEq C] [DecidableEq B]
    (a : ℝ) (rho : Mat (A × (C × B))) : EReal :=
  renyiDifference a rho (conditionalSigma rho) traceLeft

/-- Equations (1.15),(1.23), PDF pp.4–5, with the same computed marginal reference. -/
def conditionalRenyiTilde {A C B : Type} [Fintype A] [Fintype C] [Fintype B]
    [DecidableEq A] [DecidableEq C] [DecidableEq B]
    (a : ℝ) (rho : Mat (A × (C × B))) : EReal :=
  deltaTilde a rho (conditionalSigma rho) traceLeft

/-- Equations (5.4),(5.7), PDF pp.17–18: the reference equals
rho_AC^(1/2) rho_C^(-1/2) rho_BC rho_C^(-1/2) rho_AC^(1/2),
with identities on complementary registers. It is constructed by (1.11),(1.21). -/
def conditionalPetzReference {A C B : Type} [Fintype A] [Fintype C] [Fintype B]
    [DecidableEq A] [DecidableEq C] [DecidableEq B]
    (rho : Mat (A × (C × B))) : Mat (A × (C × B)) :=
  petz (conditionalSigma rho) traceLeft (traceLeft rho)

/-- Equation (5.7), PDF p.18: primary min-information definition. -/
def conditionalMinInformation {A C B : Type} [Fintype A] [Fintype C] [Fintype B]
    [DecidableEq A] [DecidableEq C] [DecidableEq B]
    (rho : Mat (A × (C × B))) : EReal :=
  minRelative rho (conditionalPetzReference rho)

/-- Equation (5.4), PDF p.17: primary max-information definition, using 2^lambda
from (3.9), rather than the inconsistent exp(lambda) in the alternative (5.5). -/
def conditionalMaxInformation {A C B : Type} [Fintype A] [Fintype C] [Fintype B]
    [DecidableEq A] [DecidableEq C] [DecidableEq B]
    (rho : Mat (A × (C × B))) : EReal :=
  maxRelative rho (conditionalPetzReference rho)

/-- Appendix A, equation (A.1), PDF p.19: output-space reference P_alpha.
Both outer N(sigma) exponents are (alpha-1)/2. No trace normalization is applied. -/
def outputReference {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] (a : ℝ) (rho sigma : Mat H)
    (N : Superop H K) : Mat K :=
  supportPower (supportPower (N sigma) ((a - 1) / 2) *
    N (supportPower sigma ((1 - a) / 2) * supportPower rho a * supportPower sigma ((1 - a) / 2)) *
    supportPower (N sigma) ((a - 1) / 2)) (1 / a)

/-- Appendix A, equations (A.10)–(A.12), PDF p.20: power stays inside the trace. -/
def jointTrace {H : Type} [Fintype H] [DecidableEq H]
    (a : ℝ) (P Q : Mat H) : ℝ :=
  tr (supportPower (supportPower Q ((a - 1) / 2) * P * supportPower Q ((a - 1) / 2)) (1 / a))

/-! Sanity checks for the kernel convention, exponential convention, zero references,
and the conditioning-register order. These prove only definition sanity, not the paper results. -/

example {H : Type} [Fintype H] [DecidableEq H] (t : ℝ) :
    supportPower (0 : Mat H) t = 0 := by
  simp [supportPower]

example {H : Type} [Fintype H] [DecidableEq H] :
    cfc Real.exp (0 : Mat H) = 1 := by
  simp

example {H K : Type} [Fintype H] [Fintype K] [DecidableEq H] [DecidableEq K]
    (a : ℝ) (rho : Mat H) (N : Superop H K) :
    renyiReference a rho 0 N = 0 ∧ sandwichedReference a rho 0 N = 0 := by
  simp [renyiReference, sandwichedReference, renyiKernel, sandwichedKernel,
    supportPower]

example {H : Type} [Fintype H] [DecidableEq H] (rho : Mat H) :
    minRelative rho 0 = ⊤ := by
  simp [minRelative, rootFidelity, elog]

example (rho : Mat (Unit × (Unit × Unit))) :
    conditionalSigma rho ((), ((), ())) ((), ((), ())) =
      rho ((), ((), ())) ((), ((), ())) := by
  simp [conditionalSigma, marginalAB]

example {H : Type} [Fintype H] [DecidableEq H] (a : ℝ) (Q : Mat H) :
    jointTrace a 0 Q = 0 := by
  simp [jointTrace, supportPower, tr]

example {H : Type} [Fintype H] [DecidableEq H]
    (hid : IsChannel (id : Superop H H)) : IsStrictChannel (id : Superop H H) := by
  exact ⟨hid, fun _ h => h⟩

example {H : Type} [Fintype H] [DecidableEq H]
    (rho sigma : Mat H) (hid : IsChannel (id : Superop H H)) :
    IsSufficient rho sigma (id : Superop H H) := by
  exact ⟨id, hid, rfl, rfl⟩

example {H : Type} [Fintype H] [DecidableEq H] (a : ℝ) (P : Mat H) :
    jointTrace a P 0 = 0 := by
  simp [jointTrace, supportPower, tr]

end QAlgorithms.Papers.Independent.Intakethird100.P52


