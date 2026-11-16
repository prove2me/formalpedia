-- Prove2me | Definitions.Def_ZLIPPadding_Padding_Supplement_Reductions
-- name    : ZLIPPadding_Padding_Supplement_Reductions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:17:57.408775+00:00
-- url     : https://prove2.me/theorems/dc033b89-8a2f-4346-abe0-18cee516ad3d
-- title:
--   Uniform oracle-reduction and recovery specifications
-- statement:
--   Specify the conclusions of the orbit-equivalence and short-shell recovery theorems using the executable finite programs and actual oracle kernels. For each fixed efficiently computable profile family, the two orbit-equivalence directions share uniform polynomial witnesses fixed before every input basis and oracle rule. Their parameter scale includes
--
--   $$n+m+\lceil\eta_a^{-1}\rceil+\lceil\log_2(1/\delta)\rceil+\ell.$$
--
--   The reverse direction requires exactly uniform conditional output on the distinct profile orbit, with explicit failure allowed. Short-shell recovery covers both exact uniform shell laws and every invariant shell law with flat mass at least one half. The positive-sign label-recovery specification uses the law's actual moments and retains the complete sample thresholds. These are conclusion predicates; no algorithm or successful solver is postulated as an input.
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed pp. 13–14, 25–26 (PDF pp. 14–15, 26–27), Theorem 3.3, Lemma 6.2 and Theorem 6.3

import Definitions.Def_ZLIPPadding_Padding_Supplement_Walk
import Definitions.Def_ZLIPPadding_Padding_Supplement_Counting

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

def orbitResources {n : ℕ} (B : QMat n) (a : ZVec n) (delta : ℝ) : ℕ :=
  n + (iznorm a).toNat + invSize (orbitEta a) + errorBits delta + (encBasis B).length

/-- Both directions, one finite program per direction and absolute polynomial witnesses
for the specified profile family, before all input bases and oracle rules. -/
def OrbitEquivalence (a : (n : ℕ) → ZVec n) : Prop :=
  ∃ (recover sample : Program) (c d : ℕ), 0 < c ∧
  ∀ n (B : QMat n) (delta : ℝ), 2 ≤ n → PromisedBasis B →
    0 < delta → delta < 1 →
    let bound := powerBound c d (orbitResources B (a n) delta)
    (∀ A : Kernel, OrbitSampler a A →
      (∀ s, run recover A bound (recoverInput B (errorBits delta)) s ≠ 0 →
        Budget bound s ∧ (s.core.output = [] ∨ correctBasisOutput B s)) ∧
      prob (run recover A bound (recoverInput B (errorBits delta)))
        {s | correctBasisOutput B s} ≥ 1-delta) ∧
    (∀ A : Kernel, BasisOracle A →
      let law := decoded (decVec n) sample A bound (recoverInput B (errorBits delta))
      (∀ s, run sample A bound (recoverInput B (errorBits delta)) s ≠ 0 → Budget bound s) ∧
      prob law {z | z.isSome} ≥ 1-delta ∧
      ∀ O M, BasisWitness B O M → ∀ z : ZVec n,
        law (some z) = mass law {z | z.isSome} *
          (if M.mulVec z ∈ orbit (a n) then ((orbit (a n)).card : ℝ≥0∞)⁻¹ else 0))

def recoveryResources {n : ℕ} (B : QMat n) (m : ℕ) (delta : ℝ) : ℕ :=
  n+m+errorBits delta+(encBasis B).length
def ShellRecovery : Prop :=
  ∃ (P : Program) (c d : ℕ), 0 < c ∧
    ∀ n m (B : QMat n) O M (μ ν : PMF (ZVec n)) (delta : ℝ),
      shortRange n m → CoordLaw B O M μ ν →
      (UniformOn μ (shell n m) ∨
        (ShellLaw m μ ∧ SignedInvariant μ ∧ prob μ (↑(flat n m)) ≥ 1/2)) →
      0 < delta → delta < 1 →
      let bound := powerBound c d (recoveryResources B m delta)
      let law := run P (incrementKernel B ν) bound (sampleInput B m (errorBits delta))
      (∀ s, law s ≠ 0 → Budget bound s ∧
        (s.core.output = [] ∨ correctBasisOutput B s) ∧
        ∀ w ∈ s.queries, w = encBasis B) ∧
      prob law {s | correctBasisOutput B s} ≥ 1-delta

/-- Complete sample/error guarantee for the positive-sign classifier; no uniform-shell
moments are substituted for the law's actual moments. -/
def PositiveLabelRecovery : Prop :=
  ∃ (P : Program) (c d : ℕ), LabelProgram P c d ∧
    ∀ n m (μ : PMF (ZVec n)), shortRange n m → ShellLaw m μ → SignedInvariant μ →
      LabelGuarantee P c d true n m μ ((m : ℝ)/(4*n))

end
end ZLIPPadding.Padding.Supplement


