-- Prove2me | Definitions.Def_BMPV1173_Verification_QueryComplexity
-- name    : BMPV1173_Verification_QueryComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:03:31.71052+00:00
-- url     : https://prove2.me/theorems/c94acda3-6063-43df-9d86-7ce67abac951
-- title:
--   Least worst-case XOR query count and uniform soft-O bounds
-- statement:
--   An achievable query count means there is one finite complex unitary circuit, with a unit start vector and a fixed Boolean measurement readout, that succeeds on every input in the domain. Its count is the number of XOR entry-oracle calls. The least count is an extended-natural infimum, with top for an empty achievable set. The soft-O interface quantifies an absolute positive coefficient, a natural logarithmic exponent and a threshold before the dimension, and then chooses a circuit before the unknown input. No desired exponent or success probability is built into an algorithm.
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, §2.1 and p.3 footnote 2, printed/PDF p.13 and p.3 footnote 2.

import Definitions.Def_BMPV1173_Verification_Problems

/-! The least achievable worst-case XOR query count, §2.1 p.13.
The infimum is taken in ENat: the empty achievable set has infimum top. -/
namespace BMPV1173.Verification

/-- One circuit and one readout, chosen before the unknown input; T counts
all calls to the direct Boolean XOR entry oracle, including any amplification. -/
def HasDecision {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Set (ι → Bool)) (f : (ι → Bool) → Bool) (ε : ℝ) (T : ℕ) : Prop :=
  ∃ (w : ℕ) (A : QAlgorithms.QueryAlg ι Bool (Fin w) T)
    (out : (ι × Bool) × Fin w → Bool),
    ∀ x ∈ D, 1 - ε ≤ A.outputProb (QAlgorithms.xorOracle x) out (f x)

noncomputable def queryComplexity {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Set (ι → Bool)) (f : (ι → Bool) → Bool) : ENat :=
  sInf {q | ∃ T : ℕ, q = (T : ENat) ∧ HasDecision D f (1 / 3) T}

noncomputable def qBMPV (n : ℕ) : ENat := queryComplexity Set.univ (@bmpv n)
noncomputable def qBMPVLE (n : ℕ) : ENat := queryComplexity Set.univ (@bmpvLE n)
noncomputable def qBMPVGE (n : ℕ) : ENat := queryComplexity Set.univ (@bmpvGE n)
noncomputable def qOV (n : ℕ) : ENat := queryComplexity Set.univ (@ov n)
noncomputable def qTriangle (n : ℕ) : ENat := queryComplexity {x | SimpleGraphInput x} (@triangle n)

/-- Only powers of log n are suppressed. Constants, exponent and threshold
precede n, and the algorithm precedes all unknown input bits. -/
def SoftDecisionBound (ι : ℕ → Type) [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (D : ∀ n, Set (ι n → Bool)) (f : ∀ n, (ι n → Bool) → Bool) (p : ℝ) : Prop :=
  ∃ (C : ℝ) (k N : ℕ), 0 < C ∧ ∀ n : ℕ, max 1 N ≤ n →
    ∃ T : ℕ, HasDecision (D n) (f n) (1 / 3) T ∧
      (T : ℝ) ≤ C * (n : ℝ) ^ p * (1 + Real.log (n : ℝ)) ^ k

end BMPV1173.Verification


