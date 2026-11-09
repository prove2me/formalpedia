-- Prove2me | Definitions.Def_LowRandomnessDP_KNorm_Sampling
-- name    : LowRandomnessDP_KNorm_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:02:18.666051+00:00
-- url     : https://prove2.me/theorems/d6842e90-9100-47f9-bb9e-1bd288883090
-- title:
--   Countable Shannon entropy and exact fair-bit decision trees
-- statement:
--   For a mass-one probability mass function $p$ on a finite or countable alphabet, Shannon entropy in bits is
--
--   $$H_2(p)=\sum_i -p_i\log_2p_i\in[0,\infty],$$
--
--   with zero-mass terms equal to zero. A decision tree is represented by a prefix-free set of finite binary terminal words and an output label on each leaf. A word $w$ has probability $2^{-|w|}$ under fresh independent unbiased bits. The leaf probabilities sum to one, expressing almost-sure termination. The induced output law sums the probabilities of all leaves with the same label. Its actual expected consumed bits are
--
--   $$\mathbb E[L]=\sum_w |w|2^{-|w|}.$$
--
--   Randomness complexity is the supremum of this expectation over inputs. Expected norm error uses this same tree's output distribution. Infinite entropy and infinite expected stopping cost remain representable. Empty terminal words allow deterministic output without consuming a bit. No finite depth, finite support or computability condition is imposed.
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf, Definitions 2.8–2.9 and Theorem 2.10, PDF 8 / printed 6

import Definitions.Def_LowRandomnessDP_KNorm_Privacy

open MeasureTheory

open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace LowRandomnessDP.KNorm

/-- Shannon entropy in BITS. A PMF has finite individual masses in [0,1]; the
zero-mass term is zero. The outer sum retains infinite entropy. -/
def entropyBits {ι : Type} (p : PMF ι) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (Real.negMulLog (p i).toReal / Real.log 2)

/-- Fresh fair independent bits give cylinder probability 2^(-length). -/
def wordMass (w : List Bool) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ w.length

/-- A possibly infinite binary decision tree encoded by prefix-free terminal words.
Mass one is almost-sure termination; multiple leaves may have the same label. -/
structure DDG (O : Type) where
  leaves : Set (List Bool)
  label : leaves → O
  prefix_free : ∀ u ∈ leaves, ∀ v ∈ leaves, List.IsPrefix u v → u = v
  terminates : HasSum (fun w : leaves => wordMass w.val) 1

def DDG.leafPMF {O : Type} (T : DDG O) : PMF T.leaves :=
  ⟨fun w => wordMass w.val, T.terminates⟩

def DDG.law {O : Type} (T : DDG O) : PMF O :=
  T.leafPMF.map T.label

/-- Actual expected consumed fair bits, NOT entropy. -/
def DDG.expectedBits {O : Type} (T : DDG O) : ℝ≥0∞ :=
  ∑' w : T.leaves, wordMass w.val * (w.val.length : ℝ≥0∞)

def randomnessComplexity {D O : Type} (T : D → DDG O) : ℝ≥0∞ :=
  ⨆ x, (T x).expectedBits

def outputEntropy {D O : Type} (M : D → PMF O) : ℝ≥0∞ :=
  ⨆ x, entropyBits (M x)

/-- Nonnegative expected K-norm error of this very tree's output law. -/
def expectedError {d : ℕ} (K : Set (Vec d)) (T : DDG (Vec d))
    (v : Vec d) : ℝ≥0∞ :=
  ∑' z, T.law z * ENNReal.ofReal (kNorm K (z - v))

end LowRandomnessDP.KNorm


