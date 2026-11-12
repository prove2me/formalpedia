-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
-- name    : QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:33:18.891365+00:00
-- url     : https://prove2.me/theorems/8968cd09-de5c-41de-9ba5-a1eacd1c9927
-- title:
--   Entropy
-- statement:
--   Definitions and structural lemmas for Entropy, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/Entropy.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
set_option autoImplicit false
open scoped BigOperators
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section
def hh18ParameterInterval : Set ℝ := Set.Ioo (1 / 6 : ℝ) (1 / 3 : ℝ)
noncomputable def hh18BinaryEntropy (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2
noncomputable def hh18Gamma (p : ℝ) : ℝ :=
  3 * (1 - hh18BinaryEntropy p) / hh18BinaryEntropy (3 * p)
noncomputable def hh18GammaSet : Set ℝ := hh18Gamma '' hh18ParameterInterval
noncomputable def hh18GammaInf : ℝ := sInf hh18GammaSet
def p0Q : ℚ := HH18ParameterSequence.p0
def p0R : ℝ := (p0Q : ℝ)
def p0q : ℝ := 1 - p0R
def p0u : ℝ := 3 * p0R
def p0v : ℝ := 1 - p0u
def logOneAddTerm (a : ℝ) (k : Nat) : ℝ :=
  (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * (a / (a + 2)) ^ (2 * k + 1)
def logOneAddPartial (a : ℝ) (N : Nat) : ℝ :=
  ∑ k ∈ Finset.range N, logOneAddTerm a k
def logOneAddRemainder (y : ℝ) (N : Nat) : ℝ :=
  2 * y ^ (2 * N + 1) / ((2 * N + 1) * (1 - y ^ 2))
def s1 (y : ℝ) : ℝ := 2 * y
def s3 (y : ℝ) : ℝ := 2 * y + 2 * y ^ 3 / 3 + 2 * y ^ 5 / 5
def s4 (y : ℝ) : ℝ := s3 y + 2 * y ^ 7 / 7
def y2 : ℝ := 1 / 3
def yA : ℝ := 20629 / 520629
def yB : ℝ := 270629 / 1729371
def yC : ℝ := 188113 / 1811887
def yD : ℝ := 61887 / 438113
def aA : ℝ := 82516 / 1000000
def aB : ℝ := p0R / p0q
def aC : ℝ := p0v / p0u
def aD : ℝ := (1 - 4 * p0v) / (4 * p0v)
def log2Upper : ℝ := s4 y2 + 1 / 78732
def logAUpper : ℝ := s1 yA + 1 / 23400
def logBLower : ℝ := s3 yB
def logCLower : ℝ := s3 yC
def logDLower : ℝ := s3 yD
def p0A : ℝ := Real.log (4 * p0R)
def p0B : ℝ := Real.log (1 / p0q)
def p0C : ℝ := Real.log (1 / p0u)
def p0D : ℝ := Real.log (1 / (4 * p0v))
def s1Q (y : ℚ) : ℚ := 2 * y
def s3Q (y : ℚ) : ℚ := 2 * y + 2 * y ^ 3 / 3 + 2 * y ^ 5 / 5
def s4Q (y : ℚ) : ℚ := s3Q y + 2 * y ^ 7 / 7
def y2Q : ℚ := 1 / 3
def yAQ : ℚ := 20629 / 520629
def yBQ : ℚ := 270629 / 1729371
def yCQ : ℚ := 188113 / 1811887
def yDQ : ℚ := 61887 / 438113
def p0CertifiedGapQ : ℚ :=
    (2188113 / 2000) * s3Q yBQ
  + (275229693 / 1000000) * s3Q yCQ
  + (63770307 / 1000000) * s3Q yDQ
  - (811887 / 2000) * (s1Q yAQ + 1 / 23400)
  - (280286193 / 500000) * (s4Q y2Q + 1 / 78732)
def p0LinearLower : ℝ :=
    (2188113 / 2000) * logBLower
  + (275229693 / 1000000) * logCLower
  + (63770307 / 1000000) * logDLower
  - (811887 / 2000) * logAUpper
  - (280286193 / 500000) * log2Upper
def p0EntropyGap : ℝ :=
  339 * Real.binEntropy p0u - 1500 * (Real.log 2 - Real.binEntropy p0R)
end
end QEC.Distillation.HH18.HH18SublogarithmicEntropy


