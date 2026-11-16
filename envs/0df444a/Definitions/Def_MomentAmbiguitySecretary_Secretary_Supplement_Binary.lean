-- Prove2me | Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Binary
-- name    : MomentAmbiguitySecretary_Secretary_Supplement_Binary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:47:42.097096+00:00
-- url     : https://prove2.me/theorems/b2065ddf-0897-4429-9910-6e11bc07155e
-- title:
--   Binary nodes, finite barycentric weights, limits and atomic measures
-- statement:
--   The Section 8.1 construction on $x_0=1,x_1=B,x_j=(nB)^{B^{j-2}}$, with actual finite barycentric products normalized at node 2, their limiting weights, parity sums, raw atomic measures, and the exact $L_M,C_M$ decay constants. No normalization, convergence, moment, or atom estimate is assumed by these definitions.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Definitions, PDF/printed pp.20–29; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Laws

open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace MomentAmbiguitySecretary.Secretary.Supplement
noncomputable section

/-- Section 8.1, pp.20–22. Parameters are unrestricted here; results require n,B ≥ 3. -/
def binaryNode (n B j : ℕ) : ℝ≥0 :=
  if j = 0 then 1 else if j = 1 then B else (n * B : ℝ≥0) ^ (B ^ (j - 2))

def barycentric (n B K j : ℕ) : ℝ :=
  (∏ i ∈ (Finset.range (K + 3)).erase j,
    ((binaryNode n B j : ℝ) - (binaryNode n B i : ℝ)))⁻¹

def finiteWeight (n B K j : ℕ) : ℝ :=
  barycentric n B K j / barycentric n B K 2

/-- A total limit selector. Lemma 8.1 asserts convergence to this value. -/
def binaryWeight (n B j : ℕ) : ℝ :=
  limUnder atTop (fun K : ℕ => finiteWeight n B K j)

def binaryW (n B : ℕ) : ℝ := ∑' j : ℕ, if Even j then binaryWeight n B j else 0
def binaryWMinus (n B : ℕ) : ℝ := ∑' j : ℕ, if Odd j then |binaryWeight n B j| else 0

def binaryP (n B j : ℕ) : ℝ := if Even j then binaryWeight n B j / binaryW n B else 0
def binaryQ (n B j : ℕ) : ℝ := if Odd j then |binaryWeight n B j| / binaryW n B else 0

def binaryNu (n B : ℕ) : Measure ℝ≥0 :=
  Measure.sum fun j : ℕ => ENNReal.ofReal (binaryP n B j) • Measure.dirac (binaryNode n B j)

def binaryMu (n B : ℕ) : Measure ℝ≥0 :=
  Measure.sum fun j : ℕ => ENNReal.ofReal (binaryQ n B j) • Measure.dirac (binaryNode n B j)

def binaryEvenSupport (n B : ℕ) : Set ℝ≥0 :=
  {x | ∃ j : ℕ, Even j ∧ x = binaryNode n B j}
def binaryOddSupport (n B : ℕ) : Set ℝ≥0 :=
  {x | ∃ j : ℕ, Odd j ∧ x = binaryNode n B j}

/-- Signed subtraction occurs in ℝ before ceiling; max(0,ceil(t)) is Int.toNat. -/
def decayL (B M : ℕ) : ℕ :=
  (Int.ceil (((M : ℝ) - 2) / (1 - 1 / (B : ℝ)))).toNat

def decayC012 (n B M : ℕ) : ℝ :=
  max (max (2 * (n : ℝ)) (2 * (n : ℝ) * (B : ℝ) ^ M)) ((n * B : ℝ) ^ M)

def decayCTail (n B M : ℕ) : ℝ :=
  if M ≤ 2 then 8 * (n * B : ℝ) ^ 2 else
    8 * (n * B : ℝ) ^ 2 *
      max ((binaryNode n B (decayL B M + 2) : ℝ) ^ ((M : ℤ) - 2))
        ((2 : ℝ) ^ decayL B M)

def decayC (n B M : ℕ) : ℝ := max (decayC012 n B M) (decayCTail n B M)

end
end MomentAmbiguitySecretary.Secretary.Supplement


