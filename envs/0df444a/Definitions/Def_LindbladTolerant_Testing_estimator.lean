-- Prove2me | Definitions.Def_LindbladTolerant_Testing_estimator
-- name    : LindbladTolerant_Testing_estimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:02:20.390879+00:00
-- url     : https://prove2.me/theorems/b1c58014-c7f6-4924-a4ce-9831571316c4
-- title:
--   The explicit three-batch jump-state functional estimator
-- statement:
--   Fix $k\ge1$ and accuracy $0<\delta\le1/16$. Let $\beta=1/300$ and $K_k=2\cdot16^k(4^k-1)/e$. The fixed routine uses discovery, fresh product-Pauli records, and fresh full-SR SWAP pairs, with sizes
--   $$m=\left\lceil\frac{2K_k}{\beta\delta}\right\rceil,\quad
--   N=\left\lceil\max\left\{\frac{32\cdot6^k(2^k-1)}{\beta\delta^2},\frac{8\cdot6^k4^k m}{\sqrt\beta\delta}\right\}\right\rceil,\quad
--   s=\left\lceil8\delta^{-2}\log(2/\beta)\right\rceil.$$
--   If a discovery label has weight greater than $k$, return zero. Otherwise average the $s$ signs to obtain $\widehat\mu$, compute the ordered-pair statistic $\widehat G$, and output
--   $$\widehat h=\min\{(2^k+1)/2,\max\{0,\widehat\mu+\widehat G/2\}\}.$$
--   Its output law is a finite sum of the actual independent batches' Born probabilities. It is defined on arbitrary input density matrices; accuracy is asserted only on the promised jump states.
--
--   The total copy count is $S(k,\delta)=m+N+2s$. With $a_k=2K_k/\beta$, $b_k=32\cdot6^k(2^k-1)/\beta$, and $d_k=8\cdot6^k4^k/\sqrt\beta$, fix the dimension-independent constant
--   $$C_k=\left\lceil a_k+4+\max\{b_k,d_k(a_k+1)\}+16\log(2/\beta)\right\rceil.$$
--   These constants depend only on $k$. Theorem 4.3 must prove the accuracy and copy bounds; neither is a field of the estimator.
--
--   **Formalization Note** On the immediate-return branch, unused measurement batches are marginalized. This gives the same output law and the same worst-case copy bound as stopping that branch immediately.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, Theorem 4.3 proof, pp.22–23, PDF pp.22–23, Eqs.(77)–(81); ceiling-derived C_k from the displayed batch sizes

import Definitions.Def_LindbladTolerant_Testing_measurement_model

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators Matrix

namespace LindbladTolerant.Testing
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proof of Theorem 4.3, pp.22–23. All batch sizes use only k and delta. -/
def beta : ℝ := 1/300
def approximationConstant (k : ℕ) : ℝ :=
  2 * (16 : ℝ)^k * ((4 : ℝ)^k - 1) / Real.exp 1
def discoveryCount (k : ℕ) (delta : ℝ) : ℕ :=
  ⌈2 * approximationConstant k / (beta * delta)⌉₊
def recordCount (k : ℕ) (delta : ℝ) : ℕ :=
  ⌈max (32 * (6 : ℝ)^k * ((2 : ℝ)^k - 1) / (beta * delta^2))
    (8 * (6 : ℝ)^k * (4 : ℝ)^k * (discoveryCount k delta : ℝ) /
      (Real.sqrt beta * delta))⌉₊
def swapCount (delta : ℝ) : ℕ := ⌈8 * delta⁻¹^2 * Real.log (2/beta)⌉₊
def copyCount (k : ℕ) (delta : ℝ) : ℕ :=
  discoveryCount k delta + recordCount k delta + 2 * swapCount delta

def copyConstant (k : ℕ) : ℝ :=
  let a := 2 * approximationConstant k / beta
  let b := 32 * (6 : ℝ)^k * ((2 : ℝ)^k - 1) / beta
  let d := 8 * (6 : ℝ)^k * (4 : ℝ)^k / Real.sqrt beta
  (⌈a + 4 + max b (d * (a+1)) + 16 * Real.log (2/beta)⌉₊ : ℝ)

def functionalBound (k : ℕ) : ℝ := ((2 : ℝ)^k + 1) / 2

abbrev EstimatorSample (n k : ℕ) (delta : ℝ) :=
  (Fin (discoveryCount k delta) → Pauli n) ×
    ((Fin (recordCount k delta) → ProductRecord n) × (Fin (swapCount delta) → Bool))

variable {n : ℕ}

def estimatorWeight (sigma : Op (Qubits n × Qubits n)) (k : ℕ) (delta : ℝ)
    (x : EstimatorSample n k delta) : ℝ :=
  discoveryWeight sigma x.1 * recordsWeight sigma (discoveredSupport x.1) x.2.1 *
    ∏ j, swapWeight sigma (x.2.2 j)

def estimatorValue (k : ℕ) (delta : ℝ) (x : EstimatorSample n k delta) : ℝ :=
  if ∃ j, k < weight (x.1 j) then 0 else
    min (functionalBound k) (max 0
      ((∑ j, sign (x.2.2 j)) / (swapCount delta : ℝ) +
        uStatistic (candidateSet k x.1) x.2.1 / 2))

/-- This is the fixed physical estimator's output law, not an assumed successful
estimator. The three products are Born laws of disjoint batches. Unused batches
on the immediate-return branch are marginalized. -/
def estimatorProbability (sigma : Op (Qubits n × Qubits n))
    (k : ℕ) (delta : ℝ) (event : ℝ → Prop) : ℝ :=
  ∑ x : EstimatorSample n k delta,
    if event (estimatorValue k delta x) then estimatorWeight sigma k delta x else 0

end LindbladTolerant.Testing


