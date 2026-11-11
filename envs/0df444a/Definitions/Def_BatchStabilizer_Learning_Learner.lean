-- Prove2me | Definitions.Def_BatchStabilizer_Learning_Learner
-- name    : BatchStabilizer_Learning_Learner
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:38:04.291104+00:00
-- url     : https://prove2.me/theorems/ce146208-fc9a-43fa-bad0-2fbb4a588830
-- title:
--   Algorithm 5 and §9.4 — the complete learner as a measurement program with classical operation counts
-- statement:
--   Algorithm 5 on parameters $(n,\tau,\varepsilon,\delta)$ runs Algorithm 1 independently $a$ times and concatenates the seed lists into $\mathcal L$; measures a fresh batch $B_3$ of $m_3$ Bell records and forms $U=B_3+B_3$; runs Algorithm 2 with a fresh batch $B_4$ of $m_4$ records, returning $|0^n\rangle$ if $\mathcal L_{\rm full}=\varnothing$; runs Algorithm 3 with a fresh batch $B_5$, returning $|0^n\rangle$ if $\mathcal L_{\rm cert}=\varnothing$; forms the greedy representatives $\mathcal R$ and returns $|0^n\rangle$ if $|\mathcal R|>4/\tau^2$, before any representative is measured; runs Algorithm 4 with $m_6$ fresh copies per representative, returning $|0^n\rangle$ if the signed list $\mathcal C$ is empty; and finally draws $GK$ independent shadow records (with $M=M_{\max}$) and returns a candidate of maximal estimated fidelity. No step is ever retried.
--
--   The output is a stabilizer projector together with the number of classical operations performed on the transcript, counted stage by stage: subset enumeration and Gaussian elimination in Algorithm 1 ($m_0\cdot\#\{R:|R|\le k\}\cdot(k+1)^2\cdot2n$ per run), the sumset ($m_3^2\cdot2n$), filtering, scoring and elimination in Algorithm 2, filtering in Algorithm 3 ($|\mathcal L_{\rm full}|m_5(2n)^2$), pairwise intersections for the representatives ($|\mathcal L_{\rm cert}|^2(2n)^3$), tableau sign computations ($|\mathcal L_{\rm cert}|m_6(2n)^3+|\mathcal C|(2n)^2$), and the shadow stage ($N_{\rm sh}(2n)^2+|\mathcal C|N_{\rm sh}(2n)^3+|\mathcal C|N_{\rm sh}^2$).
--
--   **Formalization Note** The redundant second representative cap (lines 21–23) is omitted; it never fires after the first. The operation counts are an explicit unit-cost model of the procedures named in §9.4, computed from the realized list sizes of the transcript.
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 37–41 (PDF p. 38–42), Algorithm 5, equations (107)–(114), §§9.1–9.4

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Algorithms

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
noncomputable section

namespace BatchStabilizer.Learning

open LindbladTolerant.Testing

/-! Algorithm 5 (proper agnostic stabilizer learning) as a measurement program, with an explicit
count of classical bit operations (Ching-Yi Lai, STOC 2027 submission #1629 (October 2026),
Algorithm 5, printed p. 38 (PDF p. 39), §§9.1–9.4, printed pp. 37–41 (PDF pp. 38–42)). -/

/-! ### Classical operation counts (unit: one bit or arithmetic operation; §9.4) -/

/-- Algorithm 1, one run: for every anchor and every subset of at most `k` records, Gaussian
elimination of at most `k` labels of length `2n` and pairwise isotropy tests. -/
def seedCost (n : ℕ) (τ : ℝ) : ℕ :=
  m0 τ * (smallSubsets (m1 τ) (m2 τ) (kk τ)).length * (kk τ + 1) ^ 2 * (2 * n)

/-- The sumset: `m₃²` sums of labels of length `2n`. -/
def sumsetCost (n m : ℕ) : ℕ := m ^ 2 * (2 * n)

/-- Algorithm 2: per seed, the filter test of each record, the score of each sumset label,
and Gaussian elimination of `span(L ∪ V_L)`. -/
def extendCost (n k seeds sums m : ℕ) : ℕ :=
  seeds * (m * (k + 1) * (2 * n) + sums * (m + 2 * n) * (2 * n) + (sums + k + 1) ^ 2 * (2 * n))

/-- Algorithm 3: per candidate, the filter test of every record. -/
def certCost (n full m : ℕ) : ℕ := full * m * (2 * n) ^ 2

/-- Greedy representatives and assignment: pairwise intersections by Gaussian elimination. -/
def repCost (n cert : ℕ) : ℕ := cert ^ 2 * (2 * n) ^ 3

/-- Algorithm 4: per candidate and outcome, intersection and sign computation by stabilizer
tableaux, plus `O(n²)` per enumerated signed state. -/
def signCost (n cert m cands : ℕ) : ℕ := cert * m * (2 * n) ^ 3 + cands * (2 * n) ^ 2

/-- Shadows: sampling and recording `N` Clifford tableaux, one stabilizer overlap per candidate
and record, and the medians. -/
def shadowCost (n cands N : ℕ) : ℕ := N * (2 * n) ^ 2 + cands * N * (2 * n) ^ 3 + cands * N ^ 2

/-- `a` independent runs of Algorithm 1; the seed list `ℒ` is the concatenation of their lists. -/
def seedRuns (n : ℕ) (τ : ℝ) : ℕ → Prog n (List (Sub n))
  | 0 => .ret []
  | a + 1 => (alg1Prog n τ).bind fun L => (seedRuns n τ a).bind fun rest => .ret (L ++ rest)

open Classical in
/-- Algorithm 5.  Output: a stabilizer projector `|ϕ̂⟩⟨ϕ̂|` (the classical description is a
full isotropic label space with generator signs, or `|0ⁿ⟩` on an abort) together with the
number of classical operations performed on this transcript.  Batch sizes are the explicit
schedules; the shadow count uses the deterministic bound `M_max`. -/
def algorithm5 (n : ℕ) (τ ε δ : ℝ) : Prog n (Op (Qubits n) × ℕ) :=
  (seedRuns n τ (aa δ)).bind fun seeds =>
  .bell (m3 n τ δ) fun B3 =>
  .bell (m4 τ δ seeds.length (sumsetAll B3).card) fun B4 =>
  let w2 := aa δ * seedCost n τ + sumsetCost n (m3 n τ δ) +
    extendCost n (kk τ) seeds.length (sumsetAll B3).card (m4 τ δ seeds.length (sumsetAll B3).card)
  let full := extend τ δ seeds (sumsetAll B3) B4
  if full = [] then .ret (ArbLindbladLearn.zeroProj n, w2) else
  .bell (m5 τ δ full.length) fun B5 =>
  let cert := certify τ δ full B5
  let w3 := w2 + certCost n full.length (m5 τ δ full.length)
  if cert = [] then .ret (ArbLindbladLearn.zeroProj n, w3) else
  let reps := greedyReps n (tt τ) cert
  let w4 := w3 + repCost n cert.length
  if (4 / τ ^ 2 : ℝ) < (reps.length : ℝ) then .ret (ArbLindbladLearn.zeroProj n, w4) else
  (alg4Prog n τ δ cert reps).bind fun cands =>
  let w5 := w4 + signCost n cert.length (m6 τ δ) cands.length
  if cands = [] then .ret (ArbLindbladLearn.zeroProj n, w5) else
  .shadow (shadowGroups δ (Mmax τ δ) * shadowGroupSize ε) fun R =>
  .ret (selectBest cands
      (shadowEstimate (shadowGroupSize ε) (shadowGroups δ (Mmax τ δ)) R),
    w5 + shadowCost n cands.length (shadowGroups δ (Mmax τ δ) * shadowGroupSize ε))

end BatchStabilizer.Learning


