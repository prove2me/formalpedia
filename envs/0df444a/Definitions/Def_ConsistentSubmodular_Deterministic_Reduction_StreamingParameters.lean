-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_StreamingParameters
-- name    : ConsistentSubmodular_Deterministic_Reduction_StreamingParameters
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:09:57.944918+00:00
-- url     : https://prove2.me/theorems/5ee68da1-2c5c-48ac-b838-1887adc4742c
-- title:
--   Streaming transfer parameters for accuracy $1/N$: threshold, parameter structure $(\kappa,b,J,\ell)$, and its canonical choice (Appendix B.2.4)
-- statement:
--   Fix an accuracy parameter $N$ (so that $\eta=1/N$), a bound $H$ on the number of forced (heavy) elements of a local window, and a cardinality budget $k$.
--
--   - `transferThreshold` $N\,H$: $\;N\bigl(H+2(4N+1)+2\bigr)$, the least budget $k$ for which the parameters below can be chosen.
--   - `TransferParameters` $N\,H\,k$: a structure with natural-number fields `core` $=\kappa$, `block` $=b$, `candidates` $=J$, `interval` $=\ell$ (the parameters of Appendix B.2.4), subject to: $\kappa\le k$; $H\le\kappa$; $b>0$; $H\le b$; $\ell>0$; $J\ell\le b$; $J\ge 1$; the growth condition $3\le (J-1)/N$; the capacity condition $\kappa+b+H+4b+1\le k$; the rounding slack $\kappa/N\le b$; the thinning condition $(1-10/N)\,k\le\kappa$; the time condition $k\le 4N\,J\,\ell$; and $J=4N+1$.
--   - `transferParameters` $N\,H\,k$: for $N\ge 200$ and $k\ge$ `transferThreshold` $N\,H$, the canonical instance of this structure with $b=\lfloor k/N\rfloor$, $J=4N+1$, $\ell=\lfloor b/J\rfloor$ and $\kappa=k-10b$. The hypotheses $200\le N$ and $\texttt{transferThreshold}\le k$ are arguments of the definition, and all the required inequalities are verified inside it.
--
--   These integer capacities and block lengths leave room for the forced elements, a rolling buffer, and one temporary extra insertion.
--
--   These definitions supply the numerical parameters of the reduction in Appendix B.2.4 from fractional (rounded) windows to a consistent deterministic algorithm, and are used by the protected clock and the uniform transfer statements.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/StreamingParameters.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ProtectedClock

noncomputable section

namespace ConsistentSubmodular

def transferThreshold (N H : ℕ) : ℕ := N * (H + 2 * (4 * N + 1) + 2)

/-- Integer capacities and block lengths, with enough room for forced
elements, the rolling buffer, and a temporary extra insertion. These are the
parameters `κ`, `b`, `J`, and `ℓ` of Appendix B.2.4 for `η = 1/N`, here `core`,
`block`, `candidates`, and `interval`; `transferParameters` takes
`b = ⌊k/N⌋`, `J = 4N + 1`, `ℓ = ⌊b/J⌋`, and `κ = k - 10 b`. -/
structure TransferParameters (N H k : ℕ) where
  core : ℕ
  block : ℕ
  candidates : ℕ
  interval : ℕ
  core_le : core ≤ k
  core_large : H ≤ core
  block_pos : 0 < block
  heavy_le_block : H ≤ block
  interval_pos : 0 < interval
  fit : candidates * interval ≤ block
  candidates_pos : 1 ≤ candidates
  growth : 3 ≤ ((candidates - 1 : ℕ) : ℝ) * ((1 : ℝ) / N)
  capacity : core + block + H + 4 * block + 1 ≤ k
  rounding_slack : (core : ℝ) / N ≤ block
  thinning : (1 - 10 * ((1 : ℝ) / N)) * k ≤ (core : ℝ)
  enough_time : k ≤ 4 * N * candidates * interval
  candidates_eq : candidates = 4 * N + 1

def transferParameters (N H k : ℕ) (hN : 200 ≤ N)
    (hk : transferThreshold N H ≤ k) : TransferParameters N H k := by
  let b := k / N
  let J := 4 * N + 1
  let ell := b / J
  let κ := k - 10 * b
  have hN0 : 0 < N := by omega
  have hJ0 : 0 < J := by dsimp [J]; omega
  have hbfull : H + 2 * J + 2 ≤ b := by
    apply (Nat.le_div_iff_mul_le hN0).mpr
    dsimp [transferThreshold, J] at hk ⊢
    nlinarith
  have hbH : H ≤ b := by omega
  have hbJ : 2 * J ≤ b := by omega
  have hb0 : 0 < b := by omega
  have hbN : b * N ≤ k := Nat.div_mul_le_self k N
  have hb20 : 20 * b ≤ k := by nlinarith
  have hb10 : 10 * b ≤ k := by omega
  have hκ : κ + 10 * b = k := by dsimp [κ]; omega
  have hell : 2 ≤ ell := (Nat.le_div_iff_mul_le hJ0).mpr (by nlinarith)
  have hfit : J * ell ≤ b := by simpa [ell, Nat.mul_comm] using Nat.div_mul_le_self b J
  have hkbound : k < N * (b + 1) := Nat.lt_mul_div_succ k hN0
  have hbbound : b < J * (ell + 1) := Nat.lt_mul_div_succ b hJ0
  have ht1 : b + 1 ≤ 2 * J * ell := by nlinarith
  have ht2 : N * (b + 1) ≤ N * (2 * J * ell) := Nat.mul_le_mul_left N ht1
  have htime : k ≤ 4 * N * J * ell := by nlinarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  refine {
    core := κ
    block := b
    candidates := J
    interval := ell
    core_le := by omega
    core_large := by omega
    block_pos := hb0
    heavy_le_block := hbH
    interval_pos := by omega
    fit := hfit
    candidates_pos := by omega
    growth := ?_
    capacity := by omega
    rounding_slack := ?_
    thinning := ?_
    enough_time := htime
    candidates_eq := rfl }
  · have heq : J - 1 = 4 * N := by simp [J]
    rw [heq]
    push_cast
    have hid : (4 * (N : ℝ)) * (1 / N) = 4 := by field_simp
    rw [hid]
    norm_num
  · have hbNlarge : N ≤ 10 * b := by dsimp [J] at hbfull; nlinarith
    have hcN : κ ≤ b * N := by nlinarith
    apply (div_le_iff₀ hNr).mpr
    exact_mod_cast hcN
  · have heq : (κ : ℝ) + 10 * (b : ℝ) = k := by exact_mod_cast hκ
    have hbNr : (b : ℝ) * N ≤ k := by exact_mod_cast hbN
    have hh := congrArg (fun x : ℝ => x * N) heq
    have hid : (1 - 10 * ((1 : ℝ) / N)) * k * N = ((N : ℝ) - 10) * k := by
      field_simp
    have hmul : (1 - 10 * ((1 : ℝ) / N)) * k * N ≤ (κ : ℝ) * N := by
      rw [hid]
      nlinarith only [hh, hbNr]
    exact (mul_le_mul_iff_left₀ hNr).mp (by simpa only [mul_comm] using hmul)

end ConsistentSubmodular

end


