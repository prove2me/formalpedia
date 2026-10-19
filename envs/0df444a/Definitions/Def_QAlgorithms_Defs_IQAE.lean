-- Prove2me | Definitions.Def_QAlgorithms_Defs_IQAE
-- name    : QAlgorithms_Defs_IQAE
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:08:31.817539+00:00
-- url     : https://prove2.me/theorems/833ce06e-20d7-4a15-9031-13836b9d45ea
-- title:
--   Iterative quantum amplitude estimation with Clopper–Pearson intervals (shared definition layer)
-- statement:
--   # Iterative quantum amplitude estimation with Clopper–Pearson intervals (shared definition layer)
--
--   D. Grinko, J. Gacon, C. Zoufal, S. Woerner, *Iterative quantum amplitude estimation*
--   (arXiv:1912.05559v3), cited "IQAE p.N" (PDF pages): §§II–III (Alg. 1, Alg. 2), App. B, App. C.
--
--   Model. `A` acts on `n + 1` qubits, the last qubit (`Fin.last n`) is the flag of eq. (1);
--   `Q = A S₀ A† S_{ψ₀}`, and the counted oracle queries are applications of `Q` (p.2). A measurement
--   of `Q^k A|0⟩` gives outcome `1` on the last qubit with probability `p_k`; `N` measurements give a
--   binomial count. Confidence intervals are Clopper–Pearson (`ci = "Clopper-Pearson"`), at level
--   `α/T` per round. The algorithm is a Markov chain of classical states (`iqaeStep`), halting
--   states absorbing.
--   -/
--
--   namespace QAlgorithms
--
--   open scoped NNReal
--
--   /-- IQAE p.2: `S₀ = I − 2|0⟩_{n+1}⟨0|_{n+1}` (the frozen `reflAt 0` is `−S₀`).
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\IQAE.lean

import Definitions.Def_QAlgorithms_Defs_ApproxCounting
/-!
# Iterative quantum amplitude estimation with Clopper–Pearson intervals (shared definition layer)

D. Grinko, J. Gacon, C. Zoufal, S. Woerner, *Iterative quantum amplitude estimation*
(arXiv:1912.05559v3), cited "IQAE p.N" (PDF pages): §§II–III (Alg. 1, Alg. 2), App. B, App. C.

Model. `A` acts on `n + 1` qubits, the last qubit (`Fin.last n`) is the flag of eq. (1);
`Q = A S₀ A† S_{ψ₀}`, and the counted oracle queries are applications of `Q` (p.2). A measurement
of `Q^k A|0⟩` gives outcome `1` on the last qubit with probability `p_k`; `N` measurements give a
binomial count. Confidence intervals are Clopper–Pearson (`ci = "Clopper-Pearson"`), at level
`α/T` per round. The algorithm is a Markov chain of classical states (`iqaeStep`), halting
states absorbing.
-/

namespace QAlgorithms

open scoped NNReal

/-- IQAE p.2: `S₀ = I − 2|0⟩_{n+1}⟨0|_{n+1}` (the frozen `reflAt 0` is `−S₀`). -/
noncomputable def iqaeS0 (n : ℕ) : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ :=
  1 - (2 : ℂ) • pureDensity (zeroKet (n + 1))

/-- IQAE p.2: `S_{ψ₀} = I − 2|ψ₀⟩⟨ψ₀| ⊗ |0⟩⟨0|`, the flag qubit last (frozen `snocQubit`). -/
noncomputable def iqaeSpsi0 {n : ℕ} (ψ0 : EuclideanSpace ℂ (Qubits n)) :
    Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ :=
  1 - (2 : ℂ) • pureDensity (snocQubit ψ0 false)

/-- IQAE p.2: the Grover operator `Q = A S₀ A† S_{ψ₀}`. -/
noncomputable def iqaeGrover {n : ℕ} (A : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ)
    (ψ0 : EuclideanSpace ℂ (Qubits n)) : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ :=
  A * iqaeS0 n * star A * iqaeSpsi0 ψ0

/-- IQAE p.2, eqs. (4)–(5): the probability of outcome `1` when measuring the last qubit of
`Q^k A|0⟩_n|0⟩` (it equals `sin²((2k + 1)θ_a)` under eq. (1); that is a fact, not the
definition). -/
noncomputable def iqaeShotProb {n : ℕ} (A : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ)
    (ψ0 : EuclideanSpace ℂ (Qubits n)) (k : ℕ) : ℝ :=
  probEvent (act (iqaeGrover A ψ0 ^ k * A) (zeroKet (n + 1))) fun z => z (Fin.last n) = true

/-- IQAE p.12 (App. C): the regularized incomplete beta function `I_p(x, y)`, the distribution
function of the `Beta(x, y)` law (Mathlib's `betaMeasure`, density
`t^{x−1}(1 − t)^{y−1}/B(x, y)` on `(0, 1)`); used for `x, y > 0`. -/
noncomputable def regIncBeta (x y p : ℝ) : ℝ :=
  (ProbabilityTheory.betaMeasure x y (Set.Iic p)).toReal

/-- IQAE p.12 (App. C): `I⁻¹(β; x, y)`, the `p ∈ [0, 1]` with `I_p(x, y) = β`. For `x, y > 0`
the distribution function is continuous and strictly increasing on `[0, 1]`, so the least
`p ∈ [0, 1]` with `β ⩽ I_p(x, y)` is the exact inverse for `β ∈ [0, 1]`. -/
noncomputable def regIncBetaInv (β x y : ℝ) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc 0 1 ∧ β ≤ regIncBeta x y p}

/-- IQAE p.3 (Alg. 1 l.24), p.12 ((C5)–(C6)): the lower end `a_min` of the exact two-sided
level-`(1 − β)` Clopper–Pearson interval for `x` successes in `N` trials, `I⁻¹(β/2; x, N − x + 1)`
(`0` at `x = 0`). The page's (C5)–(C6) and Alg. 1 l.24–25 swap the two ends; the standard
orientation is used (trap 30). -/
noncomputable def clopperPearsonLower (x N : ℕ) (β : ℝ) : ℝ :=
  if x = 0 then 0 else regIncBetaInv (β / 2) x ((N : ℝ) - x + 1)

/-- IQAE p.3 (Alg. 1 l.25), p.12: the upper end `a_max = I⁻¹(1 − β/2; x + 1, N − x)` (`1` at
`x = N`). -/
noncomputable def clopperPearsonUpper (x N : ℕ) (β : ℝ) : ℝ :=
  if N ≤ x then 1 else regIncBetaInv (1 - β / 2) ((x : ℝ) + 1) ((N : ℝ) - x)

/-- IQAE p.3 (Alg. 1 l.6), p.11: the round bound `T = ⌈log₂(π/(8ε))⌉`. -/
noncomputable def iqaeT (ε : ℝ) : ℕ :=
  ⌈Real.logb 2 (Real.pi / (8 * ε))⌉₊

/-- IQAE p.4 (eq. (11)), p.12 (App. C): `L_max(N, ε, α) = max_θ h_{N,ε,α}(θ)`, the maximum over
`t ∈ {0, …, N}` of the half-width
`h = ½ arccos(1 − 2a_max) − ½ arccos(1 − 2a_min)` of the `Kθ`-interval at level `α/T`. -/
noncomputable def iqaeLmax (N : ℕ) (ε α : ℝ) : ℝ :=
  (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun t =>
    (Real.arccos (1 - 2 * clopperPearsonUpper t N (α / iqaeT ε)) -
      Real.arccos (1 - 2 * clopperPearsonLower t N (α / iqaeT ε))) / 2

/-- IQAE p.11 (Theorem 2), (C9): `N_max(ε, α) = 69 log((2/α) log₂(π/(4ε)))` (natural logarithm
outside). -/
noncomputable def iqaeNmax (ε α : ℝ) : ℝ :=
  69 * Real.log (2 / α * Real.logb 2 (Real.pi / (4 * ε)))

/-- IQAE p.4 (Alg. 2): `{y}_{mod 2π} = y − 2π⌊y/(2π)⌋ ∈ [0, 2π)`. -/
noncomputable def mod2pi (y : ℝ) : ℝ :=
  y - 2 * Real.pi * ⌊y / (2 * Real.pi)⌋

/-- IQAE p.4, Alg. 2 lines 7–19: scan the candidates `K, K − 4, …` while `K ⩾ 2K_i`; return
`((K − 2)/4, true)` for the first `K` with `{Kθ_u} ⩽ π` and `{Kθ_l} ⩽ π` (upper half-plane tested
first), `((K − 2)/4, false)` if both are `⩾ π`, `none` if no candidate passes (`fuel` bounds the
number of candidates). -/
noncomputable def findNextKLoop (Ki : ℤ) (θl θu : ℝ) : ℕ → ℤ → Option (ℕ × Bool)
  | 0, _ => none
  | fuel + 1, K =>
      if 2 * Ki ≤ K then
        if mod2pi (K * θu) ≤ Real.pi ∧ mod2pi (K * θl) ≤ Real.pi then some (((K - 2) / 4).toNat, true)
        else if Real.pi ≤ mod2pi (K * θu) ∧ Real.pi ≤ mod2pi (K * θl) then
          some (((K - 2) / 4).toNat, false)
        else findNextKLoop Ki θl θu fuel (K - 4)
      else none

/-- IQAE p.4, Alg. 2 (`r = 2`): `FindNextK(k_i, θ_l, θ_u, up_i)`. `K_i = 4k_i + 2`,
`K_max = ⌊π/(θ_u − θ_l)⌋`, `K = K_max − ((K_max − 2) mod 4)` the largest candidate of the form
`4k + 2`; the candidates `K, K − 4, …, ⩾ 2K_i` are scanned (at most `K_max/4 + 1` of them), and the
old `(k_i, up_i)` is returned if none passes. -/
noncomputable def findNextK (k : ℕ) (θl θu : ℝ) (up : Bool) : ℕ × Bool :=
  let Ki : ℤ := 4 * k + 2
  let Kmax : ℤ := ⌊Real.pi / (θu - θl)⌋
  ((findNextKLoop Ki θl θu (Kmax.toNat / 4 + 1) (Kmax - (Kmax - 2) % 4))).getD (k, up)

/-- IQAE p.3 (Alg. 1), p.9 (App. B): the classical state of Alg. 1: the current `k_i`, `up_i`,
the interval `[θ_l, θ_u]`, the shots and ones accumulated in the current round (line 18), the
list of the `k_i` of all iterations so far (a round is a maximal block of equal consecutive
`k_i`), the oracle count `N_oracle = Σ N_i k_i` (B13), and whether the loop has ended. -/
structure IQAEState where
  /-- The current power `k_i`. -/
  k : ℕ
  /-- The current half-plane flag `up_i`. -/
  up : Bool
  /-- The lower end `θ_l`. -/
  thetaL : ℝ
  /-- The upper end `θ_u`. -/
  thetaU : ℝ
  /-- Shots accumulated in the current round. -/
  roundShots : ℕ
  /-- Outcomes `1` accumulated in the current round. -/
  roundOnes : ℕ
  /-- The `k_i` of all iterations so far, in order. -/
  kHist : List ℕ
  /-- The number of applications of `Q` so far. -/
  oracle : ℕ
  /-- The `while` loop has ended. -/
  halted : Bool

/-- IQAE p.3, Alg. 1 lines 2–5: `i = 0`, `k_0 = 0`, `up_0 = True`, `[θ_l, θ_u] = [0, π/2]`. -/
noncomputable def iqaeInit : IQAEState :=
  ⟨0, true, 0, Real.pi / 2, 0, 0, [], 0, false⟩

/-- IQAE p.3, Alg. 1 lines 8–28 (one iteration; `ci = "Clopper-Pearson"`): if
`θ_u − θ_l ⩽ 2ε` the loop ends; otherwise `(k', up') = FindNextK(k_{i−1}, θ_l, θ_u, up_{i−1})`,
`K = 4k' + 2`, `N = ⌈N_shots L_max/ε/K/10⌉` if `K > ⌈L_max/ε⌉` (no-overshooting) else `N_shots`,
measure `N` times, combine with the earlier shots of the same round if `k' = k_{i−1}`, compute the
Clopper–Pearson interval `[a_min, a_max]` at level `α/T`, invert `a = (1 − cos(Kθ))/2` in the
half-plane `up'`, and set `θ_l = (2π⌊Kθ_l/2π⌋ + θ_min)/K`, `θ_u = (2π⌊Kθ_u/2π⌋ + θ_max)/K`. -/
noncomputable def iqaeStep {n : ℕ} (A : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ)
    (ψ0 : EuclideanSpace ℂ (Qubits n)) (ε α : ℝ) (Nshots : ℕ) (s : IQAEState) : PMF IQAEState :=
  if s.halted then PMF.pure s
  else if s.thetaU - s.thetaL ≤ 2 * ε then PMF.pure { s with halted := true }
  else
    let k' := (findNextK s.k s.thetaL s.thetaU s.up).1
    let up' := (findNextK s.k s.thetaL s.thetaU s.up).2
    let K : ℕ := 4 * k' + 2
    let L := iqaeLmax Nshots ε α
    let N : ℕ := if ((⌈L / ε⌉₊ : ℕ) : ℝ) < (K : ℝ) then ⌈(Nshots : ℝ) * L / ε / K / 10⌉₊ else Nshots
    (PMF.binomial (min 1 (Real.toNNReal (iqaeShotProb A ψ0 k'))) (min_le_left _ _) N).bind
      fun ones =>
        let same : Bool := decide (k' = s.k ∧ s.kHist ≠ [])
        let S : ℕ := if same then s.roundShots + N else N
        let O : ℕ := if same then s.roundOnes + (ones : ℕ) else (ones : ℕ)
        let amin := clopperPearsonLower O S (α / iqaeT ε)
        let amax := clopperPearsonUpper O S (α / iqaeT ε)
        let θmin : ℝ := if up' then Real.arccos (1 - 2 * amin) else 2 * Real.pi - Real.arccos (1 - 2 * amax)
        let θmax : ℝ := if up' then Real.arccos (1 - 2 * amax) else 2 * Real.pi - Real.arccos (1 - 2 * amin)
        PMF.pure ⟨k', up',
          (2 * Real.pi * ⌊(K : ℝ) * s.thetaL / (2 * Real.pi)⌋ + θmin) / K,
          (2 * Real.pi * ⌊(K : ℝ) * s.thetaU / (2 * Real.pi)⌋ + θmax) / K,
          S, O, s.kHist ++ [k'], s.oracle + N * k', false⟩

/-- IQAE p.3: the law of the classical state after `j` steps of Alg. 1 from `iqaeInit` (halted
states absorbing). The output interval of a halted state `s` is `[sin²θ_l, sin²θ_u]` (line 29). -/
noncomputable def iqaeRun {n : ℕ} (A : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ)
    (ψ0 : EuclideanSpace ℂ (Qubits n)) (ε α : ℝ) (Nshots : ℕ) : ℕ → PMF IQAEState
  | 0 => PMF.pure iqaeInit
  | j + 1 => (iqaeRun A ψ0 ε α Nshots j).bind (iqaeStep A ψ0 ε α Nshots)

/-! ### Sanity tests -/

example (n : ℕ) (z : Qubits (n + 1)) (hz : z ≠ fun _ => false) : iqaeS0 n z z = 1 := by
  simp [iqaeS0, pureDensity, zeroKet, ket, EuclideanSpace.single_apply, hz]

example (n : ℕ) : iqaeS0 n (fun _ => false) (fun _ => false) = -1 := by
  simp [iqaeS0, pureDensity, zeroKet, ket]
  norm_num

example (N : ℕ) (β : ℝ) : clopperPearsonLower 0 N β = 0 ∧ clopperPearsonUpper N N β = 1 := by
  simp [clopperPearsonLower, clopperPearsonUpper]

example {n : ℕ} (A : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ) (ψ0 : EuclideanSpace ℂ (Qubits n))
    (ε α : ℝ) (Nshots : ℕ) (s : IQAEState) (h : s.halted = true) :
    iqaeStep A ψ0 ε α Nshots s = PMF.pure s := by
  simp [iqaeStep, h]

example {n : ℕ} (A : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ) (ψ0 : EuclideanSpace ℂ (Qubits n))
    (ε α : ℝ) (Nshots : ℕ) : iqaeRun A ψ0 ε α Nshots 0 = PMF.pure iqaeInit := rfl

example (Ki : ℤ) (θl θu : ℝ) (K : ℤ) (h : K < 2 * Ki) (fuel : ℕ) :
    findNextKLoop Ki θl θu (fuel + 1) K = none := by
  simp [findNextKLoop, not_le.2 h]

example {n : ℕ} (A : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ) (ψ0 : EuclideanSpace ℂ (Qubits n)) :
    iqaeShotProb A ψ0 0 = probEvent (act A (zeroKet (n + 1))) fun z => z (Fin.last n) = true := by
  simp [iqaeShotProb]

end QAlgorithms


