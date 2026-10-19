-- Prove2me | Definitions.Def_QAlgorithms_Defs_ApproxCounting
-- name    : QAlgorithms_Defs_ApproxCounting
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:07:39.199427+00:00
-- url     : https://prove2.me/theorems/bcb0706f-d6f9-4624-a832-7a1160414777
-- title:
--   Approximate counting by Grover coins (shared definition layer)
-- statement:
--   # Approximate counting by Grover coins (shared definition layer)
--
--   S. Aaronson, P. Rall, *Quantum approximate counting, simplified* (arXiv:1908.10846v6), cited
--   "AR p.N" (PDF pages), §2 (the algorithm of Theorem 1, p.4) and Lemma 2 (p.9).
--
--   Model. The list `[N]` is padded with `10⁶ N` unmarked items (p.4), giving `M = (10⁶ + 1) N` items
--   `Fin M`; the membership oracle is the frozen phase oracle `U|x⟩ = (−1)^{[x ∈ S]}|x⟩`, `|ψ⟩` the
--   frozen uniform superposition, `G = (I − 2|ψ⟩⟨ψ|)U`. One "shot" with odd parameter `r` prepares
--   `G^{(r−1)/2}|ψ⟩`, measures it, and costs `(r − 1)/2` queries; the number of marked outcomes in
--   `m` independent shots is binomial. Step 1 is an unbounded loop (probability of exiting at stage
--   `k`); steps 2–3 are a finite probabilistic recursion.
--   -/
--
--   namespace QAlgorithms
--
--   open scoped ENNReal NNReal
--
--   /-- AR p.4: the length `N + 10⁶ N` of the padded list.
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ApproxCounting.lean

import Definitions.Def_QAlgorithms_Defs_DQI
/-!
# Approximate counting by Grover coins (shared definition layer)

S. Aaronson, P. Rall, *Quantum approximate counting, simplified* (arXiv:1908.10846v6), cited
"AR p.N" (PDF pages), §2 (the algorithm of Theorem 1, p.4) and Lemma 2 (p.9).

Model. The list `[N]` is padded with `10⁶ N` unmarked items (p.4), giving `M = (10⁶ + 1) N` items
`Fin M`; the membership oracle is the frozen phase oracle `U|x⟩ = (−1)^{[x ∈ S]}|x⟩`, `|ψ⟩` the
frozen uniform superposition, `G = (I − 2|ψ⟩⟨ψ|)U`. One "shot" with odd parameter `r` prepares
`G^{(r−1)/2}|ψ⟩`, measures it, and costs `(r − 1)/2` queries; the number of marked outcomes in
`m` independent shots is binomial. Step 1 is an unbounded loop (probability of exiting at stage
`k`); steps 2–3 are a finite probabilistic recursion.
-/

namespace QAlgorithms

open scoped ENNReal NNReal

/-- AR p.4: the length `N + 10⁶ N` of the padded list. -/
def acPadLen (N : ℕ) : ℕ :=
  (10 ^ 6 + 1) * N

/-- AR p.4: the marked indicator of the padded list, `S` on the first `N` items, the padding
unmarked. -/
def acPadMarked {N : ℕ} (S : Finset (Fin N)) : Fin (acPadLen N) → Bool :=
  fun i => if h : (i : ℕ) < N then decide (⟨i, h⟩ ∈ S) else false

/-- AR p.4: the Grover diffusion operator `G = (I − 2|ψ⟩⟨ψ|)U` on `M` items, `U` the phase
oracle of the marked indicator `x`, `|ψ⟩` the uniform superposition (the frozen `groverIterate`
is `−G` on `Qubits n` only). -/
noncomputable def acGrover (M : ℕ) (x : Fin M → Bool) : Matrix (Fin M) (Fin M) ℂ :=
  (1 - (2 : ℂ) • pureDensity (uniformState (Fin M))) * phaseOracle x

/-- AR pp.4–5 (eq. (1)): the probability that measuring `G^{(r−1)/2}|ψ⟩` in the computational
basis yields a marked item (eq. (1) shows it is `sin²(rθ)`; that is a fact, not the definition). -/
noncomputable def acShotProb (M : ℕ) (x : Fin M → Bool) (r : ℕ) : ℝ :=
  probEvent (act (acGrover M x ^ ((r - 1) / 2)) (uniformState (Fin M))) fun i => x i = true

/-- AR p.4: the law of the number of marked outcomes among `m` independent shots with parameter
`r` (binomial; the clamp `min 1` is inactive since a measurement probability is `⩽ 1`). -/
noncomputable def acShotDist (M : ℕ) (x : Fin M → Bool) (r m : ℕ) : PMF (Fin (m + 1)) :=
  PMF.binomial (min 1 (Real.toNNReal (acShotProb M x r))) (min_le_left _ _) m

/-- AR p.4, step 1(a): `r_k`, the largest odd integer `⩽ 1.05^k` (`k = 0, 1, 2, …`; always `⩾ 1`). -/
noncomputable def acStep1R (k : ℕ) : ℕ :=
  if Odd ⌊(1.05 : ℝ) ^ k⌋₊ then ⌊(1.05 : ℝ) ^ k⌋₊ else ⌊(1.05 : ℝ) ^ k⌋₊ - 1

/-- AR p.4, step 1(a): the number of shots per stage, the least integer `⩾ 5000 · ln(5/δ)`
("at least `5000 · ln(5/δ)` times"). -/
noncomputable def acStep1Shots (δ : ℝ) : ℕ :=
  ⌈5000 * Real.log (5 / δ)⌉₊

/-- AR p.4, step 1(b): the probability that stage `k` of step 1 exits, i.e. that a marked item is
measured in `⩾ 95%` of the shots. -/
noncomputable def acStep1Exit (M : ℕ) (x : Fin M → Bool) (δ : ℝ) (k : ℕ) : ℝ≥0∞ :=
  (acShotDist M x (acStep1R k) (acStep1Shots δ)).toOuterMeasure
    {h | 0.95 * (acStep1Shots δ : ℝ) ≤ ((h : ℕ) : ℝ)}

/-- AR pp.4–5: the queries spent in step 1 when it exits at `k = k_end`. -/
noncomputable def acStep1Queries (δ : ℝ) (kend : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (kend + 1), acStep1Shots δ * ((acStep1R k - 1) / 2)

/-- AR p.9, Lemma 2 (eqs. (45)–(47)): `Δθ = θ_max − θ_min`, `k` the closest integer to
`θ_min/(2Δθ)`, `r` the closest odd integer to `πk/θ_min` (ties broken by Mathlib's `round`; the
page allows any tie rule). -/
noncomputable def acRotR (θmin θmax : ℝ) : ℕ :=
  Int.toNat (2 * round ((Real.pi * (round (θmin / (2 * (θmax - θmin))) : ℝ) / θmin - 1) / 2) + 1)

/-- AR p.4, steps 2(a)–(d) and 3, as a recursion with `fuel` iterations left at iteration `t`,
current bounds `θ_min, θ_max` and `q` step-2 queries so far; returns `(K̂, q)`. Iteration `t`
chooses `r_t` by Lemma 2, takes `⌈250 · ln δ_t⁻¹⌉` shots, `δ_t = (δε/65) · 0.9^{−t}`, sets
`γ = θ_max/θ_min − 1` and `θ_min := θ_max/(1 + 0.9γ)` if a marked item was seen in at least `12%`
of the shots, else `θ_max := (1 + 0.9γ)θ_min`, and exits with `K̂ = M sin²θ_max` once
`θ_max ⩽ (1 + ε/5)θ_min`. (Out of fuel it also returns `M sin²θ_max`; with the fuel of `acStep2`
this never happens, see there.) -/
noncomputable def acStep2Loop (M : ℕ) (x : Fin M → Bool) (ε δ : ℝ) :
    ℕ → ℕ → ℝ → ℝ → ℕ → PMF (ℝ × ℕ)
  | 0, _, _, θmax, q => PMF.pure ((M : ℝ) * Real.sin θmax ^ 2, q)
  | fuel + 1, t, θmin, θmax, q =>
      let r := acRotR θmin θmax
      let δt : ℝ := δ * ε / 65 * ((0.9 : ℝ) ^ t)⁻¹
      let mt : ℕ := ⌈250 * Real.log δt⁻¹⌉₊
      let γ : ℝ := θmax / θmin - 1
      (acShotDist M x r mt).bind fun h =>
        let hit : Bool := decide (0.12 * (mt : ℝ) ≤ ((h : ℕ) : ℝ))
        let θmin' : ℝ := if hit then θmax / (1 + 0.9 * γ) else θmin
        let θmax' : ℝ := if hit then θmax else (1 + 0.9 * γ) * θmin
        let q' : ℕ := q + mt * ((r - 1) / 2)
        if θmax' ≤ (1 + ε / 5) * θmin' then PMF.pure ((M : ℝ) * Real.sin θmax' ^ 2, q')
        else acStep2Loop M x ε δ fuel (t + 1) θmin' θmax' q'

/-- AR p.4, steps 2–3 after step 1 exited at `k_end`: start from `θ_min = 0.9 · 1.05^{−k_end}`,
`θ_max = 1.65 θ_min`, `t = 0`, `q = 0`. Each iteration replaces the ratio `1 + γ` by `1 + 0.9γ`
exactly, so `γ_t = 0.65 · 0.9^t` and the exit test passes after at most
`⌈log_{10/9}(3.25/ε)⌉` iterations; the fuel `⌈log_{10/9}(3.25/ε)⌉ + 1` is never exhausted.
Returns `(K̂, step-2 queries)`. -/
noncomputable def acStep2 (M : ℕ) (x : Fin M → Bool) (ε δ : ℝ) (kend : ℕ) : PMF (ℝ × ℕ) :=
  acStep2Loop M x ε δ (⌈Real.logb (10 / 9) (3.25 / ε)⌉₊ + 1) 0 (0.9 * ((1.05 : ℝ) ^ kend)⁻¹)
    (1.65 * (0.9 * ((1.05 : ℝ) ^ kend)⁻¹)) 0

/-- AR p.4: the probability that the algorithm (steps 1–3 on the padded list `acPadLen N`,
marked set `S`) terminates with estimate `K̂` and total query count `q` satisfying `E K̂ q`. Step 1
exits at `k_end` with probability `Π_{k < k_end} (1 − p_k) · p_k` (independent stages);
non-termination contributes nothing. -/
noncomputable def acEventProb {N : ℕ} (S : Finset (Fin N)) (ε δ : ℝ) (E : ℝ → ℕ → Prop) : ℝ≥0∞ :=
  ∑' kend : ℕ,
    (∏ k ∈ Finset.range kend, (1 - acStep1Exit (acPadLen N) (acPadMarked S) δ k)) *
      acStep1Exit (acPadLen N) (acPadMarked S) δ kend *
      (acStep2 (acPadLen N) (acPadMarked S) ε δ kend).toOuterMeasure
        {o | E o.1 (acStep1Queries δ kend + o.2)}

/-! ### Sanity tests -/

example : acPadLen 1 = 1000001 := rfl

example : acStep1R 0 = 1 := by
  simp [acStep1R]

example (M : ℕ) (x : Fin M → Bool) :
    acShotProb M x 1 = probEvent (uniformState (Fin M)) fun i => x i = true := by
  simp [acShotProb, act]

example {N : ℕ} (S : Finset (Fin N)) (i : Fin N) :
    acPadMarked S ⟨i, Nat.lt_of_lt_of_le i.isLt
      (by unfold acPadLen; exact Nat.le_mul_of_pos_left N (by norm_num))⟩ = decide (i ∈ S) := by
  simp [acPadMarked]

example (M : ℕ) (x : Fin M → Bool) (ε δ θmin θmax : ℝ) (t q : ℕ) :
    acStep2Loop M x ε δ 0 t θmin θmax q = PMF.pure ((M : ℝ) * Real.sin θmax ^ 2, q) := rfl

example {N : ℕ} (S : Finset (Fin N)) (ε δ : ℝ) : acEventProb S ε δ (fun _ _ => False) = 0 := by
  simp [acEventProb]

end QAlgorithms


