-- Prove2me | Definitions.Def_SamplingLLL_Supplement_cnfData
-- name    : SamplingLLL_Supplement_cnfData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:50:29.315483+00:00
-- url     : https://prove2.me/theorems/f88247a1-d339-49d8-979a-d9291c27e6d1
-- title:
--   Random regular $k$-CNF: the model of Theorem 2.19 and the algorithms of its proof
-- statement:
--   1. **CNF formulas.** A $k$-CNF with clause scopes $\mathrm{scope}(j)\subseteq[n]$ and literal signs is the atomic CSP on $n$ Boolean variables under the uniform measure whose forbidden word of clause $j$ is its unique falsifying assignment. `numSat` is its number of satisfying assignments.
--   2. **The random model.** The labelled simple $(r,k)$-biregular factor graphs on $n$ variables and $m=rn/k$ clauses are the scope functions with $|\mathrm{scope}(j)|=k$ for every clause and every variable in exactly $r$ clauses; `brProb` is the probability of an event under the uniform law on them.
--   3. **The algorithms of pp.48–49.** With $p_0=2^{-k+3}$, $\varepsilon_0=\min\{\varepsilon,1/2\}$ and the cutoff
--   $$
--   L=\max\Bigl\{2,\ \Bigl\lceil\log_2\frac{64\,m\,p_0}{\varepsilon_0}\Bigr\rceil\Bigr\},
--   $$
--   if $L\le\delta n$ the counter outputs $2^n$ times the deterministic estimate of Theorem 5.4 at $(p_0,L)$ and the sampler is the restarted sampler of Theorem 5.4; if $L>\delta n$ both enumerate all $2^n$ assignments, counting exactly and drawing a satisfying assignment uniformly. Here $\delta$ is the expansion constant of Lemma F.1, a parameter of the procedures.
--
--   These definitions are reused by Theorems 2.18 and F.6 (the formula type, `numSat`, $p_0$ and the cutoff).
--
--   **Formalization Note** Computing $L$ from the rational $\varepsilon$ is charged by the bit lengths of the operands. Exhaustive enumeration is charged $2^n(N+1)^2$. Which Boolean value is called "false" plays no role, since all theorems quantify over all sign patterns. $\lceil\log_2x\rceil$ is `Nat.clog 2 ⌈x⌉₊`.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Theorem 2.19, p.10; Lemma F.1 and proof of Theorem 2.19, pp.48–49

import Mathlib
import Definitions.Def_SamplingLLL_Supplement_frData

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL.Supplement

open Proc

/-! # Variable-regular random k-CNF: the model of Theorem 2.19 and the algorithms of its proof

Source: Achlioptas, *Counting and Sampling by Local Repair*, STOC 2027 submission (manuscript sha256
7a943167…), Theorem 2.19, p.10; Lemma F.1 and the proof of Theorem 2.19, pp.48–49. -/

/-- The CNF formula with clause scopes `scope j` and literal signs `sgn j v` on `n` Boolean variables under
the uniform measure, as an atomic CSP: the forbidden word of clause `j` is its falsifying assignment, the
value `sgn j v` on each `v ∈ scope j` (which value is called "false" plays no role, since the theorems
quantify over all signs). -/
noncomputable def kcnf {n m : ℕ} (scope : Fin m → Finset (Fin n)) (sgn : Fin m → Fin n → Bool) :
    AtomicCSP n m where
  dom _ := 1
  lam _ _ := 1 / 2
  lam_nonneg _ _ := by norm_num
  lam_sum _ := by norm_num
  word j v := if v ∈ scope j then some (if sgn j v then 1 else 0) else none

/-- The labelled simple `(r, k)`-biregular factor graphs on `n` variables and `m = rn/k` clauses, as clause
scopes: every clause has exactly `k` distinct variables and every variable lies in exactly `r` clauses. -/
noncomputable def biregular (n k r : ℕ) : Finset (Fin (r * n / k) → Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun scope =>
    (∀ j, (scope j).card = k) ∧ ∀ v, (Finset.univ.filter fun j => v ∈ scope j).card = r

/-- The probability of an event under the uniformly random simple `(r, k)`-biregular factor graph. -/
noncomputable def brProb (n k r : ℕ) (E : (Fin (r * n / k) → Finset (Fin n)) → Prop) : ℝ := by
  classical
  exact ((biregular n k r).filter E).card / (biregular n k r).card

/-- The number of satisfying assignments of an atomic CSP. -/
noncomputable def numSat {n m : ℕ} (I : AtomicCSP n m) : ℕ := by
  classical
  exact (Finset.univ.filter fun x => I.toCSP.sat Finset.univ x = true).card

/-- `p₀ = 2^{−k+3}` (p.48). -/
def p0k (k : ℕ) : ℚ := 8 / 2 ^ k

/-- The cutoff of p.48: `ε₀ = min{ε, 1/2}`, `L = max{2, ⌈log₂(64 m p₀/ε₀)⌉}`, with `⌈log₂ x⌉ = clog₂ ⌈x⌉`
for `x > 0`. -/
def cutoff (m k : ℕ) (ε : ℚ) : ℕ := max 2 (Nat.clog 2 ⌈(64 * m * p0k k / min ε (1 / 2) : ℚ)⌉₊)

/-- The cutoff computed by charged operations: reading the accuracy `ε` and dividing are charged by the
actual bit lengths, and the ceiling and logarithm by the bit length of the quotient. -/
noncomputable def cutoffP (m k : ℕ) (ε : ℚ) : Proc ℕ := do
  let c ← qmul (64 * m) (p0k k)
  let v ← qdiv c (min ε (1 / 2))
  tick (bits ε + bits v)
  pure (cutoff m k ε)

/-- Exhaustive enumeration of all `2^n` assignments, charged `2^n (N+1)^2`. -/
noncomputable def enumCost {n m : ℕ} (I : AtomicCSP n m) : ℕ := 2 ^ n * (frInputSize I + 1) ^ 2

/-- The deterministic counter of the proof of Theorem 2.19 (pp.48–49), for the clause size `k` and the
expansion constant `δ` of Lemma F.1: if `L ≤ δn`, `2^n` times the estimate `Ẑ` of Theorem 5.4 at `p₀`, `L`;
otherwise the exact count by enumeration. It draws no random bits. Computing `L` from `ε` is charged
(`cutoffP`). -/
noncomputable def cnfCount {n m : ℕ} (k : ℕ) (δ : ℚ) (I : AtomicCSP n m) (ε : ℚ) : Proc ℚ := do
  let L ← cutoffP m k ε
  if (L : ℚ) ≤ δ * n then do
    let z ← frCount I (p0k k) L
    qmul z (2 ^ n)
  else do
    tick (enumCost I)
    pure (numSat I)

/-- The sampler of the proof of Theorem 2.19: if `L ≤ δn`, the restarted sampler of Theorem 5.4 at `p₀`,
`L`; otherwise enumerate all satisfying assignments and draw one uniformly. -/
noncomputable def cnfSample {n m : ℕ} (k : ℕ) (δ : ℚ) (I : AtomicCSP n m) (ε : ℚ) :
    Proc I.toCSP.Config := by
  classical
  exact do
    let L ← cutoffP m k ε
    if (L : ℚ) ≤ δ * n then frRestart I (p0k k) L
    else do
      tick (enumCost I)
      let sols := (Finset.univ.filter fun x => I.toCSP.sat Finset.univ x = true).toList
      drawList (sols.map fun x => (x, (1 / sols.length : ℚ))) (fun _ => 0) 1

end SamplingLLL.Supplement


