-- Prove2me | Definitions.Def_LinfContractionFP_amplify
-- name    : LinfContractionFP_amplify
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:45.162668+00:00
-- url     : https://prove2.me/theorems/97bd7c12-0ad0-4dd4-b2ec-31ff87e9519d
-- title:
--   Amplify (Algorithm 3) with cost counters
-- statement:
--   $\mathrm{Amplify}(b,\tau,F,B_+,B_-)$, for an Oracle $O$ of accuracy $\rho$:
--
--   1. if $\tau\le\rho$, return $\mathrm{Oracle}(b)$;
--   2. if $B_+B_-<1$, return the labels of the decoding rule (8);
--   3. set all output labels unset;
--   4. while $B_+B_-\ge1$: run one boosting iteration (lines 5–15), add the weak labels $\ell'$ to the tallies $F$, and multiply $B_+$ and $B_-$ by $\sqrt3/2$;
--   5. decode the unset labels by (8) and return all labels.
--
--   A defeat declared by Oracle is propagated up the whole call tree. The run reports three counters: boosting rounds (loop iterations in the whole call tree), Oracle calls, and arithmetic operations.
--
--   **Formalization Note** Each recursive call divides $\tau$ by $2$ or $32$; the recursion is given the depth bound $\lceil\log_2(\tau/\rho)\rceil$, which for $\rho>0$ is never reached (a call with no remaining depth has $\tau\le\rho$). The loop runs its exact number of iterations, the least $j$ with $(3/4)^jB_+B_-<1$. Operation charges: $1$ for each of lines 1, 2, 18 and each loop test; $n$ for lines 3, 16–17, 19 and for decoding at line 2; the iteration as in `boostRound`. No line is charged less than the work it performs as printed.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Algorithm 3, p.15; Lemma 5, p.20

import Mathlib
import Definitions.Def_LinfContractionFP_decode
import Definitions.Def_LinfContractionFP_firstIndex
import Definitions.Def_LinfContractionFP_boostRound

open scoped Classical

namespace LinfContractionFP

/-- The counters of a run of `Amplify`: boosting rounds (iterations of the loop of line 4, in
the whole call tree), calls to Oracle, and arithmetic operations (charged per line, see
`amplifyAux`). -/
structure Cost where
  /-- Boosting rounds executed, across the entire computation. -/
  rounds : ℕ
  /-- Calls to Oracle (line 1). -/
  oracleCalls : ℕ
  /-- Arithmetic operations, charged by the schedule of `amplifyAux` and `boostRound`. -/
  ops : ℕ

/-- The monad of `Amplify`: a defeat of Oracle with payload in `α` aborts the whole call tree
(the "Convention" of Algorithm 3), and the counters are threaded as state. -/
abbrev AmpM (α : Type) := ExceptT α (StateM Cost)

/-- Charge `c` arithmetic operations. -/
def tickOps {α : Type} (c : ℕ) : AmpM α Unit :=
  modify fun s => { s with ops := s.ops + c }

/-- Count one boosting round. -/
def tickRound {α : Type} : AmpM α Unit :=
  modify fun s => { s with rounds := s.rounds + 1 }

/-- One call `Oracle(b)`: counted, and a defeat (`Sum.inl a`) is propagated up the call tree.
The Oracle is told the index `t` of the call (the number of earlier calls), so an adaptive
Oracle may answer differently at different times. -/
def callOracle {κ α : Type} (O : ℕ → (κ → ℝ) → α ⊕ (κ → Lbl)) (b : κ → ℝ) :
    AmpM α (κ → Lbl) := do
  let t := (← get).oracleCalls
  modify fun s => { s with oracleCalls := s.oracleCalls + 1 }
  match O t b with
  | .inl a => throw a
  | .inr ℓ => pure ℓ

/-- The exact number of iterations of the loop `while B₊B₋ ≥ 1` of Algorithm 3 started at
`B₊B₋ = P`: each iteration multiplies `B₊` and `B₋` by `√3/2`, i.e. the product by `3/4`, so the
loop stops at the least `j` with `(3/4)^j P < 1`. -/
noncomputable def boostCount (P : ℝ) : ℕ := firstIndex fun j => (3 / 4 : ℝ) ^ j * P < 1

/-- Algorithm 3, `Amplify(b, τ, F, B₊, B₋)`, with Oracle `O` of accuracy `ρ`, and the recursion
depth bounded by `fuel`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Algorithm 3, p.15:
```
Convention: If any call returns an admission of defeat from Oracle, immediately propagate
that up the call tree
1  if τ ≤ ρ then return Oracle(b);  // Base case
2  if B+B− < 1 then return labels according to (8);
3  ℓ_i ← ⊥ for all i = 1, ..., n;   // Output labels unset
4  while B+B− ≥ 1 do                // Perform boosting iterations
5–15 (see `boostRound`)
16   foreach i = 1, ..., n do
17     F_i ← F_i + ℓ'_i;            // Update vote tally
18   B+ ← (√3/2)B+, B− ← (√3/2)B−;
19 Decode unset (⊥) labels via (8) and return all labels ℓ_i;
```

**Formalization Note.**
* Termination. Every recursive call divides `τ` by `2` or `32`; `fuel` is a recursion-depth
  bound and `amplifyRun` starts it at `⌈log₂(τ/ρ)⌉₊`. For `ρ > 0` this never cuts the recursion
  short: a call with `fuel = 0` has `τ ≤ ρ` and returns at line 1, and the branch `fuel = 0`
  with `τ > ρ` (which then returns `Oracle(b)` as well) is unreachable. The loop of line 4 runs
  `boostCount (B₊B₋)` times, its exact iteration count (the condition `B₊B₋ ≥ 1` is also
  re-tested in every iteration).
* Defeat (`Sum.inl a` from `O`) aborts the computation with payload `a` (the monad `AmpM`).
* Oracle is adaptive: its `t`-th call (counted from `0` in the whole call tree) is `O t b`.
* Counters: `rounds` counts iterations of the loop of line 4; `oracleCalls` counts line-1 calls.
  Operation charges (`n = |κ|`): line 1: `1`; line 2: `1`, plus `n` when it decodes by (8);
  line 3: `n`; each test of line 4: `1`; lines 5–15: see `boostRound`; lines 16–17: `n`;
  line 18: `1`; line 19: `n`. Decoding by (8) is charged `1` per coordinate. Every line is
  charged at least the number of real operations it performs as printed.
* Labels: `−1` is `lo`, `+1` is `hi`, `⊥` is `none`; `F` is integer-valued. -/
noncomputable def amplifyAux {κ α : Type} [Fintype κ] (O : ℕ → (κ → ℝ) → α ⊕ (κ → Lbl))
    (ρ : ℝ) : ℕ → (κ → ℝ) → ℝ → (κ → ℤ) → ℝ → ℝ → AmpM α (κ → Lbl)
  | 0, b, _, _, _, _ => do
    tickOps 1
    callOracle O b
  | fuel + 1, b, τ, F₀, Bp₀, Bm₀ => do
    let n := Fintype.card κ
    -- line 1
    tickOps 1
    if τ ≤ ρ then
      let ℓ ← callOracle O b
      return ℓ
    -- line 2
    tickOps 1
    if Bp₀ * Bm₀ < 1 then
      tickOps n
      return decode F₀ Bp₀ Bm₀
    -- line 3
    tickOps n
    let mut ℓ : κ → Option Lbl := fun _ => none
    let mut F := F₀
    let mut Bp := Bp₀
    let mut Bm := Bm₀
    -- line 4
    for _ in List.range (boostCount (Bp₀ * Bm₀)) do
      tickOps 1
      if 1 ≤ Bp * Bm then
        tickRound
        -- lines 5–15
        let r ← boostRound tickOps (amplifyAux O ρ fuel) b τ F Bp Bm ℓ
        ℓ := r.labels
        -- lines 16–17
        tickOps n
        F := fun i => F i + (r.weak i).val
        -- line 18
        tickOps 1
        Bp := Real.sqrt 3 / 2 * Bp
        Bm := Real.sqrt 3 / 2 * Bm
    -- the failing test of line 4, and line 19
    tickOps 1
    tickOps n
    return fun i => (ℓ i).getD (decode F Bp Bm i)

/-- The recursion-depth bound `⌈log₂(τ/ρ)⌉₊` used to start `amplifyAux`. -/
noncomputable def amplifyFuel (ρ τ : ℝ) : ℕ := Nat.ceil (Real.logb 2 (τ / ρ))

/-- Run `Amplify(b, τ, F, B₊, B₋)` (Algorithm 3) with Oracle `O` of accuracy `ρ` from zero
counters. The first component is `Sum.inl a` if Oracle declared defeat with payload `a`, and
`Sum.inr ℓ` for a returned labeling; the second is the final `Cost`. -/
noncomputable def amplifyRun {κ α : Type} [Fintype κ] (O : ℕ → (κ → ℝ) → α ⊕ (κ → Lbl)) (ρ : ℝ)
    (b : κ → ℝ) (τ : ℝ) (F : κ → ℤ) (Bp Bm : ℝ) : (α ⊕ (κ → Lbl)) × Cost :=
  let r := Id.run ((amplifyAux O ρ (amplifyFuel ρ τ) b τ F Bp Bm).run.run ⟨0, 0, 0⟩)
  ((match r.1 with
    | .error a => Sum.inl a
    | .ok ℓ => Sum.inr ℓ), r.2)

end LinfContractionFP


