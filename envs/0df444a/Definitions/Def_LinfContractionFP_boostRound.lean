-- Prove2me | Definitions.Def_LinfContractionFP_boostRound
-- name    : LinfContractionFP_boostRound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:26.765974+00:00
-- url     : https://prove2.me/theorems/4ea5ffe0-0642-4009-940f-6bfe2999bfc8
-- title:
--   One boosting iteration of Amplify (Algorithm 3, lines 5–15)
-- statement:
--   One iteration of the boosting loop of Algorithm 3, with the recursive calls to Amplify replaced by a parameter $\mathrm{sub}$:
--
--   1. $\delta\gets0$.
--   2. Step I: 64 times, $\ell'\gets\mathrm{sub}(b+\delta,\tau/32,F,B_+,\tfrac34B_-)$ and $\delta_i\gets\delta_i+\tfrac{\tau}{32}\mathbf 1[\ell'_i=-1]$.
--   3. Step II: 64 times, $\ell'\gets\mathrm{sub}(b+\delta,\tau/32,F,\tfrac34B_+,B_-)$ and $\delta_i\gets\delta_i-\tfrac{\tau}{32}\mathbf 1[\ell'_i=+1]$.
--   4. Step III: an unset label becomes $-1$ if $\delta_i\ge\tau$, and otherwise $+1$ if $\delta_i\le-\tau$.
--   5. Step IV: $\ell'\gets\mathrm{sub}(b+\delta,\tau/2,F,B_+,B_-)$, the weak learner's votes.
--
--   The output records $\delta$ after Step II, the labels after Step III, and $\ell'$. Lemma 4 is a statement about this iteration.
--
--   **Formalization Note** The iteration is written for any monad, with a hook `tick` that charges operations: Amplify runs it with cost counters and with its own recursive call as $\mathrm{sub}$; Lemma 4 runs it with no counters and with any $\mathrm{sub}$ meeting Contract 1. Charges: $n$ for line 5; $1+n$ per iteration of lines 6–7 and 9–10 (loop control and forming $b+\delta$) and $n$ for lines 8 and 11; $n$ for Step III; $n$ for line 15.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Algorithm 3, lines 5–15, p.15

import Mathlib
import Definitions.Def_LinfContractionFP_Lbl

open scoped Classical

namespace LinfContractionFP

/-- What one boosting iteration of Algorithm 3 produces before the tally update: the shift
`δ` at the end of Step II (`delta`), the output labels after Step III (`labels`, `none` = `⊥`
unset), and the weak-learner labels `ℓ'` returned by the single call of Step IV, line 15
(`weak`). -/
structure RoundOut (κ : Type) where
  /-- `δ` after Step II (the shift supplied to line 15 is `b + δ`). -/
  delta : κ → ℝ
  /-- The output labels `ℓ` after Step III (`none` is `⊥`). -/
  labels : κ → Option Lbl
  /-- The labels `ℓ'` returned on line 15 (votes from the weak learner). -/
  weak : κ → Lbl

/-- Lines 5–15 of one iteration of the boosting loop of Algorithm 3 (`Amplify`), with the
recursive call `Amplify(·)` replaced by the parameter `sub`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Algorithm 3, p.15:
```
5  δ ← 0;
   // Step I: Push up coordinates with label -1
6  foreach t = 1, ..., 64 do
7    ℓ' ← Amplify(b + δ, τ/32, F, B+, (3/4)B−);
8    δ_i ← δ_i + (τ/32)·1[ℓ'_i = −1] for all i
   // Step II: Push down coordinates with label +1
9  foreach t = 1, ..., 64 do
10   ℓ' ← Amplify(b + δ, τ/32, F, (3/4)B+, B−);
11   δ_i ← δ_i − (τ/32)·1[ℓ'_i = +1] for all i
   // Step III: Set some labels directly if possible
12 foreach i = 1, ..., n do
13   if ℓ_i = ⊥ and δ_i ≥ τ then ℓ_i ← −1;
14   if ℓ_i = ⊥ and δ_i ≤ −τ then ℓ_i ← +1;
   // Step IV: Recurse once, at half precision
15 ℓ' ← Amplify(b + δ, τ/2, F, B+, B−);
```
The tally and budget updates (lines 16–18) are done by the caller (`amplifyAux`).

**Formalization Note.**
* Generic in the monad `m`: `amplifyAux` runs it in the cost-counting monad with defeat
  (`AmpM`) and `sub` its own recursive call; Lemma 4 runs it in `Id` with `tick` doing nothing
  and `sub` any procedure satisfying Contract 1 (the paper's inductive hypothesis, "we focus on
  the case in which all recursive calls return labelings", p.16).
* Labels: `−1` is `Lbl.lo`, `+1` is `Lbl.hi`, `⊥` is `none`. Lines 13 and 14 run in this order
  for each coordinate, so line 14 sees the label line 13 left.
* `tick c` charges `c` operations (`n = |κ|`): line 5 charges `n`; each of the 128 iterations of
  lines 6–7 / 9–10 charges `1` (loop control) plus `n` (forming `b + δ`), and line 8 / 11
  charges `n`; Step III charges `n`; line 15 charges `n` (forming `b + δ`). -/
noncomputable def boostRound {κ : Type} [Fintype κ] {m : Type → Type} [Monad m]
    (tick : ℕ → m Unit) (sub : (κ → ℝ) → ℝ → (κ → ℤ) → ℝ → ℝ → m (κ → Lbl))
    (b : κ → ℝ) (τ : ℝ) (F : κ → ℤ) (Bp Bm : ℝ) (ℓ : κ → Option Lbl) : m (RoundOut κ) := do
  let n := Fintype.card κ
  -- line 5
  tick n
  let mut δ : κ → ℝ := fun _ => 0
  -- Step I, lines 6–8
  for _ in List.range 64 do
    tick (1 + n)
    let ℓ' ← sub (b + δ) (τ / 32) F Bp (3 / 4 * Bm)
    tick n
    δ := fun i => δ i + (if ℓ' i = Lbl.lo then τ / 32 else 0)
  -- Step II, lines 9–11
  for _ in List.range 64 do
    tick (1 + n)
    let ℓ' ← sub (b + δ) (τ / 32) F (3 / 4 * Bp) Bm
    tick n
    δ := fun i => δ i - (if ℓ' i = Lbl.hi then τ / 32 else 0)
  -- Step III, lines 12–14
  tick n
  let ℓIII : κ → Option Lbl := fun i =>
    if ℓ i = none ∧ τ ≤ δ i then some Lbl.lo
    else if ℓ i = none ∧ δ i ≤ -τ then some Lbl.hi
    else ℓ i
  -- Step IV, line 15
  tick n
  let ℓ' ← sub (b + δ) (τ / 2) F Bp Bm
  return ⟨δ, ℓIII, ℓ'⟩

end LinfContractionFP


