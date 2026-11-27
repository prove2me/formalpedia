-- Prove2me | Definitions.Def_FreeOrderEPTAS_Supplement_pandoraReduce
-- name    : FreeOrderEPTAS_Supplement_pandoraReduce
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:39:30.270462+00:00
-- url     : https://prove2.me/theorems/472ee187-4eb8-4303-9300-b5febea18ecf
-- title:
--   The reduction of Theorem 6.1 as a program
-- statement:
--   The reduction from Pandora's Box with Commitment to Free-Order Prophets, as a counted program. On the oracle $v\mapsto\mathbb E[\max\{X_i,v\}]$, the indices $\kappa$ and the costs $c$, it
--
--   1. forms the oracle of $Y$: $\mathbb E[\max\{Y_i,v\}]$ equals $\mathbb E[\max\{X_i,v\}]$ if $\kappa_i=\infty$; $\max\{0,v\}$ if $\kappa_i<0$; and, for $\kappa_i\ge0$, $\mathbb E[\max\{X_i,v\}]-c_i$ if $v<\kappa_i$ and $v$ otherwise;
--   2. calls the Free-Order Prophets subroutine once on it, obtaining a permutation $\sigma$;
--   3. computes the thresholds of $Y$ on $\sigma$ by the backward recursion, with $n$ oracle evaluations;
--   4. returns the converted solution of Claim 6.3.
--
--   **Formalization Note** The program is written in the base cost monad `Prog`. Weitzman's indices are an input, read at one counted operation each. For Theorem 6.1 the subroutine is a black-box oracle charged one unit (`oracleCall A`); for Theorem 1.4 it is the published program `freeOrder`, whose work is counted.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, proof of Theorem 6.1, pp.31–32

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Supplement_convert
import Definitions.Def_FreeOrderEPTAS_Prog

namespace FreeOrderEPTAS.Supplement

variable {n : ℕ}

/-- The oracle of the instance `Y` built from the oracle `o` of `X`, the indices `κ` and the costs
`c` (proof of Theorem 6.1, arXiv:2007.13121v3, p.31): `E[max{Y_i, v}]` is `o i v` if `κ_i = ∞`;
`max{0, v}` if `κ_i < 0` (`Y_i = 0`); and, for `κ_i ≥ 0`, `o i v − c_i` if `v < κ_i` and `v` if
`v ≥ κ_i`, since `max{min{x, κ}, v} = max{x, v} − (x − κ)^+` for `v ≤ κ` and `E[(X_i − κ_i)^+] = c_i`.
The formula holds for every real `v`. -/
noncomputable def yOracle (o : Fin n → ℝ → ℝ) (κ : Fin n → WithTop ℝ) (c : Fin n → ℝ)
    (i : Fin n) (v : ℝ) : ℝ :=
  if h : κ i = ⊤ then o i v
  else if (κ i).untop h < 0 then max 0 v
  else if v < (κ i).untop h then o i v - c i
  else v

/-- One counted evaluation of `yOracle`: a read of `κ_i`, two comparisons, at most one query of the
`X`-oracle and at most two further operations (at most 5 operations and 1 oracle query). -/
noncomputable def callY (o : Fin n → ℝ → ℝ) (κ : Fin n → WithTop ℝ) (c : Fin n → ℝ)
    (i : Fin n) (v : ℝ) : Prog ℝ := do
  let k ← opn 1 (κ i)
  tick 2
  if h : k = ⊤ then callOrc o i v
  else if k.untop h < 0 then opn 1 (max 0 v)
  else if v < k.untop h then do
    let w ← callOrc o i v
    opn 2 (w - c i)
  else opn 1 v

/-- The thresholds of the optimal stopping rule for `Y` on `σ`, by the backward recursion
`R_{n+1} = 0`, `R_t = E[max{Y_{σ(t)}, R_{t+1}}]` (p.17) run through `callY`: `n` counted
evaluations. The result at time `s` (0-based) is `R_{s+1}` in the base convention. -/
noncomputable def thresholdsP (o : Fin n → ℝ → ℝ) (κ : Fin n → WithTop ℝ) (c : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : Prog (Fin n → ℝ) := do
  let l ← foldP (List.finRange n).reverse (fun acc s => do
    let j ← opn 1 (σ s)
    let v ← callY o κ c j (acc.headD 0)
    opn 1 (v :: acc)) [0]
  pure fun s => l.getD (s.val + 1) 0

/-- One call to an oracle `A` for Free-Order Prophets on the oracle `o`, charged as a single unit
operation: `A` runs from fresh counters, its result is returned, and its own counted work is
discarded. -/
noncomputable def oracleCall (A : (Fin n → ℝ → ℝ) → Prog (Equiv.Perm (Fin n)))
    (o : Fin n → ℝ → ℝ) : Prog (Equiv.Perm (Fin n)) :=
  fun s => do
    let r ← (A o).run 0
    pure (r.1, { s with ops := s.ops + 1 })

/-- The reduction of Theorem 6.1 (arXiv:2007.13121v3, pp.31–32), with the Free-Order Prophets
subroutine `call`, the `X`-oracle `o`, Weitzman's indices `κ` and the costs `c`:

1. build the oracle of `Y_i = min{X_i, κ_i}` (`yOracle`) and make exactly one call to `call` on it,
   obtaining a permutation `σ`;
2. compute the thresholds `t_s = R_{s+1}` of `Y` on `σ` (`thresholdsP`, `n` counted evaluations);
3. return `convertWith κ t σ` (Claim 6.3), charged `3 (n + 1)²` operations (the kept flags, their
   count, the sort by key and the rule).

**Formalization Note.** `κ_i` is read as an input, one counted read per access (the paper takes
`κ_i` "as the unique solution" without saying how it is computed). For Theorem 6.1 the subroutine is
the oracle `oracleCall A`, charged one unit; for Theorem 1.4 it is the program `freeOrder`, whose
work is counted in full. -/
noncomputable def pandoraReduce (call : (Fin n → ℝ → ℝ) → Prog (Equiv.Perm (Fin n)))
    (o : Fin n → ℝ → ℝ) (κ : Fin n → WithTop ℝ) (c : Fin n → ℝ) : Prog (PBCPolicy n) := do
  let σ ← call (yOracle o κ c)
  let t ← thresholdsP o κ c σ
  tick (3 * (n + 1) ^ 2)
  pure (convertWith κ t σ)

end FreeOrderEPTAS.Supplement


