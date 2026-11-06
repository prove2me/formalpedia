-- Prove2me | Definitions.Def_MemQueryFeas_memCode
-- name    : MemQueryFeas_memCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:45.524189+00:00
-- url     : https://prove2.me/theorems/64100e9c-e09c-4f3d-b83e-d7522f7f5907
-- title:
--   Encoding of $\mathrm{Mem}_v$
-- statement:
--   The value of $\mathrm{Mem}_v$ (a memory state, or undefined) is encoded injectively as a pair (flag, memory state) in $\{0,1\}\times\{0,1\}^M$, so that $\mathrm{Mem}_v$ is a random variable with values in a finite set.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Definitions 2 and 4, p.10 (PDF p.11)

import Mathlib

namespace MemQueryFeas

/-- **Encoding of `Mem_v` as a standard Borel random variable.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Definitions 2 and 4, p.10:
`Mem_v` is used as a random variable (in the information `I(E_w; Mem_v | …)` and as context of the
property `∆-Block_k`).

`memCode` sends `none` (phase never started) to `(false, 0)` and `some m` to `(true, m)`; it is
injective, so `memCode ∘ Mem_v` carries the same information as `Mem_v`.

**Formalization Note.** Used because `Bool × (Fin M → Bool)` carries a standard Borel (discrete)
σ-algebra. -/
def memCode {M : ℕ} : Option (Fin M → Bool) → Bool × (Fin M → Bool)
  | none => (false, fun _ => false)
  | some m => (true, m)

end MemQueryFeas


