-- Prove2me | Definitions.Def_ZKSheafPCP_queryLog
-- name    : ZKSheafPCP_queryLog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:09:52.38533+00:00
-- url     : https://prove2.me/theorems/14eac4b5-d189-4727-a909-ed3839ade04c
-- title:
--   Query logs, the bit oracle of a proof, and acceptance probability
-- statement:
--   These are the observable quantities of an oracle machine. The **query log** of a machine with oracle $O$ on input $x$ is the list of strings on its query tape at each step at which it is in the query state. The **proof oracle** of a proof $\pi:[\ell]\to\Sigma$, with $\Sigma=\{0,\dots,a-1\}$, answers the query $(i,j)$ with bit $j$ of $\pi(i)$, and every other string with $0$. Indices are in binary, since a proof may be exponentially long in the explicit input. The **positions read** in a log are the $i$ of its queries, each counted once. The **acceptance probability** over $\rho$ coins is the fraction of $r\in\{0,1\}^\rho$ on which the machine accepts $(x,r)$ within a stated number of steps.
--
--   **Formalization Note** One position is one proof symbol, so the bits of a symbol and repeated queries are free. For a binary alphabet a position is a bit.
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Definition 3.24, p.13

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace ZKSheafPCP

open Classical

/-- The query log of an oracle machine (Zeilberger, O'Connor, Gur, Spooner, STOC 2027 submission,
manuscript sha256 ac5e528f…, Definition 3.24, p.13: "the number of queries the verifier makes"): the
strings on the query tape at each of the first `t` steps at which the machine is in its query state `3`. -/
noncomputable def queryLog (M : OTM) (O : Oracle) (x : Str) (t : ℕ) : List Str :=
  (List.range t).filterMap fun i =>
    let c := M.runCfg O x i
    if c.state = 3 then some (OTM.readBits c.query c.qhi) else none

/-- A natural number in binary. Positions and bit indices are in binary, because a proof may be
exponentially long in the explicit input (Theorem 8.18, p.41). -/
def binN (n : ℕ) : Str := Nat.bits n

/-- A coin string as a bit string. -/
def coinStr {m : ℕ} (r : Fin m → Bool) : Str := List.ofFn r

/-- The bit oracle of a proof `π : Fin ℓ → Fin a` over a finite alphabet: on the query `(i, j)` it answers
bit `j` of the symbol `π i`. Every other string answers `false`. One position `i` is one proof symbol. -/
noncomputable def proofOracle {ℓ a : ℕ} (π : Fin ℓ → Fin a) : Oracle := fun q =>
  decide (∃ (i : Fin ℓ) (j : ℕ), q = tup [binN i, binN j] ∧ (π i).val.testBit j = true)

/-- The positions of a proof of length `ℓ` read in a query log. Repeated queries and the bits of one
symbol count once. -/
def queriedPositions (ℓ : ℕ) (log : List Str) : Set (Fin ℓ) :=
  {i | ∃ j : ℕ, tup [binN i, binN j] ∈ log}

/-- The acceptance probability of a machine with oracle `O` over `ρ` uniform coins, within `τ` steps, on
the input `(x, r)`. -/
noncomputable def acceptProb (V : OTM) (O : Oracle) (x : Str) (ρ τ : ℕ) : ℝ :=
  ((Finset.univ.filter fun r : Fin ρ → Bool =>
    V.result O (tup [x, coinStr r]) τ = some true).card : ℝ) / 2 ^ ρ

end ZKSheafPCP


