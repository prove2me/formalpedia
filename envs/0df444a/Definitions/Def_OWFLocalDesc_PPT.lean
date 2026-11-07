-- Prove2me | Definitions.Def_OWFLocalDesc_PPT
-- name    : OWFLocalDesc_PPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:07.620471+00:00
-- url     : https://prove2.me/theorems/f280a589-55e7-4f95-a77d-b7d2be337d35
-- title:
--   Probabilistic polynomial-time algorithm (PPT)
-- statement:
--   A **probabilistic polynomial-time algorithm** (PPT) uses independent uniform random bits and runs in time bounded by a fixed polynomial in its input length. Here a PPT algorithm $B$ consists of
--
--   1. a deterministic polynomial-time map $\mathrm{alg}$ on binary strings, and
--   2. a polynomial $c$ with natural coefficients, the number of coins as a function of the input length.
--
--   On input $u$, the algorithm draws $\rho$ uniformly from $\{0,1\}^{c(|u|)}$ and outputs $\mathrm{alg}(\langle \rho, u\rangle)$, where $\langle\cdot\rangle$ is a fixed injective tuple code. For an event $E$ on outputs, $\Pr_B[E(B(u))]$ is the fraction of coin strings $\rho$ for which $E$ holds. A test **accepts** when the first bit of its output is $1$.
--
--   This is the algorithm model of every heuristic, inverter and distinguisher in the mission: one machine for all input lengths, with no advice.
--
--   **Formalization Note** Polynomial time is the published one-tape `CookPvsNP.PolyTimeComputable`; the tuple code is the published `QuantumPRC.tupleCode`. A machine running in polynomial time reads at most polynomially many coins, so a polynomial coin count loses nothing.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), §2, p.11

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QuantumPRC_IsPolyFamily
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Probabilistic polynomial-time algorithm (PPT).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e),
§2, p.11: "A probabilistic polynomial-time algorithm, abbreviated PPT, uses independent uniform
random bits and has a running time bounded by a fixed polynomial in its input length."

A PPT algorithm is one deterministic polynomial-time machine `alg` (the published one-tape
`CookPvsNP.PolyTimeComputable`) together with a coin-count polynomial `coins`. On input `u` it
reads `coins.eval |u|` uniform coin bits `ρ` and outputs `alg (tupleCode [ρ, u])`.

**Formalization Note.** A machine whose running time is a polynomial in its input length reads at
most that many coins, so a polynomial coin count in the input length loses nothing; one machine
serves every input length (uniform algorithms, no advice). -/
structure PPT where
  /-- The deterministic polynomial-time part, run on the code of (coins, input). -/
  alg : List Bool → List Bool
  /-- The number of coin bits, as a polynomial in the input length. -/
  coins : Polynomial ℕ
  alg_poly : CookPvsNP.PolyTimeComputable alg

/-- The probability, over the uniform coins of `B`, that the output of `B` on input `u`
satisfies `E`. -/
noncomputable def PPT.prob (B : PPT) (u : List Bool) (E : List Bool → Prop) : ℝ :=
  open Classical in
  ((Finset.univ.filter fun ρ : Fin (B.coins.eval u.length) → Bool =>
      E (B.alg (QuantumPRC.tupleCode [List.ofFn ρ, u]))).card : ℝ) /
    (2 : ℝ) ^ (B.coins.eval u.length)

/-- A test accepts when the first symbol of its output is the bit `1`. -/
def Accepts (out : List Bool) : Prop := out.head? = some true

end OWFLocalDesc


