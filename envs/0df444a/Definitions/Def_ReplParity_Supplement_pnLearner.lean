-- Prove2me | Definitions.Def_ReplParity_Supplement_pnLearner
-- name    : ReplParity_Supplement_pnLearner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:54:54.100896+00:00
-- url     : https://prove2.me/theorems/0cf7f25e-0439-4d6e-b703-a8f934a3a358
-- title:
--   A finite-bit learner for $P_n$, the full Boolean class on $[n]$
-- statement:
--   $P_n$ is the class of all functions $[n]\to\{0,1\}$, written as $n$-bit truth tables. A sample point $(i,b)\in[n]\times\{0,1\}$ is identified with the labeled example $(e_i,b)$ over $\mathbb F_2^n$, where $e_i$ is the $i$-th standard basis vector; learning $P_n$ is parity learning with the marginal supported on the standard basis, since $f_z(e_i)=z_i$.
--
--   Given a total function $A$ on the base mission's machine inputs $(n,\varepsilon,\delta,\rho,\text{sample},\text{seed})$, the learner $\mathrm{pnLearner}_A(n,\varepsilon,\delta,\rho)$ runs $A$ on the sample $((e_{i_1},b_1),\dots,(e_{i_m},b_m))$ and a seed of $R$ bits, and reads the output as $\bot$ or as the truth table $[n]\to\{0,1\}$ given by its bits.
--
--   This is the learner object of statements 1 and 3 of Theorem 5.3.
--
--   **Formalization Note** Sample points are encoded with the base mission's fixed example encoding, of length $n+1$, which is polynomial in the dimension.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), §2.1 "The full Boolean class on a known finite domain", p.11 (PDF p.13)

import Mathlib
import Definitions.Def_ReplParity_Vec
import Definitions.Def_ReplParity_runLearner

set_option autoImplicit false

namespace ReplParity

namespace Supplement

/-- A labeled point `(i, b)` of `[n] × {0, 1}` as the lifted example `(e_i, b)` over `𝔽ⁿ₂`
(§2.1, p.11: "The map i ↦ e_i embeds [n] into 𝔽ⁿ₂"). -/
def toExample {n : ℕ} (p : Fin n × ZMod 2) : Example n :=
  (Pi.single p.1 1, p.2)

/-- **A finite-bit learner for `P_n`.** Shen, Zhong, *Replicable Parity Learning: Cubic Sample
Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript sha256 40424491…),
§2.1, p.11 (PDF p.13): "Let P_n be the class of all functions [n] → {0, 1}, represented by n-bit
truth tables. The map i ↦ e_i embeds [n] into 𝔽ⁿ₂, and every function on [n] is the restriction of
a parity under this map … So learning P_n is the special case of parity learning in which the
marginal distribution is supported on the standard basis."

`pnLearner A n ε δ ρ` runs the total function `A` (a machine of the base mission's finite-bit model,
input `ReplParity.LInput`) on the sample `S` of labeled points of `[n]`, each written as the example
`(e_i, b)` over `𝔽ⁿ₂`, and on the seed `r`. The output is `⊥` (`none`) or the truth table
`Fin n → ZMod 2` read from the output bits (`ReplParity.learnerOutput`).

**Formalization Note.** The encoding of a sample point `(i, b)` is the base mission's
`exampleBits (e_i, b)`, fixed independently of any learner; its length `n + 1` is polynomial in the
dimension, so polynomial time is unaffected. -/
def pnLearner (A : LInput → Option (List Bool)) (n : ℕ) (ε δ ρ : ℚ) {m R : ℕ}
    (S : Fin m → Fin n × ZMod 2) (r : Fin R → Bool) : Option (Fin n → ZMod 2) :=
  learnerOutput A n ε δ ρ (fun i => toExample (S i)) r

end Supplement

end ReplParity


