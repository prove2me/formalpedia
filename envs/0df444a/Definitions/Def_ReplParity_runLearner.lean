-- Prove2me | Definitions.Def_ReplParity_runLearner
-- name    : ReplParity_runLearner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:24.586028+00:00
-- url     : https://prove2.me/theorems/98e6bbf8-6b98-400c-aaa2-91ef624bbb8f
-- title:
--   One run of a learner on a sample and a seed
-- statement:
--   Given a learner $A$ (a total function on machine inputs), a dimension $d$, rational parameters $\varepsilon,\delta,\rho$, a sample $S$ of $m$ labeled examples over $\mathbb F_2^d$ and a seed $r\in\{0,1\}^R$, the run $A(S;r)$ is $A$ applied to the input $(d,\varepsilon,\delta,\rho,S,r)$. Its output is read as $\bot$ or as a vector $z$, naming the parity $f_z$.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), §2.1, p.10 (PDF p.12); §2.2, p.11

import Mathlib
import Definitions.Def_ReplParity_Vec
import Definitions.Def_ReplParity_encIn
import Definitions.Def_ReplParity_encOut

namespace ReplParity

/-- **One run of a learner machine.** Shen, Zhong, *Replicable Parity Learning: Cubic Sample
Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript sha256 40424491…),
§2.1, p.10 (PDF p.12) and §2.2, p.11.

`runLearner A d ε δ ρ S r` is the raw output of the total function `A` on the input
`(d, ε, δ, ρ, S, r)`: the sample `S` is a sequence of `m` labeled examples over 𝔽ᵈ₂, each written
by `exampleBits`, and `r` is the seed, a string of `R` bits. -/
def runLearner (A : LInput → Option (List Bool)) (d : ℕ) (ε δ ρ : ℚ) {m R : ℕ}
    (S : Fin m → Example d) (r : Fin R → Bool) : Option (List Bool) :=
  A (d, ε, δ, ρ, List.ofFn (fun i => exampleBits (S i)), List.ofFn r)

/-- The output of a run read as `⊥` (`none`) or as a vector `z` (`some z`), naming the parity
`f_z`. -/
def learnerOutput (A : LInput → Option (List Bool)) (d : ℕ) (ε δ ρ : ℚ) {m R : ℕ}
    (S : Fin m → Example d) (r : Fin R → Bool) : Option (Vec d) :=
  decodeOut d (runLearner A d ε δ ρ S r)

end ReplParity


