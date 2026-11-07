-- Prove2me | Definitions.Def_CosDensity_OneWayProtocol
-- name    : CosDensity_OneWayProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:28.386035+00:00
-- url     : https://prove2.me/theorems/80b55943-ea52-4a8b-8fe3-0b5e2d033253
-- title:
--   Public-coin one-way protocols for $\mathrm{INDEX}_N$
-- statement:
--   In the **$\mathrm{INDEX}_N$ problem**, Alice receives a string $z\in\{0,1\}^N$, Bob receives an index $q\in[N]$, and Bob must output $z_q$ after receiving one message from Alice.
--
--   A **public-coin one-way protocol** consists of a shared random seed $\omega$ from a probability space $(\Omega,\mu)$, Alice's message $\mathrm{msg}(\omega,z)\in M$ for a finite message set $M$, and Bob's answer $\mathrm{dec}(\omega,\mathrm{msg}(\omega,z),q)\in\{0,1\}$. Its communication is $\log_2|M|$ bits. It **solves $\mathrm{INDEX}_N$ with error at most $1/3$** if, for every input pair $(z,q)$, Bob answers $z_q$ with probability at least $2/3$ (some measurable event of measure at least $2/3$ is contained in the set of seeds on which he does).
--
--   The reduction from $\mathrm{INDEX}_N$ is how the paper turns its hard instances into a memory lower bound.
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §3 "Communication Complexity", p.13

import Mathlib
import Definitions.Def_CosDensity_StreamAlg

open MeasureTheory

namespace CosDensity

/-!
# Public-coin one-way protocols and the INDEX_N problem

Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*, arXiv:2609.06925
(held version, sha256 f4d4df22…), §3 "Communication Complexity", p.13 (pdf_page 14): "In the
INDEX_N problem, Alice receives a string X ∈ {0, 1}^N, Bob receives an index J ∈ [N], and Bob must
output X_J after receiving one message from Alice."

**Formalization Note.**
* Strings are `Fin N → Bool` and indices `Fin N` (`0`-based).
* A protocol has a shared random seed `ω` from `(Ω, μ)` (public coins), Alice's message
  `msg ω z ∈ M` and Bob's answer `dec ω m q`. Its communication is `log₂ |M|` bits for a finite
  message set `M` (`memoryBits M`).
* "Error at most 1/3" is, for every input pair `(z, q)`, `SucceedsWP μ (Bob answers z q) (2/3)`.
-/

/-- A public-coin one-way protocol for inputs `z : Fin N → Bool` (Alice) and `q : Fin N` (Bob),
with seed space `Ω` and message set `M`. -/
structure OneWayProtocol (N : ℕ) (Ω M : Type*) where
  /-- Alice's message. -/
  msg : Ω → (Fin N → Bool) → M
  /-- Bob's output from the seed, the message and his index. -/
  dec : Ω → M → Fin N → Bool

/-- The protocol solves INDEX_N with error at most 1/3: on every input pair, Bob outputs `z q`
with probability at least 2/3 (inner-measure form). -/
def SolvesIndex {N : ℕ} {Ω M : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (π : OneWayProtocol N Ω M) : Prop :=
  ∀ (z : Fin N → Bool) (q : Fin N), SucceedsWP μ (fun ω => π.dec ω (π.msg ω z) q = z q) (2 / 3)

end CosDensity


