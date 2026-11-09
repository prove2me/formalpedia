-- Prove2me | Definitions.Def_PermutationStreams_Parity_Protocols
-- name    : PermutationStreams_Parity_Protocols
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:34.746565+00:00
-- url     : https://prove2.me/theorems/94c5367b-bdc4-4f04-9c74-28f20b853eed
-- title:
--   Three-party number-in-hand blackboard protocols with public coins
-- statement:
--   Three players hold private inputs $x\in X$ (Alice), $y\in Y$ (Bob) and $z\in Z$ (Charlie). A **deterministic blackboard protocol** is a finite binary tree. Each internal node, which stands for the transcript written so far, names a speaker and a rule that maps the speaker's own input to the next bit written on the board; the two children correspond to the two values of that bit. Each leaf carries an output. The execution on $(x,y,z)$ follows the bits from the root to a leaf; its **cost** is the number of bits written along that path, and its output is the label of the leaf reached. Speakers, rules and the number of rounds are arbitrary, and local computation is unrestricted.
--
--   A **public-coin randomized protocol** draws an input-independent outcome $\omega$ of a finite probability space $(\Omega,w)$ and runs the deterministic protocol $P_\omega$; private coins can be assumed public. The probability that the output on $(x,y,z)$ differs from a value $v$ is
--
--   $$
--   \sum_{\omega\in\Omega} w(\omega)\,\mathbf 1\{P_\omega(x,y,z)\ne v\}.
--   $$
--
--   This is the communication model of Lemma 4.4.
--
--   **Formalization Note** The output is the label of the leaf, a function of the complete transcript. The paper counts its final output bit as communication; a protocol that writes its output as its last bit is a tree of the same cost whose leaves are labelled by that bit, so this model contains every protocol of the source at the same cost (and some cheaper ones). Cost is measured on actual executions, so branches no input reaches cost nothing. A finite coin space loses no generality: on a fixed finite input set only finitely many protocol behaviors of bounded cost exist.
--
--   Differences from the source:
--   - generalization: the final output bit is written on the board and counted → the output is a leaf label, a function of the transcript, and costs nothing; reason: a source protocol writing its output last is a tree of the same cost with leaves labelled by that bit
--   - encoding: public randomness → a finite probability space of coin outcomes selecting deterministic trees; reason: finitely many bounded-cost behaviors exist on finite inputs
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §4.2, p. 7 (number-in-hand blackboard model, public randomness, unrestricted rounds, output bit counted)

import Mathlib

namespace PermutationStreams.Parity

/-- Deterministic three-party number-in-hand blackboard protocols (§4.2 p.7) as binary trees.
A node is the transcript so far; it names the speaker, whose bit is a function of that
speaker's own input only (`X` for Alice, `Y` for Bob, `Z` for Charlie). A leaf carries the
output, a function of the complete transcript. -/
inductive Protocol3 (X Y Z O : Type) where
  | leaf (output : O)
  | alice (bit : X → Bool) (zero one : Protocol3 X Y Z O)
  | bob (bit : Y → Bool) (zero one : Protocol3 X Y Z O)
  | charlie (bit : Z → Bool) (zero one : Protocol3 X Y Z O)

/-- The output of the execution on inputs `(x, y, z)`. -/
def Protocol3.run {X Y Z O : Type} : Protocol3 X Y Z O → X → Y → Z → O
  | .leaf o, _, _, _ => o
  | .alice b p0 p1, x, y, z => if b x then p1.run x y z else p0.run x y z
  | .bob b p0 p1, x, y, z => if b y then p1.run x y z else p0.run x y z
  | .charlie b p0 p1, x, y, z => if b z then p1.run x y z else p0.run x y z

/-- The number of bits written on the blackboard in the execution on `(x, y, z)`. -/
def Protocol3.cost {X Y Z O : Type} : Protocol3 X Y Z O → X → Y → Z → ℕ
  | .leaf _, _, _, _ => 0
  | .alice b p0 p1, x, y, z => 1 + if b x then p1.cost x y z else p0.cost x y z
  | .bob b p0 p1, x, y, z => 1 + if b y then p1.cost x y z else p0.cost x y z
  | .charlie b p0 p1, x, y, z => 1 + if b z then p1.cost x y z else p0.cost x y z

/-- A public-coin randomized protocol: input-independent coins `ω ∈ Ω` with arbitrary real
probability weights, each selecting a deterministic protocol (private coins revealed
publicly). -/
structure PublicCoinProtocol3 (Ω X Y Z O : Type) [Fintype Ω] where
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum : ∑ ω, weight ω = 1
  tree : Ω → Protocol3 X Y Z O

/-- Probability over the coins that the output on `(x, y, z)` differs from `v`. -/
noncomputable def PublicCoinProtocol3.errorProb {Ω X Y Z O : Type} [Fintype Ω] [DecidableEq O]
    (P : PublicCoinProtocol3 Ω X Y Z O) (x : X) (y : Y) (z : Z) (v : O) : ℝ :=
  ∑ ω, P.weight ω * (if (P.tree ω).run x y z = v then 0 else 1)

end PermutationStreams.Parity


