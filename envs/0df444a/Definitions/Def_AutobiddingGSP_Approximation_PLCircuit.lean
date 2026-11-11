-- Prove2me | Definitions.Def_AutobiddingGSP_Approximation_PLCircuit
-- name    : AutobiddingGSP_Approximation_PLCircuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:27:32.343685+00:00
-- url     : https://prove2.me/theorems/a0dbb2a7-7be4-4162-a31b-0e3dce51abe6
-- title:
--   PL pseudo-circuits with Heaviside and discretization pseudogates, and their fixed points
-- statement:
--   $D_\aleph(x)$ (p. 22): $0$ for $x\le0$; $[x-1,x]$ for $x\in\{1,\dots,\aleph\}$; $\lfloor x\rfloor$ for other $x\in[0,\aleph]$; $\aleph$ for $x>\aleph$.
--
--   A gate list defines nodes $0,1,\dots$ (gate $k$ produces node $k$; arguments may be any nodes, so the circuit is cyclic). Gates: constants, rational linear combinations, max, min, a Heaviside pseudogate (output in $H(x)$), the product pseudogate $y\cdot H(x)$ and the scaled discretization $y\cdot D_\aleph(x/s)\cdot s$. A **fixed point** is an assignment of reals to the nodes at which every gate's relation holds. Gates and gate lists have binary codes.
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], §4.1 p. 12–13; §5.1–5.2, pp. 22–23 (pseudogate framework of [FRHHH23, FRHHH24])

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_AutobiddingGSP_Approximation_Insertion

namespace AutobiddingGSP.Approximation

open QAlgorithms.LocalHamiltonian

/-- **The piecewise-constant correspondence** `D_ℵ` represented by the identity Boolean circuit on
`d + 1` bits, `ℵ = 2^d` (§5.2, p. 22, following [FRHHH24, Definition 3.6]):
`D_ℵ(x) = 0` for `x ≤ 0`; `[x − 1, x]` for `x ∈ {1, 2, …, ℵ}`; `⌊x⌋` for the other
`x ∈ [0, ℵ]`; and `ℵ` for `x > ℵ`. -/
noncomputable def Dset (aleph : ℕ) (x : ℝ) : Set ℝ := by
  classical
  exact if x ≤ 0 then {0}
  else if (aleph : ℝ) < x then {(aleph : ℝ)}
  else if ∃ j : ℕ, 1 ≤ j ∧ j ≤ aleph ∧ x = j then Set.Icc (x - 1) x
  else {((⌊x⌋ : ℤ) : ℝ)}

/-- **A gate of a PL pseudo-circuit** (§4 and §5, pp. 12–25, in the pseudogate framework of
[FRHHH23, FRHHH24]). Nodes are numbered `0, 1, 2, …`; the gate at position `k` of the gate list
produces node `k`, and its arguments are node numbers (earlier or later: the circuit is cyclic and
is read as a fixed-point system).

* `const q`: the constant `q`;
* `lin ts c`: `∑ (λ, x) ∈ ts, λ · node x + c` (addition, subtraction and multiplication by
  rational constants);
* `max x y`, `min x y`;
* `heav x`: a Heaviside pseudogate, output in `H(node x)`;
* `mulHeav x y`: the correspondence `(x, y) ↦ y · H(x)` ([FRHHH24, Lemma 3.1]);
* `mulDisc ℵ s x y`: the correspondence `y · D_ℵ(x / s) · s` with the positive rational scale `s`
  ([FRHHH24, Proposition 3.3]). -/
inductive PGate where
  | const (q : ℚ)
  | lin (ts : List (ℚ × ℕ)) (c : ℚ)
  | max (x y : ℕ)
  | min (x y : ℕ)
  | heav (x : ℕ)
  | mulHeav (x y : ℕ)
  | mulDisc (aleph : ℕ) (s : ℚ) (x y : ℕ)

/-- The input–output relation of a gate at an assignment `v` of real values to the nodes: the value
`out` of the gate's own node is admissible. -/
def PGate.Holds (v : ℕ → ℝ) (out : ℝ) : PGate → Prop
  | PGate.const q => out = q
  | PGate.lin ts c => out = (ts.map (fun p => (p.1 : ℝ) * v p.2)).sum + c
  | PGate.max x y => out = Max.max (v x) (v y)
  | PGate.min x y => out = Min.min (v x) (v y)
  | PGate.heav x => out ∈ Hset (v x)
  | PGate.mulHeav x y => ∃ e ∈ Hset (v x), out = v y * e
  | PGate.mulDisc aleph s x y => ∃ e ∈ Dset aleph (v x / s), out = v y * (e * s)

/-- **A fixed point of a PL pseudo-circuit**: an assignment of reals to the nodes `0, …, L − 1`
(`L` the number of gates; later nodes are ignored) at which every gate's relation holds. For a
circuit whose update nodes feed back into its inputs, this is the paper's
`F(α, ζ, π) = (α, ζ, π)` with every pseudogate at its specified input–output relation. -/
def IsFixedPoint (gates : List PGate) (v : ℕ → ℝ) : Prop :=
  ∀ k (hk : k < gates.length), (gates[k]).Holds v (v k)

/-- A list of (coefficient, node) terms in binary. -/
def encTerms (ts : List (ℚ × ℕ)) : List Bool :=
  encBin ts.length ++ ts.flatMap (fun p => encRat p.1 ++ encBin p.2)

/-- The binary code of a gate: a three-bit tag followed by its rational constants (`encRat`) and
node numbers (`encBin`). -/
def encPGate : PGate → List Bool
  | PGate.const q => [false, false, false] ++ encRat q
  | PGate.lin ts c => [false, false, true] ++ encTerms ts ++ encRat c
  | PGate.max x y => [false, true, false] ++ encBin x ++ encBin y
  | PGate.min x y => [false, true, true] ++ encBin x ++ encBin y
  | PGate.heav x => [true, false, false] ++ encBin x
  | PGate.mulHeav x y => [true, false, true] ++ encBin x ++ encBin y
  | PGate.mulDisc aleph s x y => [true, true, false] ++ encBin aleph ++ encRat s ++ encBin x ++ encBin y

/-- The binary code of a gate list. -/
def encPGates (gates : List PGate) : List Bool :=
  encBin gates.length ++ gates.flatMap encPGate

end AutobiddingGSP.Approximation


