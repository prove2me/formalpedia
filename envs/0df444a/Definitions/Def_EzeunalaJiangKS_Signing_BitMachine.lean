-- Prove2me | Definitions.Def_EzeunalaJiangKS_Signing_BitMachine
-- name    : EzeunalaJiangKS_Signing_BitMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T01:01:59.161448+00:00
-- url     : https://prove2.me/theorems/e4e6c888-7818-4dc4-8929-773cdf0e8068
-- title:
--   Finite Turing-machine clock and signing output predicate
-- statement:
--   A program is a Mathlib Post-Turing machine with finitely many states and alphabet consisting of a blank and two bit symbols. Each transition moves the head one cell or writes one symbol. Starting from the encoded input, a valid run must reach a halting configuration after $t$ transitions with
--   $$t\le C(|w|+1)^k.$$
--   The output is the first $N$ actual tape cells starting at the final head, each required to be a bit; zero means $-1$ and one means $+1$. The predicate requires their signed matrix sum to meet the exact discrepancy bound with constant $13$.
--
--   This is an operational bit-time specification, not a chosen runtime function. The finite program and clock constants precede every input. Choice-based analytic objects in later definitions are not instructions available to this machine.
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), Theorem 1.1 and rationality footnote, printed p. 1 (PDF p. 2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_BinaryCodec
import Mathlib.Computability.TuringMachine.PostTuringMachine

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

/-- Blank=none; input/output bits=some false, some true. Fin(q+1) is a finite state set. -/
abbrev BitProgram (q : ℕ) := Turing.TM0.Machine (Option Bool) (Fin (q + 1))
abbrev BitConfig (q : ℕ) := Turing.TM0.Cfg (Option Bool) (Fin (q + 1))

def bitRun {q : ℕ} (M : BitProgram q) (w : List Bool) : ℕ → Option (BitConfig q)
  | 0 => some (Turing.TM0.init (w.map some))
  | n+1 => (bitRun M w n).bind (Turing.TM0.step M)

def bitSign (b : Bool) : ℝ := if b then 1 else -1

/-- Output is the N consecutive actual tape cells starting at the final head. -/
def correctOutput {q : ℕ} (I : RationalInput) (c : BitConfig q) : Prop :=
  ∃ bits : Fin I.N → Bool,
    (∀ i, c.Tape.right₀.nth i.val = some (bits i)) ∧
    spectral (∑ i, bitSign (bits i) • I.matrices i) ≤
      13 * Real.sqrt (variance I.matrices)

def polynomialSigning (q : ℕ) (M : BitProgram q) (C k : ℕ) : Prop :=
  1 ≤ C ∧ ∀ I : RationalInput, I.valid →
    ∃ (t : ℕ) (c : BitConfig q), t ≤ C * (I.word.length + 1)^k ∧
      bitRun M I.word t = some c ∧ Turing.TM0.step M c = none ∧ correctOutput I c

end EzeunalaJiangKS.Signing


