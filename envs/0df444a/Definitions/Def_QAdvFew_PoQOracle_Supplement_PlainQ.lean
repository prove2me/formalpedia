-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Supplement_PlainQ
-- name    : QAdvFew_PoQOracle_Supplement_PlainQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:20:44.198191+00:00
-- url     : https://prove2.me/theorems/014143a0-7ece-476e-94e7-4ff60f326f83
-- title:
--   Plain-model quantum algorithms and samplers
-- statement:
--   In the **plain model** (no oracle) a **nonuniform QPT algorithm** with input length $\mathrm{in}(n)$ is, for each $n$, a polynomial-size quantum circuit that reads its input on its first wires, uses ancillas initialized to $|0\rangle$, and outputs the measurement of $\mathrm{olen}(n)$ further wires; a **QPT sampler** is a uniform polynomial-size circuit family started in $|0\cdots0\rangle$ whose output is the measurement of its first wires. Quantum advice is not allowed ("We do not allow quantum advice unless stated explicitly").
--
--   These are the algorithms of Appendix B: the sampler of an EV-OWPuzz and the adversaries against it.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §3.2.1, p. 12 (PDF p. 14); Appendix B, pp. 52–53 (PDF pp. 54–55)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_UCirc

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle.Supplement

open QAdvFew.PoQOracle

/-- The **plain model** (no oracle), for Appendix B (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Appendix B, pp. 52–53 (PDF pp. 54–55)):
the unitary oracle with every component of arity `0` (the `1 × 1` identity) and the constant-`false`
classical oracle; with them every oracle gate acts as the identity. -/
def ar0 : ℕ → ℕ → ℕ := fun _ _ => 0

/-- The trivial unitary oracle. -/
def O0 : UOracle ar0 := fun _ _ => 1

/-- The trivial classical oracle. -/
def C0 : Oracle := fun _ => false

/-- The probability that measuring the first `a` wires of the unnormalized state `ψ` on `a + b`
qubits gives `o`. -/
noncomputable def probFirst {a b : ℕ} (ψ : QState (a + b)) (o : Bits a) : ℝ :=
  ∑ y : Bits (a + b), if lft y = o then ‖ψ y‖ ^ 2 else 0

/-- A **nonuniform QPT algorithm** in the plain model with input length `inLen n` (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, §3.2.1,
p. 12 (PDF p. 14): "Nonuniform algorithms are polynomial-size circuit families … We do not allow
quantum advice unless stated explicitly"): at length `n`, an output length `olen n`, `anc n`
ancillas, and a circuit on `(inLen n + olen n) + anc n` wires; it reads its input on the first
`inLen n` wires and its output is the measurement of the next `olen n` wires. One polynomial bounds
circuit size, output length and ancilla count. -/
structure NUQAlg (inLen : ℕ → ℕ) where
  olen : ℕ → ℕ
  anc : ℕ → ℕ
  circ : (n : ℕ) → UCirc ar0 ((inLen n + olen n) + anc n)
  bound : Polynomial ℕ
  size_le : ∀ n, (circ n).size ≤ bound.eval n ∧ olen n ≤ bound.eval n ∧ anc n ≤ bound.eval n

namespace NUQAlg

variable {inLen : ℕ → ℕ}

/-- `Pr[A(x) = a]` for an input `x` of length `inLen n` and an output `a` of length `olen n`. -/
noncomputable def outProb (A : NUQAlg inLen) (n : ℕ) (x : Bits (inLen n)) (a : Bits (A.olen n)) :
    ℝ :=
  let ψ := (A.circ n).run O0 C0
    (basisState fun k => if h : (k : ℕ) < inLen n then x ⟨k, h⟩ else false)
  ∑ y : Bits ((inLen n + A.olen n) + A.anc n), if rgt (lft y) = a then ‖ψ y‖ ^ 2 else 0

end NUQAlg

/-- A **QPT sampler** in the plain model with output length `len n`: at length `n`, `anc n` ancillas
and a circuit on `len n + anc n` wires started in `|0…0⟩`; its output is the measurement of the first
`len n` wires. It is uniform and polynomially bounded where it is used. -/
structure QSampler (len : ℕ → ℕ) where
  anc : ℕ → ℕ
  circ : (n : ℕ) → UCirc ar0 (len n + anc n)

namespace QSampler

variable {len : ℕ → ℕ}

/-- `Pr[Samp(1^n) = o]`. -/
noncomputable def outProb (S : QSampler len) (n : ℕ) (o : Bits (len n)) : ℝ :=
  probFirst ((S.circ n).run O0 C0 (basisState fun _ => false)) o

/-- Uniformity: a polynomial-time map sends `1^n` to the ancilla count and circuit description. -/
def Uniform (S : QSampler len) : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ n : ℕ, f (unary n) = bnat (S.anc n) ++ (S.circ n).desc

/-- One polynomial bounds the circuit size and the ancilla count. -/
def PolyBounded (S : QSampler len) : Prop :=
  ∃ q : Polynomial ℕ, ∀ n : ℕ, (S.circ n).size ≤ q.eval n ∧ S.anc n ≤ q.eval n

end QSampler

end QAdvFew.PoQOracle.Supplement


