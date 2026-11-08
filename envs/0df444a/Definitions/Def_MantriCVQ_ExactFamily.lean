-- Prove2me | Definitions.Def_MantriCVQ_ExactFamily
-- name    : MantriCVQ_ExactFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:39.476046+00:00
-- url     : https://prove2.me/theorems/b82eec12-18cb-4864-a52b-c1a0434e6d42
-- title:
--   Uniform families of oracle circuits
-- statement:
--   A family assigns to each input length $n$ a number of ancillas, a circuit on $n+\mathrm{anc}(n)+1$ wires and an output wire. It is **uniform** if a classical polynomial-time machine with no oracle maps $1^n$ to the description of the family at length $n$. It is **polynomial-size** if one polynomial bounds the size and the ancilla count. Its acceptance probability on $x$ with oracle $O$ is the probability that the output wire reads $1$ after the circuit for $|x|$ runs on $|x,0\cdots0\rangle$.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_MantriCVQ_Circ
import Definitions.Def_MantriCVQ_ket

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

/-- A family of quantum circuits with oracle gates over the gate set `G` (Mantri, arXiv:2610.37635
(PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)): for each input length `n`, a number of
ancillas, a circuit on `n + anc n + 1` wires, and an output wire. -/
structure ExactFamily (G : List Gate) where
  /-- ancilla count at input length `n` (beyond one mandatory wire) -/
  anc : ℕ → ℕ
  /-- the circuit at input length `n` -/
  circ : (n : ℕ) → Circ G (n + anc n + 1)
  /-- the output wire at input length `n` -/
  out : (n : ℕ) → Fin (n + anc n + 1)

/-- Uniformity: a classical polynomial-time machine, with no oracle, maps `1^n` to the description
of the family at length `n`. -/
def ExactFamily.Uniform {G : List Gate} (F : ExactFamily G) : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ n : ℕ, f (unary n) = encNat (F.anc n) ++ encNat (F.out n : ℕ) ++ (F.circ n).enc

/-- Polynomial size: one polynomial bounds the size and the ancilla count. -/
def ExactFamily.PolyBounded {G : List Gate} (F : ExactFamily G) : Prop :=
  ∃ q : Polynomial ℕ, ∀ n : ℕ, (F.circ n).size ≤ q.eval n ∧ F.anc n ≤ q.eval n

/-- The probability that the family, with the oracle `O`, accepts `x`: the circuit for `|x|` is run
on `|x, 0…0⟩` and the output wire is measured. -/
noncomputable def ExactFamily.acceptProb {G : List Gate} (F : ExactFamily G) (O : Oracle) (x : Str) :
    ℝ :=
  probOne ((F.circ x.length).run O
    (ket _ (x ++ List.replicate (F.anc x.length + 1) false))) (F.out x.length)

end MantriCVQ


