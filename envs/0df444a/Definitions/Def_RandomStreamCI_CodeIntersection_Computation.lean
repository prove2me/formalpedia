-- Prove2me | Definitions.Def_RandomStreamCI_CodeIntersection_Computation
-- name    : RandomStreamCI_CodeIntersection_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:26:15.761194+00:00
-- url     : https://prove2.me/theorems/31162836-1a02-4786-aabd-b8009788aa41
-- title:
--   Finite deterministic computation with polynomial runtime
-- statement:
--   A finite-control, finite-alphabet deterministic stack Turing machine computes a specified Boolean-list output from a specified input when its actual execution halts with that output in a polynomial number of transitions. One machine and one natural-coefficient polynomial precede every input.
--
--   $$\exists T,p\ \forall x,\quad T(\operatorname{in}(x))=\operatorname{out}(x)\text{ within }p(|\operatorname{in}(x)|)\text{ steps}.$$
--
--   Self-delimiting unary parameter encodings are used only for quantities polynomially bounded in the blocklength; this changes neither explicitness nor the polynomial-time decoder requirement. Mathlib execution certificates are wrapped in nonemptiness to make computation a proposition. No algorithmic correctness is postulated.
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Proposition 7 explicitness and deterministic polynomial-time decoder, pp. 8–9

import Mathlib

namespace RandomStreamCI.CodeIntersection

/-- Self-delimiting unary integers. All encoded parameters have polynomial
size in n, so this convention is polynomially equivalent to binary here. -/
def encodeNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

def encodeNats (s : List ℕ) : List Bool := s.flatMap encodeNat

/-- One uniform, finite-alphabet, finite-control deterministic stack TM and
one polynomial bound, before every input. The additional finite-alphabet
condition covers every work stack, not just Mathlib FinTM2's input stack. -/
def PolyComputes {α : Type} (input output : α → List Bool) : Prop :=
  ∃ machine : Turing.TM2ComputableAux Bool Bool,
    (∀ k : machine.tm.K, Finite (machine.tm.Γ k)) ∧
    ∃ p : Polynomial ℕ, ∀ x : α,
      Nonempty (Turing.TM2OutputsInTime machine.tm
        ((input x).map machine.inputAlphabet.symm)
        (some ((output x).map machine.outputAlphabet.symm))
        (p.eval (input x).length))

end RandomStreamCI.CodeIntersection


