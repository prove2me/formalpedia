-- Prove2me | Definitions.Def_BeyondConvexity_APTAS_PolynomialOn
-- name    : BeyondConvexity_APTAS_PolynomialOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:11:01.613109+00:00
-- url     : https://prove2.me/theorems/62c6c843-ba24-41c4-ab3c-448986d42415
-- title:
--   Binary geometric encodings and finite-machine execution
-- statement:
--   Coordinates are encoded as signed, reduced rational numerators and denominators in binary, using the published rational encoder. Cycles and hole lists have self-delimiting lengths. Packing outputs encode the bin count and every occurrence’s bin index and rational translation. The input length is at least two.
--
--   A procedure is polynomial on a promise if one finite machine, with finite alphabets on every stack, produces the encoded value of the specified function within
--
--   $$C\max\{2,|\mathrm{enc}(x)|\}^{d}$$
--
--   steps on every input satisfying the promise. The constants and machine precede the input. Effective functions have a machine with no prescribed runtime bound. Execution is Mathlib’s operational TM2 execution relation. Correctness on a geometric class is a promise and does not require decidable membership. These are computation primitives, rather than an APTAS specification or a geometric oracle.
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/890.pdf, Definition 1, printed p.5 / PDF p.6; Appendix D.9, printed pp.32–33 / PDF pp.33–34.

import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_AbelianCayleyHDX_encRat
import Definitions.Def_BeyondConvexity_APTAS_Packing

namespace BeyondConvexity.APTAS

/- Section 2 (printed p.5 / PDF p.6) uses total binary input length.
Definition 1 and Appendix D.9 (printed p.33 / PDF p.34) use finite-machine bit time.
The encoders below are fixed and contain no geometric validity or optimization oracle. -/

open RSListDecodingCapacity.AllRates (encNat encList)

def encPoint (q : QPoint) : List Bool :=
  AbelianCayleyHDX.encRat q.1 ++ AbelianCayleyHDX.encRat q.2

def encPolygon (P : Polygon) : List Bool :=
  encList encPoint P.outer ++ encList (encList encPoint) P.holes

def encInstance (I : Instance) : List Bool := encList encPolygon I

def encPacking (p : Packing ℚ) : List Bool :=
  encNat p.bins ++ encList (fun q => encNat q.1 ++ encPoint q.2) p.placements

def inputLength (I : Instance) : ℕ := max 2 (encInstance I).length

abbrev BitMachine := Turing.TM2ComputableAux Bool Bool

/-- All stacks have finite alphabets; Mathlib's FinTM2 only requires this for its input stack. -/
def BitMachine.Finite (M : BitMachine) : Prop :=
  ∀ k : M.tm.K, _root_.Finite (M.tm.Γ k)

def BitMachine.Runs (M : BitMachine) (input output : List Bool) (steps : ℕ) : Prop :=
  Nonempty (Turing.TM2OutputsInTime M.tm (input.map M.inputAlphabet.symm)
    (some (output.map M.outputAlphabet.symm)) steps)

def Effective {A B : Type} (encA : A → List Bool) (encB : B → List Bool)
    (f : A → B) : Prop :=
  ∃ M : BitMachine, M.Finite ∧ ∀ a, ∃ t, M.Runs (encA a) (encB (f a)) t

def PolynomialOn {A B : Type} (encA : A → List Bool) (encB : B → List Bool)
    (promise : A → Prop) (f : A → B) : Prop :=
  ∃ (M : BitMachine) (C d : ℕ), M.Finite ∧
    ∀ a, promise a → M.Runs (encA a) (encB (f a))
      (C * (max 2 (encA a).length)^d)

end BeyondConvexity.APTAS


