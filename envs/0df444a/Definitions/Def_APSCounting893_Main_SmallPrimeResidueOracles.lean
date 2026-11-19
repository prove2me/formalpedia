-- Prove2me | Definitions.Def_APSCounting893_Main_SmallPrimeResidueOracles
-- name    : APSCounting893_Main_SmallPrimeResidueOracles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T22:34:22.501772+00:00
-- url     : https://prove2.me/theorems/b4fa3c7e-80d6-4895-a92f-cf01714f1fd2
-- title:
--   Binary generator and logarithm routines for prime residues
-- statement:
--   For a prime $p$, a positive residue generator covers every nonzero residue by a power with exponent below $p-1$. The generator routine chooses the least positive $g<p$ with this coverage property. For a framed input containing $p,g,a$, the logarithm routine chooses the least exponent satisfying
--   $$0\le e<p-1,\qquad g^e\equiv a\pmod p.$$
--   Each routine returns zero when its bounded search has no witness. The searches are defined as actual bounded least-witness functions on finite binary encodings. The modular-power routine uses binary repeated squaring; it reduces every state modulo $\max(2,p)$.
--   These definitions provide uniform short arithmetic values for implicit Chinese remainder multiplication. Their finite-machine hierarchy bounds and their correctness for prime fields are separate theorem statements.
-- source:
--   Hesse, Allender and Barrington, Uniform Constant-Depth Threshold Circuits for Division and Iterated Multiplication, JCSS 65(4), 2002, author manuscript Section 4, Steps 2–3, pp. 9–11, https://www.cs.rutgers.edu/~allender/papers/division.pdf. The explicit bounded searches and finite-machine interfaces support Agarwal, Hari, Pandey and Shukla, STOC 2027 submission #893, Theorem 6.4, pp. 25–26.

import Definitions.Def_APSCounting893_Main_BoundedLeastArithmetic
set_option autoImplicit false
namespace APSCounting893.Main
open Turing.MultiTapeTM
def modularPowerStep (p : ℕ) (state : ℕ × ℕ) (b : Bool) : ℕ × ℕ :=
  (if b then state.1*state.2%max 2 p else state.1%max 2 p,
    state.2*state.2%max 2 p)

def modularPower (a e p : ℕ) : ℕ :=
  (e.bits.foldl (modularPowerStep p) (1%max 2 p,a%max 2 p)).1

def discreteLogInput (p g a : ℕ) : Word := pairWord p.bits (pairWord g.bits a.bits)

def discreteLogPredicate (q : Word) : Bool :=
  let x := Turing.MultiTapeTM.unframe q
  let p := ofBits (Turing.MultiTapeTM.unframe x)
  let g := ofBits (Turing.MultiTapeTM.unframe (Turing.MultiTapeTM.dropFrame x))
  let a := ofBits (Turing.MultiTapeTM.dropFrame (Turing.MultiTapeTM.dropFrame x))
  let e := ofBits (Turing.MultiTapeTM.dropFrame q)
  decide (e < p-1) && decide (modularPower g e p=a)

noncomputable def discreteLogValue : Word → ℕ :=
  boundedLeastValue (fun q => discreteLogPredicate q=true) 1 1


def GeneratorProperty (p g : ℕ) : Prop :=
  0 < g ∧ g < p ∧ ∀ a : ℕ,0 < a → a < p →
    ∃ e : ℕ,e < p-1 ∧ modularPower g e p=a

def generatorLanguage (root : Word) : Prop :=
  GeneratorProperty (ofBits (Turing.MultiTapeTM.unframe root)) (ofBits (Turing.MultiTapeTM.dropFrame root))

def generatorVerifier (z : Word) : Bool :=
  let root := Turing.MultiTapeTM.unframe (Turing.MultiTapeTM.unframe z)
  let p := ofBits (Turing.MultiTapeTM.unframe root)
  let g := ofBits (Turing.MultiTapeTM.dropFrame root)
  let a := ofBits (Turing.MultiTapeTM.dropFrame (Turing.MultiTapeTM.unframe z))
  let e := ofBits (Turing.MultiTapeTM.dropFrame z)
  (decide (0 < g) && decide (g < p)) &&
    ((decide (a=0) || decide (p ≤ a)) ||
      (decide (e < p-1) && decide (modularPower g e p=a)))

noncomputable def generatorValue : Word → ℕ := boundedLeastValue generatorLanguage 1 1

end APSCounting893.Main


