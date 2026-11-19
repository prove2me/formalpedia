-- Prove2me | Definitions.Def_APSCounting893_Main_BoundedLeastArithmetic
-- name    : APSCounting893_Main_BoundedLeastArithmetic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T22:11:15.159209+00:00
-- url     : https://prove2.me/theorems/4d6f3a3d-d152-4e4a-8cf6-52c07f647fc9
-- title:
--   Bounded least witnesses for binary oracle arithmetic
-- statement:
--   Let $A$ be a language of binary words, fix natural numbers $a,b$, and put $r=a(|x|+1)^b$. The bounded least-witness function is
--   $$\mu_{A,a,b}(x)=
--   \begin{cases}
--   \min\{n<2^r: \operatorname{frame}(x)\Vert\operatorname{bits}(n)\in A\},&\text{if this set is nonempty},\\
--   0,&\text{otherwise}.
--   \end{cases}$$
--   The auxiliary query function encodes a positive query for a proposed witness and a negative query for a smaller candidate, using a one-bit selector. Bounded quantification of these queries expresses comparison with the least witness. These definitions support uniform generator and discrete-logarithm searches in implicit Chinese remainder arithmetic.
-- source:
--   Bounded-search implementation for the discrete logarithms and primitive generators in Hesse, Allender and Barrington, Uniform Constant-Depth Threshold Circuits for Division and Iterated Multiplication, JCSS 65(4), 2002, Section 4, Steps 2–3 and Lemmas 4.1–4.3, pp. 9–11, https://www.cs.rutgers.edu/~allender/papers/division.pdf. Used in the finite-machine arithmetic foundations for Agarwal, Hari, Pandey and Shukla, STOC 2027 submission #893, Theorem 6.4.

import Definitions.Def_APSCounting893_Main_ImplicitCountingArithmetic
import Mathlib.Data.Nat.Find
set_option autoImplicit false
namespace APSCounting893.Main
open Turing.MultiTapeTM
noncomputable def boundedLeastValue (A : Language) (a b : ℕ) (x : Word) : ℕ :=
  open Classical in
  if h : ∃ n : ℕ,n < 2^polyBound a b x.length ∧ A (Turing.MultiTapeTM.frame x++n.bits)
    then Nat.find h else 0

def leastValueRoot (z : Word) : Word := unframe (unframe (unframe z))

def leastValueWitness (z : Word) : ℕ := ofBits (dropFrame (unframe (unframe z)))

def leastValueCandidate (z : Word) : ℕ := ofBits (dropFrame (unframe z))

def leastValueBound (a b : ℕ) (root : Word) : ℕ :=
  2^polyBound a b (Turing.MultiTapeTM.unframe root).length

def leastValueQuery (a b : ℕ) (z : Word) : Word :=
  let root := leastValueRoot z
  let x := Turing.MultiTapeTM.unframe root
  let u := ofBits (Turing.MultiTapeTM.dropFrame root)
  let n := leastValueWitness z
  let m := leastValueCandidate z
  if u < leastValueBound a b root ∧ n < leastValueBound a b root then
    if (Turing.MultiTapeTM.dropFrame z).headD false then
      if m ≤ u then [false,true]++Turing.MultiTapeTM.frame x++m.bits else [true,true]
    else [false,false]++Turing.MultiTapeTM.frame x++n.bits
  else [true,false]

def leastValueClock (a b : ℕ) (z : Word) : ℕ := polyBound (a+1) (b+1) z.length
end APSCounting893.Main


