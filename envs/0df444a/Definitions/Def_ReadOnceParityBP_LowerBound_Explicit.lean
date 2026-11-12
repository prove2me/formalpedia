-- Prove2me | Definitions.Def_ReadOnceParityBP_LowerBound_Explicit
-- name    : ReadOnceParityBP_LowerBound_Explicit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:27:41.054195+00:00
-- url     : https://prove2.me/theorems/48c1ab69-cbe4-4020-afe4-b3046fd60066
-- title:
--   Uniform polynomial-time explicitness, exact-count input, and padding
-- statement:
--   For a family F_N on N-bit tuples, Explicit(F) means that one function g on all Boolean lists is computed by one finite Mathlib TM2 machine with one polynomial bound on actual machine steps, and g agrees with F_N on every N-bit input.
--
--   $$\operatorname{Explicit}(F)\iff\exists g,M,p,\quad M(z)=g(z)\text{ in at most }p(|z|)\text{ steps},\quad g(z)=F_{|z|}(z).$$
--
--   countInput splits a list of length 2n into x followed by y and returns validEligibleCount when n is even; it returns zero at every other length. The empty list has n=0 and returns one. Counting output is subsequently encoded by Mathlib's binary natural encoding, whose zero code is empty.
--
--   paddedEval takes n=2⌊N/4⌋ at length N≥4, evaluates fBool on the first 2n bits, and ignores the remaining at most three bits; at N<4 it returns false. paddedFamily is the same function on finite tuples. These are mathematical function bodies, not assertions that an evaluator or a runtime bound exists. The TM2 representation charges stack operations through its step relation; the fixed finite machine has bounded work per step, and writing output is included.
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Theorem 1.2 and explicitness sentence p.2; Theorem 3.2 pp.9–10; all-length encoding from Definition 2.3 p.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_CanonicalMatching

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Volk, p. 2 (after Theorem 1.2): a family `{f_N : {0,1}^N → {0,1}}_{N ∈ ℕ}` is explicit if a
single polynomial-time Turing machine computes `f_N(x)` on input `x = (x_0, …, x_{N-1})`.
Machines are Mathlib's finite multi-stack Turing machines (`Turing.FinTM2`); the input is the
bit string `x` itself, the output is one bit, and the number of steps is bounded by a fixed
polynomial in the input length `N`. -/
def Explicit (F : (N : ℕ) → (Fin N → Bool) → Bool) : Prop :=
  ∃ g : List Bool → Bool,
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      Computability.encodeBool g) ∧
    ∀ (N : ℕ) (z : Fin N → Bool), g (List.ofFn z) = F N z

/-- Theorem 3.2's exact-count input convention: the first half of a string is x,
the second half is y. On length 2n with n even return the exact count; on every
other length return zero. In particular the empty string has count one. -/
noncomputable def countInput (bits : List Bool) : ℕ :=
  let n := bits.length / 2
  if bits.length = 2 * n ∧ Even n then
    validEligibleCount n (fun i => bits.getD i.val false)
      (fun i => bits.getD (n + i.val) false)
  else 0

/-- Padding the construction to every input length: n = 2 floor(N/4), use its
first 2n bits, and ignore the at most three trailing bits. For N < 4 return false. -/
noncomputable def paddedEval (bits : List Bool) : Bool :=
  let n := 2 * (bits.length / 4)
  if bits.length < 4 then false
  else fBool n (fun v => match v with
    | .inl i => bits.getD i.val false
    | .inr i => bits.getD (n + i.val) false)

/-- The same padded Boolean family on finite tuples. -/
noncomputable def paddedFamily (N : ℕ) (z : Fin N → Bool) : Bool :=
  paddedEval (List.ofFn z)

end ReadOnceParityBP.LowerBound


