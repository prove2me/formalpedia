-- Prove2me | Definitions.Def_OWFLocalDesc_Supplement_GlobalDecoder
-- name    : OWFLocalDesc_Supplement_GlobalDecoder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:39:49.014264+00:00
-- url     : https://prove2.me/theorems/c2e587a3-5141-4957-b2bb-ac8d1f38873b
-- title:
--   The global decoder $V$: an efficiently universal machine with a conditioning input (Appendix B)
-- statement:
--   Appendix B compares the pointwise decoder $U$ of §2.1 with a **global decoder** $V$: an efficiently universal machine that takes a finite program $\beta$, a sequential **conditioning input** $e$ and a public tape $W$, and outputs a finite binary string.
--
--   The run of $V$ after $s$ steps is either "not halted" or "halted with output $y\in\{0,1\}^*$". A machine qualifies as a global decoder when:
--
--   1. a halted run stays halted with the same output, so a step count is a clock;
--   2. the program and the conditioning input are read sequentially, each followed by an end marker, and the tape is read sequentially, so an $s$-step run depends only on the first $s$ symbols of each;
--   3. (efficient universality) for every procedure that is computable in polynomial time from a payload $v$, the conditioning input $e$ and a prefix of the public tape whose length is computed in polynomial time from $(v,e)$, there is a self-delimiting header $\sigma$ and a constant $c$ such that, for every payload $v$, the program $\sigma v$ halts with exactly the procedure's output within
--   $$(|\sigma v|+|e|)^c+c$$
--   steps, a bound that does not depend on the length of the public tape.
--
--   This is the counterpart of the pointwise decoder `OWFLocalDesc.Decoder`: the paper writes "The simulation overhead of V is polynomial in the simulated time and the lengths of the program and conditioning input, independently of unread public bits."
--
--   **Formalization Note** The paper fixes one machine; the definition records the properties p.37 states and the theorems quantify over every machine having them. Polynomial time is the published one-tape `CookPvsNP.PolyTimeComputable`, and tuples are coded by `QuantumPRC.tupleCode`.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Appendix B, p.37

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_Decoder
set_option autoImplicit false

namespace OWFLocalDesc.Supplement

open OWFLocalDesc

/-- **The global decoder `V`: an efficiently universal machine with a conditioning input.**
Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Appendix B, p.37: "Fix an efficiently universal machine
V that takes a finite program, a sequential conditioning input, and a public tape, and outputs a
finite binary string. As for the pointwise decoder U, a fixed procedure is specified by a
self-delimiting header, whose length depends only on that procedure, followed by an arbitrary
finite payload. The simulation overhead of V is polynomial in the simulated time and the lengths
of the program and conditioning input, independently of unread public bits."

`run β e W s` is the state of the run of `V` on program `β`, conditioning input `e` and public
tape `W` after `s` steps: `none` if it has not halted, `some y` if it has halted with output the
binary string `y`.

**Formalization Note.** The paper fixes one machine; the formalization records the properties
p.37 states, in the same way as the published pointwise `OWFLocalDesc.Decoder`, and quantifies
over every machine having them. Each field is one clause of p.37:
1. `run_mono`: a halted run stays halted with the same output (a step count is a clock).
2. `run_prefix`: the program and the conditioning input are sequential inputs followed by an end
   marker (`OWFLocalDesc.seqIn`) and the tape is read sequentially, so an `s`-step run depends only
   on the first `s` symbols of each ("reads these fields sequentially and needs no length oracle").
3. `universal`: every procedure computable in polynomial time from the payload, the conditioning
   input and a prefix of the public tape whose length is computed in polynomial time from the
   payload and the conditioning input has a header `σ` (self-delimiting: every payload `v` may
   follow it) such that `σ ++ v` halts with exactly the procedure's output within a polynomial in
   the lengths of the program and the conditioning input, not of the tape ("independently of
   unread public bits"). -/
structure GlobalDecoder where
  /-- The step-indexed result of the run on (program, conditioning input, public tape). -/
  run : List Bool → List Bool → List Bool → ℕ → Option (List Bool)
  /-- Once halted, a run stays halted with the same output. -/
  run_mono : ∀ (β e W : List Bool) (s s' : ℕ) (y : List Bool),
    s ≤ s' → run β e W s = some y → run β e W s' = some y
  /-- A run of `s` steps depends only on the first `s` symbols of each sequential input. -/
  run_prefix : ∀ (β β' e e' W W' : List Bool) (s : ℕ),
    (seqIn β).take s = (seqIn β').take s → (seqIn e).take s = (seqIn e').take s →
      W.take s = W'.take s → run β e W s = run β' e' W' s
  /-- Efficient universality with self-delimiting headers and sequential tape access. -/
  universal : ∀ K P : List Bool → List Bool,
    CookPvsNP.PolyTimeComputable K → CookPvsNP.PolyTimeComputable P →
      ∃ (σ : List Bool) (c : ℕ), ∀ v e W : List Bool,
        (K (QuantumPRC.tupleCode [v, e])).length ≤ W.length →
          ∃ s ≤ ((σ ++ v).length + e.length) ^ c + c,
            run (σ ++ v) e W s =
              some (P (QuantumPRC.tupleCode
                [v, e, W.take (K (QuantumPRC.tupleCode [v, e])).length]))

end OWFLocalDesc.Supplement


