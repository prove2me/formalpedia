-- Prove2me | Definitions.Def_OWFLocalDesc_Decoder
-- name    : OWFLocalDesc_Decoder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:15.873098+00:00
-- url     : https://prove2.me/theorems/088db79d-edf4-49de-afea-07bdb0eebf41
-- title:
--   The decoder $U$: an efficiently universal machine with sequential inputs
-- statement:
--   The paper fixes an **efficiently universal Turing machine** $U$ once and for all. A run of $U$ has four **sequential inputs**: a program $\beta$, an anchor list $L$, a public tape $w$ and a query $z$. They are read one symbol at a time and the machine is not told their lengths; $\beta$, $L$ and $z$ are each followed by a blank end marker. Write $U_s(\beta,L,w,z)$ for the state of the run after $s$ steps: not halted, halted with an invalid output, or halted with first output symbol a bit $b$.
--
--   A **decoder** is any such step-indexed run with the following properties, each stated in §2.1.
--
--   1. **Clock.** A run that has halted by step $s$ stays halted with the same output at every later step.
--   2. **Sequential reading.** "A run of a given number of steps reads at most that many initial symbols of each" sequential input: $U_s$ depends only on the first $s$ symbols of $\beta$, $L$ and $z$ (each followed by its end marker) and on the first $s$ bits of $w$.
--   3. **Efficient universality with self-delimiting headers.** For every procedure computable in polynomial time from a payload $v$, the anchor list, the query and a prefix of the public tape whose length is itself computed in polynomial time from $(v,L,z)$, there are a header $\sigma$ and a polynomial bound such that for every payload $v$ the program $\sigma v$ halts with the procedure's answer within a polynomial in $|\sigma v|$, $|L|$ and $|z|$ steps, whenever the tape is long enough. The bound does not depend on the tape length.
--   4. **Efficient simulation.** $U_s(\beta,L,w,z)$ is computable in time polynomial in $s$ and the lengths of $\beta$, $L$, the first $s$ bits of $w$, and $z$.
--
--   The certificate model of the paper is built on this machine: a certificate's hypothesis answers a query by running $U$ for $t$ steps.
--
--   **Formalization Note** Instead of one fixed machine, every statement quantifies over all decoders with these four properties; a real efficiently universal machine with sequential inputs has them. The answer of a procedure is the first symbol of its output. Field 4 is used where the paper evaluates "the $t$-step hypothesis" inside a polynomial-time function (Theorem 5.1, p.25). The helper `seqIn` appends the end marker; `resultCode` is a fixed binary code of the three possible run states.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), §2.1, p.12

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QuantumPRC_IsPolyFamily
set_option autoImplicit false

namespace OWFLocalDesc

/-- A sequential input as the decoder sees it: its bits (`some b`) followed by the blank end
marker (`none`). §2.1, Definition 2.5, p.12: "Each of the inputs β and L_A, and the query z …, is
followed by a blank end marker, the only symbol on these inputs that is not a bit." -/
def seqIn (u : List Bool) : List (Option Bool) := u.map some ++ [none]

/-- A fixed binary code of a step-indexed decoder result: `[]` for "not halted", `[0]` for
"halted with an invalid output", `[1, b]` for "halted with first output symbol the bit `b`". -/
def resultCode : Option (Option Bool) → List Bool
  | none => []
  | some none => [false]
  | some (some b) => [true, b]

/-- **The decoder `U`: an efficiently universal machine with sequential inputs.**
Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), §2.1, p.12: "Fix an efficiently universal Turing machine U
once and for all. Every program for U consists of a self-delimiting header followed by an arbitrary
finite payload. The header names a fixed procedure, its length depends only on that procedure, and
it shows where the payload starts. Simulating a program on U has polynomial overhead in the
simulated running time and in the lengths of the program, the anchor list and the query … This
overhead does not depend on the total public-tape length, because public bits are read sequentially
… The program and every random tape the machine reads … are sequential inputs, read one symbol at a
time; the machine is not told their lengths. Each step reads at most one new symbol of a sequential
input, so a run of a given number of steps reads at most that many initial symbols of each."

`run β L w z s` is the state of the run of `U` on program `β`, anchor list `L`, public tape
`w` and query `z` after `s` steps: `none` if it has not halted, `some none` if it has halted
with an invalid output (no output symbol, or a first output symbol that is not a bit), and
`some (some b)` if it has halted with first output symbol the bit `b`.

**Formalization Note.** The paper fixes one machine; the formalization records the properties
§2.1 states and quantifies over every machine having them. Each field is one sentence of §2.1:
1. `run_mono`: a halted run stays halted with the same output (a step count is a clock).
2. `run_prefix`: "a run of a given number of steps reads at most that many initial symbols of
   each" sequential input; `β`, `L`, `z` are followed by their end marker, the tape `w` is not,
   and the machine is not told any length.
3. `universal`: every procedure computable in polynomial time from the payload, the anchor list,
   the query and a polynomially long, adaptively computed prefix of the public tape has a header
   `σ` (self-delimiting: every payload `v` may follow it) such that `σ ++ v` halts with the
   procedure's answer within a polynomial in the lengths of the program, the anchor list and the
   query, not of the tape. The number of tape bits read is the length of the output of a
   polynomial-time map `K`; the answer is the first output symbol of a polynomial-time map `P`.
4. `simulable`: `U` is itself a Turing machine with this overhead, so its `s`-step result is
   computable in time polynomial in `s` and the input lengths (used where the paper evaluates "the
   t-step hypothesis", Theorem 5.1, p.25). -/
structure Decoder where
  /-- The step-indexed result of the run on (program, anchor list, public tape, query). -/
  run : List Bool → List Bool → List Bool → List Bool → ℕ → Option (Option Bool)
  /-- Once halted, a run stays halted with the same output. -/
  run_mono : ∀ (β L w z : List Bool) (s s' : ℕ) (o : Option Bool),
    s ≤ s' → run β L w z s = some o → run β L w z s' = some o
  /-- A run of `s` steps depends only on the first `s` symbols of each sequential input. -/
  run_prefix : ∀ (β β' L L' w w' z z' : List Bool) (s : ℕ),
    (seqIn β).take s = (seqIn β').take s → (seqIn L).take s = (seqIn L').take s →
      w.take s = w'.take s → (seqIn z).take s = (seqIn z').take s →
        run β L w z s = run β' L' w' z' s
  /-- Efficient universality with self-delimiting headers and sequential tape access. -/
  universal : ∀ K P : List Bool → List Bool,
    CookPvsNP.PolyTimeComputable K → CookPvsNP.PolyTimeComputable P →
      ∃ (σ : List Bool) (c : ℕ), ∀ v L w z : List Bool,
        (K (QuantumPRC.tupleCode [v, L, z])).length ≤ w.length →
          ∃ s ≤ ((σ ++ v).length + L.length + z.length) ^ c + c,
            run (σ ++ v) L w z s =
              some (P (QuantumPRC.tupleCode
                [v, L, w.take (K (QuantumPRC.tupleCode [v, L, z])).length, z])).head?
  /-- The decoder's own `s`-step result is computable in polynomial time. -/
  simulable : ∃ g : List Bool → List Bool, CookPvsNP.PolyTimeComputable g ∧
    ∀ (β L w z : List Bool) (s : ℕ),
      g (QuantumPRC.tupleCode [β, L, w.take s, z, QuantumPRC.unary s]) =
        resultCode (run β L w z s)

end OWFLocalDesc


