-- Prove2me | Definitions.Def_MantriCVQ_Protocol53
-- name    : MantriCVQ_Protocol53
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:27.728428+00:00
-- url     : https://prove2.me/theorems/44895c32-3aba-463f-9009-0c4cb503cf37
-- title:
--   Protocol 5.3: verification batched by height
-- statement:
--   Protocol 5.3 keeps an ordered list of claims $(w,b)$ about nodes of one height. In one height, the prover sends one $m$-bit secret per entry in one message, the verifier sends three fresh uniform $m$-bit strings per entry in one message, and each entry $(w',b')$ with secret $s$ and challenges $x_1,x_2,x_3$ is replaced by the four claims
--   $$(w'0x_1,C_m(s,x_1)),\ (w'0x_2,C_m(s,x_2)),\ (w'0x_3,C_m(s,x_3)),\ (w'1s,b'),$$
--   in this order. At the leaves the verifier accepts iff every claim matches the leaf table. This module gives the list update, the acceptance probability from a list and a history against a strategy, and the list after a whole transcript.
--
--   **Formalization Note** Strategies are typed by the prescribed message length, so a malformed message, which the protocol rejects, cannot occur.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Protocol 5.3, pp. 20–21 (PDF pp. 22–23)

import Mathlib
import Definitions.Def_MantriCVQ_Strategy

open QAlgorithms.Complexity

namespace MantriCVQ

/-- The first `m` bits of a string, as a bit vector. -/
def strBits (m : ℕ) (s : Str) : Bits m := fun i => s.getD i false

/-- The list update of Protocol 5.3 at nodes of dimension `m` (Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), Protocol 5.3, step 3, pp. 20–21 (PDF pp. 22–23)): the secrets are read off the
prover's message and the triples off the verifier's, in list order, and each entry `(w, b)` with
secret `s` and challenges `x₁, x₂, x₃` becomes the four claims
`(w0x₁, C(s, x₁)), (w0x₂, C(s, x₂)), (w0x₃, C(s, x₃)), (w1s, b)`, in this order. -/
def nextList (C : (m : ℕ) → Bits m → Bits m → Bool) (m : ℕ) :
    List (Str × Bool) → Str → Str → List (Str × Bool)
  | [], _, _ => []
  | e :: L, msg, ch =>
    let s := msg.take m
    let x₁ := ch.take m
    let x₂ := (ch.drop m).take m
    let x₃ := (ch.drop (2 * m)).take m
    (e.1 ++ false :: x₁, C m (strBits m s) (strBits m x₁)) ::
    (e.1 ++ false :: x₂, C m (strBits m s) (strBits m x₂)) ::
    (e.1 ++ false :: x₃, C m (strBits m s) (strBits m x₃)) ::
    (e.1 ++ true :: s, e.2) ::
    nextList C m L (msg.drop m) (ch.drop (3 * m))

/-- The acceptance probability of Protocol 5.3 continued from the list `L` (Protocol 5.3, pp. 20–21),
when the current nodes have the listed dimensions from the top down, the leaf table is `Y`, and the
prover plays `σ` after the history `hist`. At each height the prover sends one `m`-bit secret per entry
in one message, the verifier then sends three fresh uniform `m`-bit strings per entry in one message,
and at the leaves the verifier accepts iff every claim matches the leaf table.

**Formalization Note** The strategy is typed by the prescribed message length, so a malformed message
cannot occur (the protocol rejects it). `w` is the input passed to the strategy. -/
noncomputable def accept53 (C : (m : ℕ) → Bits m → Bits m → Bool) (Y : Str → Bool) (σ : Strategy)
    (w : Str) : List ℕ → List Str → List (Str × Bool) → ℝ
  | [], _, L => by
    classical exact if ∀ e ∈ L, Y e.1 = e.2 then 1 else 0
  | m :: ms, hist, L =>
    ∑ msg : Bits (L.length * m), (σ w hist _ msg).toReal *
      ∑ ch : Bits (3 * (L.length * m)), ((2 : ℝ) ^ (3 * (L.length * m)))⁻¹ *
        accept53 C Y σ w ms (hist ++ [List.ofFn msg, List.ofFn ch])
          (nextList C m L (List.ofFn msg) (List.ofFn ch))

/-- The list after a whole transcript of Protocol 5.3: alternately a prover message and a verifier
message at each height. -/
def runList (C : (m : ℕ) → Bits m → Bits m → Bool) :
    List ℕ → List (Str × Bool) → List Str → List (Str × Bool)
  | m :: ms, L, msg :: ch :: tr => runList C ms (nextList C m L msg ch) tr
  | _, L, _ => L

end MantriCVQ


