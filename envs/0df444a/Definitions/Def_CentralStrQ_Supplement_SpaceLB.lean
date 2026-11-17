-- Prove2me | Definitions.Def_CentralStrQ_Supplement_SpaceLB
-- name    : CentralStrQ_Supplement_SpaceLB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:22:17.075804+00:00
-- url     : https://prove2.me/theorems/bcf379bc-f64a-4868-8324-7250124a9741
-- title:
--   Stored representations of at most $s$ bits that determine every query answer
-- statement:
--   Let $\mathcal I$ be a set of inputs, $\mathcal Q$ a set of queries and $\mathrm{ans}(x,q)$ the answer to query $q$ on input $x$. A **stored representation of at most $s$ bits** is a map $E$ from $\mathcal I$ to binary strings with $|E(x)|\le s$ for every $x\in\mathcal I$, such that
--   $$E(x)=E(y)\ \Longrightarrow\ \mathrm{ans}(x,q)=\mathrm{ans}(y,q)\quad\text{for every } q\in\mathcal Q .$$
--
--   Section 5 of the paper proves lower bounds of the form "any data structure supporting these queries for every input has worst-case space usage $\Omega(f)$ bits"; its proofs use a data structure only through its stored representation, which must determine every answer.
--
--   **Formalization Note** Every data structure in any model with stored bits, in particular every word-RAM index, yields such a map with $s$ equal to its worst-case size, so a lower bound on $s$ for this notion applies to all of them.
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Section 5, pp.41–49 (pdf pp.42–50); proof of Theorem 5.4, p.42 (pdf p.43)

import Mathlib

set_option autoImplicit false

namespace CentralStrQ.Supplement

/-!
# Space usage of a data structure, information-theoretically (Section 5)

Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*,
STOC 2027 submission (manuscript sha256 dea2f74f…c96f346), Section 5, pp.41–49 (PDF pp.42–50).
Section 5 bounds the worst-case space usage of "any data structure supporting X queries for every
input" of a class. Its proofs use such a structure only through its stored representation: the
stored bits for an input determine the answer to every query (proof of Theorem 5.4, p.42: "its
stored representation uniquely determines the input sequence W"; Lemma 5.1 answers a query by
making several queries to the same stored representation).

**Formalization Note.** A data structure for the inputs `inputs` and the queries `queries`, with
answers `ans`, using at most `s` bits in the worst case, is a map `E` from inputs to bit strings of
length at most `s` such that two inputs with the same stored bits have the same answer to every
query. Every word-RAM index (`ConstTimeISA.Main.Achieves`: the query program sees only the index
cells and the query) gives such a map with `s` = the index size in bits, so a lower bound stated
for `EncodesWithin` applies to word-RAM data structures and to any other model with stored bits.
-/

/-- There is a stored representation of at most `s` bits from which every query answer is
determined: a map `E` from inputs to bit strings of length `≤ s` with `E x = E y` implying
`ans x q = ans y q` for every query `q`. -/
def EncodesWithin {I Q A : Type} (inputs : Set I) (queries : Set Q) (ans : I → Q → A)
    (s : ℕ) : Prop :=
  ∃ E : I → List Bool, (∀ x ∈ inputs, (E x).length ≤ s) ∧
    ∀ x ∈ inputs, ∀ y ∈ inputs, E x = E y → ∀ q ∈ queries, ans x q = ans y q

end CentralStrQ.Supplement


