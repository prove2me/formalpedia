-- Prove2me | Definitions.Def_GyoriLovasz_encInstance
-- name    : GyoriLovasz_encInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:50:45.968295+00:00
-- url     : https://prove2.me/theorems/556f654d-db4b-4bff-9086-2e509fdbb295
-- title:
--   Tape encodings of inputs and outputs
-- statement:
--   Inputs and outputs are written over the four-symbol alphabet $\{0,1,2,3\}$. A number is written in binary followed by the separator $3$. An input is written as $n$, the number of edges, the endpoints of each edge, and then each terminal with its capacity, all as numbers. An output (a list of labels) is the sequence of its numbers.
--
--   **Formalization Note** Every word ends with $3$, because the binary word of $0$ is empty; this makes both encodings injective (proved in the mission's sanity file). On valid inputs the input length is polynomially related to $n+m+k$, since then every non-terminal has an outgoing edge.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Theorem 1, p.5 ("polynomial-time algorithm")

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_GyoriLovasz_Instance

namespace GyoriLovasz

open OnlineCRS.Combine

/-- A number as a tape word: its binary digits followed by the separator symbol `3`. The separator ends every
word, because `Computability.encodeNat 0 = []`. -/
def encNum (x : ℕ) : List Sym := encNat x ++ [3]

/-- A list of pairs of numbers, as consecutive words. -/
def encPairs (l : List (ℕ × ℕ)) : List Sym := l.flatMap fun e => encNum e.1 ++ encNum e.2

/-- **The input encoding.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Theorem 1, p.5 ("polynomial-time"): the words `n`, `|edges|`, the pairs of `edges`, the
pairs of `terms`, with numbers in binary.

**Formalization Note.** The encoding is fixed and injective (`Mathlib`'s machines take a bare function, so injectivity
is a real requirement; it is proved in `Solutions/verification/GyoriLovasz_sanity.lean`). The input length is
polynomially related to `n + m + k` on valid inputs, since then each non-terminal has an outgoing edge. -/
def encInstance (I : Instance) : List Sym :=
  encNum I.n ++ encNum I.edges.length ++ encPairs I.edges ++ encPairs I.terms

/-- **The output encoding**: each label's binary word in turn. Also injective (same file). -/
def encLabels (L : List ℕ) : List Sym := L.flatMap encNum

end GyoriLovasz


