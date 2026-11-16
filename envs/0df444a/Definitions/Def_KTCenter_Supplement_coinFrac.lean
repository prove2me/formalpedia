-- Prove2me | Definitions.Def_KTCenter_Supplement_coinFrac
-- name    : KTCenter_Supplement_coinFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:06:37.149918+00:00
-- url     : https://prove2.me/theorems/1046bf28-ce54-4e92-bd12-488e0f8727fe
-- title:
--   Randomized machines on fair coin strings, and the success probability $\mathrm{coinFrac}$
-- statement:
--   A **randomized algorithm** in the sense of Theorems 5.1 and 5.13 is a deterministic machine that reads, besides its input $a$, a string $b\in\{0,1\}^N$ of fair coins. Its tape word is
--
--   $$\mathrm{encPair}(a,b)=b_1\cdots b_N\;\mathtt 3\;\mathrm{enc}(a),$$
--
--   the coin bits written as the symbols $0,1$, the separator symbol $3$, and the binary encoding of the input. For a coin length $N$, an input $a$ and an event $E$ on outputs, the **success probability**
--
--   $$\mathrm{coinFrac}(\mathrm{alg},N,a,E)=\frac{\#\{b\in\{0,1\}^N:\ E(\mathrm{alg}(a,b))\}}{2^N}$$
--
--   is the exact probability that the output satisfies $E$ when the $N$ coins are independent and fair.
--
--   These two objects express "with probability at least 4/5" and "runs in time … on every execution" for the randomized algorithms of the paper, whose draws are implemented with fair bits (Remark 5.14).
--
--   **Formalization Note** The coin bits never contain the symbol $3$, so the first $3$ ends the coin string and $\mathrm{encPair}$ is injective whenever the input encoding is (checked in a local sanity file). The coin length is not part of this definition: each theorem fixes it as a polynomial in the input length.
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Theorem 5.1, p.22 (PDF p.24); Theorem 5.13, p.53 (PDF p.55); Remark 5.14, p.55 (PDF p.57)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit

namespace KTCenter.Supplement

open OnlineCRS.Combine

/-- **Input of a randomized machine: coin string and instance**, for the randomized algorithms of
Theorem 5.1 (p.22, PDF p.24) and Theorem 5.13 (p.53, PDF p.55).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…); Remark 5.14, p.55 (PDF p.57): draws are implemented "using a fixed number of fair
bits per draw".

`encPair enc (a, b)` writes the coin string `b` as the bits `0`/`1`, then the separator `3`, then
the encoding `enc a` of the instance.

**Formalization Note.** A randomized algorithm is a deterministic Mathlib TM2 machine reading this
word. Coins never contain the symbol `3`, so the first `3` ends the coin string and `encPair enc` is
injective whenever `enc` is. -/
def encPair {α : Type} (enc : α → List Sym) (x : α × List Bool) : List Sym :=
  x.2.map bit ++ [3] ++ enc x.1

open Classical in
/-- **Success probability over fair coins**, for "with probability at least 4/5" in Theorems 5.1
(p.22, PDF p.24) and 5.13 (p.53, PDF p.55).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…); Remark 5.14, p.55 (PDF p.57).

`coinFrac alg N a E` is the fraction of the `2^N` coin strings `b ∈ {0,1}^N` for which the output
`alg (a, b)` satisfies `E`: the exact probability of `E` when the `N` coins are fair and independent.

**Formalization Note.** The coin length `N` is supplied by the theorem (a polynomial in the input
length), so the probability is over uniformly random strings of that length, on input `a`. The
probability of the paper already includes the loss of the finite-bit implementation of Remark 5.14
(p.54: "16/20 = 4/5"). -/
noncomputable def coinFrac {α β : Type} (alg : α × List Bool → β) (N : ℕ) (a : α) (E : β → Prop) :
    ℚ :=
  ((Finset.univ.filter fun b : Fin N → Bool => E (alg (a, List.ofFn b))).card : ℚ) / 2 ^ N

end KTCenter.Supplement


