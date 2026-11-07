-- Prove2me | Definitions.Def_KTCenter_encInstance
-- name    : KTCenter_encInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:30.990856+00:00
-- url     : https://prove2.me/theorems/d47c946a-f6e9-4d0d-b3d9-9687823144d1
-- title:
--   Binary encodings of an input list and of an output ranking
-- statement:
--   To speak about running time, an input $\Pi=(\pi_1,\dots,\pi_n)$ is written as a word over a four-letter alphabet $\{0,1,2,3\}$: the numbers $n$ and $d$, followed, for each input $i$ and each position $j$, by the (1-based) candidate $\pi_i(j)$ at that position, all written in binary and separated by the symbol $3$. An output ranking $\sigma$ is its one-line form $(\sigma(1),\dots,\sigma(d))$, also as binary numbers separated by $3$.
--
--   The length of the encoding of an input lies between $nd$ and a polynomial in $nd$, so a running time polynomial in the encoding length is a running time polynomial in $nd$.
--
--   **Formalization Note** The paper names no machine model; it counts in "total binary encoding length" (Theorems 5.13 and 6.1). The mission reads "algorithm" and "time" in Mathlib's `Turing.TM2ComputableInPolyTime`, with the published alphabet `OnlineCRS.Combine.Sym` and binary numbers `OnlineCRS.Combine.encNat`.
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Theorem 1.1, p.2 (PDF p.4), and §3, p.13 (PDF p.15); encoding chosen by the mission (paper names no machine)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_KTCenter_Instance

namespace KTCenter

open OnlineCRS.Combine

/-- **Encoding of an input for the time bound of Theorem 1.1**, p.2 (PDF p.4).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** Reading: the paper names no machine, and counts "in the total binary
encoding length" (Theorems 5.13 and 6.1). Lean uses Mathlib's `Turing.TM2ComputableInPolyTime` over
the alphabet `OnlineCRS.Combine.Sym`. The layout is `n`, `d`, then for each input `i` and each
position `j` the 1-based candidate at that position, all in binary, separated by the symbol `3`. -/
def encInstance (I : Instance) : List Sym :=
  [3].intercalate
    ([encNat I.n, encNat I.d] ++
      (List.ofFn fun i : Fin I.n =>
        List.ofFn fun j : Fin I.d => encNat (((I.π i j : Fin I.d) : ℕ) + 1)).flatten)

/-- **One-line form of a ranking**, p.13: position `j` carries the 1-based candidate `σ j`. -/
def rankingList {d : ℕ} (σ : Equiv.Perm (Fin d)) : List ℕ :=
  List.ofFn fun j : Fin d => ((σ j : Fin d) : ℕ) + 1

/-- **Encoding of an output list**: the numbers in binary, separated by the symbol `3`. -/
def encRanking (l : List ℕ) : List Sym :=
  [3].intercalate (l.map encNat)

end KTCenter


