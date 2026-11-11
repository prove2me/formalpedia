-- Prove2me | Definitions.Def_IPEComm1531_Main_Addresses
-- name    : IPEComm1531_Main_Addresses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:26.323141+00:00
-- url     : https://prove2.me/theorems/7da4f033-56fc-4848-b57d-9deb9a1f0957
-- title:
--   The deterministic address code $\sigma\mapsto w_\sigma$ of Appendix C
-- statement:
--   For $d\ge1$, scan $\{0,1\}^{8d}$ in lexicographic order and retain a string when its Hamming distance to every previously retained string is at least $2d$, stopping after $2^d$ strings; label them $s_\sigma$ in lexicographic order of $\sigma\in\{0,1\}^d$. Then $w_\sigma\in\{0,1\}^r$ repeats $s_\sigma$ exactly $\lfloor r/(8d)\rfloor$ times and pads with zeros to length $r$.
--
--   This is the map used to shift Bob's string to $y\oplus w_\sigma$ for each address $\sigma$ in the definition of IPE.
--
--   **Formalization Note** Strings are ordered by reading them as binary numbers, most significant bit first. If the scan retained fewer than $2^d$ strings the missing ones would be the zero string; Lemma 3.4 rules this out in the relevant regime. For $d=0$ the single address gets the zero string.
-- source:
--   Haoyu Wang, Pei Wu, Efficient Randomized Communication Without Large Monochromatic Rectangles, STOC 2027 submission #1531 (October 2026), PDF sha256 b5961a61deb8c9214217a3a78e8963de31cc748f73e562aad19dd584eb9eb136, Lemma 3.4, p.8; Appendix C proof of Lemma 3.4, p.18

import Mathlib
import Definitions.Def_IPEComm1531_Main_Basic

set_option autoImplicit false

namespace IPEComm1531.Main

/-- Appendix C, proof of Lemma 3.4, step 1: scan `{0,1}^{8d}` in lexicographic order and retain
a string when its distance from every previously retained string is at least `2d`, stopping after
`2^d` strings. -/
def addressStrings (d : ℕ) : List (Bits (8 * d)) :=
  (List.range (2 ^ (8 * d))).foldl (fun kept k =>
    let v := bitsOfNat (8 * d) k
    if kept.length < 2 ^ d ∧ ∀ w ∈ kept, 2 * d ≤ distance w v
    then kept ++ [v] else kept) []

/-- Appendix C, step 2: `w_σ` repeats the `σ`-th retained string (in lexicographic order of `σ`)
exactly `⌊r/(8d)⌋` times and pads with zeros to length `r`. -/
def address (r d : ℕ) (s : Bits d) : Bits r :=
  fun i => if h : i.val < 8 * d * (r / (8 * d)) then
    ((addressStrings d)[bitsNat s]?.getD 0) ⟨i.val % (8 * d), by
      have : 0 < 8 * d := by
        rcases Nat.eq_zero_or_pos (8 * d) with h0 | h0
        · rw [h0] at h; simp at h
        · exact h0
      exact Nat.mod_lt _ this⟩
  else 0

end IPEComm1531.Main


