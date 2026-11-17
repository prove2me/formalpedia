-- Prove2me | Definitions.Def_MatroidOptGame_Supplement_partner
-- name    : MatroidOptGame_Supplement_partner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:49:08.922128+00:00
-- url     : https://prove2.me/theorems/9a4901c5-0cd9-45c9-a859-788469a8e52e
-- title:
--   The pairing $\{2i,2i+1\}$ of $E_n$
-- statement:
--   On $E_n=\{0,1,\dots,2n-1\}$ the **partner** of an element is the other element of its pair $\{2i,2i+1\}$:
--   $$
--   \pi(2i)=2i+1,\qquad \pi(2i+1)=2i .
--   $$
--   With $S_0$ the even elements this is the pairing of the family $\mathcal M_{n,H}$ of Section 2.2.2.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2.2, p.14 and p.16

import Mathlib

namespace MatroidOptGame.Supplement

/-- The partner of an element in the pairing `{2i, 2i+1}` of `E_n = Fin (2n)`: `π(2i) = 2i + 1`
and `π(2i + 1) = 2i`.
Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2.2, p.14 ("S₀ consists of the even-indexed elements of E_n, and π matches
every pair 2i, 2i+1"); p.16 ("The partner of an element j is π(j), the other element in its
pair"). -/
def partner (n : ℕ) (i : Fin (2 * n)) : Fin (2 * n) :=
  ⟨if i.val % 2 = 0 then i.val + 1 else i.val - 1, by have := i.isLt; split_ifs <;> omega⟩

end MatroidOptGame.Supplement


