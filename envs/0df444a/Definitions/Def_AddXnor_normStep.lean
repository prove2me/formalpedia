-- Prove2me | Definitions.Def_AddXnor_normStep
-- name    : AddXnor_normStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:37.493935+00:00
-- url     : https://prove2.me/theorems/7b281cc5-8fbd-441b-aa31-45e4914f024f
-- title:
--   Normalized state $Y$ and the normalized update (3)
-- statement:
--   Let $E$ be the current value of a left-associative Add/XNOR computation on $m$-bit words and $\varepsilon \in \{0,1\}$ the parity of the number of XNORs performed so far. The **normalized state** is
--   $$
--   Y = \begin{cases} E, & \varepsilon = 0,\\ \overline{E}, & \varepsilon = 1,\end{cases}
--   $$
--   where $\overline{E} = E \oplus (2^m-1)$ is the bitwise complement. The **normalized update** with operand $a$ is
--   $$
--   (Y, \varepsilon) \longmapsto \begin{cases} (Y + (-1)^{\varepsilon} a \bmod 2^m,\ \varepsilon), & \text{for } +,\\ (Y \oplus a,\ \varepsilon \oplus 1), & \text{for } \odot,\end{cases}
--   $$
--   and iterating it over a sequence of operator–operand pairs from left to right gives the normalized run.
--
--   Normalization turns the chain into a sequence of additions, subtractions and XORs on $Y$, which makes the effect of each operand on the low bits of $Y$ explicit.
--
--   **Formalization Note** The parity $\varepsilon$ is a Boolean (`true` = odd). `normStep o (Y, ε) a` is the update with operator bit `o` (`true` = XNOR), and `normRun` folds it over a list.
-- source:
--   Wang, Lv, Shen, Zhang, Add/XNOR Chains: An NP-Complete Boolean–Arithmetic Problem at the Meet-in-the-Middle Barrier, manuscript (sha256 405d6dda…), Lemma 2, equation (3), p.6 (PDF p.6)

import Mathlib

namespace AddXnor

/-- The normalized state `Y` of Lemma 2 (Wang, Lv, Shen, Zhang, manuscript, sha256 405d6dda…,
Lemma 2, p.6 (PDF p.6)): `Y = E` if the XNOR parity `ε` is `0`, and `Y = Ē` (the bitwise
complement on `m` bits) if `ε = 1`.

**Formalization Note** The parity `ε` is a `Bool` (`true` = odd number of XNORs so far). -/
def normY {m : ℕ} (ε : Bool) (E : BitVec m) : BitVec m :=
  if ε then ~~~E else E

/-- The normalized update (3) of Lemma 2 (Wang, Lv, Shen, Zhang, manuscript, sha256 405d6dda…,
p.6 (PDF p.6)): on operand `a`,
`(Y, ε) ↦ (Y + (−1)^ε a mod 2^m, ε)` for `+` (`o = false`), and `(Y ⊕ a, ε ⊕ 1)` for `⊙`
(`o = true`). -/
def normStep {m : ℕ} (o : Bool) (q : BitVec m × Bool) (a : BitVec m) : BitVec m × Bool :=
  if o then (q.1 ^^^ a, !q.2) else ((if q.2 then q.1 - a else q.1 + a), q.2)

/-- Iterating the normalized update (3) over a list of (operator, operand) pairs, from left to
right, starting at `q₀` (used for the four-bit guard of Lemma 5, p.9 (PDF p.9)). -/
def normRun {m : ℕ} (q₀ : BitVec m × Bool) (l : List (Bool × BitVec m)) : BitVec m × Bool :=
  l.foldl (fun q p => normStep p.1 q p.2) q₀

end AddXnor


