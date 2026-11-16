-- Prove2me | Definitions.Def_StochAutoreg_Supplement_tailBits
-- name    : StochAutoreg_Supplement_tailBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:17:42.89061+00:00
-- url     : https://prove2.me/theorems/a39a663a-e059-46bb-ab3f-b565b839d301
-- title:
--   Window $\mathrm{tail}_d(s)\in\{0,1\}^d$: the last $d$ bits, left-padded with zeros
-- statement:
--   For a string $s\in\{0,1\}^\star$ and $d\in\mathbb N$, $\mathrm{tail}_d(s)\in\{0,1\}^d$ is the string of the last $d$ bits of $s$, padded by zeros on the left if $|s|<d$. For example $\mathrm{tail}_3(1)=001$ and $\mathrm{tail}_2(101)=01$.
--
--   The window is the input of the logistic rule of Eq. (1.2): a logistic generator of memory $d$ looks only at the last $d$ tokens of its state.
--
--   **Formalization Note** Strings are lists of booleans, oldest token first; the window is again oldest first, so its last entry is the newest bit of $s$, and it always has length $d$.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §1.2, p.5 (before Eq. (1.2))

import Mathlib

namespace StochAutoreg

namespace Supplement

/-- The **window** `tail_d(s) ∈ {0,1}^d`: the last `d` bits of `s`, padded by zeros on the left if
`|s| < d`. Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §1.2,
p.5 (before Eq. (1.2)).

**Formalization Note.** A string is a `List Bool`, oldest token first, so the result is again oldest
first and its last entry is the newest bit of `s`. The result always has length `d`. -/
def tailBits (d : ℕ) (s : List Bool) : List Bool :=
  List.replicate (d - s.length) false ++ s.drop (s.length - d)

end Supplement

end StochAutoreg


