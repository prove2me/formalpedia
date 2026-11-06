-- Prove2me | Definitions.Def_ConstrSOSP_MCode
-- name    : ConstrSOSP_MCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:54.153297+00:00
-- url     : https://prove2.me/theorems/46be45e7-0560-4b03-a61e-141b53eabdac
-- title:
--   Turing machine description
-- statement:
--   The white-box model supplies "the description of a polynomial-time Turing machine". A **machine description** consists of finitely many tape symbols and states, a start, an accepting and a distinct rejecting state, two distinct symbols used to write the bits $0$ and $1$, and a transition table. It describes a one-tape machine in the sense of the public `CookPvsNP.TM`.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace ConstrSOSP

/-- **A Turing machine description** (arXiv:2604.02285, 2 Nov 2026, §4.1, p.17: "we are given the
description of a polynomial-time Turing machine C_f that computes f(x), ∇f(x) and ∇²f(x)").

A one-tape machine in the sense of the public `CookPvsNP.TM`, given by finite data: `g` non-blank
tape symbols `Fin g`, `q` states `Fin q`, the start, accepting and rejecting states (the latter two
distinct), two distinct symbols `i0`, `i1` that write the bits `false`, `true` of inputs and
outputs, and the transition table `δ`.

**Formalization Note** The binary code of such a description is `encMCode`; `MCode.toTM` is the
machine it describes. -/
structure MCode where
  g : ℕ
  q : ℕ
  q₀ : Fin q
  qa : Fin q
  qr : Fin q
  hne : qa ≠ qr
  i0 : Fin g
  i1 : Fin g
  hi : i0 ≠ i1
  δ : Fin q → Option (Fin g) → Fin q × Option (Fin g) × CookPvsNP.Move

end ConstrSOSP


