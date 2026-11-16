-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_Gate
-- name    : DoublyEffIP_Supplement_Gate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:24:30.6708+00:00
-- url     : https://prove2.me/theorems/161ff81d-a36b-4d38-b1bb-edbecf45ccff
-- title:
--   A gate of an arithmetic circuit
-- statement:
--   A **gate** of an arithmetic circuit is one of: a fan-in-2 addition $\mathrm{ADD}(i,j)$ or multiplication $\mathrm{MULT}(i,j)$ of the values on wires $i$ and $j$; a constant $0$ or $1$; or the generator $\alpha$ of the field presentation $\mathbb F=\mathbb F_p[X]/(f)$ (the class of $X$).
--
--   Wires are numbered with the inputs first and then the gates in order, so a gate refers to inputs and earlier gates. These are the fan-in-2 ADD and MULT gates of the paper's arithmetic circuits, with the constant sources an implementation circuit needs (the trivial predicate $\top$ outputs the constant $1$).
--
--   **Formalization Note** The constants $0$, $1$ and $\alpha$ are fan-in-0 sources; with them every element of $\mathbb F$ can be built by ADD and MULT gates.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9, Definition 3 (gates of arithmetic circuits)

import Mathlib

set_option autoImplicit false

namespace DoublyEffIP.Supplement

/-- **A gate of an arithmetic circuit** — the "fan-in 2 ADD and MULT gates over a field F" of
Definition 3 (Uniform Arithmetic Circuits) of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9.

A gate is a fan-in-2 addition `add i j` or multiplication `mul i j` of the values on wires `i`
and `j`, a constant `const b` (`0` or `1`), or `gen`, the generator `α` of the field presentation
(`F = F_p[X]/(f)`, `α` the class of `X`).

**Formalization Note.** Wires are numbered: the inputs first, then the gates in order, so `i`, `j`
refer to an input or an earlier gate. The constants `0`, `1` and the field generator `α` are
fan-in-0 sources; with them, every element of `F` is computed by `add`/`mul` gates, so the circuits
of Definition 3 (which name no constants) together with the constants an implementation circuit
uses (e.g. the trivial predicate `⊤`, which outputs `1`) are all expressible. -/
inductive Gate where
  /-- the sum of the values on wires `i` and `j` -/
  | add (i j : ℕ)
  /-- the product of the values on wires `i` and `j` -/
  | mul (i j : ℕ)
  /-- the constant `1` (`b = true`) or `0` (`b = false`) -/
  | const (b : Bool)
  /-- the generator `α` of the field presentation -/
  | gen

end DoublyEffIP.Supplement


