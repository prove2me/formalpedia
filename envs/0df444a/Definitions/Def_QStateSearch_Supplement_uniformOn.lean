-- Prove2me | Definitions.Def_QStateSearch_Supplement_uniformOn
-- name    : QStateSearch_Supplement_uniformOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:28:06.71759+00:00
-- url     : https://prove2.me/theorems/95ba58aa-4196-4266-8a18-c8570a0425b4
-- title:
--   Uniform distribution on a finite set of strings
-- statement:
--   The uniform distribution on a finite set $S\subseteq\{0,1\}^n$, as a mass function: $1/|S|$ on $S$ and $0$ elsewhere. Theorem 6 uses it for $L_n$ and its complement.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Theorem 6, p.19; Lemma 4, p.17

import Mathlib

set_option autoImplicit false

namespace QStateSearch.Supplement

open Classical in
/-- The **uniform distribution** on a finite set `S ⊆ {0,1}^n`, as a probability mass function:
`x ↦ 1/|S|` for `x ∈ S`, and `0` otherwise.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Theorem 6, p.19: "the uniform distributions on L_n and its complement"; Lemma 4, p.17.

**Formalization Note.** For `S = ∅` the function is identically `0` (no distribution); the
sets it is used with, `L_n` and its complement for `n ≥ 1` in a realization, are nonempty. -/
noncomputable def uniformOn {n : ℕ} (S : Finset (Fin n → Bool)) : (Fin n → Bool) → ℝ :=
  fun x => if x ∈ S then ((S.card : ℝ))⁻¹ else 0

end QStateSearch.Supplement


