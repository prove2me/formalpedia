-- Prove2me | Definitions.Def_CompNonlocal_Certificate_recEffect
-- name    : CompNonlocal_Certificate_recEffect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:36.7807+00:00
-- url     : https://prove2.me/theorems/803f9cef-67c7-4ea6-b9d5-cc4fe234df73
-- title:
--   Effect of Alice's complete measurement record
-- statement:
--   For the honest Alice circuit on question $x$, the effect $E_{x,z}$ on her input qubit of the event that measuring **every** wire of her circuit gives the complete record $z$. Her honest answer is part of $z$ ("The verifier ignores the additional bits").
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §8.1, p.35 and Lemma 11, p.36

import Mathlib
import Definitions.Def_CompNonlocal_Certificate
import Definitions.Def_CompNonlocal_ICirc_recordEffectOn
import Definitions.Def_CompNonlocal_toQubit

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The effect on Alice's input qubit of the complete measurement record of her honest circuit.
Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*,
manuscript (STOC 2027 submission, sha256 e245edd7…), §8.1, p.35 ("The receiver measures every output
register of this circuit and reports the complete record") and Lemma 11, p.36: "Let E_{x,a} be the
effect on Alice's input qubit A corresponding to the complete outcome a on question x".

**Formalization Note** The complete record is the computational-basis outcome `z` of every wire of
the honest circuit `A κ` on question `x` (the record effect `recordEffectOn` for a one-qubit input,
read on `Bool`). The honest answer contained in it is `(c.A κ).clOut z`. -/
noncomputable def Certificate.recEffect (c : Certificate) (κ : ℕ) (x : Str)
    (z : Bits (c.A κ).width) : Matrix Bool Bool ℂ :=
  toQubit ((c.A κ).recordEffectOn 1 x z)

end CompNonlocal


