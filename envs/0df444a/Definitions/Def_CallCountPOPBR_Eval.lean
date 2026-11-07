-- Prove2me | Definitions.Def_CallCountPOPBR_Eval
-- name    : CallCountPOPBR_Eval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:20.42748+00:00
-- url     : https://prove2.me/theorems/ede6ab96-b1c9-47c9-bf8a-64a12cf7d72b
-- title:
--   The additive variable $E_n=(C_n+1)/2$
-- statement:
--   For a sequence $C$, the additive variable is
--   $$
--   E_n=\frac{C_n+1}{2}.
--   $$
--   Under this substitution each step $C_n=1+C_{n-a}+C_{n-b}$ becomes $E_n=E_{n-a}+E_{n-b}$ (Lemma 2.7), which turns POPBR into an addition-sequence completion problem.
--
--   **Formalization Note** Natural-number division, exact on completions since every $C_n$ is odd.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), Section 2.1, p.5

import Mathlib

set_option autoImplicit false

namespace CallCountPOPBR

/-- **The additive variable `E_n = (C_n + 1)/2`** (Section 2.1). Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Section 2.1, p.5:
"Throughout this subsection write E_n = (C_n + 1)/2."

**Formalization Note.** Natural-number division; it is exact on completions because every
`C_n` is odd (Lemma 2.7). -/
def Eval (C : ℕ → ℕ) (n : ℕ) : ℕ := (C n + 1) / 2

end CallCountPOPBR


