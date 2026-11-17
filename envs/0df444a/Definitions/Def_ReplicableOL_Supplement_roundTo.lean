-- Prove2me | Definitions.Def_ReplicableOL_Supplement_roundTo
-- name    : ReplicableOL_Supplement_roundTo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:14:58.095362+00:00
-- url     : https://prove2.me/theorems/65709175-5188-4fda-b653-fb9fd9851826
-- title:
--   Rounding to a shifted grid $r_{G,\omega}$
-- statement:
--   For $G>0$ and $\omega\in\mathbb R$, the **rounding** of $x\in\mathbb R$ to the shifted grid $\omega+G\mathbb Z$ is
--
--   $$
--   r_{G,\omega}(x)=\omega+G\left\lfloor \frac{x-\omega}{G}+\frac12\right\rfloor ,
--   $$
--
--   the nearest point of $\omega+G\mathbb Z$ to $x$, with ties rounded up. With a uniformly random offset $\omega$ this is the dithered rounding that DALR applies at every anchor.
--
--   **Formalization Note** The floor is `Int.floor`, exactly the formula of the page.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 5.1, p.17

import Mathlib

namespace ReplicableOL.Supplement

/-- **Rounding to a shifted grid $r_{G,\omega}$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 5.1, p.17. "For G > 0 and ω ∈ ℝ let r_{G,ω}(x) := ω + G⌊(x − ω)/G + 1/2⌋ be the nearest point of ω + Gℤ to x."

**Formalization Note.** The floor is `Int.floor`, exactly the page's formula, so ties are rounded up. -/
noncomputable def roundTo (G ω x : ℝ) : ℝ := ω + G * (⌊(x - ω) / G + 1 / 2⌋ : ℝ)

end ReplicableOL.Supplement


