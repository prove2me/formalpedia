-- Prove2me | Definitions.Def_BartlettBousquetMendelson_LocalRad_IsSubRoot
-- name    : BartlettBousquetMendelson_LocalRad_IsSubRoot
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:57:47.688859+00:00
-- url     : https://prove2.me/theorems/170d9fbe-6cea-43b9-b132-c6db0cd8705f
-- title:
--   Sub-root function
-- statement:
--   A function $\psi:[0,\infty)\to[0,\infty)$ is **sub-root** if it is nonnegative, nondecreasing, and
--
--   $$
--   r\mapsto\frac{\psi(r)}{\sqrt r}\quad\text{is nonincreasing for } r>0.
--   $$
--
--   Sub-root functions are the upper bounds on local Rademacher averages used by the paper; they have a unique positive fixed point (Lemma 3.2).
--
--   **Formalization Note** $\psi$ is typed $\mathbb R\to\mathbb R$; only its values on $[0,\infty)$ are constrained.
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), Definition 3.1, p. 9 (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib

namespace BartlettBousquetMendelson.LocalRad

/-- **Sub-root function.**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), Definition 3.1, p. 9: "A function ψ : [0,∞) → [0,∞) is sub-root if it is nonnegative,
nondecreasing and if r ↦ ψ(r)/√r is nonincreasing for r > 0."

`IsSubRoot ψ` says: `ψ r ≥ 0` for `r ≥ 0`, `ψ` is nondecreasing on `[0, ∞)`, and
`r ↦ ψ r / √r` is nonincreasing on `(0, ∞)`.

**Formalization Note.** `ψ` is typed `ℝ → ℝ`; only its values on `[0, ∞)` are constrained,
and its values at negative arguments never enter a statement of the mission. -/
def IsSubRoot (ψ : ℝ → ℝ) : Prop :=
  (∀ r, 0 ≤ r → 0 ≤ ψ r) ∧ MonotoneOn ψ (Set.Ici 0) ∧
    AntitoneOn (fun r => ψ r / Real.sqrt r) (Set.Ioi 0)

end BartlettBousquetMendelson.LocalRad


