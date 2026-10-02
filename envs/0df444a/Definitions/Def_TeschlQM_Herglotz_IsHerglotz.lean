-- Prove2me | Definitions.Def_TeschlQM_Herglotz_IsHerglotz
-- name    : TeschlQM_Herglotz_IsHerglotz
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:32:34.113927+00:00
-- url     : https://prove2.me/theorems/9a15da93-ee5b-49f4-8082-03390a733ccc
-- title:
--   Herglotz function: a holomorphic map of the upper half plane into itself
-- statement:
--   Let $\mathbb{C}_+ = \{z \in \mathbb{C} \mid \operatorname{Im}(z) > 0\}$ be the open upper half plane. A function $F$ is a **Herglotz function** (also called a **Nevanlinna function**) if it is holomorphic on $\mathbb{C}_+$ and maps $\mathbb{C}_+$ into itself:
--   $$F \text{ holomorphic on } \mathbb{C}_+, \qquad \operatorname{Im} F(z) > 0 \quad \text{for all } z \in \mathbb{C}_+ .$$
--   Herglotz functions are the analytic side of the correspondence with finite Borel measures on $\mathbb{R}$ developed in this mission; the resolvent quadratic forms $\langle \psi, R_A(z)\psi\rangle$ of a self-adjoint operator are the motivating examples.
--
--   **Formalization Note.** $F$ is a function `ℂ → ℂ`; only its values on $\mathbb{C}_+$ are constrained (holomorphy is `DifferentiableOn ℂ F {z | 0 < z.im}`). "Into itself" is read with the open half plane, $\operatorname{Im} F > 0$, exactly as the book writes $F : \mathbb{C}_+ \to \mathbb{C}_+$; in particular the constant function $0$ is not a Herglotz function. The definition is analytic and does not mention measures.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 106, Section 3.4 (also p. 94)

import Mathlib

namespace TeschlQM.Herglotz

/-- Teschl, p. 106, Sec. 3.4 (also p. 94, after (3.41)): with `ℂ₊ = {z ∈ ℂ | Im(z) > 0}`, a
**Herglotz function** is a holomorphic function `F : ℂ₊ → ℂ₊` mapping the upper half plane to
itself. `F` is given on all of `ℂ`; only its values on `ℂ₊` matter. "Into itself" is the open
half plane: `Im F(z) > 0` for every `z ∈ ℂ₊`. -/
def IsHerglotz (F : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ F {z : ℂ | 0 < z.im} ∧ ∀ z : ℂ, 0 < z.im → 0 < (F z).im

end TeschlQM.Herglotz


