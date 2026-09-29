-- Prove2me | Definitions.Def_FoundationsML_MaxEnt_MaxEntPrimalObjective
-- name    : FoundationsML_MaxEnt_MaxEntPrimalObjective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:14:18.851986+00:00
-- url     : https://prove2.me/theorems/859d7c88-592e-44cf-b86f-6ccd98add886
-- title:
--   Maxent primal objective F (Eq. 12.8)
-- statement:
--   **Eq. (12.8), p. 300, PDF p. 317.** $F(p) = \tilde D(p\|p_0) + I_C(E_p[\Phi])$, where
--   $\tilde D(p\|p_0)=D(p\|p_0)$ if $p\in\Delta$, $+\infty$ otherwise, and $I_C(u)=0$ if $u\in C$,
--   $+\infty$ otherwise.
--
--   **Formalization Note.** Uses `EReal` so the book's own `+∞` values are represented exactly,
--   not replaced by a large real sentinel.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 300, Eq. (12.8) (PDF p. 317)

import Mathlib
import Definitions.Def_FoundationsML_MaxEnt_RelativeEntropy
import Definitions.Def_FoundationsML_MaxEnt_Simplex
import Definitions.Def_FoundationsML_MaxEnt_FeatureConstraintSet

namespace FoundationsML.MaxEnt

open Classical in
/-- The Maxent primal objective `F` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Eq. (12.8), p. 300, PDF p. 317), for `p : X → ℝ` over a
finite set `X`: `F(p) = D̃(p‖p0) + I_C(E_p[Φ])`, where `D̃(p‖p0) = D(p‖p0)` if `p ∈ Δ` and `+∞`
otherwise, and `I_C(u) = 0` if `u ∈ C`, `+∞` otherwise.

**Formalization Note.** `EReal` (the extended reals) is used so that the indicator-function
values `+∞` the book's own `I_K` and `D̃` explicitly assign are represented exactly, rather than
silently replaced by a large real sentinel. `E_p[Φ]`, the vector `fun j => ∑_x p(x)Φ(x)_j`, is
written out inline rather than named separately, since it is used nowhere else in this chunk. -/
noncomputable def MaxEntPrimalObjective {X : Type*} [Fintype X] {N m : ℕ}
    (p0 : X → ℝ) (Φ : X → Fin N → ℝ) (S : Fin m → X) (lam : ℝ) (p : X → ℝ) : EReal :=
  (if p ∈ Simplex X then (RelativeEntropy p p0 : EReal) else ⊤) +
    (if (fun j => ∑ x, p x * Φ x j) ∈ FeatureConstraintSet Φ S lam then (0 : EReal) else ⊤)

end FoundationsML.MaxEnt


