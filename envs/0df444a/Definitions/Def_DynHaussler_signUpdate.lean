-- Prove2me | Definitions.Def_DynHaussler_signUpdate
-- name    : DynHaussler_signUpdate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:46.131442+00:00
-- url     : https://prove2.me/theorems/765b1b29-d850-48d9-a8cd-cef12dd2225e
-- title:
--   Sign-update classes $V^-_x$, $V^+_x$ of Eq. (33)
-- statement:
--   For a class $V$ and an instance $x$, the two **sign-update classes** are
--   $$
--   V^-_x=\{f\in V: f(x)\le a(V,x)-\eta\},\qquad V^+_x=\{f\in V: f(x)\ge a(V,x)+\eta\},
--   $$
--   where $a(V,x)$ is the center of Eq. (32). A sign update replaces the current version space $V$ by $V^-_x$ or $V^+_x$; it is valid when the result is nonempty.
--
--   **Formalization Note** The sign is a `Bool`: `true` is $+$ (the class $V^+_x$) and `false` is $-$ (the class $V^-_x$).
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Eq. (33), p.19 (PDF p.21)

import Mathlib
import Definitions.Def_DynHaussler_center

set_option autoImplicit false

namespace DynHaussler

/-- The two **sign-update classes** of Eq. (33):
`V⁻_x = {f ∈ V : f(x) ≤ a(V, x) − η}` and `V⁺_x = {f ∈ V : f(x) ≥ a(V, x) + η}`.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Eq. (33), p.19 (PDF p.21).

**Formalization Note** The sign is a `Bool`: `true` is `+` (the class `V⁺_x`), `false` is `−`
(the class `V⁻_x`). -/
noncomputable def signUpdate {X : Type*} (η : ℝ) (V : Set (X → ℝ)) (x : X) (σ : Bool) :
    Set (X → ℝ) :=
  if σ then {f ∈ V | center η V x + η ≤ f x} else {f ∈ V | f x ≤ center η V x - η}

end DynHaussler


