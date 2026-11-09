-- Prove2me | Definitions.Def_OracleStateHSP_IsSimonFn
-- name    : OracleStateHSP_IsSimonFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:29:36.884051+00:00
-- url     : https://prove2.me/theorems/aa9b4a08-9106-4cb1-8f28-19140ac22e68
-- title:
--   Simon function hiding the period $s$ (eq. (51))
-- statement:
--   A function $f : \mathbb Z_2^m \to \mathbb Z_2^m$ **hides the period** $s$ if
--   $$
--   f(x) = f(y) \iff x + y \in \{0, s\} \qquad \text{for all } x, y .
--   $$
--   The period $s = 0$ means that $f$ is a bijection; for $s \ne 0$, $f$ is two-to-one.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, eq. (51), p.36

import Mathlib
import Definitions.Def_OracleStateHSP_V

namespace OracleStateHSP

/-- `f : Z_2^m → Z_2^m` is a Simon function hiding the period `s` (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, eq. (51), p.36):
`f(x) = f(y) ⟺ x + y ∈ {0, s}` for all `x, y`. Period `s = 0` means that `f` is a bijection. -/
def IsSimonFn {m : ℕ} (f : V m → V m) (s : V m) : Prop :=
  ∀ x y, f x = f y ↔ (x + y = 0 ∨ x + y = s)

instance {m : ℕ} (f : V m → V m) (s : V m) : Decidable (IsSimonFn f s) := by
  unfold IsSimonFn; infer_instance

end OracleStateHSP


