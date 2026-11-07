-- Prove2me | Definitions.Def_LiftSAParity_IsOneStifling
-- name    : LiftSAParity_IsOneStifling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:33.545445+00:00
-- url     : https://prove2.me/theorems/66c8fc05-bf2c-4c8e-a80f-fc4eb0531496
-- title:
--   1-stifling gadget
-- statement:
--   A gadget $g:\{0,1\}^\ell\to\{0,1\}$ is **1-stifling** if, for every coordinate $j\in[\ell]$ and every $b\in\{0,1\}$, the other coordinates can be fixed so that $g$ evaluates to $b$ regardless of the value of coordinate $j$: there is $w\in\{0,1\}^\ell$ with $g(w[j\mapsto c])=b$ for both $c\in\{0,1\}$.
--
--   For example $\mathrm{MAJ}_3$ is 1-stifling. No gadget on a single bit is.
--
--   **Formalization Note** Coordinates are `Fin ℓ` and bits are `Bool`; the value of $w$ at $j$ is irrelevant.
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §1.1, p.4

import Mathlib

namespace LiftSAParity

/-- **1-stifling gadget** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary
Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), §1.1, p.4): "A gadget
g: {0, 1}^ℓ → {0, 1} is 1-stifling if, for every coordinate j ∈ [ℓ] and every b ∈ {0, 1}, the
other coordinates can be fixed so that g evaluates to b regardless of the value of coordinate j."

**Formalization Note** Coordinates are `Fin ℓ`, bits are `Bool`. "The other coordinates can be
fixed" is an input `w`; "regardless of the value of coordinate j" is `g (update w j c) = b` for both
`c`, so the value of `w` at `j` is irrelevant. -/
def IsOneStifling {ℓ : ℕ} (g : (Fin ℓ → Bool) → Bool) : Prop :=
  ∀ (j : Fin ℓ) (b : Bool), ∃ w : Fin ℓ → Bool, ∀ c : Bool, g (Function.update w j c) = b

end LiftSAParity


