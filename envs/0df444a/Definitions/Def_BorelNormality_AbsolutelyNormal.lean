-- Prove2me | Definitions.Def_BorelNormality_AbsolutelyNormal
-- name    : BorelNormality_AbsolutelyNormal
-- status  : Definition
-- author  : @LG
-- created : 2026-11-18T17:08:29.9552+00:00
-- url     : https://prove2.me/theorems/9cc7e3dd-8693-47b8-b326-69fe1ba0caee
-- title:
--   Absolutely normal real numbers
-- statement:
--   A real number $x$ is **absolutely normal** if it is normal in every integer base $b \ge 2$: for each such base, every finite block of $k$ base-$b$ digits occurs in the base-$b$ expansion of $x$ with limiting frequency $b^{-k}$.
--
--   This is the notion of normality appearing in Borel's conjecture on irrational algebraic numbers, and the standard notion of a normal number in the literature (Borel 1950; Becher, *Normal numbers and computer science*, Definition 1). It is reusable by any mission on normality.
--
--   **Formalization Note.** The definition wraps `Normal.IsNormalReal` from the platform definition file `Normal_Core`; digits are those of the fractional part of $x$, in the canonical expansion that does not end in an infinite tail of $b-1$.
-- source:
--   É. Borel, Sur les chiffres décimaux de √2 et divers problèmes de probabilités en chaîne, C. R. Acad. Sci. Paris 230 (1950), 591–593; V. Becher, Normal numbers and computer science (MPRI chapter), Definition 1, https://www.irif.fr/~carton/Enseignement/MPRI/Dynam-symbol/Documents/chapter.pdf ; https://en.wikipedia.org/wiki/Normal_number

import Mathlib
import Definitions.Def_Normal_Core

set_option autoImplicit false

namespace BorelNormality

/-- A real number is **absolutely normal** if it is normal in every integer base `b ≥ 2`. -/
def AbsolutelyNormal (x : ℝ) : Prop :=
  ∀ b : ℕ, 2 ≤ b → Normal.IsNormalReal b x

end BorelNormality


