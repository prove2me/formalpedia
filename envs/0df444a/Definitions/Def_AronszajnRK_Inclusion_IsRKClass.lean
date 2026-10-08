-- Prove2me | Definitions.Def_AronszajnRK_Inclusion_IsRKClass
-- name    : AronszajnRK_Inclusion_IsRKClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:07:49.997735+00:00
-- url     : https://prove2.me/theorems/b26e08f4-f785-4fde-810f-46ea0966e6ea
-- title:
--   (R.K.)-class: a class of functions admitting a Hilbert norm with a reproducing kernel
-- statement:
--   Let $E$ be a set. A class $F$ of complex functions defined everywhere on $E$ is an **(R.K.)-class** if a norm can be defined on $F$ giving $F$ the structure of a complex Hilbert space with a reproducing kernel; equivalently, $F$ is the set of functions of some reproducing kernel Hilbert space on $E$.
--
--   Such a class is automatically linear. An (R.K.)-class carries infinitely many admissible norms (all equivalent, by Corollary IV₁ of §13), and correspondingly infinitely many reproducing kernels.
--
--   **Formalization Note** The witnessing Hilbert space is taken in the same universe as $E$. This is no restriction: every reproducing kernel Hilbert space on $E$ is isometric to one carried by its own set of functions, which lives in that universe.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 380, §13 (A)

import Mathlib

universe u

namespace AronszajnRK.Inclusion

/-- An **(R.K.)-class** (Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68
(1950), §13 (A), p. 380, PDF p. 44): a class `S` of functions `X → ℂ` on which a norm can be defined
giving `S` the structure of a (complex) Hilbert space with a reproducing kernel, i.e. `S` is the set
of functions of some RKHS `H`. The witness `H` is taken in the universe of `X`; this loses nothing,
since every RKHS on `X` is isometric to one carried by its own set of functions, a type in that
universe. Linearity of `S` is a consequence. -/
def IsRKClass {X : Type u} (S : Set (X → ℂ)) : Prop :=
  ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (_ : RKHS ℂ H X ℂ), Set.range (fun f : H => (f : X → ℂ)) = S

end AronszajnRK.Inclusion


