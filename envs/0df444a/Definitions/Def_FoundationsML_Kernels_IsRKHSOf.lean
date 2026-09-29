-- Prove2me | Definitions.Def_FoundationsML_Kernels_IsRKHSOf
-- name    : FoundationsML_Kernels_IsRKHSOf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T22:58:15.56712+00:00
-- url     : https://prove2.me/theorems/d96abc89-4f8c-4796-b939-f52bf4e94840
-- title:
--   Reproducing kernel Hilbert space (RKHS) of a kernel
-- statement:
--   Formalization scaffolding for Theorem 6.8's conclusion (p. 110, PDF p. 127): `H` (with
--   feature map $\Phi:X\to H$ and evaluation map giving $h(x)$ for $h\in H$) is the RKHS of $K$
--   if $K(x,x')=\langle\Phi(x),\Phi(x')\rangle$ for all $x,x'\in X$ (6.8), and the reproducing
--   property $h(x)=\langle h,\Phi(x)\rangle$ holds for all $h\in H$, $x\in X$ (6.9, with
--   $\Phi(x)$ standing for the book's $K(x,\cdot)$, since the book's own proof sets
--   $\Phi(x)(x')=K(x,x')$, i.e. $\Phi(x)$ *is* $K(x,\cdot)$).
--
--   **Formalization Note.** `ev : H → X → ℝ` stands in for "elements of `H` are functions on
--   `X`" (`ev h x` = the book's `h(x)`), since Mathlib's abstract Hilbert spaces are not spaces
--   of functions; this predicate is shared between Theorem 6.8 (its conclusion) and Theorem
--   6.11 (its "`H` its corresponding RKHS" hypothesis), not itself a book-numbered definition.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 110, Theorem 6.8 (PDF p. 127)

import Mathlib

namespace FoundationsML.Kernels

/-- `H` (with feature map `Φ : X → H` and evaluation map `ev : H → X → ℝ`) is the reproducing
kernel Hilbert space (RKHS) of the kernel `K` (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, Theorem 6.8, p. 110, PDF p. 127): `K(x,x') =
⟨Φ(x),Φ(x')⟩` for all `x,x' ∈ X` (6.8), and the reproducing property `h(x) = ⟨h,Φ(x)⟩` for all
`h ∈ H`, `x ∈ X` (6.9, with `Φ(x)` standing for the book's `K(x,·)`, since the book's own proof
sets `Φ(x)(x') = K(x,x')`, i.e. `Φ(x)` *is* `K(x,·)`).

**Formalization Note.** Since Mathlib's abstract Hilbert spaces are not spaces of functions,
`ev : H → X → ℝ` stands in for "elements of `H` are functions on `X`" (`ev h x` = the book's
`h(x)`); this is the structural device used to state both Theorem 6.8's conclusion and Theorem
6.11's "`H` its corresponding RKHS" hypothesis without re-deriving `H` in the latter. -/
def IsRKHSOf {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ) : Prop :=
  (∀ x x' : X, K x x' = inner ℝ (Φ x) (Φ x')) ∧
  ∀ (h : H) (x : X), ev h x = inner ℝ h (Φ x)

end FoundationsML.Kernels


