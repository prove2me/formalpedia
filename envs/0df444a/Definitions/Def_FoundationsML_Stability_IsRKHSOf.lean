-- Prove2me | Definitions.Def_FoundationsML_Stability_IsRKHSOf
-- name    : FoundationsML_Stability_IsRKHSOf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:23:00.564081+00:00
-- url     : https://prove2.me/theorems/75169886-e750-4c2a-9076-ab123c5d935c
-- title:
--   Reproducing kernel Hilbert space of a kernel
-- statement:
--   **Theorem 6.8, p. 110, PDF p. 127, used here without restating the representer machinery.**
--   `H` (with feature map $\Phi:X\to H$ and evaluation map $\mathrm{ev}:H\to X\to\mathbb R$) is
--   the RKHS of $K$: $K(x,x')=\langle\Phi(x),\Phi(x')\rangle$ for all $x,x'\in X$, and the
--   reproducing property $h(x)=\langle h,\Phi(x)\rangle$ for all $h\in H$, $x\in X$.
--
--   **Formalization Note.** Restated locally in `Stability`, byte-identical to chunk
--   `06-kernels`'s own copy (drafts cannot import another chunk's draft module).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 110, Theorem 6.8 (PDF p. 127)

import Mathlib

namespace FoundationsML.Stability

/-- `H` (with feature map `Φ : X → H` and evaluation map `ev : H → X → ℝ`) is the reproducing
kernel Hilbert space (RKHS) of the kernel `K` (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, Theorem 6.8, p. 110, PDF p. 127; used in this
chapter's §14.3 without restating the representer machinery): `K(x,x') = ⟨Φ(x),Φ(x')⟩` for all
`x,x' ∈ X`, and the reproducing property `h(x) = ⟨h,Φ(x)⟩` for all `h ∈ H`, `x ∈ X`.

**Formalization Note.** Restated locally in `Stability`, byte-identical to chunk `06-kernels`'s
own copy (drafts cannot import another chunk's draft module). Since Mathlib's abstract Hilbert
spaces are not spaces of functions, `ev : H → X → ℝ` stands in for "elements of `H` are
functions on `X`" (`ev h x` = the book's `h(x)`). -/
def IsRKHSOf {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ) : Prop :=
  (∀ x x' : X, K x x' = inner ℝ (Φ x) (Φ x')) ∧
  ∀ (h : H) (x : X), ev h x = inner ℝ h (Φ x)

end FoundationsML.Stability


