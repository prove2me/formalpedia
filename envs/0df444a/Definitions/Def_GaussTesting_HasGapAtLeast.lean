-- Prove2me | Definitions.Def_GaussTesting_HasGapAtLeast
-- name    : GaussTesting_HasGapAtLeast
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:31.092486+00:00
-- url     : https://prove2.me/theorems/470fc5f1-f4ff-491d-9998-8f673614b01f
-- title:
--   Spectral gap at least $\Delta$
-- statement:
--   A bounded operator $\Xi$ has **spectral gap at least $\Delta$** if every nonzero point $z$ of the spectrum of $I-\Xi$ satisfies $\operatorname{Re} z\ge\Delta$:
--
--   $$
--   z\in\operatorname{spec}(I-\Xi),\ z\ne0\ \Longrightarrow\ \Delta\le\operatorname{Re}z .
--   $$
--
--   Definition 3.1 defines the spectral gap of $\Xi$ as the smallest nonzero eigenvalue of $I-\Xi$, and Theorem 3.5 assumes it is at least $\Delta$. For the self-adjoint operators $\Xi$ of the paper the spectrum is real.
--
--   **Formalization Note** Eigenvalues are read through the spectrum of the operator. On finite-dimensional spaces these coincide; on the infinite-dimensional bosonic spaces the spectrum also contains limit points of eigenvalues, and the gap condition is the one the soundness argument uses ($T^2\succeq\Delta T$ off the kernel).
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Definition 3.1, p.21; Theorem 3.5, p.26

import Mathlib

namespace GaussTesting

/-- "`Ξ` has spectral gap at least `Δ`": every nonzero point of the spectrum of `I − Ξ` has real part
at least `Δ`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Definition 3.1, p.21 ("The spectral gap `Δ` of `Ξ` is the smallest nonzero
eigenvalue of `I − Ξ`"), Theorem 3.5, p.26 ("has spectral gap at least `Δ`").

**Formalization Note.** The eigenvalues of `I − Ξ` are read through the spectrum `spectrum ℂ (1 − T)` of
the bounded operator. In finite dimension this is the set of eigenvalues; on the infinite-dimensional
bosonic spaces it also contains the accumulation points, which is what the soundness argument of the
paper uses (`T² ⪰ Δ T` on the complement of the kernel). For the self-adjoint `Ξ` of the paper the
spectrum is real, so `Δ ≤ z.re` is `Δ ≤ z`. -/
def HasGapAtLeast {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (T : E →L[ℂ] E) (Δ : ℝ) :
    Prop :=
  ∀ z ∈ spectrum ℂ (1 - T), z = 0 ∨ Δ ≤ z.re

end GaussTesting


