-- Prove2me | Definitions.Def_ROLDescent_specGap
-- name    : ROLDescent_specGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:07.129396+00:00
-- url     : https://prove2.me/theorems/59a2c51b-c8d4-4f57-9c45-0f39d564c5cf
-- title:
--   Spectral gap above the kernel, $\mathrm{gap}(A)$
-- statement:
--   Let $A \succeq 0$ be a self-adjoint operator on a finite-dimensional complex Hilbert space $\mathcal H$, and $\mathcal N = \ker A$. If $\mathcal N^\perp \ne \{0\}$, the **spectral gap above the kernel** is
--
--   $$\mathrm{gap}(A) = \min_{0 \ne f \in \mathcal N^\perp} \frac{\langle f, A f\rangle}{\|f\|^2} .$$
--
--   **Formalization Note** Written as the infimum (`sInf`) of the Rayleigh quotients over nonzero $f \in (\ker A)^\perp$; for positive $A$ in finite dimension this infimum is attained. When $(\ker A)^\perp = \{0\}$ the paper assigns no value and the infimum of the empty set is the junk value $0$; no statement of the mission reads it there.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Definition 2.1, eq. (5), p.9 (PDF 9)

import Mathlib

namespace ROLDescent

open scoped InnerProductSpace

/-- **Spectral gap above the kernel.** Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Definition 2.1, eq. (5), p.9 (PDF 9):
"Let A ⪰ 0 be self-adjoint on H, and set N = ker A. If N^⊥ ≠ {0}, define
gap(A) = min_{0≠f∈N^⊥} ⟨f, Af⟩ / ‖f‖²."

**Formalization Note** The minimum is written as `sInf` of the Rayleigh quotients over nonzero
vectors of `(ker A)ᗮ`; for positive `A` on a finite-dimensional space with `(ker A)ᗮ ≠ {0}` the
infimum is attained, so it is the paper's minimum. When `(ker A)ᗮ = {0}` the paper assigns no value;
here `sInf ∅ = 0` is a junk value, and every statement of the mission reads `specGap` only when
`(ker A)ᗮ ≠ {0}`. -/
noncomputable def specGap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) : ℝ :=
  sInf {r : ℝ | ∃ f ∈ (LinearMap.ker (A : E →ₗ[ℂ] E))ᗮ, f ≠ 0 ∧ r = RCLike.re ⟪f, A f⟫_ℂ / ‖f‖ ^ 2}

end ROLDescent


