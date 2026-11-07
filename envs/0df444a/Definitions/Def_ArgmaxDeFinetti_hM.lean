-- Prove2me | Definitions.Def_ArgmaxDeFinetti_hM
-- name    : ArgmaxDeFinetti_hM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:40.951208+00:00
-- url     : https://prove2.me/theorems/f088787a-418d-4407-a9f0-eebeb99533f5
-- title:
--   $a_M(u)=\langle u^{\otimes2}|M|u^{\otimes2}\rangle$ and $h(M)=\max_{\|u\|=1}a_M(u)$
-- statement:
--   For a two-site operator $M$ and $u\in\mathbb C^d$,
--   $$
--   a_M(u)=\langle u^{\otimes2}|M|u^{\otimes2}\rangle,\qquad h(M)=\max_{\|u\|=1}a_M(u).
--   $$
--   $h(M)$ is the support function of the Hartree mixtures at $M$.
--
--   **Formalization Note** $a_M(u)$ is real for Hermitian $M$ and its real part is taken; the maximum over the compact Euclidean unit sphere is written as a supremum.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §3.1, p.22, eqs. (3.2)–(3.3)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_vnorm
import Definitions.Def_ArgmaxDeFinetti_tensorPow

open Matrix

namespace ArgmaxDeFinetti

/-- `a_M(u) = ⟨u^{⊗2}| M |u^{⊗2}⟩`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), eq. (3.2), p.22.

**Formalization Note** The value is real for Hermitian `M`; its real part is taken. -/
noncomputable def aM {d : ℕ} (M : Op 2 d) (u : Fin d → ℂ) : ℝ :=
  (vinner (tensorPow u 2) (M *ᵥ tensorPow u 2)).re

/-- `h(M) = max_{∥u∥=1} a_M(u)`, the maximum of `M` over Hartree states, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), eq. (3.3), p.22.

**Formalization Note** The maximum over the (compact) Euclidean unit sphere is written as `sSup`; `∥u∥` is the
Euclidean norm `vnorm`. -/
noncomputable def hM {d : ℕ} (M : Op 2 d) : ℝ :=
  sSup {r | ∃ u : Fin d → ℂ, vnorm u = 1 ∧ r = aM M u}

end ArgmaxDeFinetti


