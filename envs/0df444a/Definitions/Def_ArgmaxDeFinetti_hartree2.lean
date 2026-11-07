-- Prove2me | Definitions.Def_ArgmaxDeFinetti_hartree2
-- name    : ArgmaxDeFinetti_hartree2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:17.558204+00:00
-- url     : https://prove2.me/theorems/621933c6-6324-4d41-9a7a-12a7b7120f30
-- title:
--   Two-site Hartree mixtures $\mathrm{SEP}^{(2)}_H(d)$
-- statement:
--   The two-site Hartree mixtures are the convex hull of the pure product states $|u\rangle\langle u|^{\otimes2}$ of unit vectors:
--   $$
--   \mathrm{SEP}^{(2)}_H(d)=\operatorname{conv}\{|u\rangle\langle u|^{\otimes2}:\ u\in\mathbb C^d,\ \|u\|=1\}.
--   $$
--   They are the approximants in the bosonic de Finetti theorem.
--
--   **Formalization Note** $\operatorname{conv}$ is the real convex hull (finite convex combinations) in the space of matrices, and $\|u\|$ is the Euclidean norm.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 'Separable state families', p.18 (also (1.1), p.6), t = 2

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_vnorm
import Definitions.Def_ArgmaxDeFinetti_tensorPow

open Matrix

namespace ArgmaxDeFinetti

/-- The pure two-site product state `|u⟩⟨u|^{⊗2} = |u^{⊗2}⟩⟨u^{⊗2}|`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1, p.18. -/
def pureTensor2 {d : ℕ} (u : Fin d → ℂ) : Op 2 d :=
  Matrix.vecMulVec (tensorPow u 2) (star (tensorPow u 2))

/-- The two-site Hartree mixtures `SEP^{(2)}_H(d) = conv { |u⟩⟨u|^{⊗2} : u ∈ ℂ^d, ∥u∥ = 1 }`,
Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 "Separable state families", p.18 (also (1.1), p.6), with `t = 2`.

**Formalization Note** `conv` is the real convex hull `convexHull ℝ` (finite convex combinations) in the
space of matrices; `∥u∥` is the Euclidean norm `vnorm`. -/
def hartree2 (d : ℕ) : Set (Op 2 d) :=
  convexHull ℝ {σ | ∃ u : Fin d → ℂ, vnorm u = 1 ∧ σ = pureTensor2 u}

end ArgmaxDeFinetti


