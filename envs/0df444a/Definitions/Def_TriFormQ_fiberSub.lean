-- Prove2me | Definitions.Def_TriFormQ_fiberSub
-- name    : TriFormQ_fiberSub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:46.085669+00:00
-- url     : https://prove2.me/theorems/53b7e013-0092-4fbf-bcb4-4d698bbd6ad4
-- title:
--   Fiber $Z_v$ as a subspace
-- statement:
--   For a trilinear form $f$ and $v\in\mathbb F^n$, the fiber $Z_v$ is the subspace
--
--   $$Z_v=\{u\in\mathbb F^n:\ u^\top f\langle v\rangle=0\},$$
--
--   the left kernel of the slice matrix $f\langle v\rangle$. Its codimension $n-\dim Z_v$ equals $\mathrm{rk}\,f\langle v\rangle$. The paper uses this codimension in Fact 1.
--
--   **Formalization Note** The carrier of this subspace is the Finset `fiber θ v` (a proved sanity check); codimension is written $n-\dim$.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), §2.2.1, pp.13–14 (PDF pp.16–17)

import Definitions.Def_TriFormQ_sliceV

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), §2.2.1, p.13 (PDF p.16): "Note
that in this setting, a fiber is always a subspace of the vector space U"; p.14: "Z_v is a
subspace of U, codim(Z_v) = rk f⟨v⟩". The fiber `Z_v` as a subspace of `𝔽ⁿ`: the left kernel
`{u | uᵀ f⟨v⟩ = 0}` of the slice matrix.

**Formalization Note.** Its carrier is the Finset `fiber θ v` (`uᵀ f⟨v⟩ = 0` iff `f(u, v, w) = 0`
for every `w`); codimensions are `n − Module.finrank`. -/
def fiberSub {F : Type} [Field F] {n : ℕ} (θ : TriForm F n) (v : Vec F n) :
    Submodule F (Vec F n) :=
  LinearMap.ker (Matrix.vecMulLinear (sliceV θ v))

end TriFormQ


