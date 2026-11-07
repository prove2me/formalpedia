-- Prove2me | Definitions.Def_QSDMixing_GU_tensorVec
-- name    : QSDMixing_GU_tensorVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:18.426725+00:00
-- url     : https://prove2.me/theorems/1a5bb435-3579-4b09-aa72-8fd9b5053d2b
-- title:
--   The pure tensor $v_1\otimes\dots\otimes v_k\in\ell^2(\mathrm{Fin}\,k\to\iota)$
-- statement:
--   For vectors $v_1,\dots,v_k\in\ell^2(\iota)$, the pure tensor $v_1\otimes\dots\otimes v_k$ is the element of $\ell^2(\mathrm{Fin}\,k\to\iota)$ with coordinates
--
--   $$
--   f\mapsto\prod_{j}v_j(f(j)).
--   $$
--
--   Taking all $v_j=\psi$ gives the $k$-copy vector $\psi^{\otimes k}$, whose Gram matrix over an ensemble is the $k$-th Schur power of the one-copy Gram matrix.
--
--   **Formalization Note** The file also proves that the coordinates are square summable. At $k=0$ the result is the unit vector of $\ell^2$ of a one-point type.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (4), p.4; §3, p.17

import Mathlib
import Definitions.Def_GaussTesting_Ell2

set_option autoImplicit false
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- Coordinates of a pure tensor are square summable: the `Memℓp` proof behind `tensorVec`. -/
theorem tensorVec_memℓp {ι : Type} {k : ℕ} (v : Fin k → Ell2 ι) :
    Memℓp (fun (f : Fin k → ι) => ∏ j, (v j : ι → ℂ) (f j)) 2 := by
  classical
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  rw [memℓp_gen_iff h2]
  have hs : ∀ j, Summable fun i => ‖(v j : ι → ℂ) i‖ ^ (2 : ENNReal).toReal := fun j =>
    (memℓp_gen_iff h2).1 (lp.memℓp (v j))
  refine summable_of_sum_le (c := ∏ j, ∑' i, ‖(v j : ι → ℂ) i‖ ^ (2 : ENNReal).toReal)
    (fun _ => by positivity) (fun S => ?_)
  let t : Fin k → Finset ι := fun j => S.image (fun f => f j)
  have hprod : ∀ f : Fin k → ι,
      ‖∏ j, (v j : ι → ℂ) (f j)‖ ^ (2 : ENNReal).toReal
        = ∏ j, ‖(v j : ι → ℂ) (f j)‖ ^ (2 : ENNReal).toReal := by
    intro f
    rw [norm_prod, Real.finsetProd_rpow _ _ (fun _ _ => norm_nonneg _)]
  calc ∑ f ∈ S, ‖∏ j, (v j : ι → ℂ) (f j)‖ ^ (2 : ENNReal).toReal
      ≤ ∑ f ∈ Fintype.piFinset t, ‖∏ j, (v j : ι → ℂ) (f j)‖ ^ (2 : ENNReal).toReal := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro f hf
        exact Fintype.mem_piFinset.2 fun j => Finset.mem_image_of_mem _ hf
    _ = ∏ j, ∑ i ∈ t j, ‖(v j : ι → ℂ) i‖ ^ (2 : ENNReal).toReal := by
        simp_rw [hprod]
        exact (Finset.prod_univ_sum t (fun j i => ‖(v j : ι → ℂ) i‖ ^ (2 : ENNReal).toReal)).symm
    _ ≤ ∏ j, ∑' i, ‖(v j : ι → ℂ) i‖ ^ (2 : ENNReal).toReal := by
        refine Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
          fun j _ => (hs j).sum_le_tsum _ fun _ _ => by positivity

/-- The pure tensor `v₁ ⊗ … ⊗ v_k ∈ ℓ²(Fin k → ι)`, with coordinates `f ↦ ∏ j, v j (f j)`.

This is the `k`-copy vector `ψ^{⊗k}` of Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (4), p.4, and §3, p.17.

**Formalization Note.** `Ell2 ι = ℓ²(ι)` is the published `GaussTesting.Ell2`. Every complex Hilbert space is
unitarily `ℓ²(ι)` for some `ι`, so quantifying over `ι : Type` covers the paper's "a Hilbert space `ℋ`" (§3, p.17).
`ℓ²(ι)^{⊗k}` is identified with `ℓ²(Fin k → ι)`. At `k = 0` the result is the unit vector of `ℓ²` of the
one-point type. -/
noncomputable def tensorVec {ι : Type} {k : ℕ} (v : Fin k → Ell2 ι) : Ell2 (Fin k → ι) :=
  ⟨fun f => ∏ j, (v j : ι → ℂ) (f j), tensorVec_memℓp v⟩

end QSDMixing.GU


