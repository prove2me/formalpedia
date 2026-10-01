-- Prove2me | Definitions.Def_burau_red_hom
-- name    : burau_red_hom
-- status  : Definition
-- author  : @lt9
-- created : 2026-10-01T00:50:14.949132+00:00
-- url     : https://prove2.me/theorems/be76cdd1-476a-4d31-803f-2d42f516dd34
-- title:
--   The t = -1 specialization of the reduced Burau representation as a homomorphism
-- statement:
--   **The $t=-1$ specialization of the reduced Burau representation.** Let $\sigma_0,\sigma_1$ be the
--   Artin generators of $B_3$; the reduced Burau representation at $t=-1$ sends them to the two integral
--   matrices
--   $$ \sigma_0\mapsto \begin{pmatrix}1&-1\\0&1\end{pmatrix},\qquad
--      \sigma_1\mapsto \begin{pmatrix}2&-1\\1&0\end{pmatrix}, $$
--   which satisfy the braid relation, so the assignment descends to a homomorphism
--   $\overline{\rho}_3:B_3\to\mathrm{SL}(2,\mathbb Z)$. The definition node records this homomorphism (under
--   the name `redHom`) together with its two generators `redGen`, so that later nodes can state — without
--   depending on still-unproved nodes — how the $t=-1$ specialization of the *unreduced* Burau representation
--   compares with it: the bridge that reduces the milestone frontier to the kernel statement for
--   $\overline{\rho}_3$.
-- source:
--   Reduced Burau representation at t = -1; J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82 (1974), §3.3.

import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open Matrix BraidsLinksMCG

/-- The two Artin generators under the `t = -1` specialization of the reduced Burau representation. -/
noncomputable def redGen : Fin 2 → Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  fun i => if (i : ℕ) = 0 then ⟨!![1, -1; 0, 1], by decide⟩ else ⟨!![2, -1; 1, 0], by decide⟩

/-- The specialization respects Artin's braid relation. -/
lemma redGen_braid : ∀ r ∈ braidRels 3, FreeGroup.lift redGen r = 1 := by
  intro r hr
  simp only [braidRels, Set.mem_union] at hr
  rcases hr with ⟨i, j, h, rfl⟩ | ⟨i, j, h, rfl⟩
  · exfalso
    fin_cases i <;> fin_cases j <;> norm_num at h
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [mul_inv_eq_one]
    fin_cases i <;> fin_cases j <;>
      first
        | (exfalso; omega)
        | (ext a b; fin_cases a <;> fin_cases b <;> decide)

/-- The `t = -1` specialization of the reduced Burau representation of `B₃`, as a homomorphism. -/
noncomputable def redHom : BraidsLinksMCG.ArtinBraidGroup 3 →* Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  PresentedGroup.toGroup redGen_braid


