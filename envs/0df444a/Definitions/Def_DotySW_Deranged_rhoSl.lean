-- Prove2me | Definitions.Def_DotySW_Deranged_rhoSl
-- name    : DotySW_Deranged_rhoSl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:35:17.312142+00:00
-- url     : https://prove2.me/theorems/ad52cf84-51c7-4735-be88-a01df7792513
-- title:
--   The action of $\mathrm{GL}_n$ on $\mathfrak{sl}_n^{\otimes r}$
-- statement:
--   For $g\in\mathrm{GL}_n(\mathbb C)$, the restriction of $\rho(g)$ on $V^{r,r}$ to the invariant subspace $\mathfrak{sl}_n^{\otimes r}$. On pure tensors it is conjugation in every slot,
--
--   $$
--   \rho(g)(X_0\otimes\cdots\otimes X_{r-1})=gX_0g^{-1}\otimes\cdots\otimes gX_{r-1}g^{-1},
--   $$
--
--   so this is the $r$-th tensor power of the adjoint representation.
--
--   **Formalization Note** The module also contains the reindexing `pairEquiv` and the two lemmas showing that $\rho(g)$ acts as above and preserves the subspace, which the restriction needs.
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §4.1, p. 10, and §4.3, Eq. (19), p. 11

import Mathlib
import Definitions.Def_DotySW_Deranged_rho
import Definitions.Def_DotySW_Deranged_slTensor

namespace DotySW.Deranged

/-- Reindexing a label of `V^{r,r}` as the `r` pairs (position `a`, position `r + a`). -/
def pairEquiv (n r : ℕ) : Idx n (r + r) ≃ (Fin r → Fin n × Fin n) where
  toFun v a := (v (Fin.castAdd r a), v (Fin.natAdd r a))
  invFun p := Fin.append (fun a => (p a).1) (fun a => (p a).2)
  left_inv v := by
    funext c
    refine Fin.addCases (fun a => ?_) (fun a => ?_) c <;>
      simp only [Fin.append_left, Fin.append_right]
  right_inv p := by
    funext a
    simp only [Fin.append_left, Fin.append_right]

/-- `ρ(g)` conjugates every slot of a pure tensor: `ρ(g)(⊗ X_a) = ⊗ g X_a g⁻¹`. -/
theorem rho_mulVec_pureGl (n r : ℕ) (g : GL (Fin n) ℂ) (X : Fin r → Matrix (Fin n) (Fin n) ℂ) :
    (rho n r r g).mulVec (pureGl n r X) =
      pureGl n r (fun a => (g : Matrix (Fin n) (Fin n) ℂ) * X a *
        ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
  funext u
  simp only [Matrix.mulVec, dotProduct, rho, Matrix.of_apply, pureGl]
  rw [← (pairEquiv n r).symm.sum_comp]
  have key : ∀ p : Fin r → Fin n × Fin n,
      ((∏ a, (g : Matrix (Fin n) (Fin n) ℂ) (u (Fin.castAdd r a))
            ((pairEquiv n r).symm p (Fin.castAdd r a))) *
          ∏ b, ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
            ((pairEquiv n r).symm p (Fin.natAdd r b)) (u (Fin.natAdd r b))) *
        ∏ a, X a ((pairEquiv n r).symm p (Fin.castAdd r a))
          ((pairEquiv n r).symm p (Fin.natAdd r a)) =
      ∏ a, ((g : Matrix (Fin n) (Fin n) ℂ) (u (Fin.castAdd r a)) (p a).1 * X a (p a).1 (p a).2 *
        ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (p a).2 (u (Fin.natAdd r a))) := by
    intro p
    simp only [pairEquiv, Equiv.coe_fn_symm_mk, Fin.append_left, Fin.append_right,
      Finset.prod_mul_distrib]
    ring
  simp only [key]
  have hsum : ∀ a : Fin r,
      ((g : Matrix (Fin n) (Fin n) ℂ) * X a * ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
        (u (Fin.castAdd r a)) (u (Fin.natAdd r a)) =
      ∑ q : Fin n × Fin n, (g : Matrix (Fin n) (Fin n) ℂ) (u (Fin.castAdd r a)) q.1 *
        X a q.1 q.2 * ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) q.2 (u (Fin.natAdd r a)) := by
    intro a
    rw [Fintype.sum_prod_type_right]
    simp only [Matrix.mul_apply, Finset.sum_mul]
  simp only [hsum]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- `ρ(g)` maps `sl_n^{⊗r}` into itself. -/
theorem rho_mulVec_mem_slTensor (n r : ℕ) (g : GL (Fin n) ℂ) (w : Idx n (r + r) → ℂ)
    (hw : w ∈ slTensor n r) : (rho n r r g).mulVec w ∈ slTensor n r := by
  induction hw using Submodule.span_induction with
  | mem w h =>
    obtain ⟨X, hX, rfl⟩ := h
    rw [rho_mulVec_pureGl]
    refine Submodule.subset_span ⟨_, fun a => ?_, rfl⟩
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    have : ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * (g : Matrix (Fin n) (Fin n) ℂ) = 1 := by
      rw [← Units.val_mul]; simp
    rw [this, Matrix.one_mul, hX a]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hx

/-- **The action of `GL_n` on `sl_n^{⊗r}`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §4.1, p. 10, and §4.3, Eq. (19), p. 11.

The restriction of `ρ` on `V^{r,r}` to the invariant subspace `sl_n^{⊗r}`; by
`rho_mulVec_pureGl` it is conjugation by `g` in every slot, i.e. the `r`-th tensor power of the
adjoint representation.

**Formalization Note** The two auxiliary declarations before this one are the invariance proof
that the restriction needs, and `pairEquiv` is the reindexing it uses. -/
noncomputable def rhoSl (n r : ℕ) (g : GL (Fin n) ℂ) : Module.End ℂ (slTensor n r) :=
  (Matrix.mulVecLin (rho n r r g)).restrict (fun w hw => rho_mulVec_mem_slTensor n r g w hw)

end DotySW.Deranged


