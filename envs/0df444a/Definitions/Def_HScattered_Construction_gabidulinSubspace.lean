-- Prove2me | Definitions.Def_HScattered_Construction_gabidulinSubspace
-- name    : HScattered_Construction_gabidulinSubspace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:18.169651+00:00
-- url     : https://prove2.me/theorems/f6d10aa8-db33-4a4c-8081-97ab47a75651
-- title:
--   The subspace {(x, x^q, …, x^{q^{r−1}}) : x ∈ 𝔽_{qⁿ}} of 𝔽_{qⁿ}^r (Example 2.5)
-- statement:
--   Let $q=|\mathbb F_q|$ and $r\ge 0$. The map
--
--   $$
--   \gamma_r:\ \mathbb F_{q^n}\to\mathbb F_{q^n}^{\,r},\qquad x\mapsto \bigl(x,\,x^{q},\,x^{q^2},\,\dots,\,x^{q^{r-1}}\bigr)
--   $$
--
--   is $\mathbb F_q$-linear, because each coordinate $x\mapsto x^{q^j}$ is a power of the Frobenius automorphism and fixes $\mathbb F_q$ pointwise. Its image
--
--   $$
--   G_r=\{(x,x^{q},x^{q^2},\dots,x^{q^{r-1}}) : x\in\mathbb F_{q^n}\}
--   $$
--
--   is an $\mathbb F_q$-subspace of $\mathbb F_{q^n}^{\,r}$. It is the subspace associated with the Gabidulin codes, and Example 2.5 of the paper states that it is maximum $(r-1)$-scattered of dimension $n$ when $n\ge r$.
--
--   **Formalization Note** `gabidulinMap F K r` is the linear map $\gamma_r$ with coordinates indexed by `j : Fin r` and value `x ^ (Fintype.card F ^ j)`; `gabidulinSubspace F K r` is its range. The file also contains the structural lemmas `frobeniusAlgHom_pow_apply` (used to prove linearity) and `mem_gabidulinSubspace`.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 7, Example 2.5 (also the proof of Lemma 2.2, p. 3)

import Mathlib

namespace HScattered.Construction

/-- The `j`-th power of the Frobenius `F`-algebra endomorphism `x ↦ x ^ q` of `K`, `q = |F|`,
is `x ↦ x ^ (q ^ j)`. -/
theorem frobeniusAlgHom_pow_apply (F K : Type*) [Field F] [Fintype F] [Field K] [Algebra F K]
    (j : ℕ) (x : K) :
    ((FiniteField.frobeniusAlgHom F K) ^ j) x = x ^ (Fintype.card F ^ j) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, AlgHom.mul_apply, ih, FiniteField.coe_frobeniusAlgHom, pow_succ', pow_mul]

/-- The `𝔽_q`-linear map `x ↦ (x, x^q, x^{q²}, …, x^{q^{r−1}})` from `𝔽_{qⁿ}` to `𝔽_{qⁿ}^r`,
where `𝔽_q = F`, `𝔽_{qⁿ} = K` and `q = |F|` (arXiv:1906.10590v2, Example 2.5, p. 7). -/
noncomputable def gabidulinMap (F K : Type*) [Field F] [Fintype F] [Field K] [Algebra F K]
    (r : ℕ) : K →ₗ[F] (Fin r → K) where
  toFun x j := x ^ (Fintype.card F ^ (j : ℕ))
  map_add' x y := by
    funext j
    have := map_add ((FiniteField.frobeniusAlgHom F K) ^ (j : ℕ)) x y
    simpa only [frobeniusAlgHom_pow_apply, Pi.add_apply] using this
  map_smul' c x := by
    funext j
    have := map_smul ((FiniteField.frobeniusAlgHom F K) ^ (j : ℕ)) c x
    simpa only [frobeniusAlgHom_pow_apply, Pi.smul_apply, RingHom.id_apply] using this

/-- Example 2.5 (arXiv:1906.10590v2, p. 7): the `𝔽_q`-subspace
`{(x, x^q, x^{q²}, …, x^{q^{r−1}}) : x ∈ 𝔽_{qⁿ}}` of `𝔽_{qⁿ}^r`. -/
noncomputable def gabidulinSubspace (F K : Type*) [Field F] [Fintype F] [Field K] [Algebra F K]
    (r : ℕ) : Submodule F (Fin r → K) :=
  LinearMap.range (gabidulinMap F K r)

/-- Membership in the subspace of Example 2.5, unfolded. -/
theorem mem_gabidulinSubspace (F K : Type*) [Field F] [Fintype F] [Field K] [Algebra F K]
    (r : ℕ) (v : Fin r → K) :
    v ∈ gabidulinSubspace F K r ↔ ∃ x : K, ∀ j : Fin r, x ^ (Fintype.card F ^ (j : ℕ)) = v j := by
  simp only [gabidulinSubspace, LinearMap.mem_range, funext_iff]
  rfl

end HScattered.Construction


