-- Prove2me | Definitions.Def_StrongConvG2
-- name    : StrongConvG2
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-05T22:11:37.584302+00:00
-- url     : https://prove2.me/theorems/4af5397e-0640-4da5-9e20-5d76090b9657
-- title:
--   Random Schreier graphs of S_N on k-tuples (Chen–Garza-Vargas–Tropp–van Handel)
-- statement:
--   Definitions for the Schreier-graph application after Theorem 3.14 of Chen–Garza-Vargas–Tropp–van Handel, *A new approach to strong convergence* (pp. 14–15). Page numbers are those of arXiv:2405.16026v3. Probabilities and expectations over $\sigma_1, \dots, \sigma_d \in \mathbf S_N$ are normalized counts over `Fin d → Equiv.Perm (Fin N)`, as in the mission's main bundle.
--
--   **Schreier graphs on $k$-tuples (CGTvH pp. 14–15).** p. 14: “random $2d$-regular Schreier graphs defined by the action of $\mathbf S_N$ on $k$-tuples of distinct elements of $\{1, \dots, N\}$”; pp. 14–15: “the restricted adjacency matrix $A^N = \bar A^N|_{\{1^\perp\}}$ of such a random graph”.
--   - A $k$-tuple of distinct elements of $\{1, \dots, N\}$ is an injective map `Fin k ↪ Fin N`. `StrongConv.tuplePerm k σ` is the action $t \mapsto \sigma \circ t$ of $\sigma \in \mathbf S_N$ on these tuples.
--   - `StrongConv.tuplePermOp k σ` is the permutation operator of that action on $\mathbb C^{(N)_k}$, sending the basis vector $e_t$ to $e_{\sigma \circ t}$.
--   - `StrongConv.schreierAdj k σ` is $\bar A^N = \sum_{i=1}^d (P_{\sigma_i} + P_{\sigma_i}^*)$, the adjacency matrix of the Schreier graph that joins each tuple $t$ to $\sigma_i \circ t$, $i = 1, \dots, d$. Loops and multiple edges are counted with multiplicity, so every row sums to $2d$.
--   - `StrongConv.tupleOnes k N` is the all-ones vector $1$, and `StrongConv.TupleOnesPerp k N` is $\{1\}^\perp$. `StrongConv.schreierAdjPerp k σ` is $A^N = \bar A^N|_{\{1\}^\perp}$.
--
--   Source: C.-F. Chen, J. Garza-Vargas, J. A. Tropp and R. van Handel, *A new approach to strong convergence*, Ann. of Math. 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, pp. 14–15).
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), pp. 14–15, the random Schreier graphs on k-tuples (pp. 14–15)

import Mathlib

/-!
# Random Schreier graphs on `k`-tuples (CGTvH)

C.-F. Chen, J. Garza-Vargas, J. A. Tropp and R. van Handel, *A new approach to strong convergence*,
Ann. of Math. 203 (2026) 555–602, arXiv:2405.16026v3 (CGTvH), pp. 14–15: the Schreier graph of the
action of `S_N` on `k`-tuples of distinct elements of `{1, …, N}` defined by `d` permutations.

Conventions:
- A `k`-tuple of distinct elements of `{1, …, N}` is an embedding `Fin k ↪ Fin N`.
-/

noncomputable section

namespace StrongConv

open scoped InnerProductSpace

/-! ## Schreier graphs on `k`-tuples of distinct points (CGTvH pp. 14–15) -/

/-- The action of `σ ∈ S_N` on `k`-tuples of distinct elements: `t ↦ σ ∘ t`. -/
def tuplePerm (k : ℕ) {N : ℕ} (σ : Equiv.Perm (Fin N)) : Equiv.Perm (Fin k ↪ Fin N) :=
  (Equiv.refl (Fin k)).embeddingCongr σ

/-- The permutation operator of `σ` on `ℂ^{k-tuples}`, sending the basis vector `e_t` to
`e_{σ ∘ t}`. -/
def tuplePermOp (k : ℕ) {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    EuclideanSpace ℂ (Fin k ↪ Fin N) →L[ℂ] EuclideanSpace ℂ (Fin k ↪ Fin N) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (tuplePerm k σ)).toContinuousLinearEquiv.toContinuousLinearMap

/-- `Ā = ∑ᵢ (P_{σᵢ} + P_{σᵢ}*)`: the adjacency matrix of the `2d`-regular Schreier graph on the
`k`-tuples of distinct elements of `{1, …, N}` defined by `σ₁, …, σ_d`, which joins `t` to
`σᵢ ∘ t` for each `i`. -/
def schreierAdj (k : ℕ) {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    EuclideanSpace ℂ (Fin k ↪ Fin N) →L[ℂ] EuclideanSpace ℂ (Fin k ↪ Fin N) :=
  ∑ i, (tuplePermOp k (σ i) + star (tuplePermOp k (σ i)))

/-- The all-ones vector `1` in `ℂ^{k-tuples}`. -/
def tupleOnes (k N : ℕ) : EuclideanSpace ℂ (Fin k ↪ Fin N) :=
  WithLp.toLp 2 (fun _ => (1 : ℂ))

/-- The subspace `{1}⊥ ⊆ ℂ^{k-tuples}`. -/
abbrev TupleOnesPerp (k N : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin k ↪ Fin N)) :=
  (ℂ ∙ tupleOnes k N)ᗮ

/-- CGTvH p. 14: `A = Ā|_{1⊥}`, the adjacency matrix of the Schreier graph on `k`-tuples
restricted to `{1}⊥`. -/
def schreierAdjPerp (k : ℕ) {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    TupleOnesPerp k N →L[ℂ] TupleOnesPerp k N :=
  ((schreierAdj k σ).comp (TupleOnesPerp k N).subtypeL).codRestrict (TupleOnesPerp k N)
    (fun x => by
      have hones : ∀ τ : Equiv.Perm (Fin N), tuplePermOp k τ (tupleOnes k N) = tupleOnes k N := by
        intro τ
        ext j
        simp [tuplePermOp, tupleOnes, LinearIsometryEquiv.piLpCongrLeft_apply]
      have hx := x.2
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hx ⊢
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, schreierAdj, sum_apply,
        add_apply, inner_sum, inner_add_right]
      refine Finset.sum_eq_zero fun i _ => ?_
      have h1 : ⟪tupleOnes k N, tuplePermOp k (σ i) x⟫_ℂ = 0 := by
        rw [← hones (σ i)]
        simp only [tuplePermOp, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.inner_map_map]
        simpa [tuplePermOp] using hx
      have h2 : ⟪tupleOnes k N, star (tuplePermOp k (σ i)) x⟫_ℂ = 0 := by
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right, hones]
        exact hx
      rw [h1, h2, add_zero])

end StrongConv

end


