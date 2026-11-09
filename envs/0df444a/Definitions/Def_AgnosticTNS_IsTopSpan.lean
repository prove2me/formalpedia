-- Prove2me | Definitions.Def_AgnosticTNS_IsTopSpan
-- name    : AgnosticTNS_IsTopSpan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:17.950235+00:00
-- url     : https://prove2.me/theorems/967aca89-5429-4802-81b6-ccb914a08ffc
-- title:
--   Span of eigenvectors for the $\Lambda$ largest eigenvalues
-- statement:
--   For a Hermitian matrix $A$ on a $D$-dimensional space and $\Lambda\in\mathbb N$, a subspace $W$ is **a span of eigenvectors for the $\Lambda$ largest eigenvalues of $A$, counted with multiplicity**, if $W$ is spanned by $k=\min(\Lambda,D)$ orthonormal eigenvectors $v_1,\dots,v_k$ of $A$, with eigenvalues $\mu_1,\dots,\mu_k$, such that every vector $x$ orthogonal to all $v_j$ satisfies $\langle x|A|x\rangle\le\mu_i\|x\|^2$ for every $i$. For Hermitian $A$ this says exactly that $\mu_1,\dots,\mu_k$ are $k$ largest eigenvalues counted with multiplicity; every choice inside a degenerate eigenspace is allowed, and $W$ is the whole space when $\Lambda\ge D$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Lemma 3.2, p.17; Corollary 3.3, p.18; Algorithm 1 line 11, p.19

import Mathlib
open Matrix

namespace AgnosticTNS

/-- **Span of eigenvectors for the `Λ` largest eigenvalues, counted with multiplicity**, Lemma 3.2
(p.17), Corollary 3.3 (p.18), Algorithm 1 line 11 (p.19) (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
`IsTopSpan A Λ W`: `W` is spanned by `k = min(Λ, dim)` orthonormal eigenvectors `v_1, …, v_k` of `A`
with eigenvalues `μ_1, …, μ_k`, and every Rayleigh quotient of a vector orthogonal to all `v_j` is at
most every `μ_i`. For Hermitian `A` the last condition says exactly that `μ_1, …, μ_k` are the `k`
largest eigenvalues counted with multiplicity; every choice of eigenvectors in a degenerate eigenspace
is allowed, and `W` is the whole space when `Λ ≥ dim`.

**Formalization Note** Orthonormality is written with the standard inner product
`⟨v_i, v_j⟩ = star v_i ⬝ᵥ v_j`. -/
def IsTopSpan {α : Type*} [Fintype α] (A : Matrix α α ℂ) (Λ : ℕ) (W : Submodule ℂ (α → ℂ)) :
    Prop :=
  ∃ (v : Fin (min Λ (Fintype.card α)) → α → ℂ) (μ : Fin (min Λ (Fintype.card α)) → ℝ),
    (∀ i j, star (v i) ⬝ᵥ v j = if i = j then 1 else 0) ∧
    (∀ i, A *ᵥ v i = (μ i : ℂ) • v i) ∧
    W = Submodule.span ℂ (Set.range v) ∧
    ∀ i (x : α → ℂ), (∀ j, star (v j) ⬝ᵥ x = 0) →
      (star x ⬝ᵥ (A *ᵥ x)).re ≤ μ i * ∑ a, ‖x a‖ ^ 2

end AgnosticTNS


