-- Prove2me | Definitions.Def_DRSubmodHull_IsValidPerm
-- name    : DRSubmodHull_IsValidPerm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:25:02.688167+00:00
-- url     : https://prove2.me/theorems/05131486-3360-4e86-8c18-fd45022a6a18
-- title:
--   Valid permutations (Definition 5.2), the sets $\mathcal T^{\delta,k}$, and valid partial permutations (Definition 5.6)
-- statement:
--   A permutation $\delta=(\delta(1),\dots,\delta(|\mathcal V|))$ of $\mathcal V$, with $\delta^{-1}(i)$ the position of $i$, is **valid** (Definition 5.2) if
--
--   1. for any two distinct $i,j$ with $j\in R^+(i)$ and $u_i=u_j$: $\delta^{-1}(i)>\delta^{-1}(j)$;
--   2. for every $\psi\in\Psi$ with $\lfloor u_\psi\rfloor=0$: $\delta^{-1}(\mathrm{ch}(\psi))<\delta^{-1}(\psi)$;
--   3. for every $\psi\in\Psi$ and every $i\in R^-(\psi)$ with $u_i=\lfloor u_\psi\rfloor$: not both $\delta^{-1}(i)<\delta^{-1}(\psi)$ and $\delta^{-1}(\psi)<\delta^{-1}(\mathrm{ch}(\psi))$.
--
--   $\mathcal T^{\delta,k}=\{\delta(1),\dots,\delta(k)\}$, with $\mathcal T^{\delta,0}=\emptyset$, and $P(\delta,k)=P(\mathcal T^{\delta,k})$ (p.13). A **partial permutation** $\delta'=(\delta'(1),\dots,\delta'(|\mathcal V'|))$ of a subset $\mathcal V'$ is **valid** if some valid $\delta$ agrees with it on its first $|\mathcal V'|$ positions (Definition 5.6).
--
--   Validity removes the permutations whose chains $P(\delta,0),\dots,P(\delta,|\mathcal V|)$ repeat a point; the DR inequalities are indexed by valid permutations only.
--
--   **Formalization Note** $\delta$ is an equivalence `Fin |V| ≃ V`; Lean position $m$ is the paper's position $m+1$, and `δ.symm` plays $\delta^{-1}$. A partial permutation is a list of vertices; it is valid iff it is the length-$|\mathcal V'|$ prefix of the list of a valid permutation.
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, Definition 5.2, p.14; §5, p.13 (𝒯^{δ,k}); Definition 5.6, p.15

import Mathlib
import Definitions.Def_DRSubmodHull_CZ

set_option autoImplicit false

open Classical

noncomputable section

namespace DRSubmodHull

/-- **Valid permutation** (arXiv:2211.07726v2, Definition 5.2, p.14). A permutation `δ` of `𝒱` is
valid if
1. for any two distinct `i, j` with `j ∈ R⁺(i)` and `u_i = u_j`, `δ⁻¹(i) > δ⁻¹(j)`;
2. for every `ψ ∈ Ψ` with `⌊u_ψ⌋ = 0`, `δ⁻¹(ch(ψ)) < δ⁻¹(ψ)`;
3. for every `ψ ∈ Ψ` and every `i ∈ R⁻(ψ)` with `u_i = ⌊u_ψ⌋`, not both `δ⁻¹(i) < δ⁻¹(ψ)` and
   `δ⁻¹(ψ) < δ⁻¹(ch(ψ))`.

**Formalization Note.** A permutation `δ = (δ(1), …, δ(|𝒱|))` is an equivalence
`δ : Fin |V| ≃ V`; the Lean position `m` is the paper's position `m + 1`, so `δ.symm` compares
positions exactly as `δ⁻¹` does. -/
def IsValidPerm {V : Type*} [Fintype V] (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (δ : Fin (Fintype.card V) ≃ V) : Prop :=
  (∀ i j : V, i ≠ j → Relation.ReflTransGen A i j → u i = u j → δ.symm j < δ.symm i) ∧
  (∀ ψ ∈ Psi A N u, Int.floor (u ψ) = 0 → δ.symm (child A ψ) < δ.symm ψ) ∧
  (∀ ψ ∈ Psi A N u, ∀ i : V, Relation.ReflTransGen A i ψ → u i = (Int.floor (u ψ) : ℝ) →
    ¬ (δ.symm i < δ.symm ψ ∧ δ.symm ψ < δ.symm (child A ψ)))

/-- **The first `k` entries `𝒯^{δ,k} = {δ(1), …, δ(k)}`** of a permutation (arXiv:2211.07726v2, §5,
p.13), with `𝒯^{δ,0} = ∅` (and `𝒯^{δ,k} = 𝒱` for `k ≥ |𝒱|`). -/
def Tset {V : Type*} [Fintype V] (δ : Fin (Fintype.card V) ≃ V) (k : ℕ) : Finset V :=
  ((List.ofFn δ).take k).toFinset

/-- **Valid partial permutation** (arXiv:2211.07726v2, Definition 5.6, p.15): a partial permutation
`δ′ = (δ′(1), …, δ′(|𝒱′|))` is valid if there is a valid `δ ∈ 𝔖(𝒱)` with `δ′(i) = δ(i)` for
`i ∈ {1, …, |𝒱′|}`.

**Formalization Note.** A partial permutation is a list of vertices; it is valid iff it is the
prefix of length `L.length` of the list `(δ(1), …, δ(|𝒱|))` of some valid `δ` (so it has no
repetitions). -/
def IsValidPartialPerm {V : Type*} [Fintype V] (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (L : List V) : Prop :=
  ∃ δ : Fin (Fintype.card V) ≃ V, IsValidPerm A N u δ ∧ L = (List.ofFn δ).take L.length

end DRSubmodHull


