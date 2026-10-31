-- Prove2me | Definitions.Def_KallMayerSLP_RecourseBounds_IsBoxPartition
-- name    : KallMayerSLP_RecourseBounds_IsBoxPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:11:47.701218+00:00
-- url     : https://prove2.me/theorems/096eb2a8-8db2-4003-92bd-a3c57169535b
-- title:
--   Partition of the box $\Xi$ into interval cells
-- statement:
--   Let $\Xi=\times_{i=1}^r[\alpha_i,\beta_i]$. A **partition** $\mathcal X=\{\Xi_k;\ k=1,\dots,K\}$ of $\Xi$ into cells consists of sets $\Xi_k$ such that
--
--   1. each $\Xi_k$ is an interval of $\mathbb R^r$: a product $\times_{i=1}^r I_{k,i}$ of one-dimensional intervals with endpoints $\mathrm{lo}_{k,i}\le \mathrm{hi}_{k,i}$, each closed $[\mathrm{lo},\mathrm{hi}]$ or half-open $[\mathrm{lo},\mathrm{hi})$, $(\mathrm{lo},\mathrm{hi}]$;
--   2. each $\Xi_k$ is nonempty;
--   3. $\Xi_k\cap\Xi_\ell=\emptyset$ for $k\ne\ell$;
--   4. $\bigcup_{k=1}^K\Xi_k=\Xi$.
--
--   The closed box $[\mathrm{lo}_k,\mathrm{hi}_k]$ is the closure of the cell $\Xi_k$; the cell's Edmundson–Madansky distribution $\mathbb Q_k$ lives on its vertices.
--
--   **Formalization Note** Cells are indexed by `Fin K`; the corners $\mathrm{lo}_k,\mathrm{hi}_k$ are part of the data. The kind of each one-dimensional factor is chosen independently, which covers every reading of "half-open or closed intervals". $\Xi$ is `Set.Icc α β` in the pointwise order of `Fin r → ℝ`.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, §2.1, p.221 (PDF 230)

import Mathlib

namespace KallMayerSLP.RecourseBounds

/-- **A partition `X = {Ξₖ; k = 1, …, K}` of the box `Ξ` into interval cells.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, §2.1, printed p.221 (PDF 230):
"Assume that we have a disjoint partition `X = {Ξₖ; k = 1, ···, K}` of `Ξ`, where the `Ξₖ ≠ ∅` are
half-open or closed intervals, the cells, such that `Ξₖ ∩ Ξ_ℓ = ∅` for `k ≠ ℓ` and
`⋃_{k=1}^K Ξₖ = Ξ`."

Cell `k` is a product `×ᵢ Iₖᵢ` of one-dimensional intervals with endpoints `lo k i ≤ hi k i`, each
factor closed `[lo, hi]` or half-open `[lo, hi)`, `(lo, hi]`; the cells are nonempty, pairwise
disjoint, and their union is `Ξ = ×ᵢ [αᵢ, βᵢ]`.

**Formalization Note.** Cells are indexed by `Fin K` (0-based). The endpoints `lo k`, `hi k` are part
of the data: they are the corners of the closure `[lo k, hi k]` of the nonempty cell `Ξₖ`, on whose
vertices the cell's E–M distribution `Q_k` lives. Every factor may be chosen independently among the
three kinds, which covers every reading of "half-open or closed intervals" of `ℝ^r`. The box `Ξ` is
`Set.Icc α β` in the pointwise order of `Fin r → ℝ`, i.e. `×ᵢ [αᵢ, βᵢ]`. -/
def IsBoxPartition {r K : ℕ} (α β : Fin r → ℝ) (lo hi : Fin K → Fin r → ℝ)
    (cell : Fin K → Set (Fin r → ℝ)) : Prop :=
  (∀ k, ∃ I : Fin r → Set ℝ,
      (∀ i, I i = Set.Icc (lo k i) (hi k i) ∨ I i = Set.Ico (lo k i) (hi k i) ∨
        I i = Set.Ioc (lo k i) (hi k i)) ∧
      cell k = Set.univ.pi I) ∧
  (∀ k, (cell k).Nonempty) ∧
  Pairwise (Function.onFun Disjoint cell) ∧
  (⋃ k, cell k) = Set.Icc α β

end KallMayerSLP.RecourseBounds


