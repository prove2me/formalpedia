-- Prove2me | Definitions.Def_GaussTesting_amplSub
-- name    : GaussTesting_amplSub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:23.75101+00:00
-- url     : https://prove2.me/theorems/88bf54bd-6bd8-4a49-bcdd-c71d6eb06baa
-- title:
--   The range of $\Pi^{(1,\dots,k)}=\Pi\otimes I$ on $m=k+l$ registers
-- statement:
--   Let $K\subseteq\mathcal H^{\otimes k}$ be a closed subspace with projector $\Pi=\Pi_K$, and $l\ge 0$. On $\mathcal H^{\otimes(k+l)}=\mathcal H^{\otimes k}\otimes\mathcal H^{\otimes l}$, the operator $\Pi^{(1,\dots,k)}=\Pi\otimes I$ acts as $\Pi$ on the first $k$ registers and as the identity on the last $l$. Its range is the closed subspace
--
--   $$
--   K\otimes\mathcal H^{\otimes l}=\overline{\operatorname{span}}\{u\otimes v: u\in K,\ v\in\mathcal H^{\otimes l}\},
--   $$
--
--   so $\Pi^{(1,\dots,k)}$ is the orthogonal projector onto it.
--
--   **Formalization Note** Registers $1,\dots,k$ are the first $k$ coordinates of a label $x\in\iota^{k+l}$ (`Fin.castAdd`), the remaining $l$ the last ones; the split is the equivalence `splitEquiv`.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Definition 3.1, p.21

import Definitions.Def_GaussTesting_Ell2

namespace GaussTesting

/-- Splitting `m = k + l` registers into the first `k` and the last `l`:
`ℋ^{⊗(k+l)} ≅ ℋ^{⊗k} ⊗ ℋ^{⊗l}` on basis labels. -/
def splitEquiv (ι : Type*) (k l : ℕ) : (Fin (k + l) → ι) ≃ (Fin k → ι) × (Fin l → ι) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl ι)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

/-- For a closed subspace `K ⊆ ℋ^{⊗k}` with projector `Π = Π_K`, the closed subspace
`K ⊗ ℋ^{⊗l} ⊆ ℋ^{⊗(k+l)}`, i.e. the range of `Π^{(1,…,k)} = Π ⊗ I`, the projector `Π` acting on the
first `k` registers and the identity on the remaining `l`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Definition 3.1, p.21 ("`Π^{(1,…,k)}_test` acts on the original `k` copies of
`ℋ`").

**Formalization Note.** `Π ⊗ I` is encoded by its range: the closure of the span of the elementary
tensors `u ⊗ v` with `u ∈ K` and `v ∈ ℋ^{⊗l}` (the first `k` registers are `Fin.castAdd`, the last
`l` are `Fin.natAdd`, via `splitEquiv`). Its projector `proj (amplSub K l)` equals `Π_K ⊗ I`. -/
noncomputable def amplSub {ι : Type*} {k : ℕ} (K : ClosedSubmodule ℂ (Ell2 (Fin k → ι))) (l : ℕ) :
    ClosedSubmodule ℂ (Ell2 (Fin (k + l) → ι)) :=
  (Submodule.span ℂ {F | ∃ u ∈ K, ∃ v : Ell2 (Fin l → ι),
      F = reindexVec (splitEquiv ι k l) (tensorVec u v)}).closure

end GaussTesting


