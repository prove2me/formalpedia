-- Prove2me | Definitions.Def_TolProdTest_symProjOn
-- name    : TolProdTest_symProjOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:25:30.708202+00:00
-- url     : https://prove2.me/theorems/788b4575-a239-48e3-8aab-33702fb427ee
-- title:
--   Blockwise symmetric-subspace projectors $Q_{k,C}$ and $Q_k$
-- statement:
--   For $k$ copies of an $n$-site system, let $Q_{k,i}$ be the orthogonal projector onto $\mathrm{Sym}^k(\mathcal H_i)$ acting on the $i$-th register of each copy. For a coloring $C$, $Q_{k,c}$ is the projector onto $\mathrm{Sym}^k(\mathcal H_c)$ acting on the $k$ copies of block $B_c$. This module defines, for a set $T$ of colours,
--
--   $$
--   \prod_{c\in T}Q_{k,c}=\frac{1}{(k!)^{|T|}}\sum_{(\sigma_c)_{c\in T}\in S_k^T}\ \prod_{c\in T}P^{(c)}_{\sigma_c},
--   $$
--
--   where $P^{(c)}_{\sigma}$ permutes the $k$ copies of every site of $B_c$ by the same permutation $\sigma$. With $T$ all colours this is $Q_{k,C}=\prod_cQ_{k,c}$; with every site its own colour it is the accepting projector of the $k$-copy product test,
--
--   $$
--   Q_k=\prod_{i=1}^nQ_{k,i}.
--   $$
--
--   These are the accepting projectors of Protocol 2.1 and of its blockwise variant used in the analysis.
--
--   **Formalization Note** The basis of the $k$-copy space is `Fin k → S → Fin d` (copy, site, level). The average $(1/k!)\sum_{\pi\in S_k}P_\pi$ is the orthogonal projector onto the symmetric subspace, and projectors of different blocks commute; an empty block contributes the identity ($\mathrm{Sym}^k(\mathbb C)=\mathbb C$).
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), §2.2, eq. (20), p.8; §3.2, p.10; §3.3, p.14

import Mathlib

set_option autoImplicit false

namespace TolProdTest

/-- The register permutation operator on `k` copies of a system with sites `S`: copy `j` of site `i` receives
the content of copy `(τ i)⁻¹ j` of the same site, i.e. `|y⟩ ↦ |y'⟩` with `y' j i = y ((τ i)⁻¹ j) i`. A basis
string of the `k`-copy space is `x : Fin k → S → Fin d` (copy `j`, site `i`). -/
def regPermOp {S : Type} [Fintype S] [DecidableEq S] (d : ℕ) {k : ℕ} (τ : S → Equiv.Perm (Fin k)) :
    Matrix (Fin k → S → Fin d) (Fin k → S → Fin d) ℂ :=
  Matrix.of fun x y => if x = (fun j i => y ((τ i).symm j) i) then 1 else 0

/-- **Blockwise symmetric-subspace projectors** `∏_{c ∈ T} Q_{k,c}`, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), §2.2, p.8 and §3.3, p.14:
"For an integer k ≥ 1 and each i ∈ [n], let Q_{k,i} denote the orthogonal projector onto Sym^k(H_i) ⊆ H_i^{⊗k}.
It acts on the i-th register of each of the k copies and as the identity on all remaining registers", and
"For a fixed coloring C, let Q_{k,c} denote the block projector onto Sym^k(H_c) on the k copies of block B_c,
acting as the identity on all other blocks."

For a coloring `C : S → ι` and a set `T` of colours, this is the average over `σ : ι → S_k` of the operator
that permutes the `k` copies of every site `i` with `C i ∈ T` by `σ (C i)` (the same permutation for all sites
of a block) and leaves the other sites alone. Since `(1/k!) Σ_{π ∈ S_k} P_π` is the orthogonal projector onto
`Sym^k(H_c)`, and the block operators commute, this equals `∏_{c ∈ T} Q_{k,c}`.

**Formalization Note** The normalization is `(k!)^{|ι|}`; the colours outside `T` are averaged over a constant,
which contributes a factor 1. An empty block gives the identity (`Sym^k(ℂ) = ℂ`). -/
noncomputable def symProjOn {S ι : Type} [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι]
    (d : ℕ) (C : S → ι) (T : Finset ι) (k : ℕ) :
    Matrix (Fin k → S → Fin d) (Fin k → S → Fin d) ℂ :=
  (((k.factorial : ℂ) ^ Fintype.card ι)⁻¹) •
    ∑ σ : ι → Equiv.Perm (Fin k), regPermOp d (fun i => if C i ∈ T then σ (C i) else 1)

/-- `Q_{k,C} := ∏_{c} Q_{k,c}`, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), p.10 (`k = 2`) and p.14: the accepting projector of the blockwise
`k`-copy test for the coloring `C`. -/
noncomputable def symProjBlocks {S ι : Type} [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι]
    (d : ℕ) (C : S → ι) (k : ℕ) : Matrix (Fin k → S → Fin d) (Fin k → S → Fin d) ℂ :=
  symProjOn d C Finset.univ k

/-- `Q_k := ∏_{i=1}^n Q_{k,i}`, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (20), p.8: the accepting projector of the `k`-copy product test
(every site is its own block). -/
noncomputable def qk (S : Type) [Fintype S] [DecidableEq S] (d k : ℕ) :
    Matrix (Fin k → S → Fin d) (Fin k → S → Fin d) ℂ :=
  symProjBlocks d (id : S → S) k

end TolProdTest


