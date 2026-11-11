-- Prove2me | Definitions.Def_RandKSATSample_Main_PolymerModel
-- name    : RandKSATSample_Main_PolymerModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:58:26.59389+00:00
-- url     : https://prove2.me/theorems/00da811c-3451-4320-821e-aa749f39d835
-- title:
--   Abstract polymer models: the partition function Ξ(w), the Ursell coefficient φ, the cluster series L(w) and the pinned sum of (2.7)
-- statement:
--   An **abstract polymer model** is a finite set $\mathcal P$ of polymers, a symmetric incompatibility relation $\not\sim$ with $\gamma\not\sim\gamma$ for every $\gamma$, and complex activities $w_\gamma$. A family is compatible when no two distinct members are incompatible, and
--   $$\Xi(w)=\sum_{F\text{ compatible}}\prod_{\gamma\in F}w_\gamma\quad(2.3).$$
--   For a tuple $\Gamma=(\gamma_1,\dots,\gamma_\ell)\in\mathcal P^\ell$, $\ell\ge1$, the incompatibility graph $I(\Gamma)$ on $[\ell]$ joins distinct $i,j$ with $\gamma_i\not\sim\gamma_j$, and the **Ursell coefficient** is $\varphi(\Gamma)=\sum(-1)^{|F|}$ over the edge sets $F\subseteq E(I(\Gamma))$ for which $([\ell],F)$ is connected (2.4). The **cluster series** is
--   $$L(w)=\sum_{\ell\ge1}\frac1{\ell!}\sum_{(\gamma_1,\dots,\gamma_\ell)\in\mathcal P^\ell}\varphi(\gamma_1,\dots,\gamma_\ell)\prod_{i=1}^\ell w_{\gamma_i}\quad(2.5),$$
--   and for weights $u$ and a polymer $\gamma_0$ the $\ell$-th term of the pinned sum (2.7) is $\frac1{(\ell-1)!}\sum_{\gamma_2,\dots,\gamma_\ell}|\varphi(\gamma_0,\gamma_2,\dots,\gamma_\ell)|\prod_{i\ge2}u_{\gamma_i}$.
--
--   **Formalization Note.** The relation `inc` is arbitrary in the definitions; symmetry and reflexivity are hypotheses of Theorem 2.1. A tuple of length $\ell=\ell'+1$ is `Fin (ℓ'+1) → P`; cluster labels are the pairs `⟨ℓ', Γ⟩` and `clusterSeries` is the `tsum` over them (the double series of (2.5) regrouped, meaningful under absolute summability). The pinned term is indexed by $\ell'=\ell-1\ge0$, with the tuple `Fin.cons γ0 tail`.
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), §2.3, pp. 8–9, (2.3)–(2.5), (2.7)

import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace RandKSATSample.Main

noncomputable section

open Classical

/-!
# Abstract polymer models: partition function, Ursell coefficient, cluster series

He, Li, Yang, *Fast Almost-Uniform Sampling of Random k-SAT Solutions*, arXiv:2610.10474
(version not printed; file sha256 563a4d84…), §2.3, pp. 8–9, (2.3)–(2.5), (2.7).

A polymer model is a finite type `P` of polymers, an incompatibility relation `inc` (symmetric,
every polymer incompatible with itself: these are hypotheses of the theorems using it) and
complex activities `w : P → ℂ`. An ordered tuple `(γ_1, …, γ_ℓ)` with `ℓ ≥ 1` is encoded as
`Fin (ℓ' + 1) → P` with `ℓ = ℓ' + 1`, and a cluster label as the pair `⟨ℓ', Γ⟩`.
-/

variable {P : Type} [Fintype P]

/-- A family `F` of polymers is compatible: no two distinct members are incompatible. -/
def IsCompatibleFamily (inc : P → P → Prop) (F : Finset P) : Prop :=
  ∀ γ ∈ F, ∀ γ' ∈ F, γ ≠ γ' → ¬ inc γ γ'

/-- The partition function `Ξ(w) = Σ_{F compatible} Π_{γ ∈ F} w_γ` (2.3); the empty family
contributes `1`. -/
def partitionFn (inc : P → P → Prop) (w : P → ℂ) : ℂ :=
  ∑ F ∈ Finset.univ.filter (IsCompatibleFamily inc), ∏ γ ∈ F, w γ

/-- The edges of the incompatibility graph `I(Γ)` of a tuple `Γ` on `[ℓ]`: unordered pairs of
distinct positions `i, j` with `γ_i ≁ γ_j`. -/
def incEdges (inc : P → P → Prop) {ℓ : ℕ} (Γ : Fin ℓ → P) : Finset (Sym2 (Fin ℓ)) :=
  Finset.univ.filter fun e => ¬ e.IsDiag ∧ ∃ i j : Fin ℓ, e = s(i, j) ∧ inc (Γ i) (Γ j)

/-- The Ursell coefficient (2.4): `φ(Γ) = Σ (−1)^{|F|}` over the edge sets `F ⊆ E(I(Γ))` such
that the spanning graph `([ℓ], F)` is connected. -/
def ursell (inc : P → P → Prop) {ℓ : ℕ} (Γ : Fin ℓ → P) : ℤ :=
  ∑ F ∈ (incEdges inc Γ).powerset.filter
      (fun F : Finset (Sym2 (Fin ℓ)) =>
        (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin ℓ)))).Connected),
    (-1) ^ F.card

/-- The cluster labels: ordered tuples of polymers of length `ℓ' + 1 ≥ 1`, repetitions allowed. -/
abbrev ClusterLabel (P : Type) : Type := Σ ℓ' : ℕ, (Fin (ℓ' + 1) → P)

/-- The term of the cluster series (2.5) for the tuple `Γ` of length `ℓ`:
`φ(Γ)/ℓ! · Π_i w_{γ_i}`. -/
def clusterTerm (inc : P → P → Prop) (w : P → ℂ) (Γ : ClusterLabel P) : ℂ :=
  ((ursell inc Γ.2 : ℤ) : ℂ) / ((Γ.1 + 1).factorial : ℂ) * ∏ i, w (Γ.2 i)

/-- The cluster series `L(w) = Σ_{ℓ ≥ 1} (1/ℓ!) Σ_{(γ_1,…,γ_ℓ) ∈ P^ℓ} φ(γ_1,…,γ_ℓ) Π_i w_{γ_i}`
(2.5), as the sum over all cluster labels (a meaningful value when the terms are absolutely
summable). -/
def clusterSeries (inc : P → P → Prop) (w : P → ℂ) : ℂ := ∑' Γ : ClusterLabel P, clusterTerm inc w Γ

/-- The `ℓ`-th term (`ℓ = ℓ' + 1`) of the pinned sum (2.7):
`1/(ℓ−1)! · Σ_{γ_2,…,γ_ℓ ∈ P} |φ(γ_0, γ_2, …, γ_ℓ)| Π_{i ≥ 2} u_{γ_i}`. -/
def pinnedTerm (inc : P → P → Prop) (u : P → ℝ) (γ0 : P) (ℓ' : ℕ) : ℝ :=
  (1 / (ℓ'.factorial : ℝ)) *
    ∑ tail : Fin ℓ' → P, |((ursell inc (Fin.cons γ0 tail : Fin (ℓ' + 1) → P) : ℤ) : ℝ)| *
      ∏ i, u (tail i)

end

end RandKSATSample.Main


