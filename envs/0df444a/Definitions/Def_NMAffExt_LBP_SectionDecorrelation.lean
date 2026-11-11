-- Prove2me | Definitions.Def_NMAffExt_LBP_SectionDecorrelation
-- name    : NMAffExt_LBP_SectionDecorrelation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:29:03.534204+00:00
-- url     : https://prove2.me/theorems/b9f9b2f0-d9da-4163-9f1b-feac1aa65648
-- title:
--   $(k,\delta)$ section decorrelation: decorrelation across disjoint affine sections (Definition 4.3)
-- statement:
--   For an affine map $J$ on an affine subspace $A$, an **affine section** of $J|_A$ is an affine map $\sigma:J(A)\to A$ with $J(\sigma(a))=a$ for all $a$; two sections are **disjoint** when their images are disjoint (Definition 2.4).
--
--   **Definition 4.3.** Let $1\le k<n$. A Boolean function $f:\mathbb F_2^n\to\mathbb F_2$ has **$(k,\delta)$ section decorrelation** if for every rank-$k$ linear map $Q:\mathbb F_2^n\to\mathbb F_2^k$ and all affine maps $\sigma,\tau:\mathbb F_2^k\to\mathbb F_2^n$ with
--   $$Q\circ\sigma=Q\circ\tau=\mathrm{id}_{\mathbb F_2^k},\qquad \mathrm{Im}(\sigma)\cap\mathrm{Im}(\tau)=\emptyset,$$
--   one has
--   $$\Bigl|\mathbb E_{a\sim U_k}(-1)^{f(\sigma(a))+f(\tau(a))}\Bigr|\le\delta.$$
--
--   **Formalization Note.** `HasSectionDecorrelation k δ f`; affine maps are the published `QuadExt.Main.IsAffineMap`, "rank $k$" is `finrank (range Q) = k`, disjointness is `Disjoint (Set.range σ) (Set.range τ)`. The predicate is defined for every $k$; the theorems that use it assume $1\le k<n$, the range of Definition 4.3.
-- source:
--   Xin Li, Yan Zhong, Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds, arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 56 (PDF 58), Definition 4.3; p. 20 (PDF 22), Definition 2.4

import Mathlib
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_NMAffExt_LBP_Basic

/-!
# Decorrelation across disjoint affine sections

Xin Li, Yan Zhong, *Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds*,
arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 56 (PDF 58), Definition 4.3;
p. 20 (PDF 22), Definition 2.4 (affine sections, disjoint sections).

"Let 1 ≤ k < n. A Boolean function f : 𝔽₂ⁿ → 𝔽₂ has (k, δ) section decorrelation if, for every
rank-k linear map Q : 𝔽₂ⁿ → 𝔽₂ᵏ and affine maps σ, τ : 𝔽₂ᵏ → 𝔽₂ⁿ satisfying
Q ∘ σ = Q ∘ τ = id, Im(σ) ∩ Im(τ) = ∅, one has |E_{a∼U_k} (−1)^{f(σ(a))+f(τ(a))}| ≤ δ."

Conventions.
* Affine maps are the published `QuadExt.Main.IsAffineMap` (x ↦ ℓ(x) + b over `ZMod 2`).
* "Rank-k" is `finrank (range Q) = k`.
* The definition is made for every `k`; the source states it for `1 ≤ k < n`, and every theorem
  that uses it carries `1 ≤ k < n` as hypotheses.
-/

namespace NMAffExt.LBP

/-- **Definition 4.3.** `f : 𝔽₂ⁿ → 𝔽₂` has `(k, δ)` **section decorrelation**: for every rank-`k`
linear `Q : 𝔽₂ⁿ → 𝔽₂ᵏ` and affine `σ, τ : 𝔽₂ᵏ → 𝔽₂ⁿ` with `Q ∘ σ = Q ∘ τ = id` and disjoint images,
`|E_{a∼U_k} (-1)^{f(σ a) + f(τ a)}| ≤ δ`. -/
def HasSectionDecorrelation {n : ℕ} (k : ℕ) (δ : ℝ) (f : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∀ Q : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2),
    Module.finrank (ZMod 2) (LinearMap.range Q) = k →
    ∀ σ τ : (Fin k → ZMod 2) → (Fin n → ZMod 2),
      QuadExt.Main.IsAffineMap σ → QuadExt.Main.IsAffineMap τ →
      (∀ a, Q (σ a) = a) → (∀ a, Q (τ a) = a) →
      Disjoint (Set.range σ) (Set.range τ) →
      |avg (fun a : Fin k → ZMod 2 => sgn (f (σ a) + f (τ a)))| ≤ δ

end NMAffExt.LBP


