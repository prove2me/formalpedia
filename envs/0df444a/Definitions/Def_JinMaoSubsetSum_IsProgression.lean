-- Prove2me | Definitions.Def_JinMaoSubsetSum_IsProgression
-- name    : JinMaoSubsetSum_IsProgression
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:39:09.734343+00:00
-- url     : https://prove2.me/theorems/d820a4e2-f08e-456a-a031-450741164b36
-- title:
--   Progressions $f(K\cap\Gamma)$ (Definition 3.3), $s$-proper, and $s$-generating multisets (Definition 3.4)
-- statement:
--   **Definition 3.3.** Let $\Gamma$ be a lattice of rank $d$, $K\subseteq\operatorname{span}(\Gamma)$ an origin-symmetric compact convex set with $\dim\operatorname{span}(K\cap\Gamma)=d$, and $f:\operatorname{span}(\Gamma)\to\mathbb R^k$ linear. The set $f(K\cap\Gamma)$, together with its representation $(K,\Gamma,f)$, is a **progression of rank $d$**. For $s\ge1$ it is **$s$-proper** if $f$ is injective on $sK\cap\Gamma$; proper means $1$-proper.
--
--   **Definition 3.4.** Let $f(K\cap\Gamma)$ be a proper progression and $s\ge 1$. A multiset $X$ of vectors of $K\cap\Gamma$ is **$s$-generating** for $K\cap\Gamma$ if
--   $$
--   \Sigma(X)\supseteq(\tau+sK)\cap\Gamma\quad\text{for some }\tau\in\Gamma .
--   $$
--
--   These notions describe the additive structure extracted from the Conlon–Fox–Pham theorem; a generating sub-multiset guarantees that deep lattice points of a zonotope are subset sums (Lemma 3.5).
--
--   **Formalization Note** The ambient space is $\mathbb R^m$ and $\Gamma$ an additive subgroup required to be discrete. `IsProgression Γ K d` records the conditions on $(\Gamma,K)$; the linear map enters only through `IsSProper f K Γ s` (injectivity on $sK\cap\Gamma$), and a linear map on $\operatorname{span}\Gamma$ is given as one on $\mathbb R^m$ (only its restriction matters). `IsSGenerating K Γ s X` states that $X$ lies in $K\cap\Gamma$ and the displayed containment; properness is a separate hypothesis wherever the notion is used.
-- source:
--   Jin, Mao, Subset Sum in Almost-Linear Time, arXiv:2610.20742v1 (sha256 8b604948862d9188e922b8abf95831fde3a3699e26d39177d20a1460e31a926a), Definitions 3.3 and 3.4, pp.16–17 (PDF pp.18–19)

import Mathlib
import Definitions.Def_JinMaoSubsetSum_subsetSums
import Definitions.Def_JinMaoSubsetSum_zonotope

set_option autoImplicit false

namespace JinMaoSubsetSum

open scoped Pointwise

/-!
# Progressions `f(K ∩ Γ)`, `s`-properness and `s`-generating multisets

Jin, Mao, *Subset Sum in Almost-Linear Time*, arXiv:2610.20742v1, §3.4, pp.16–17.

Definition 3.3 (p.16): "Let Γ be a rank-d lattice, K ⊆ span(Γ) be an origin-symmetric compact
convex set such that dim span(K ∩ Γ) = d, and f : span(Γ) → ℝ^k be a linear map. The set
f(K ∩ Γ) is called a progression of rank d. [...] For s ≥ 1, we say the progression f(K ∩ Γ) is
s-proper if f is injective on sK ∩ Γ. We abbreviate 1-proper to proper. The progression f(K ∩ Γ)
with f being the identity map is simply referred to as K ∩ Γ."

Definition 3.4 (p.17): "Let f(K ∩ Γ) be a proper progression (Definition 3.3). For s ≥ 1, if a
multiset X of vectors in K ∩ Γ satisfies Σ(X) ⊇ (τ + sK) ∩ Γ for some τ ∈ Γ, then we say X is
s-generating for K ∩ Γ, and we also say the multiset f(X) is s-generating for f(K ∩ Γ)."

**Formalization Note.**
* The ambient space is `ℝ^m` (`Fin m → ℝ`); `Γ` is an additive subgroup, required discrete (a
  lattice) with `rankOf Γ = d`, and `K ⊆ span Γ`. The progression's linear map `f` does not enter
  `IsProgression` (any linear `f` on `span Γ` gives a progression of the representation
  `(K, Γ, f)`); a linear map on `span Γ` is given in statements as a linear map on the ambient
  space, of which only the restriction to `span Γ` matters.
* `IsSProper f K Γ s` is injectivity of `f` on `sK ∩ Γ`; `proper` is `s = 1`.
* `IsSGenerating K Γ s X`: every element of `X` lies in `K ∩ Γ` and some `τ ∈ Γ` has
  `(τ + sK) ∩ Γ ⊆ Σ(X)`. The hypothesis of Definition 3.4 that the progression be proper is stated
  separately wherever the notion is used.
-/

/-- Definition 3.3: `K ∩ Γ` (with any linear map on `span Γ`) is a progression of rank `d`. -/
def IsProgression {m : ℕ} (Γ : AddSubgroup (Fin m → ℝ)) (K : Set (Fin m → ℝ)) (d : ℕ) : Prop :=
  DiscreteTopology Γ ∧ rankOf Γ = d ∧
  K ⊆ (Submodule.span ℝ (Γ : Set (Fin m → ℝ)) : Set (Fin m → ℝ)) ∧
  IsOriginSymm K ∧ IsCompact K ∧ Convex ℝ K ∧
  Module.finrank ℝ (Submodule.span ℝ (K ∩ (Γ : Set (Fin m → ℝ)))) = d

/-- Definition 3.3: the progression `f(K ∩ Γ)` is `s`-proper, i.e. `f` is injective on `sK ∩ Γ`. -/
def IsSProper {m : ℕ} {F : Type*} (f : (Fin m → ℝ) → F) (K : Set (Fin m → ℝ))
    (Γ : AddSubgroup (Fin m → ℝ)) (s : ℝ) : Prop :=
  Set.InjOn f ((s • K) ∩ (Γ : Set (Fin m → ℝ)))

/-- Definition 3.4: the multiset `X` of vectors of `K ∩ Γ` is `s`-generating for `K ∩ Γ`:
`Σ(X) ⊇ (τ + sK) ∩ Γ` for some `τ ∈ Γ`. -/
def IsSGenerating {m : ℕ} (K : Set (Fin m → ℝ)) (Γ : AddSubgroup (Fin m → ℝ)) (s : ℝ)
    (X : Multiset (Fin m → ℝ)) : Prop :=
  (∀ x ∈ X, x ∈ K ∧ x ∈ Γ) ∧
  ∃ τ ∈ Γ, ∀ y ∈ Γ, y - τ ∈ s • K → y ∈ subsetSums X

end JinMaoSubsetSum


