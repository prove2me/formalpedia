-- Prove2me | Definitions.Def_PolyContract_IsComb
-- name    : PolyContract_IsComb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:50:54.536221+00:00
-- url     : https://prove2.me/theorems/8b359c50-cc0f-42d4-8d12-5b1ad03f3d85
-- title:
--   Combs (Def. C.1), perturbed powers of 8 (Def. C.5), contact sets and subset sums
-- statement:
--   Let $\Gamma\subseteq[0,\infty)$ be finite, $L(\alpha)=p+q\alpha$ affine and $\kappa,\delta>0$. An instance is a **comb** with contact set $\Gamma$, line $L$, dip $\kappa$ and width $\delta$ if $r(x^\star(\gamma))=L(\gamma)$ for $\gamma\in\Gamma$ and
--   $$L(\alpha)-r(x^\star(\alpha))\ge\kappa\min\{\operatorname{dist}(\alpha,\Gamma),\delta\}\quad\text{for all }\alpha\ge0,$$
--   where $\operatorname{dist}(\alpha,\emptyset):=\infty$.
--
--   The module also defines the set $\mathcal F$ of **perturbed powers of 8** — the vectors $\mu\in\mathbb Z^k_{>0}$, $k\ge1$, for which some integer $H\ge1$ has $H8^{i-1}\le\mu_i<\tfrac{11}{10}H8^{i-1}$ for $i\in[k]$ — the subset sums $\mu^\top\chi$ for $\chi\in\{0,1\}^k$, the contact sets $\{\delta(N+\chi^\top\mu):\chi\in\{0,1\}^k\}$, Subset Sum yes-instances, and the vectors $\mu_i:=H8^{i-1}+a_i$, $\mu'_i:=H8^{i-1}$ with $H:=10\sum_ia_i+1$ of Lemma C.7.
--
--   **Formalization Note** $\operatorname{dist}(\alpha,\emptyset)=\infty$ is implemented by taking the minimum to be $\delta$ when $\Gamma=\emptyset$. Vectors are lists of naturals indexed from $0$, so $\mu_i$ is the entry at index $i-1$; selections $\chi$ are lists of booleans of the same length.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Definition C.1, p.48 (PDF p.49); Definition C.5, p.51; Theorem C.6 and Lemma C.7, p.52

import Mathlib
import Definitions.Def_PolyContract_QuadInstance

set_option autoImplicit false

namespace PolyContract

open Classical in
/-- `min{dist(α, Γ), δ}` with the convention `dist(α, ∅) := ∞` (Klimm, Lippke, Warode,
arXiv:2611.04934, version of November 3, 2026, sha256 18cfc0a5…, Definition C.1, p.48).

**Formalization Note** Mathlib's `Metric.infDist α ∅` is `0`; the paper's `dist(α, ∅) = ∞` makes
the minimum equal to `δ`, which is the value taken here for `Γ = ∅`. -/
noncomputable def combDist (Γ : Set ℝ) (δ α : ℝ) : ℝ :=
  if Γ = ∅ then δ else min (Metric.infDist α Γ) δ

/-- A **comb** (arXiv:2611.04934, Definition C.1, p.48): "Let `Γ ⊆ [0, ∞)` be finite,
`L(α) = p + qα` affine, and `κ, δ > 0`. An instance is a comb with contact set `Γ`, line `L`, dip
`κ`, and width `δ` if `r(x⋆(γ)) = L(γ)` for `γ ∈ Γ` and
`L(α) − r(x⋆(α)) ≥ κ min{dist(α, Γ), δ}` for all `α ≥ 0`, where `dist(α, ∅) := ∞`."

**Formalization Note** `r(x⋆(α))` is `brReward`, the reward under the best response with the
principal-favouring tie rule. The side conditions on `Γ`, `κ`, `δ` are part of the predicate. -/
def IsComb {ι : Type} [Fintype ι] [DecidableEq ι] (I : QuadInstance ι) (Γ : Set ℝ)
    (p q κ δ : ℝ) : Prop :=
  Γ.Finite ∧ Γ ⊆ Set.Ici 0 ∧ 0 < κ ∧ 0 < δ ∧ (∀ γ ∈ Γ, I.brReward γ = p + q * γ) ∧
    ∀ α : ℝ, 0 ≤ α → κ * combDist Γ δ α ≤ p + q * α - I.brReward α

/-- The **perturbed powers of 8** `F` (arXiv:2611.04934, Definition C.5, p.51): the vectors
`µ ∈ ℤ^k_{>0}`, `k ≥ 1`, for which there is an integer `H ≥ 1` with
`H 8^{i−1} ≤ µ_i < (11/10) H 8^{i−1}` for `i ∈ [k]`.

**Formalization Note** `µ` is a list of natural numbers, indexed from `0`, so the bound for the
entry at index `i` is `H 8^i ≤ µ[i]` and `10 µ[i] < 11 H 8^i` (the upper bound multiplied by
`10`, in exact integer arithmetic). -/
def PerturbedPow8 (μ : List ℕ) : Prop :=
  μ ≠ [] ∧ (∀ x ∈ μ, 0 < x) ∧
    ∃ H : ℕ, 1 ≤ H ∧ ∀ (i : ℕ) (h : i < μ.length), H * 8 ^ i ≤ μ[i] ∧ 10 * μ[i] < 11 * H * 8 ^ i

/-- The subset sum `µ⊤χ` of a vector `µ` for a selection `χ ∈ {0, 1}^k`, given as a list of
booleans of the same length (arXiv:2611.04934, App. C.3, p.52). -/
def selSum (μ : List ℕ) (χ : List Bool) : ℕ :=
  ((μ.zip χ).map fun p => if p.2 then p.1 else 0).sum

/-- The contact set `{δ(N + χ⊤µ) : χ ∈ {0, 1}^k}` of Theorem C.6 and Lemma C.7
(arXiv:2611.04934, p.52). -/
def contacts (δ : ℝ) (N : ℤ) (μ : List ℕ) : Set ℝ :=
  {γ | ∃ χ : List Bool, χ.length = μ.length ∧ γ = δ * ((N : ℝ) + (selSum μ χ : ℝ))}

/-- `(a, T)` is a **yes-instance** of Subset Sum (arXiv:2611.04934, App. C.3, p.52): some
`χ ∈ {0, 1}^k` has `a⊤χ = T`. -/
def IsYesInstance (a : List ℕ) (T : ℤ) : Prop :=
  ∃ χ : List Bool, χ.length = a.length ∧ (selSum a χ : ℤ) = T

/-- `H := 10 Σ_i a_i + 1` (arXiv:2611.04934, Lemma C.7, p.52). -/
def lemmaC7H (a : List ℕ) : ℕ := 10 * a.sum + 1

/-- `µ_i := H 8^{i−1} + a_i` for `i ∈ [k]` (arXiv:2611.04934, Lemma C.7, p.52), indexed from `0`. -/
def itemWeights (a : List ℕ) : List ℕ := a.mapIdx fun i ai => lemmaC7H a * 8 ^ i + ai

/-- `µ′_i := H 8^{i−1}` for `i ∈ [k]` (arXiv:2611.04934, Lemma C.7, p.52), indexed from `0`. -/
def baseWeights (a : List ℕ) : List ℕ := a.mapIdx fun i _ => lemmaC7H a * 8 ^ i

end PolyContract


