-- Prove2me | Definitions.Def_MinSumFPT_labD
-- name    : MinSumFPT_labD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:58.372903+00:00
-- url     : https://prove2.me/theorems/389cf7cb-6415-411b-86dc-9357bf29e29e
-- title:
--   Stage 2: close, middle and far points, the redirected points $C_j^{\mapsto}$ and the clustering $\mathcal D$
-- statement:
--   Fix a clustering $\sigma$ with clusters $C_0,\dots,C_{k-1}$, estimates as in Hypothesis 1 with $\alpha=5$, and $0<\beta<1$. Let $\widehat{\widehat{\Delta}}_{C_i}$ be the threshold (13). Then:
--
--   - $C_i^{\mathrm{cls}}$ is the set of points that are $\beta^{-2}$-close for $C_i$;
--   - $C_i^{\mathrm{far}}$ is the set of points that are $\beta^{-7}$-far for $C_i$;
--   - $C_i^{\mathrm{mid}}=A\setminus(C_i^{\mathrm{cls}}\cup C_i^{\mathrm{far}})$.
--
--   A point $p\in C_j$ is **redirected**, $p\in C_j^{\mapsto}$, if $p\in C_j^{\mathrm{far}}$ and $p\in C_i^{\mathrm{cls}}$ for some $i$ with $\widehat{|C_i|}\ge\beta^4\widehat{|C_j|}$. A **redirection map** $g$ sends every redirected $p\in C_j$ to such a cluster: $\widehat{|C_j|}\le\beta^{-4}\widehat{|C_{g(p)}|}$ and $p\in C_{g(p)}^{\mathrm{cls}}$. The clustering $\mathcal D=\{D_1,\dots,D_k\}$ moves every redirected point to its target cluster:
--
--   $$
--   D_i=(C_i\setminus C_i^{\mapsto})\cup g^{-1}(i).
--   $$
--
--   Lemma 13 shows that $\mathcal D$ is near-optimal when $\sigma$ is optimal. $\mathcal D$ is the reference clustering against which the Stage 2 assignment is analyzed.
--
--   **Formalization Note** A redirected point belongs to its own cluster, so $\mathcal D$ is the labelling that sends a redirected point $p$ to $g(p)$ and keeps every other point's label.
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), §2.4, Eq. (13) and the definitions of C^cls, C^far, C^mid, C_j^↦, g and 𝒟, p.19

import Mathlib
import Definitions.Def_MinSumFPT_IsFar
import Definitions.Def_MinSumFPT_Hyp1

open scoped Classical

namespace MinSumFPT

/-!
# Stage 2: close, middle and far points; the redirected points C_j^↦; the clustering 𝒟

Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation
Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256
12e81235…), §2.4, p.19: Δ̂̂_{C_i} of (13); C^cls (β⁻²-close points), C^far (β⁻⁷-far points),
C^mid = A ∖ (C^cls ∪ C^far), C^{¬far} = C^cls ∪ C^mid; C_j^↦ = {p ∈ C_j ∩ C_j^far : ∃ i,
|Ĉ_i| ≥ β⁴|Ĉ_j| ∧ p ∈ C_i^cls}; an arbitrary redirection map g with |Ĉ_j| ≤ β⁻⁴|Ĉ_i| and p ∈ C_i^cls;
D_i = (C_i ∖ C_i^↦) ∪ C_{i↦}.

This module bundles `dblHat`, `IsFarFor`, `clsSet`, `farSet`, `midSet`, `IsSource`, `IsRedirection`
and `labD` (the construction of 𝒟).

**Formalization Note.** α = 5 throughout §2.4, so Δ̂̂_{C_i} = `farThreshold k ε 5 γ ÔPT |Ĉ_i| Δ̂_i`
and "p is s-far for C_i" is `IsFar … s (µ̂_i) |Ĉ_i| Δ̂_i p` (Definition 4 with α = 5). Clusters are
labels `Fin k` of the labelling `σ`. Since the clusters partition A, `p ∈ C_j^↦` can only hold for
`j = σ p`, so 𝒟 is the labelling `labD`: a source point goes to `g p`, every other point keeps
`σ p`. `g` is a total function whose values matter on the source points only. -/

/-- `Δ̂̂_{C_i}` of (13): `ε(1+γ)²ÔPT/(20k|Ĉ_i|²) + 5Δ̂_{C_i}`. -/
noncomputable def dblHat {n k : ℕ} (ε γ : ℝ) (E : Estimates n k) (i : Fin k) : ℝ :=
  farThreshold k ε 5 γ E.optHat (E.chat i) (E.deltaHat i)

/-- `p` is `s`-far for `C_i` (Definition 4 with α = 5): `‖e_p − e_{µ̂_i}‖_{W₁} ≥ s ⋅ Δ̂̂_{C_i}`. -/
def IsFarFor {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ : ℝ) (E : Estimates n k) (s : ℝ) (i : Fin k)
    (p : Fin n) : Prop :=
  IsFar d k ε 5 γ E.optHat s (E.muHat i) (E.chat i) (E.deltaHat i) p

/-- `C_i^cls`: the points that are β⁻²-close for `C_i`. -/
noncomputable def clsSet {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (i : Fin k) : Finset (Fin n) :=
  Finset.univ.filter (fun p => ¬ IsFarFor d ε γ E (β⁻¹ ^ 2) i p)

/-- `C_i^far`: the points that are β⁻⁷-far for `C_i`. -/
noncomputable def farSet {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (i : Fin k) : Finset (Fin n) :=
  Finset.univ.filter (fun p => IsFarFor d ε γ E (β⁻¹ ^ 7) i p)

/-- `C_i^mid = A ∖ (C_i^cls ∪ C_i^far)`. -/
noncomputable def midSet {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (i : Fin k) : Finset (Fin n) :=
  Finset.univ \ (clsSet d ε γ β E i ∪ farSet d ε γ β E i)

/-- `p ∈ C_{σ p}^↦`: `p` is β⁻⁷-far for its own cluster and β⁻²-close for some cluster `i` with
`|Ĉ_i| ≥ β⁴ |Ĉ_{σ p}|`. -/
def IsSource {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (σ : Fin n → Fin k) (p : Fin n) : Prop :=
  p ∈ farSet d ε γ β E (σ p) ∧ ∃ i, β ^ 4 * E.chat (σ p) ≤ E.chat i ∧ p ∈ clsSet d ε γ β E i

/-- `g` is a redirection map: every source point `p` goes to a cluster `i = g p` with
`|Ĉ_{σ p}| ≤ β⁻⁴ |Ĉ_i|` and `p ∈ C_i^cls`. -/
def IsRedirection {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (σ : Fin n → Fin k) (g : Fin n → Fin k) : Prop :=
  ∀ p, IsSource d ε γ β E σ p →
    E.chat (σ p) ≤ β⁻¹ ^ 4 * E.chat (g p) ∧ p ∈ clsSet d ε γ β E (g p)

/-- The clustering 𝒟 = {D_1, …, D_k}, `D_i = (C_i ∖ C_i^↦) ∪ C_{i↦}`, as a labelling. -/
noncomputable def labD {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (σ : Fin n → Fin k) (g : Fin n → Fin k) (p : Fin n) : Fin k :=
  if IsSource d ε γ β E σ p then g p else σ p

end MinSumFPT


