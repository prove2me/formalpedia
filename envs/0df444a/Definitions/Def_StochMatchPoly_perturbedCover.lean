-- Prove2me | Definitions.Def_StochMatchPoly_perturbedCover
-- name    : StochMatchPoly_perturbedCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:25:59.44662+00:00
-- url     : https://prove2.me/theorems/2202f848-e197-4218-9d47-dfaa556bc2a0
-- title:
--   Generic weights, optimal covered sets $S(G,w)$, the perturbed optimum $M^\theta$, $m_v(\theta)$, $F(\theta)$ and $\Psi(\theta)$
-- statement:
--   Let $G=(V,E)$ be a finite graph and $w\in\mathbb R^V$ a vertex weight vector (weights may be negative). The **score** of a matching $L$ is $\sum_{v\in V(L)}w_v$. The weight vector is **generic** if distinct vertex subsets have distinct weight sums. A set $T$ is an **optimal covered set** if $T=V(L)$ for a matching $L$ of $G$ maximizing the score over all matchings, the empty one included; for generic $w$ it is unique and is denoted $S(G,w)$.
--
--   Fix offsets $\theta\in\mathbb R^V$ and let $\xi_v\sim\mathrm{Unif}[-1,1]$ be independent for each vertex and independent of the edge realization $G(\omega)$. In $G(\omega)$ let $M^\theta$ be the (almost surely unique) matching maximizing the score under $w_v=\theta_v+\xi_v$, and $X^\theta_v=\mathbf 1\{v\in V(M^\theta)\}$. Define
--
--   $$m_v(\theta)=\mathbb E X^\theta_v,\qquad F(\theta)=\mathbb E\max_L\sum_{u\in V(L)}(\theta_u+\xi_u),\qquad \Psi(\theta)=F(\theta)-\sum_u\theta_u s_u,$$
--
--   for a target vector $s\in\mathbb R^V$, and $\operatorname{Cov}(X^\theta_u,X^\theta_v)$ under the joint law of $(G(\omega),\xi)$.
--
--   These objects carry the proof of Lemma 3.1: stability (Lemma 3.2), the covariance bound (7) and the calibration of the offsets (Lemma 3.3).
--
--   **Formalization Note** $X^\theta_v$ is defined for every realization and perturbation without choosing a maximizer: it is $1$ iff some matching covering $v$ scores strictly more than every matching not covering $v$. For generic weights this is exactly $\mathbf 1\{v\in S(G(\omega),\theta+\xi)\}$, and $\theta+\xi$ is generic outside a null set. The law of $\xi$ is $2^{-|V|}$ times Lebesgue measure on $[-1,1]^V$. $F(\theta)$ is the expected optimal score, a maximum over finitely many matchings.
-- source:
--   S. Behnezhad, Stochastic Matching with Polynomial Degree, arXiv:2611.03367 (preprint, held version, sha256 409beb43bd8ab862a4a4a595be9c08afd92590790382102cb640d81d9b564017), §3.1 p.5 (PDF p.6); §3.2 p.5 (PDF p.6); §3.3 p.7, eq. (10) (PDF p.8)

import Mathlib
import Definitions.Def_StochMatchPoly_mu
import Definitions.Def_StochMatchPoly_edgeLaw

open Classical MeasureTheory

namespace StochMatchPoly

/-! # Vertex-weighted matchings and their random perturbations (§3)

S. Behnezhad, *Stochastic Matching with Polynomial Degree*, arXiv:2611.03367 (held version,
sha256 409beb43…), §3.1 p.5 (generic weights, `S(G, w)`), §3.2 p.5 (`M^θ`, `X^θ`), §3.3 p.7
(`m_v(θ)`, the score `W_θ(L)`, `F(θ)` and `Ψ(θ)` of (10)).

"We say a weight vector w ∈ ℝ^V is generic if distinct vertex subsets have distinct weight sums.
Note that for generic w, every matching L maximizing Σ_{v∈V(L)} w_v has the same covered set. We
denote this set by S(G, w). The optimization is over all matchings, including the empty matching;
it has no additional cardinality constraint. Weights may be negative."
"Let θ ∈ ℝ^V be deterministically fixed, and let ξ_v ∼ Unif[−1, 1] be chosen independently for
each vertex and also of ω. In G(ω) choose the (unique) matching M^θ maximizing the sum of
covered-vertex weights w_v = θ_v + ξ_v. Let X^θ_v := 1{v∈V(M^θ)} be the indicator that vertex v
is matched." "m_v(θ) := E X^θ_v". "W_θ(L) := Σ_{u∈V(L)} (θ_u + ξ_u) … F(θ) := E W_θ(M^θ),
Ψ(θ) := F(θ) − Σ_u θ_u s_u."

**Formalization Note.**
1. `IsOptCovered E w T` says that `T` is the covered set of some matching `L ⊆ E` that maximizes
   `Σ_{v∈V(L)} w_v` over all matchings in `E`, the empty one included. For generic `w` this set is
   unique and is `S(G, w)`.
2. `M^θ` is unique only for generic weights, which `θ + ξ` is almost surely. The indicator
   `X^θ_v` is defined on every realization and every perturbation, without a choice of
   maximizer: `coverIndicator S w v = 1` iff some matching of `S` covering `v` has a strictly
   larger score than every matching of `S` not covering `v`. For generic `w` this is exactly
   `1{v ∈ S(S, w)}`; it differs from the paper's `X^θ` only on ties, a null set. It is a
   measurable function of `ξ` (finitely many strict comparisons of linear functions).
3. The perturbation law `ξ ∼ Unif[−1, 1]^V` is `(1/2)^{|V|}` times Lebesgue measure on the cube
   `[−1, 1]^V`, a probability measure, independent of the edge realization. Expectations over
   (realization, ξ) are the finite edge-law sum of Bochner integrals over `ξ`.
4. `F(θ) = E W_θ(M^θ)` is the expectation of the optimal score `max_L W_θ(L)`, a maximum over the
   finite nonempty family of matchings of the realization; it needs no choice of maximizer.
5. `Ψ` takes the target vector `s` as an explicit argument. -/

variable {V : Type*} [Fintype V]

/-- The weight vector `w` is generic: distinct vertex subsets have distinct weight sums. -/
def IsGeneric (w : V → ℝ) : Prop :=
  ∀ A B : Finset V, A ≠ B → ∑ v ∈ A, w v ≠ ∑ v ∈ B, w v

/-- The covered-vertex score `Σ_{v∈V(L)} w_v` of an edge set `L`. -/
noncomputable def coverScore (w : V → ℝ) (L : Finset (Sym2 V)) : ℝ :=
  ∑ v ∈ covered L, w v

/-- `T` is an optimal covered set of the graph with edge set `E` under the vertex weights `w`:
the covered set of a matching `L ⊆ E` maximizing `Σ_{v∈V(L)} w_v` among all matchings `L' ⊆ E`
(the empty matching included). For generic `w` it is unique, and is the paper's `S(G, w)`. -/
def IsOptCovered (E : Finset (Sym2 V)) (w : V → ℝ) (T : Finset V) : Prop :=
  ∃ L ⊆ E, IsMatchingSet L ∧ covered L = T ∧
    ∀ L' ⊆ E, IsMatchingSet L' → coverScore w L' ≤ coverScore w L

/-- The optimal score `max_{L ⊆ S matching} Σ_{v∈V(L)} w_v` (the empty matching is admissible). -/
noncomputable def optScore (S : Finset (Sym2 V)) (w : V → ℝ) : ℝ :=
  (S.powerset.filter IsMatchingSet).sup'
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset S, by simp [IsMatchingSet]⟩⟩
    (coverScore w)

/-- The coverage indicator of the optimal matching of the realization `S` under the weights `w`:
`1` iff some matching of `S` covering `v` scores strictly more than every matching of `S` not
covering `v`. For generic `w` it is `1{v ∈ V(M)}` for the unique optimal matching `M`. -/
noncomputable def coverIndicator (S : Finset (Sym2 V)) (w : V → ℝ) (v : V) : ℝ :=
  if ∃ L ⊆ S, IsMatchingSet L ∧ v ∈ covered L ∧
      ∀ L' ⊆ S, IsMatchingSet L' → v ∉ covered L' → coverScore w L' < coverScore w L
  then 1 else 0

/-- The law of the perturbation vector `ξ`, with independent coordinates `ξ_v ∼ Unif[−1, 1]`:
`(1/2)^{|V|}` times Lebesgue measure on the cube `[−1, 1]^V`. -/
noncomputable def xiLaw (V : Type*) [Fintype V] : Measure (V → ℝ) :=
  ((2 : ENNReal)⁻¹) ^ Fintype.card V •
    Measure.pi fun _ : V => (volume : Measure ℝ).restrict (Set.Icc (-1) 1)

/-- The expectation over the edge realization `S` (independent edges with probabilities `q` on
`E`) and the independent perturbation `ξ ∼ Unif[−1, 1]^V`. -/
noncomputable def pertExpect (q : Sym2 V → ℝ) (E : Finset (Sym2 V))
    (f : Finset (Sym2 V) → (V → ℝ) → ℝ) : ℝ :=
  ∑ S ∈ E.powerset, edgeWeight q E S * ∫ ξ, f S ξ ∂(xiLaw V)

/-- The vertex marginal `m_v(θ) = E X^θ_v = P[v ∈ V(M^θ)]`. -/
noncomputable def mθ (q : Sym2 V → ℝ) (E : Finset (Sym2 V)) (θ : V → ℝ) (v : V) : ℝ :=
  pertExpect q E fun S ξ => coverIndicator S (θ + ξ) v

/-- `Cov(X^θ_u, X^θ_v)`. -/
noncomputable def covθ (q : Sym2 V → ℝ) (E : Finset (Sym2 V)) (θ : V → ℝ) (u v : V) : ℝ :=
  pertExpect q E (fun S ξ => coverIndicator S (θ + ξ) u * coverIndicator S (θ + ξ) v) -
    mθ q E θ u * mθ q E θ v

/-- The expected optimal score `F(θ) = E W_θ(M^θ) = E max_L Σ_{u∈V(L)} (θ_u + ξ_u)` of (10). -/
noncomputable def Fθ (q : Sym2 V → ℝ) (E : Finset (Sym2 V)) (θ : V → ℝ) : ℝ :=
  pertExpect q E fun S ξ => optScore S (θ + ξ)

/-- The potential `Ψ(θ) = F(θ) − Σ_u θ_u s_u` of (10), for the target vector `s`. -/
noncomputable def Ψ (q : Sym2 V → ℝ) (E : Finset (Sym2 V)) (s θ : V → ℝ) : ℝ :=
  Fθ q E θ - ∑ u, θ u * s u

end StochMatchPoly


