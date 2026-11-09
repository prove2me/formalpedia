-- Prove2me | Definitions.Def_StochMatchPoly_IsRandMatching
-- name    : StochMatchPoly_IsRandMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:25:48.033854+00:00
-- url     : https://prove2.me/theorems/2c8f0a9e-965b-444b-8b32-cdd2b2f8e747
-- title:
--   Randomized matching algorithms on a stochastic graph: marginals, covariances and expected size
-- statement:
--   Let $G(\omega)$ be the random subgraph of a finite graph $G=(V,E)$ with independent edges of probabilities $q_e$. A **randomized matching algorithm** $\mathcal A$ maps the realized graph $G(\omega)$, using private randomness, to a matching $M=\mathcal A(G(\omega))$ of $G(\omega)$. Equivalently, it is a kernel $\pi$: for each realization $S\subseteq E$, a probability distribution $\pi(S,\cdot)$ on the matchings contained in $S$.
--
--   For a vertex $v$ let $X_v=\mathbf 1\{v\in V(M)\}$. Under the joint law of $(G(\omega),M)$ define
--
--   1. the vertex marginal $\mathbb E X_v$,
--   2. the covariance $\operatorname{Cov}(X_u,X_v)=\mathbb E[X_uX_v]-\mathbb E X_u\,\mathbb E X_v$,
--   3. the expected size $\mathbb E|M|$.
--
--   These are the quantities compared in Lemma 3.1.
--
--   **Formalization Note** The kernel must be a distribution on matchings of $S$ for every $S\subseteq E$, including realizations of probability zero. Every private-randomness algorithm induces such a kernel, and every kernel is realized by a private seed.
-- source:
--   S. Behnezhad, Stochastic Matching with Polynomial Degree, arXiv:2611.03367 (preprint, held version, sha256 409beb43bd8ab862a4a4a595be9c08afd92590790382102cb640d81d9b564017), Lemma 3.1, p.4 (PDF p.5); §4.1 p.9 (PDF p.10)

import Mathlib
import Definitions.Def_StochMatchPoly_mu
import Definitions.Def_StochMatchPoly_edgeLaw

open Classical

namespace StochMatchPoly

/-! # Randomized matching algorithms on a stochastic graph, their marginals and covariances

S. Behnezhad, *Stochastic Matching with Polynomial Degree*, arXiv:2611.03367 (held version,
sha256 409beb43…), Lemma 3.1, p.4 (PDF p.5), and §4.1, p.9.

"For every randomized matching algorithm A … Write M = A(G(ω)), M′ = A′(G(ω)),
X_v = 1{v∈V(M)}, X′_v = 1{v∈V(M′)}." "All sums of covariances indexed by u, v are over ordered
pairs and include the diagonal."

**Formalization Note.** A randomized matching algorithm sees only the realized graph `G(ω)` and
private randomness, and outputs a matching of `G(ω)`. Such an algorithm is exactly a kernel
`π S M`: for each realization `S ⊆ E`, a probability distribution on the matchings `M ⊆ S`
(any private randomness induces such a kernel, and every kernel is realized by a private seed).
Joint expectations are over the realization (independent edges, probabilities `q`) and the
matching drawn from `π S`. The kernel must be a distribution on every `S ⊆ E`, including
realizations of probability zero. `X_v` is `coverInd M v`. -/

variable {V : Type*} [Fintype V]

/-- `π` is a randomized matching algorithm on the random subgraph of the graph with edge set `E`:
for every realization `S ⊆ E`, `π S ·` is a probability distribution supported on the matchings
contained in `S`. -/
def IsRandMatching (E : Finset (Sym2 V)) (π : Finset (Sym2 V) → Finset (Sym2 V) → ℝ) : Prop :=
  ∀ S ⊆ E, (∀ M, 0 ≤ π S M) ∧ (∑ M ∈ S.powerset, π S M = 1) ∧
    ∀ M, π S M ≠ 0 → M ⊆ S ∧ IsMatchingSet M

/-- The coverage indicator `X_v = 1{v ∈ V(M)}`. -/
noncomputable def coverInd (M : Finset (Sym2 V)) (v : V) : ℝ :=
  if v ∈ covered M then 1 else 0

/-- The joint expectation `E f(G(ω), M)` with `M = A(G(ω))`, where `A` has kernel `π`. -/
noncomputable def jointExpect (q : Sym2 V → ℝ) (E : Finset (Sym2 V))
    (π : Finset (Sym2 V) → Finset (Sym2 V) → ℝ) (f : Finset (Sym2 V) → Finset (Sym2 V) → ℝ) : ℝ :=
  ∑ S ∈ E.powerset, edgeWeight q E S * ∑ M ∈ S.powerset, π S M * f S M

/-- The vertex marginal `E X_v = P[v ∈ V(M)]`. -/
noncomputable def marg (q : Sym2 V → ℝ) (E : Finset (Sym2 V))
    (π : Finset (Sym2 V) → Finset (Sym2 V) → ℝ) (v : V) : ℝ :=
  jointExpect q E π fun _ M => coverInd M v

/-- `Cov(X_u, X_v) = E[X_u X_v] − E X_u · E X_v`. -/
noncomputable def covCover (q : Sym2 V → ℝ) (E : Finset (Sym2 V))
    (π : Finset (Sym2 V) → Finset (Sym2 V) → ℝ) (u v : V) : ℝ :=
  jointExpect q E π (fun _ M => coverInd M u * coverInd M v) - marg q E π u * marg q E π v

/-- The expected matching size `E|M|`. -/
noncomputable def expectedSize (q : Sym2 V → ℝ) (E : Finset (Sym2 V))
    (π : Finset (Sym2 V) → Finset (Sym2 V) → ℝ) : ℝ :=
  jointExpect q E π fun _ M => (M.card : ℝ)

end StochMatchPoly


