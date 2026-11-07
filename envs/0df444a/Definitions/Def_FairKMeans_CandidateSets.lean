-- Prove2me | Definitions.Def_FairKMeans_CandidateSets
-- name    : FairKMeans_CandidateSets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:06.439448+00:00
-- url     : https://prove2.me/theorems/8a023186-8cbb-4095-a838-bfa322718489
-- title:
--   Candidate sets for weighted centroids $\mathrm{WCS}_\delta(Q)$ and the multiset-means construction
-- statement:
--   Let $Q$ be a finite indexed set in $\mathbb R^d$ and $\delta\in(0,1]$. A finite family $W$ is a **candidate set for weighted centroids** of $Q$ with accuracy $\delta$ if every choice of nonnegative weights $\mu(q)$ admits $t\in W$ with
--
--   $$\sum_{q\in Q}\mu(q)\|q-t\|^2\le(1+\delta)\min_{c\in\mathbb R^d}\sum_{q\in Q}\mu(q)\|q-c\|^2. \tag{17}$$
--
--   The mission fixes $\mathrm{WCS}_\delta(Q)$ to the set of Lemma 15, part 2: the means $\frac1r\sum_{\ell=1}^r q_{f(\ell)}$ of all multisets of $r=\lceil 1/\delta\rceil$ points of $Q$. Building it from $|Q|$ points is charged $|Q|^r\cdot r\cdot d$ arithmetic operations.
--
--   Algorithm 1 takes all its candidate centers from such sets.
--
--   **Formalization Note** The means are indexed by the $|Q|^r$ ordered $r$-tuples of indices, which contain every $r$-multiset, re-indexed to `Fin (|Q|^r)`. The minimum in (17) is a real infimum over $\mathbb R^d$; it is attained at the $\mu$-weighted centroid. The paper uses the set of part 2 when $d$ is part of the input and notes that part 2 alone suffices for polynomial time (p.20); the mission uses it in every dimension.
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Definition 14, (17), and Lemma 15, part 2, p.20 (PDF p.22); Appendix A, pp.49–50 (PDF pp.51–52)

import Mathlib
import Definitions.Def_FairKMeans_Model

namespace FairKMeans

/-!
# Candidate sets for weighted centroids and the multiset-means construction

Cheng–Mo–Song–Ding, arXiv:2609.07974 (held version, sha256 73e9312c…), Definition 14, (17),
p.20 (PDF 22); Lemma 15, part 2, p.20 (PDF 22) and its proof in Appendix A, pp.49–50
(PDF 51–52).

**Formalization Note.** A finite indexed set is a family `Q : Fin q → E d`, a candidate set a
family `W : Fin w → E d`. The minimum `min_{c ∈ ℝ^d}` of (17) is written `⨅ c`; the index type is
nonempty, the function is bounded below by `0` for `μ ≥ 0`, and the minimum is attained at the
μ-weighted centroid (p.20), so `⨅` is the paper's minimum. `WCS_δ(Q)` is fixed to the set of
Lemma 15, part 2 in every dimension (p.20: "Part 2 alone would therefore suffice for a polynomial
running time"): the means of all multisets of `r = ⌈1/δ⌉` points of `Q`, indexed by the ordered
`r`-tuples `Fin r → Fin q` (there are `q^r` of them; every `r`-multiset is the image of a tuple,
so the family contains the mean of every multiset and nothing else), re-indexed to
`Fin (q ^ r)` by `finFunctionFinEquiv`.
-/

variable {d : ℕ}

/-- `W` is a candidate set for weighted centroids of `Q` with accuracy `δ` (Definition 14, (17)):
every choice of nonnegative weights `μ` admits `t ∈ W` with
`∑_q μ(q)‖q − t‖² ≤ (1+δ) min_c ∑_q μ(q)‖q − c‖²`. -/
def IsWCS {q w : ℕ} (δ : ℝ) (Q : Fin q → E d) (W : Fin w → E d) : Prop :=
  ∀ μ : Fin q → ℝ, (∀ i, 0 ≤ μ i) →
    ∃ t : Fin w, ∑ i, μ i * ‖Q i - W t‖ ^ 2 ≤ (1 + δ) * ⨅ c : E d, ∑ i, μ i * ‖Q i - c‖ ^ 2

/-- The multiset size `r = ⌈1/δ⌉` of Lemma 15, part 2. -/
noncomputable def wcsR (δ : ℝ) : ℕ := ⌈1 / δ⌉₊

/-- The mean `(1/r) ∑_ℓ Q(f ℓ)` of the multiset of `r` points selected by the tuple `f`. -/
noncomputable def multisetMeans {q : ℕ} (r : ℕ) (Q : Fin q → E d) : (Fin r → Fin q) → E d :=
  fun f => (1 / (r : ℝ)) • ∑ ℓ, Q (f ℓ)

/-- `WCS_δ(Q)`: the set of Lemma 15, part 2 (means of all multisets of `⌈1/δ⌉` points of `Q`),
as a family of `q ^ ⌈1/δ⌉` points. -/
noncomputable def wcs {q : ℕ} (δ : ℝ) (Q : Fin q → E d) : Fin (q ^ wcsR δ) → E d :=
  fun i => multisetMeans (wcsR δ) Q (finFunctionFinEquiv.symm i)

/-- The operation charge for building `WCS_δ(Q)` in `ℝ^d` from `q` points: `q^r · r · d`
(`r − 1` vector additions and one scaling, `r·d` operations, per mean; Lemma 15, part 2:
"computed in `O(n^r r d)` time"). -/
noncomputable def wcsCharge (q : ℕ) (δ : ℝ) (d : ℕ) : ℕ := q ^ wcsR δ * wcsR δ * d

end FairKMeans


