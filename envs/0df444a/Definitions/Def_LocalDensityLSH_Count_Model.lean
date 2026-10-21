-- Prove2me | Definitions.Def_LocalDensityLSH_Count_Model
-- name    : LocalDensityLSH_Count_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:28.964289+00:00
-- url     : https://prove2.me/theorems/04ef2570-5883-4f5b-91ae-8d14a9b4f8bf
-- title:
--   §3, §4, pp. 3–12 — data on the unit sphere, 𝒜q, t-bit hash tables, buckets at Hamming distance ℐ, and the collision probabilities p(x), p(x,y)
-- statement:
--   This file sets up the model of *LSH Count* (Wu, Charikar and Natchu, §3–§4).
--
--   **Data and query.** The dataset $\mathcal D$ consists of $n$ vectors $v_1,\dots,v_n\in\mathbb R^d$ and the query is $q\in\mathbb R^d$; in the paper all of them lie on the unit sphere. For a set $\mathcal A\subseteq\mathbb R$ of angles of interest,
--   $$\mathcal A_q=\{\,i : \theta_{q v_i}\in\mathcal A\,\},\qquad \theta_{qx}=\arccos(q\cdot x),$$
--   is the set of data points within angle $\mathcal A$ of $q$. The dataset is indexed, so repeated vectors are counted separately, and $|\mathcal A_q|$ is the quantity to be estimated.
--
--   **Hash tables.** A hash function $g:\mathbb R^d\to\{0,1\}^t$ stores each $v_i$ in the bucket $g(v_i)$; the query's bucket is $g(q)$. The estimator only ever looks at the codes $(g(v_1),\dots,g(v_n),g(q))$, so a *table* is such a tuple of $n+1$ codes in $\{0,1\}^t$. A *hash law* $\mu$ is a probability measure on tables: the law of the codes for one random $g$ (for random-hyperplane LSH, $g$ is given by $t$ independent Gaussian hyperplanes).
--
--   **Buckets at Hamming distance $\mathcal I$.** For a finite set $\mathcal I\subseteq\mathbb N$ of Hamming distances, $v_i$ lies in $\mathcal B_q(\mathcal I)$ in a table $\tau$ when the Hamming distance between $g(v_i)$ and $g(q)$ belongs to $\mathcal I$.
--
--   **Collision probabilities.** Computed from the hash law $\mu$,
--   $$p(x)=\mu\big(x\in\mathcal B_q(\mathcal I)\big),\qquad p(x,y)=\mu\big(x\in\mathcal B_q(\mathcal I)\ \text{and}\ y\in\mathcal B_q(\mathcal I)\big),$$
--   so that $p(x,x)=p(x)$. For a nonempty set $\mathcal A_q$, $\min_{x\in\mathcal A_q}p(x)$ is written $p_{\min}$, and
--   $$\mathbb E(C_q(\mathcal I))=\sum_{y\in\mathcal D}p(y)$$
--   is the expected number of data points in the probed buckets of one table.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Data points are indexed by `Fin n`, vectors live in `EuclideanSpace ℝ (Fin d)`, and the angle is `InnerProductGeometry.angle q (v i)`, which equals $\arccos\langle q,v_i\rangle$ for unit vectors. A table is `(Fin n → Fin t → Bool) × (Fin t → Bool)`. The paper writes $p(x)$ as a function of the angle $\theta_{qx}$ because, for random-hyperplane LSH, it depends only on that angle. Here $p$ and $p(x,y)$ are defined from an arbitrary hash law $\mu$; this generalizes the paper, whose proofs use only that $p(x)$ is the probability that $x$ lands in $\mathcal B_q(\mathcal I)$ for one random table. Probabilities are `μ.real`.
-- source:
--   Wu, Charikar & Natchu, Local Density Estimation in High Dimensions, arXiv:1809.07471v1, §3, pp. 3–5 (𝒜q, θ_qx, p(x)); §4, p. 9 (hash tables, ℬ^k_q(ℐ)); p. 10 (p(x, y)); p. 6 and proof of Lemma 6, p. 17 (𝔼(C_q(ℐ)))

import Mathlib

namespace LocalDensityLSH.Count

open MeasureTheory

/-- The content of one `t`-bit hash table, as seen by the estimator (Wu–Charikar–Natchu, §4,
p. 9): the codes `g(v₁), …, g(vₙ) ∈ {0,1}ᵗ` of the `n` data points and the code `g(q)` of the
query, for one hash function `g`. -/
abbrev Table (n t : ℕ) := (Fin n → Fin t → Bool) × (Fin t → Bool)

/-- `InBucket I τ i`: in the table `τ`, the data point `vᵢ` lies in a bucket at Hamming distance
in `I` from the query's bucket, i.e. `vᵢ ∈ ℬ_q(ℐ)` (pp. 9, 12). -/
def InBucket {n t : ℕ} (I : Finset ℕ) (τ : Table n t) (i : Fin n) : Prop :=
  hammingDist (τ.1 i) τ.2 ∈ I

instance {n t : ℕ} (I : Finset ℕ) (τ : Table n t) (i : Fin n) : Decidable (InBucket I τ i) := by
  unfold InBucket; infer_instance

/-- `𝒜q` (§3, p. 3): the indices `i` of the data vectors `vᵢ` whose angle to the query `q`,
`θ_{q vᵢ} = arccos ⟪q, vᵢ⟫` for unit vectors, lies in the range of interest `A`. The dataset is
indexed, so repeated vectors are counted separately. -/
noncomputable def Aq {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)) (q : EuclideanSpace ℝ (Fin d))
    (A : Set ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => InnerProductGeometry.angle q (v i) ∈ A)

/-- The collision probability `p(x)` (p. 5, p. 10): the probability, under the hash law `μ`
(the law of one random table), that `vᵢ` lands at Hamming distance `ℐ` from `q`. -/
noncomputable def p {n t : ℕ} (μ : Measure (Table n t)) (I : Finset ℕ) (i : Fin n) : ℝ :=
  μ.real {τ | InBucket I τ i}

/-- The joint collision probability `p(x, y)` (p. 10): the probability, under `μ`, that both
`vᵢ` and `vⱼ` land at Hamming distance `ℐ` from `q`. Note `p2 μ I i i = p μ I i`. -/
noncomputable def p2 {n t : ℕ} (μ : Measure (Table n t)) (I : Finset ℕ) (i j : Fin n) : ℝ :=
  μ.real {τ | InBucket I τ i ∧ InBucket I τ j}

/-- `min_{x ∈ 𝒜q} p(x)`, taken over a nonempty finite set of indices. -/
noncomputable def pmin {n t : ℕ} (μ : Measure (Table n t)) (I : Finset ℕ) {s : Finset (Fin n)}
    (h : s.Nonempty) : ℝ :=
  s.inf' h (p μ I)

/-- `𝔼(C_q(ℐ)) = Σ_{y ∈ 𝒟} p(y)`: the expected number of data points in the probed buckets of
one table (p. 6; proof of Lemma 6, p. 17). -/
noncomputable def EC {n t : ℕ} (μ : Measure (Table n t)) (I : Finset ℕ) : ℝ :=
  ∑ i, p μ I i

end LocalDensityLSH.Count


