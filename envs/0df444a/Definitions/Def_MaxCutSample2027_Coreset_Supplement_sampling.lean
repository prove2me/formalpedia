-- Prove2me | Definitions.Def_MaxCutSample2027_Coreset_Supplement_sampling
-- name    : MaxCutSample2027_Coreset_Supplement_sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:57:31.167984+00:00
-- url     : https://prove2.me/theorems/b6dbcb11-720d-4733-a914-985ba71851d5
-- title:
--   Finite laws, lower-bound graphs and multinomial counts
-- statement:
--   For a finite vertex set $V$ of size $n>0$, the uniform law assigns probability $1/n$ to each vertex. The probability of a sample event $E$ is
--   $$\Pr_p(E)=\sum_{x\in V^k}\Bigl(\prod_i p_{x_i}\Bigr)\mathbf1_E(x).$$
--   A rectangular sign average enumerates all $2^{mr}$ Boolean sign matrices uniformly, using the base convention false = +1. Importance sampling assigns $p_v=d(v)/D$, with $d(v)=\sum_u A_{vu}$ and $D=\sum_vd(v)$.
--   For positive $n$ divisible by six, $B_n$ has two consecutive parts of size $n/2$, and $T_n$ has three consecutive parts of size $n/3$. Both have weight one between parts and zero within parts. Set $G_{n,k}=B_n$ when $k<512$, and $G_{n,k}=T_n$ otherwise. For a sequence of labels in $\{0,1,2\}$, $N_j$ counts occurrences and $L=\max_jN_j-k/3$.
--   These laws and graphs specify the exact finite probability spaces in the sampling and lower-bound statements. Importance sampling is used only for the regular graphs with positive total degree.
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), §1.2; §4; App. A.3–A.4, p. 3, 19–22, 34–35. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_model
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

/-- Uniform probability vector on a finite vertex set. -/
def uniformLaw {V : Type*} [Fintype V] : V → ℝ :=
  fun _ => 1 / (Fintype.card V : ℝ)

/-- Probability under the base explicit product law. -/
def eventProbability {V : Type*} [Fintype V] (p : V → ℝ) (k : ℕ)
    (E : (Fin k → V) → Prop) : ℝ := by
  classical
  exact sampleAverage p k (fun x => if E x then 1 else 0)

/-- Independent Boolean signs indexed by a rectangle. -/
def matrixSignAverage (m r : ℕ) (f : (Fin m → Fin r → Bool) → ℝ) : ℝ :=
  (∑ σ : Fin m → Fin r → Bool, f σ) / (2 : ℝ) ^ (m * r)

/-- Degree-proportional sampling, not silently replaced by the uniform law. -/
def importanceLaw {V : Type*} [Fintype V] (A : V → V → ℝ) : V → ℝ :=
  fun v => weightedDegree A v / totalDegree A

/-- Balanced bipartite graph, used only when n is a positive multiple of six. -/
def bipartiteGraph (n : ℕ) (u v : Fin n) : ℝ :=
  if u.val / (n / 2) = v.val / (n / 2) then 0 else 1

/-- Balanced tripartite graph, with three consecutive parts. -/
def tripartiteGraph (n : ℕ) (u v : Fin n) : ℝ :=
  if 3 * u.val / n = 3 * v.val / n then 0 else 1

def lowerBoundGraph (n k : ℕ) : Fin n → Fin n → ℝ :=
  if k < 512 then bipartiteGraph n else tripartiteGraph n

/-- Counts of k independent draws from three equally likely labels. -/
def partCount {k : ℕ} (ω : Fin k → Fin 3) (j : Fin 3) : ℝ :=
  ((Finset.univ.filter (fun i => ω i = j)).card : ℝ)

def imbalance {k : ℕ} (ω : Fin k → Fin 3) : ℝ :=
  (Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty (partCount ω) - (k : ℝ) / 3

end MaxCutSample2027.Coreset.Supplement


