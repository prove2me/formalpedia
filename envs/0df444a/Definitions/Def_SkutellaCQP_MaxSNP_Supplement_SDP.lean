-- Prove2me | Definitions.Def_SkutellaCQP_MaxSNP_Supplement_SDP
-- name    : SkutellaCQP_MaxSNP_Supplement_SDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:46:24.673033+00:00
-- url     : https://prove2.me/theorems/8bef230b-ec0a-444e-9cf6-451c4f9a894e
-- title:
--   §5 — the strengthened two-machine SDP, assignment laws and optima
-- statement:
--   There are $n$ jobs, two machines, processing times $p_{ij}$ and weights $w_j$. A vector configuration consists of machine vectors $v_0,v_{-1}$ and job vectors $v_j$ in $\mathbb R^{n+1}$. Set
--   $$a_{ij}=\frac{1+\langle v_i,v_j\rangle}{2},\qquad t_{ijk}=\frac{\langle v_j,v_k\rangle+\langle v_i,v_j\rangle+\langle v_i,v_k\rangle+1}{4}.$$
--   The feasible SDP configurations have unit vectors, antipodal machine vectors, $t_{ijk}\ge0$ for both machines and every pair of jobs, and both objective lower bounds:
--   $$Z\ge\sum_jw_j\sum_i\left(a_{ij}p_{ij}+\sum_{k\prec_i j}t_{ijk}p_{ik}\right),\qquad Z\ge Z_{\rm CQP}(a).$$
--   The quadratic bound uses the published $c,D$ definitions unchanged. An assignment law is any nonnegative finite probability weight on assignments; independence is not built into it. The marginal and joint probabilities, $c^Ta$, expected schedule value, and finite minimum $Z^*$ over all assignments are defined from these data. Almost optimal means feasible and within additive $\delta$ of every feasible SDP value. Finally $L=\sum_j w_j\min_i p_{ij}$ is a computable lower bound.
--
--   **Formalization Note** Machines 0 and 1 represent the paper's labels 0 and $-1$. Smith ordering and schedule values are the published definitions. The zero-job case has one empty assignment and optimum zero.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), DOI 10.1145/375827.375840, pp. 24–26, (28)–(35)

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

namespace SkutellaCQP.MaxSNP.Supplement

open Finset
open scoped RealInnerProductSpace

/-- Two machines: `0` is the paper's machine 0 and `1` its machine −1. -/
abbrev Two := Fin 2

/-- The ambient space of the vector program, including the zero-job case. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

/-- Vectors before rounding. Unit lengths and antipodality are program constraints, not fields. -/
structure Vectors (n : ℕ) where
  machine : Two → Vec n
  job : Fin n → Vec n

/-- (30): the fractional assignment induced by the vectors. -/
noncomputable def assignment {n : ℕ} (v : Vectors n) (i : Two) (j : Fin n) : ℝ :=
  (1 + ⟪v.machine i, v.job j⟫) / 2

/-- The coefficient of the pair `j,k` in (28), divided by four. -/
noncomputable def triple {n : ℕ} (v : Vectors n) (i : Two) (j k : Fin n) : ℝ :=
  (⟪v.job j, v.job k⟫ + ⟪v.machine i, v.job j⟫ + ⟪v.machine i, v.job k⟫ + 1) / 4

/-- `cᵀa`, using the published matrix data. -/
noncomputable def linearValue {n : ℕ} (p : Two → Fin n → ℝ) (w : Fin n → ℝ)
    (v : Vectors n) : ℝ :=
  dotProduct (SkutellaCQP.NoRel.cvec p w) (SkutellaCQP.NoRel.vec (assignment v))

/-- The vector-program lower bound (28). -/
noncomputable def vectorValue {n : ℕ} (p : Two → Fin n → ℝ) (w : Fin n → ℝ)
    (v : Vectors n) : ℝ :=
  ∑ j, w j * ∑ i, (assignment v i j * p i j +
    ∑ k ∈ univ.filter (fun k => SkutellaCQP.NoRel.prec p w i k j), triple v i j k * p i k)

/-- All constraints of (SDP), (28)–(31). Antipodality as equality is equivalent to inner
product −1 for unit vectors. The quadratic cut uses the original published `D,c`. -/
def SDPFeasible {n : ℕ} (p : Two → Fin n → ℝ) (w : Fin n → ℝ)
    (v : Vectors n) (Z : ℝ) : Prop :=
  (∀ i, ‖v.machine i‖ = 1) ∧ (∀ j, ‖v.job j‖ = 1) ∧
  v.machine 1 = -v.machine 0 ∧ vectorValue p w v ≤ Z ∧
  (∀ i j k, 0 ≤ triple v i j k) ∧
  SkutellaCQP.NoRel.ZCQP p w (assignment v) ≤ Z

/-- An arbitrary law on assignments; correlations are allowed in Lemma 5.2. -/
def IsAssignmentLaw {n : ℕ} (μ : (Fin n → Two) → ℝ) : Prop :=
  (∀ σ, 0 ≤ μ σ) ∧ ∑ σ, μ σ = 1

/-- Marginal probability that `j` goes to machine `i`. -/
noncomputable def marginal {n : ℕ} (μ : (Fin n → Two) → ℝ) (i : Two) (j : Fin n) : ℝ :=
  ∑ σ ∈ univ.filter (fun σ : Fin n → Two => σ j = i), μ σ

/-- Joint probability that `j,k` both go to machine `i`, including `j=k` as on the page. -/
noncomputable def joint {n : ℕ} (μ : (Fin n → Two) → ℝ) (i : Two) (j k : Fin n) : ℝ :=
  ∑ σ ∈ univ.filter (fun σ : Fin n → Two => σ j = i ∧ σ k = i), μ σ

/-- Both probability bounds (34) and (35). Parameter order is a theorem hypothesis. -/
def ProbabilityBounds {n : ℕ} (v : Vectors n) (μ : (Fin n → Two) → ℝ)
    (ρ₁ ρ₂ : ℝ) : Prop :=
  (∀ i j, marginal μ i j ≤ ρ₁ / 2 *
    ((1 + ⟪v.machine i, v.job j⟫) / 2 + (1 + assignment v i j) * assignment v i j / 2)) ∧
  (∀ i j k, joint μ i j k ≤ ρ₂ / 2 *
    (triple v i j k + assignment v i j * assignment v i k))

/-- Expected weighted completion value after sequencing each assignment by Smith's rule. -/
noncomputable def expectedValue {n : ℕ} (p : Two → Fin n → ℝ) (w : Fin n → ℝ)
    (μ : (Fin n → Two) → ℝ) : ℝ :=
  SkutellaCQP.NoRel.E μ (SkutellaCQP.NoRel.val p w)

/-- The source's scheduling optimum: the finite nonempty set of all assignments. -/
noncomputable def optimum {n : ℕ} (p : Two → Fin n → ℝ) (w : Fin n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (SkutellaCQP.NoRel.val p w)

/-- Almost optimal with additive error `δ`, without presupposing attainment of the SDP infimum.
The output is feasible and lies within `δ` of every feasible SDP value. -/
def AlmostOptimal {n : ℕ} (p : Two → Fin n → ℝ) (w : Fin n → ℝ)
    (v : Vectors n) (Z δ : ℝ) : Prop :=
  SDPFeasible p w v Z ∧ ∀ u Y, SDPFeasible p w u Y → Z ≤ Y + δ

/-- Computable lower bound `L=∑ w_j min_i p_ij`, zero precisely for zero-weight instances
under the standing positive processing-time assumptions. -/
noncomputable def lowerBound {n : ℕ} (p : Two → Fin n → ℝ) (w : Fin n → ℝ) : ℝ :=
  ∑ j, w j * min (p 0 j) (p 1 j)

end SkutellaCQP.MaxSNP.Supplement


