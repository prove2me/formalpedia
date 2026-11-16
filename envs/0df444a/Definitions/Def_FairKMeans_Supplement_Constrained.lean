-- Prove2me | Definitions.Def_FairKMeans_Supplement_Constrained
-- name    : FairKMeans_Supplement_Constrained
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:59:06.736791+00:00
-- url     : https://prove2.me/theorems/236aa9bc-c8a1-4d16-9b1b-bc5089211801
-- title:
--   $k$-means with homogeneous cluster constraints (Definition 30): weighted instances, feasible assignments, cost, $\mathrm{OPT}_{\mathrm{frac}}$ and $\mathrm{OPT}$
-- statement:
--   An instance of **$k$-means with homogeneous cluster constraints** consists of $n$ points $p\in P$ of $\mathbb R^d$ (an indexed family) with positive weights $w(p)>0$, an integer $k\ge1$, and $r$ linear constraints given by coefficients $a_j(p)\in\mathbb R$ for $p\in P$ and $j\in[r]$.
--
--   For a family $S$ of centers, an assignment matrix $\phi_S$ (nonnegative entries, rows summing to one) is **feasible** if
--
--   $$\sum_{p\in P}a_j(p)\,\phi_S(p,s)\ge0\qquad\text{for all } s\in S,\ j\in[r]. \tag{40}$$
--
--   Its weighted cost is $\mathrm{Cost}(P,S,\phi_S)=\sum_{p}\sum_{s}w(p)\,\phi_S(p,s)\,\|p-s\|^2$. An optimal solution of the **feasible assignment LP** of $S$ is a feasible fractional assignment to $S$ of minimum cost among all of them. The instance **has a feasible solution** if some family of at most $k$ centers admits a feasible fractional assignment. $\mathrm{OPT}_{\mathrm{frac}}$ and $\mathrm{OPT}$ are the infima of the cost over all families of at most $k$ centers anywhere in $\mathbb R^d$ with a feasible fractional, respectively feasible integral, assignment.
--
--   Fair $k$-means is the special case with $r=2m$ (Remark 31), and the $k$-sparse barycenter problem is a special case of that; these objects carry Theorems 4 and 32.
--
--   **Formalization Note** Center sets are indexed families with duplicates allowed (merging equal centers adds columns, which keeps (40), since it is homogeneous). Weights are strictly positive as in Remark 44. The number of constraints $r$ may be $0$.
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Definition 30 and (40), p.36 (PDF p.38); Remark 44, p.48 (PDF p.50); cost (10), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_FairKMeans_Model

namespace FairKMeans.Supplement

/-!
# k-means with homogeneous cluster constraints (Definition 30), weighted points

Cheng–Mo–Song–Ding, *A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound*,
arXiv:2609.07974 (held version, sha256 73e9312c…), Definition 30, (40), p.36 (PDF 38);
weighted points, Remark 44, p.48 (PDF 50); cost (10), p.18 (PDF 20).

**Formalization Note.** Points are an indexed family `Fin n → E d` with weights `w : Fin n → ℝ`,
all strictly positive (Remark 44: "positive weights `w(p)`"). The `r` constraints have
coefficients `a j p`; `r = 0` (no constraint) is allowed, which only adds instances (Definition
30 says `r ≥ 1`). A center set is an indexed family `S : Fin s → E d`, duplicates allowed;
`IsAssignment` and `IsIntegral` are the published ones (`FairKMeans.Model`). Merging equal centers
adds their columns, which keeps (40) (it is homogeneous) and integrality and leaves the cost
unchanged, so the infima below are the paper's. Every sum over input points of the cost is
multiplied by `w(p)` (Remark 44; (10)).
-/

open FairKMeans

/-- An instance of k-means with homogeneous cluster constraints (Definition 30, p.36): `n`
weighted points of `ℝ^d` with positive weights, an integer `k ≥ 1`, and `r` constraints with
coefficients `a_j(p)`. -/
structure HInstance (d n r : ℕ) where
  /-- The input points `P`. -/
  pts : Fin n → E d
  /-- The weights `w(p)`. -/
  w : Fin n → ℝ
  w_pos : ∀ p, 0 < w p
  /-- The number of centers. -/
  k : ℕ
  one_le_k : 1 ≤ k
  /-- The coefficients `a_j(p)` of the `r` constraints. -/
  a : Fin r → Fin n → ℝ

variable {d n r : ℕ}

/-- An assignment matrix is feasible (40): `∑_p a_j(p) φ(p,s) ≥ 0` for every center `s` and
every constraint `j`. -/
def IsFeasible {s : ℕ} (I : HInstance d n r) (φ : Fin n → Fin s → ℝ) : Prop :=
  ∀ (j : Fin r) (t : Fin s), 0 ≤ ∑ p, I.a j p * φ p t

/-- The weighted cost `Cost(P, S, φ_S) = ∑_p ∑_s w(p) φ_S(p,s) ‖p − s‖²` ((10), p.18). -/
noncomputable def hcost {s : ℕ} (I : HInstance d n r) (S : Fin s → E d)
    (φ : Fin n → Fin s → ℝ) : ℝ :=
  ∑ p, ∑ t, I.w p * φ p t * ‖I.pts p - S t‖ ^ 2

/-- `φ` is an optimal solution of the feasible assignment LP of `S` ("fair" read as "feasible",
proof of Theorem 32, p.37): a feasible fractional assignment of `P` to `S` of minimum weighted
cost among all feasible fractional assignments. -/
def IsOptFeasAssign {s : ℕ} (I : HInstance d n r) (S : Fin s → E d) (φ : Fin n → Fin s → ℝ) :
    Prop :=
  IsAssignment φ ∧ IsFeasible I φ ∧
    ∀ ψ : Fin n → Fin s → ℝ, IsAssignment ψ → IsFeasible I ψ → hcost I S φ ≤ hcost I S ψ

/-- The instance has a feasible solution: some family of at most `k` centers admits a feasible
fractional assignment (Definition 30; Theorem 32). -/
def HasFeasibleSolution (I : HInstance d n r) : Prop :=
  ∃ s ≤ I.k, ∃ (S : Fin s → E d) (φ : Fin n → Fin s → ℝ), IsAssignment φ ∧ IsFeasible I φ

/-- `OPT_frac` (Definition 30): the infimum of the weighted cost over all families of at most `k`
centers anywhere in `ℝ^d` and all feasible fractional assignments. -/
noncomputable def hOPTfrac (I : HInstance d n r) : ℝ :=
  sInf {c : ℝ | ∃ s ≤ I.k, ∃ (S : Fin s → E d) (φ : Fin n → Fin s → ℝ),
    IsAssignment φ ∧ IsFeasible I φ ∧ hcost I S φ = c}

/-- `OPT` (Definition 30): the same infimum over feasible integral assignments. -/
noncomputable def hOPT (I : HInstance d n r) : ℝ :=
  sInf {c : ℝ | ∃ s ≤ I.k, ∃ (S : Fin s → E d) (φ : Fin n → Fin s → ℝ),
    IsAssignment φ ∧ IsIntegral φ ∧ IsFeasible I φ ∧ hcost I S φ = c}

end FairKMeans.Supplement


