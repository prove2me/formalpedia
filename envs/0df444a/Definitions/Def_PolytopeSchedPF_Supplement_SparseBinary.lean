-- Prove2me | Definitions.Def_PolytopeSchedPF_Supplement_SparseBinary
-- name    : PolytopeSchedPF_Supplement_SparseBinary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:19:52.384606+00:00
-- url     : https://prove2.me/theorems/53965e45-4c3d-42fb-9523-87728d5a8b24
-- title:
--   $c$-sparse binary polytopes and the integer hull $\mathcal Q_{\mathrm{int}}$ (Definition 6.7)
-- statement:
--   A downward-closed polytope $\mathcal Q=\{y\in\mathbb R^n_{\ge0}: By\le\mathbf 1\}$ is **$c$-sparse binary** ($c\in\mathbb N$) if $B\in\{0,1\}^{D\times n}$ and every column of $B$ contains at least one and at most $c$ ones; equivalently, with $R_j:=\{d\in[D]: B_{dj}=1\}$ the resources used by job $j$, $1\le|R_j|\le c$ for every job.
--
--   The **integer hull** of $\mathcal Q$ is
--
--   $$\mathcal Q_{\mathrm{int}}:=\mathrm{conv}\big(\mathcal Q\cap\{0,1\}^n\big).$$
--
--   For a loopless multigraph the fractional matching polytope is $2$-sparse binary and its integer hull is the matching polytope, which is how graph scheduling enters Theorem 6.8.
--
--   **Formalization Note** $\mathcal Q$ is a base `RatePolytope`; the integer hull is Mathlib's `convexHull ℝ` of its $0/1$ points.
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, §6.2, Definition 6.7, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_PolytopeSchedPF_RatePolytope

namespace PolytopeSchedPF

namespace Supplement

/-- **`c`-sparse binary polytope** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1,
Definition 6.7, p.37). A downward-closed polytope `Q = {y ∈ ℝⁿ_{≥0} | By ≤ 1}` is `c`-sparse binary
if `B ∈ {0,1}^{D×n}` and every column of `B` contains at least one and at most `c` ones, i.e.
`1 ≤ |R_j| ≤ c` with `R_j := {d ∈ [D] | B_{dj} = 1}`.

**Formalization Note** `Q` is a base `RatePolytope` (reading R1); `c ∈ ℕ` as in the paper. -/
def IsSparseBinary {n D : ℕ} (Q : RatePolytope n D) (c : ℕ) : Prop :=
  (∀ d j, Q.B d j = 0 ∨ Q.B d j = 1) ∧
    ∀ j, 1 ≤ (Finset.univ.filter (fun d => Q.B d j = 1)).card ∧
      (Finset.univ.filter (fun d => Q.B d j = 1)).card ≤ c

/-- The **integer hull** `Q_int := conv(Q ∩ {0,1}ⁿ)` of `Q` (Definition 6.7, p.37). -/
def intHull {n D : ℕ} (Q : RatePolytope n D) : Set (Fin n → ℝ) :=
  convexHull ℝ (Q.rates ∩ {y | ∀ j, y j = 0 ∨ y j = 1})

end Supplement

end PolytopeSchedPF


