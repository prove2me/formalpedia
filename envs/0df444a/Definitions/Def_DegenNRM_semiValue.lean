-- Prove2me | Definitions.Def_DegenNRM_semiValue
-- name    : DegenNRM_semiValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:33.035876+00:00
-- url     : https://prove2.me/theorems/da7e84db-f279-416a-9a21-1584174c2e03
-- title:
--   The semi-fluid relaxation $\bar V^{\mathrm{Semi}}_c(d)$, problem (9)
-- statement:
--   For remaining capacities $c\in\mathbb R^m$ and type counts $d\in\mathbb R^n$, a family of measurable acceptance functions $x_j:\mathbb R\to[0,1]$ is **feasible** for (9) if
--   $$\sum_{j=1}^n d_j\,a_{j,i}\,\mathbb E_{r\sim F_j}[x_j(r)]\le c_i\quad\forall i\in[m],$$
--   its objective is $\sum_{j=1}^n d_j\,\mathbb E_{r\sim F_j}[r\,x_j(r)]$, and the **semi-fluid value** $\bar V^{\mathrm{Semi}}_c(d)$ is the supremum of the objective over feasible families.
--
--   The semi-fluid relaxation knows how many queries of each type remain, but collects the expected value of each type's accepted rewards. It upper-bounds the prophet (Lemma 2) and is the relaxation $\bar V$ of the regret decomposition in Section 3.
--
--   **Formalization Note** The paper writes a maximum; Lemma 3 and (12) show it is attained. The paper asks $x_j(r)\in[0,1]$ only for $r\in[l_j,u_j]$, where $F_j$ lives. For a capacity vector with a negative entry the feasible set is empty and the value is Lean's $\sup\emptyset=0$.
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, §3.2, (9), p.13

import Mathlib
import Definitions.Def_DegenNRM_Instance

open MeasureTheory

namespace DegenNRM

/-- **Feasible solutions of the semi-fluid relaxation (9)** (Jiang, Ma & Zhang,
arXiv:2210.07996v5, §3.2, (9), p.13).

For remaining capacities `c` and type counts `d`, a family `x_j : ℝ → [0, 1]` of measurable
acceptance probabilities (accept a type-`j` query of reward `r` with probability `x_j(r)`) is
feasible if `Σ_j d_j a_{j,i} E_{r∼F_j}[x_j(r)] ≤ c_i` for every resource `i`.

**Formalization Note.** The paper requires `x_j(r) ∈ [0,1]` for `r ∈ [l_j, u_j]`; here `x_j` is
defined on all of `ℝ` with values in `[0,1]`, which changes nothing since `F_j` lives on
`[l_j, u_j]` under Assumption 1. Measurability makes the expectations meaningful. -/
def SemiFeasible {m n : ℕ} (inst : Instance m n) (c : Fin m → ℝ) (d : Fin n → ℝ)
    (x : Fin n → ℝ → ℝ) : Prop :=
  (∀ j, Measurable (x j)) ∧ (∀ j r, x j r ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ i, ∑ j, d j * inst.a j i * ∫ r, x j r ∂(inst.F j) ≤ c i

/-- The objective of (9): `Σ_j d_j E_{r∼F_j}[r · x_j(r)]`. -/
noncomputable def semiObjective {m n : ℕ} (inst : Instance m n) (d : Fin n → ℝ)
    (x : Fin n → ℝ → ℝ) : ℝ :=
  ∑ j, d j * ∫ r, r * x j r ∂(inst.F j)

/-- **The semi-fluid value `V̄^Semi_c(d)`, (9)** (arXiv:2210.07996v5, §3.2, (9), p.13): the
supremum of the objective of (9) over its feasible solutions.

**Formalization Note.** The maximum of (9) is written as a supremum (`sSup`); Lemma 3 and (12)
(milestones of this mission) show it is attained. It is used for `c ≥ 0` and `d ≥ 0`. For a
capacity vector with a negative entry the feasible set is empty and the value is Lean's
`sSup ∅ = 0`; it only appears multiplied by an acceptance probability `0` in (19). -/
noncomputable def semiValue {m n : ℕ} (inst : Instance m n) (c : Fin m → ℝ) (d : Fin n → ℝ) : ℝ :=
  sSup (semiObjective inst d '' {x | SemiFeasible inst c d x})

end DegenNRM


