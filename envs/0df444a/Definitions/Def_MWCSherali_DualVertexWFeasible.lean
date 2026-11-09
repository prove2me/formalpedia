-- Prove2me | Definitions.Def_MWCSherali_DualVertexWFeasible
-- name    : MWCSherali_DualVertexWFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:46.960201+00:00
-- url     : https://prove2.me/theorems/caf9e826-86c4-4365-9aae-c2daa2deaa01
-- title:
--   Feasible solutions of (dual-LP$^{\mathrm{no}}_{\mathrm{vertex}}$-w)
-- statement:
--   A **feasible solution of (dual-LP$^{\mathrm{no}}_{\mathrm{vertex}}$-w)** consists of reals $y_C$ ($C\in D_{k,n}$), $z_{C,v,a}$ ($v\in C$, $a\in L^{\mathrm{no}}(v)$) and weights $w_e\ge0$ ($e\in E_{k,n}$) with
--
--   1. $y_C+\sum_{v\in C}z_{C,v,\sigma(v)}\le\sum_{\{u,v\}\subseteq C,\ u\neq v}w_{\{u,v\}}\,\mathbf 1[\sigma(u)\neq\sigma(v)]$ for every $C\in D_{k,n}$ and $\sigma\in\Omega^{\mathrm{no}}_C$;
--   2. $\sum_{C:\,v\in C}z_{C,v,a}=0$ for every $v\in\Delta_{k,n}$ and $a\in L^{\mathrm{no}}(v)$;
--   3. $\sum_{e\in E_{k,n}}w_e=n$.
--
--   The objective is $\sum_{C}y_C$. It is the dual of (LP$^{\mathrm{no}}_{\mathrm{vertex}}$) with the weights made variables and normalized; a feasible solution of value $r$ certifies UG-hardness within $r-\epsilon$ (Lemma 2.5).
--
--   **Formalization Note** The sum over unordered pairs $\{u,v\}\subseteq C$, $u\neq v$, is half the sum over ordered pairs. Any two distinct vertices of a cell form an edge, so only values of $w$ on $E_{k,n}$ enter.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), (dual-LP^no_vertex-w), p.17

import Mathlib
import Definitions.Def_MWCSherali_Grid
import Definitions.Def_MWCSherali_edges
import Definitions.Def_MWCSherali_IsNormalized
import Definitions.Def_MWCSherali_Lno
import Definitions.Def_MWCSherali_cell
import Definitions.Def_MWCSherali_Omega

namespace MWCSherali

/-- **Feasible solutions of (dual-LP^no_vertex-w).** Brakensiek–Huang–Potechin–Zwick,
arXiv:2611.05511 (version of Nov. 3, 2026), (dual-LP^no_vertex-w), p.17: real variables `y_C`,
`z_{C,v,a}` and weights `w_e ≥ 0` with
* `y_C + ∑_{v ∈ C} z_{C,v,σ(v)} ≤ ∑_{{u,v} ⊆ C, u ≠ v} w_{u,v} · 1[σ(u) ≠ σ(v)]` for every
  `C ∈ D_{k,n}` and `σ ∈ Ω^no_C`;
* `∑_{C : v ∈ C} z_{C,v,a} = 0` for every `v ∈ Δ_{k,n}` and `a ∈ L^no(v)`;
* `∑_{e ∈ E_{k,n}} w_e = n` (normalization) and `w_e ≥ 0`.
Its objective is `∑_{C ∈ D_{k,n}} y_C`.

**Formalization Note.**
* Cells `C = D(V)` are indexed by `V : Grid k (n+1)`; `z V u a` is `z_{C,u,a}`, and only its
  values with `u ∈ C`, `a ∈ L^no(u)` enter the constraints.
* The sum over unordered pairs `{u, v} ⊆ C`, `u ≠ v`, is written as half the sum over ordered
  pairs `(u, v) ∈ C × C` (a pair with `σ u ≠ σ v` has `u ≠ v`). Any two distinct vertices of a
  cell form an edge (p.17), so only values of `w` on `E_{k,n}` enter. -/
def DualVertexWFeasible (k n : ℕ) (y : Grid k (n + 1) → ℝ)
    (z : Grid k (n + 1) → Grid k n → Fin (k + 1) → ℝ) (w : Sym2 (Grid k n) → ℝ) : Prop :=
  (∀ (V : Grid k (n + 1)) (σ : Omega V),
      y V + ∑ u ∈ cell V, z V u (σ.1 u) ≤
        (1 / 2 : ℝ) * ∑ u ∈ cell V, ∑ v ∈ cell V, if σ.1 u ≠ σ.1 v then w s(u, v) else 0) ∧
  (∀ (u : Grid k n), ∀ a ∈ Lno u,
      ∑ V ∈ Finset.univ.filter (fun V : Grid k (n + 1) => u ∈ cell V), z V u a = 0) ∧
  IsNormalized w ∧
  (∀ e ∈ edges k n, 0 ≤ w e)

end MWCSherali


