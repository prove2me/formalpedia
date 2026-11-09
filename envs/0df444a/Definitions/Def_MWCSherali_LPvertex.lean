-- Prove2me | Definitions.Def_MWCSherali_LPvertex
-- name    : MWCSherali_LPvertex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:55.557285+00:00
-- url     : https://prove2.me/theorems/f9b83623-2975-4c7c-90bb-7537c24eb5e9
-- title:
--   The vertex-consistency LP value $\mathrm{LP}^{\mathrm{no}}_{\mathrm{vertex}}(w)$
-- statement:
--   For a weight function $w$ on $E_{k,n}$, $\mathrm{LP}^{\mathrm{no}}_{\mathrm{vertex}}(w)$ is the optimal value of the **vertex-consistency LP** (LP$^{\mathrm{no}}_{\mathrm{vertex}}$):
--
--   $$\min\sum_{e\in E_{k,n}}w_ep_e$$
--
--   subject to
--
--   1. $\sum_{\sigma\in\Omega^{\mathrm{no}}_C}\mu_{C,\sigma}=1$ for every $C\in D_{k,n}$;
--   2. $\sum_{\sigma\in\Omega^{\mathrm{no}}_C,\ \sigma(u)=a}\mu_{C,\sigma}=\lambda_{u,a}$ for every $C\in D_{k,n}$, $u\in C$, $a\in L^{\mathrm{no}}(u)$;
--   3. $p_e=\sum_{\sigma\in\Omega^{\mathrm{no}}_{D(e)},\ \sigma(u)\neq\sigma(v)}\mu_{D(e),\sigma}$ for $e=\{u,v\}\in E_{k,n}$;
--   4. $\mu_{C,\sigma}\ge0$,
--
--   where $D(e)$ is the unique downward cell containing $e$ (Lemma 2.3). Each cell carries a distribution over its valid labelings, whose vertex marginals agree across cells.
--
--   **Formalization Note** $D(e)$ for $e=\{x,y\}$ is written explicitly as the cell indexed by the coordinatewise maximum $x\vee y$ (in integer coordinates), the cell $D((nx+e_j)/(n+1))$ of the proof of Lemma 2.3. The value is the real infimum of the objective over the feasible set, which is nonempty and on which the objective is bounded, so it is the LP optimum.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), (LP^no_vertex), p.16

import Mathlib
import Definitions.Def_MWCSherali_Grid
import Definitions.Def_MWCSherali_edges
import Definitions.Def_MWCSherali_Lno
import Definitions.Def_MWCSherali_cell
import Definitions.Def_MWCSherali_Omega

namespace MWCSherali

/-- **The vertex-consistency LP value `LP^no_vertex(w)`.** Brakensiek–Huang–Potechin–Zwick,
arXiv:2611.05511 (version of Nov. 3, 2026), (LP^no_vertex), p.16: the optimal value of

  minimize `∑_{e ∈ E_{k,n}} w_e p_e` subject to
  * `∑_{σ ∈ Ω^no_C} μ_{C,σ} = 1` for every cell `C ∈ D_{k,n}`;
  * `∑_{σ ∈ Ω^no_C, σ(u) = a} μ_{C,σ} = λ_{u,a}` for every `C ∈ D_{k,n}`, `u ∈ C`,
    `a ∈ L^no(u)`;
  * `p_e = ∑_{σ ∈ Ω^no_{D(e)}, σ(u) ≠ σ(v)} μ_{D(e),σ}` for `e = {u, v} ∈ E_{k,n}`;
  * `μ_{C,σ} ≥ 0`,

where `D(e)` is the unique downward cell containing the edge `e` (Lemma 2.3).

**Formalization Note.**
* Cells are indexed by `V : Grid k (n+1)`; labelings by `Omega V` (see there).
* `D(e)` for `e = {x, y}` is written out explicitly as the cell `V` with `V = x ⊔ y`
  (coordinatewise maximum of the integer coordinates); this is the cell `D((n x + e_j)/(n+1))` of
  the proof of Lemma 2.3, p.15, and for an edge it is the unique cell containing `e`.
* The value is the real infimum of the objective over the feasible set. The feasible set is
  nonempty (any non-opposite cut gives a point, proof of Lemma 2.4) and every `μ_C` is a
  probability vector, so the objective is bounded on it: the infimum is the LP optimum, with no
  junk value. -/
noncomputable def LPvertex {k n : ℕ} (w : Sym2 (Grid k n) → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ (μ : (V : Grid k (n + 1)) → Omega V → ℝ) (lam : Grid k n → Fin (k + 1) → ℝ),
    (∀ V σ, 0 ≤ μ V σ) ∧
    (∀ V, ∑ σ, μ V σ = 1) ∧
    (∀ V, ∀ u ∈ cell V, ∀ a ∈ Lno u,
      ∑ σ ∈ Finset.univ.filter (fun σ : Omega V => σ.1 u = a), μ V σ = lam u a) ∧
    r = ∑ e ∈ edges k n, w e *
      Sym2.lift ⟨fun x y => ∑ V : Grid k (n + 1),
          if V.1 = x.1 ⊔ y.1 then ∑ σ : Omega V, (if σ.1 x ≠ σ.1 y then μ V σ else 0) else 0,
        fun x y => by simp only [sup_comm, ne_comm]⟩ e}

end MWCSherali


