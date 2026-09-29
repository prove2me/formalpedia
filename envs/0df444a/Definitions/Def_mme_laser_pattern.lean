-- Prove2me | Definitions.Def_mme_laser_pattern
-- name    : mme_laser_pattern
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-31T17:44:01.301451+00:00
-- url     : https://prove2.me/theorems/6d99a974-a5c7-4096-b144-cf5d937d6ae5
-- statement:
--   **Laser-method support patterns and the value formula.**
--
--   This Definition file packages three abstract data structures used by every laser-method argument:
--
--   **1. `LaserSymmetric S`** — the predicate that a support pattern $S \subseteq (\mathrm{Fin}\,t)^3$ is closed under the cyclic permutation $(\alpha, \beta, \gamma) \mapsto (\beta, \gamma, \alpha)$. This is the symmetry the laser method exploits to produce a *symmetric* family of restriction witnesses.
--
--   **2. `TensorObj.LaserAlignedSupport G S`** — the structural hypothesis that the rank-one expansion of `T.t` only uses type-triples drawn from $S$. Formally:
--
--   $$T.t \;=\; \sum_{j=1}^{k} \bigotimes_{i=0}^{2} f_j(i),\quad \text{where}\quad \forall j,\; \bigl(\tau_j^{(0)}, \tau_j^{(1)}, \tau_j^{(2)}\bigr) \in S \;\wedge\; \forall i,\; f_j(i) \in G_{i, \tau_j^{(i)}}.$$
--
--   For the CW tensor at parameter $q$ with the canonical 3-grading, every rank-one term has type-triple in $\{(0,1,1), (1,0,1), (1,1,0), (0,0,2), (0,2,0), (2,0,0)\}$ — the canonical cyclic-closed support pattern of `T_q`.
--
--   **3. `laserValueFormula G S`** — the explicit closed-form value-formula lower bound produced by the laser construction. *Placeholder in this Layer-2 file*; the closed-form Stirling-derived formula (a supremum over probability distributions on $S$ of an entropy-style expression in $p$ and the grading class dimensions) is derived in Layer 3 from the Salem–Spencer-indexed restriction of $T^{\otimes 2N}$.
--
--   **Why abstract here.** The abstract laser theorem `mme_laser_value_lower_bound` is stated against these three structures so that Layer-2 work remains decoupled from the Layer-3 closed-form numeric content. Each subsequent ω-bound improvement (Stothers 2010, Vassilevska Williams 2012, Le Gall 2014, Alman–VW 2020) reuses this abstract framework verbatim and provides only its own tensor, grading, and support pattern.
-- source:
--   https://arxiv.org/abs/2212.11824

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_mme_tensor_type_grading
import Definitions.Def_mme_tensor_rank

/-! # Laser-method support patterns and the value formula

This file packages the abstract data structures used by the laser method:

* `TensorObj.LaserAlignedSupport G Σ` — the hypothesis that the rank-one
  expansion of `T.t` only uses *type-triples* drawn from a fixed support set
  `Σ ⊆ (Fin t)^3`. This is the **structural input** to every laser-style
  argument: it certifies that `T` factors through the type-grading `G` with
  controlled support.

* `LaserSymmetric Σ` — the cyclic-symmetry hypothesis on `Σ`. The CW
  support pattern `{(0,1,1), (1,0,1), (1,1,0), (0,0,2), (0,2,0), (2,0,0)}`
  is closed under both cyclic and full 3-symmetric permutations of its
  type-triples; this is what makes the laser method produce a *symmetric*
  family of restriction witnesses.

* `laserValueFormula G Σ` — the explicit closed-form value lower bound
  produced by the laser construction. **Placeholder definition** in this
  layer; the closed-form Stirling-derived formula and its connection to
  the Salem–Spencer indexing live in Layer 3. The abstract theorem in
  `Thm_mme_laser_value_lower_bound` is stated against this placeholder so
  that Layer 2 work remains decoupled from the Layer 3 numeric closed form.

All three structures are **paper-agnostic** — the same definitions support
CW 1990, Stothers 2010, Vassilevska Williams 2012, Le Gall 2014, etc. -/

universe u

open BigOperators

namespace MME

variable {K : Type u} [Field K]

/-- A support pattern `Σ ⊆ (Fin t)^3` is `LaserSymmetric` if it is closed under
the cyclic permutation `(α, β, γ) ↦ (β, γ, α)`. This is the symmetry the
laser method exploits. -/
def LaserSymmetric {t : ℕ} (S : Finset (Fin t × Fin t × Fin t)) : Prop :=
  ∀ x ∈ S, (x.2.1, x.2.2, x.1) ∈ S

/-- `T.t` has *laser-aligned support* with respect to `G : TypeGrading T t` and a
support set `Σ ⊆ (Fin t)^3` if it admits a rank-one expansion in which every term
has its three mode-factors belonging to grading classes whose type-triple lies in
`Σ`. -/
def TensorObj.LaserAlignedSupport
    {T : TensorObj K 3} {t : ℕ}
    (G : T.TypeGrading t) (S : Finset (Fin t × Fin t × Fin t)) : Prop :=
  ∃ (k : ℕ) (f : Fin k → ∀ i : Fin 3, T.V i)
    (τ : Fin k → Fin t × Fin t × Fin t),
      T.t = ∑ j, PiTensorProduct.tprod K (f j) ∧
      ∀ j, τ j ∈ S ∧
           f j 0 ∈ G.classOf 0 (τ j).1 ∧
           f j 1 ∈ G.classOf 1 (τ j).2.1 ∧
           f j 2 ∈ G.classOf 2 (τ j).2.2

/-- **Placeholder** for the explicit closed-form laser value formula.

In the canonical CW/WZ analysis, this is the supremum over probability
distributions `p : Σ → ℝ≥0` (with marginal constraints from `LaserSymmetric`)
of an explicit entropy-style expression in `p` and the grading class
dimensions:

  `laserValueFormula G Σ  =  sup_p  ( ∏_{(α,β,γ) ∈ Σ} (3p_{αβγ})^{p_{αβγ}}
                                       · ∏_α (d_α)^{q_α} · … )^{1/3}`

The closed-form derivation from Salem–Spencer-indexed restrictions of
`T^{⊗2N}` is the deepest single piece of the abstract laser machinery and
lives in Layer 3 (`Thm_mme_laser_value_closed_form`). The present file
exposes only the placeholder symbol so that the abstract Layer-2 theorem
`mme_laser_value_lower_bound` is statable in terms of it. -/
noncomputable def laserValueFormula
    {T : TensorObj K 3} {t : ℕ}
    (_G : T.TypeGrading t) (_S : Finset (Fin t × Fin t × Fin t)) : ℝ := 1

end MME


