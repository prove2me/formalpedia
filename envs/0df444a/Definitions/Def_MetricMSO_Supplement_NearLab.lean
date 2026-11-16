-- Prove2me | Definitions.Def_MetricMSO_Supplement_NearLab
-- name    : MetricMSO_Supplement_NearLab
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:55:57.378886+00:00
-- url     : https://prove2.me/theorems/3a1704a6-4eef-42d8-b947-65b274ceb650
-- title:
--   Single-interface nearest-label formulas and label partitions
-- statement:
--   Assume the unary input predicates $L_1,\dots,L_q$ **partition** $V(G)$: every vertex lies in exactly one of them.
--
--   A **single-interface nearest-label formula** $\theta(S,\bar X)$ (Definition 6.2) is a $\mathrm{CMSO}_2[\mathrm{SP},\mathrm{EqGC}]$ formula in which the atoms $\mathrm{NearLab}_i(v;S)$ are also allowed, all referring to the same distinguished free vertex-set variable $S$, which no quantifier binds; the additional free vertex sets $\bar X$ are optional. No $\mathrm{Dist}$, $\mathrm{EqDist}$ or $\mathrm{Close}$ atom occurs.
--
--   Its **solutions** are the assignments of all displayed free sets $(S,\bar X)$ with $S\ne\emptyset$ that satisfy $\theta$. The input of a task is the task, the instance code (which contains $q$ and the labels), the formula, the number of free sets, and the weights for the weighted tasks.
--
--   **Formalization Note** $S$ is the vertex-set variable of level $0$; quantified set variables get higher levels, so $S$ is never bound.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c5863…), Definitions 2.13, 6.2, pp.18, 30 (PDF 20, 32); §1, p.9 (PDF 11)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_MetricMSO_encodeInput
import Definitions.Def_MetricMSO_Supplement_XSat

set_option autoImplicit false

namespace MetricMSO.Supplement

open MetricMSO
open ExponomialAssortment.FPTAS (encodeNat)

/-- **The input labels partition the vertex set** (Definition 2.13, p.18 (PDF 20): "we assume that
the unary input label sets L1, . . . , Lq form a partition of V(G)"): every vertex lies in exactly
one vertex input predicate. -/
def IsLabelPartition (I : Instance) : Prop :=
  ∀ v : Fin I.n, ∃! j : Fin I.q, v ∈ I.vpred j

/-- **Single-interface nearest-label formulas** `θ(S, X₁, …, X_{r−1})` (Definition 6.2, p.30 (PDF
32); §1, p.9 (PDF 11)): "a CMSO2[SP, EqGC] formula in which we also allow atoms NearLab_i(v; S),
all referring to the same distinguished free set S. We require S ≠ ∅, and no quantifier may bind
this distinguished variable. The additional free sets X̄ are optional".

`IsNearLabFormula θ r`: `r ≥ 1`; `θ` uses the features of CMSO2[SP, EqGC] plus `NearLab` (no
`Dist`, `EqDist`, `Close`); its free variables are the vertex-set variables of levels
`0, …, r − 1` (`S` is level `0`, the optional `X̄` are levels `1, …, r − 1`); and every `NearLab`
atom has the set variable of level `0` as its set argument.

**Formalization Note** Quantified vertex-set variables get the levels `≥ r`, so level `0` is never
bound by a quantifier. The additional free sets are vertex sets ("additive vertex-weight
optimization"). -/
def IsNearLabFormula (θ : XFormula) (r : ℕ) : Prop :=
  1 ≤ r ∧ Logic nearLabFeatures θ ∧ θ.wellScoped 0 0 r 0 = true ∧ θ.nearLabSetIs 0 = true

/-- **The solutions of a nearest-label formula**: the assignments `(S, X₁, …)` of all displayed free
sets with `S ≠ ∅` and `G ⊨ θ(S, X̄)` ("For optimization and counting, we consider assignments to
all displayed free sets", p.30). -/
def NLSol (I : Instance) (θ : XFormula) (r : ℕ) : Set (Assignment I r 0) :=
  {A | ∃ h : 0 < r, (A.1 ⟨0, h⟩).Nonempty ∧ XSat I [] A.toEnv θ}

open Classical in
/-- **The binary input for a nearest-label task**: the task, the instance (graph and the label
predicates; their number `q` is part of the instance code), the formula, the number `r` of free
sets, and for the weighted tasks the signed binary vertex weights. -/
noncomputable def nearLabInput (task : Task) (I : Instance) (θ : XFormula) (r : ℕ)
    (w : Weights I r 0) : List Bool :=
  encodeNat task.index ++ encodeInstance I ++ θ.encode ++ encodeNat r ++
    (if task.weighted then encodeWeights w else [])

end MetricMSO.Supplement


