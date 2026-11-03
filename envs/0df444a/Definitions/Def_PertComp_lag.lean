-- Prove2me | Definitions.Def_PertComp_lag
-- name    : PertComp_lag
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:28.854945+00:00
-- url     : https://prove2.me/theorems/38bd301a-d8a9-46e5-a901-b82b5f4c5fdd
-- title:
--   Rockafellar perturbation duality: Lagrangian, dual problem, Kuhn–Tucker operator
-- statement:
--   Let $X$ and $U$ be real normed spaces and let $\Phi\colon X\oplus U\to\,]-\infty,+\infty]$ be a perturbation (Definition 2.10). Then:
--
--   1. the **Lagrangian** is $\mathscr L_\Phi(x,u^*)=\inf_{u\in U}\big(\Phi(x,u)-\langle u,u^*\rangle\big)\in[-\infty,+\infty]$ (2.24);
--   2. the **dual problem** is to minimize over $u^*\in U^*$ the function $\sup_{x\in X}\big(-\mathscr L_\Phi(x,u^*)\big)$ (2.25);
--   3. the **Kuhn–Tucker operator** is $\mathscr K_\Phi(x,u^*)=\partial\big(\mathscr L_\Phi(\cdot,u^*)\big)(x)\times\partial\big(-\mathscr L_\Phi(x,\cdot)\big)(u^*)\subset X^*\oplus U$ (2.26);
--   4. $\operatorname{zer}\mathscr K_\Phi=\{(x,u^*) : (0,0)\in\mathscr K_\Phi(x,u^*)\}$.
--
--   These are the abstract objects that Theorem 3.3 computes for the perturbation $F$ of (1.8) and Proposition 3.1 for $\Psi$ of (3.1).
--
--   **Formalization Note** $X\oplus U$ is the Lean product; $U^*$ is `StrongDual ℝ U`. The subdifferential is the formula (2.6), applied as in the paper also to functions taking $\pm\infty$. The second factor of $\mathscr K_\Phi$ is a subset of $U^{**}$, read in $U$ through the canonical embedding (`subdiffPre`), which is the paper's identification under reflexivity.
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Definition 2.10, (2.24)–(2.26), p.9

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_PertComp_subdiffPre

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, Definition 2.10, (2.24), p.9 (after
Rockafellar [50]): for a perturbation `Φ : X ⊕ U → ]−∞, +∞]` the *Lagrangian* is
`𝓛_Φ(x, u*) = inf_{u ∈ U} (Φ(x, u) − ⟨u, u*⟩) ∈ [−∞, +∞]`.

**Formalization Note.** `X ⊕ U` is the Lean product `X × U` (same topology and pairing (2.1);
Lean's product norm is the sup norm, not (2.2), which no statement depends on); `U*` is
`StrongDual ℝ U` and `⟨u, u*⟩` is `u' u`. Computed in `EReal`. -/
noncomputable def lag {X U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (Φ : X × U → EReal) (x : X) (u' : StrongDual ℝ U) : EReal :=
  ⨅ u : U, Φ (x, u) - ((u' u : ℝ) : EReal)

/-- Definition 2.10, (2.25), p.9: the objective of the *dual problem*
`minimize_{u* ∈ U*} sup_{x ∈ X} (−𝓛_Φ(x, u*))`. -/
noncomputable def dualFun {X U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (Φ : X × U → EReal) (u' : StrongDual ℝ U) : EReal :=
  ⨆ x : X, -lag Φ x u'

/-- Definition 2.10, (2.26), p.9: the *Kuhn–Tucker operator*
`𝒦_Φ(x, u*) = ∂(𝓛_Φ(·, u*))(x) × ∂(−𝓛_Φ(x, ·))(u*) ⊂ X* ⊕ U`.

**Formalization Note.** `∂` is the formula (2.6) (`RockafellarMaxMono.Shared.subdiff`), applied as
in the paper also to functions that take `±∞`. The second factor is a subdifferential of a
function on `U*`, whose subgradients lie in `U** = U`; they are pulled back to `U` with
`subdiffPre` (reflexivity). -/
def kt {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup U]
    [NormedSpace ℝ U] (Φ : X × U → EReal) (x : X) (u' : StrongDual ℝ U) :
    Set (StrongDual ℝ X × U) :=
  RockafellarMaxMono.Shared.subdiff (fun z => lag Φ z u') x ×ˢ
    subdiffPre (fun w => -lag Φ x w) u'

/-- The set of zeros `zer 𝒦_Φ = {(x, u*) | (0, 0) ∈ 𝒦_Φ(x, u*)}` (notation of §2, p.5). -/
def zerKt {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup U]
    [NormedSpace ℝ U] (Φ : X × U → EReal) : Set (X × StrongDual ℝ U) :=
  {p | ((0 : StrongDual ℝ X), (0 : U)) ∈ kt Φ p.1 p.2}

end PertComp


