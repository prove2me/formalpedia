-- Prove2me | Definitions.Def_DynHaussler_IsGlobalCover
-- name    : DynHaussler_IsGlobalCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:35:46.242196+00:00
-- url     : https://prove2.me/theorems/5ae90777-df74-4172-8fe5-2d0690495c39
-- title:
--   Global dynamic $\ell_p$ cover (Definition 4, Eq. (19))
-- statement:
--   Let $F\subseteq[0,1]^X$, $T\ge1$ and $\varepsilon>0$. A finite family $G$ of deterministic causal experts at horizon $T$ is a **global dynamic $\ell_p$ cover** of $F$ at accuracy $\varepsilon$ if
--   $$
--   \forall x_{1:T}\in X^T\ \ \forall f\in F\ \ \exists g\in G:\quad \rho_{p,T}\bigl(g[x_{1:T}],f[x_{1:T}]\bigr)\le\varepsilon,
--   $$
--   where $f[x_{1:T}]=(f(x_t))_{t=1}^T$. The whole family is fixed before the sequence; the witnessing expert may depend on the target and the complete sequence.
--
--   **Formalization Note** The family is indexed, $G:\{0,\dots,k-1\}\to$ experts; repetitions are allowed, which does not change the least size of a cover. The standing conditions $F\subseteq[0,1]^X$, $T\ge1$, $\varepsilon>0$ are hypotheses of the statements that use the predicate.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Definition 4, Eq. (19), p.14 (PDF p.16)

import Mathlib
import Definitions.Def_DynHaussler_CausalExpert
import Definitions.Def_DynHaussler_rho

set_option autoImplicit false

namespace DynHaussler

/-- A finite family `G = (G_i)_{i < k}` of deterministic causal experts is a **global dynamic
`ℓ_p` cover** of `F` at accuracy `ε` and horizon `T` if
`∀ x_{1:T} ∈ X^T ∀ f ∈ F ∃ g ∈ G : ρ_{p,T}(g[x_{1:T}], f[x_{1:T}]) ≤ ε`.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Definition 4, Eq. (19), p.14 (PDF p.16).

**Formalization Note** The family is indexed by `Fin k` (it is fixed before the sequence, as the
paper requires); repetitions are allowed, which does not change the least size of a cover. The
paper's standing `F ⊆ [0,1]^X`, `T ≥ 1`, `ε > 0` are hypotheses of the statements that use this
predicate. -/
def IsGlobalCover {X : Type*} (p ε : ℝ) (F : Set (X → ℝ)) {T k : ℕ}
    (G : Fin k → CausalExpert X T) : Prop :=
  ∀ x : Fin T → X, ∀ f ∈ F, ∃ i : Fin k, rho p ((G i).run x) (fun t => f (x t)) ≤ ε

end DynHaussler


