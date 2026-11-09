-- Prove2me | Definitions.Def_PolyContract_FullPlane
-- name    : PolyContract_FullPlane
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:47:52.662058+00:00
-- url     : https://prove2.me/theorems/a3da8dda-573c-4d86-893d-60ac0383f09e
-- title:
--   Full plane $B^{(\pm)}(g)$, full-plane best response $\xi^g$, translation extension $g'$
-- statement:
--   Let $g:2^E\to\mathbb R$ be submodular with $g(\emptyset)=0$, not necessarily monotone, and $m,\beta\in\mathbb R^E_{>0}$. The **full plane** is the base polyhedron without sign constraint,
--   $$B^{(\pm)}(g):=\{y\in\mathbb R^E: y(S)\le g(S)\text{ for all }S\subseteq E,\ y(E)=g(E)\}.$$
--   The **full-plane best response** $\xi^g(\alpha)$, $\alpha\in\mathbb R$, maximizes $U_A(\cdot\mid\alpha)=\alpha m^\top y-\sum_e\beta_ey_e^2/2$ over $B^{(\pm)}(g)$; its marginals are $\rho^g(\alpha)=\alpha m-\beta\xi^g(\alpha)$ and its reward is $r(\xi^g(\alpha))$.
--
--   The module also defines the **translation extension** $g'$ on $E\cup\{b\}$, $g'(S):=g(S)$ and $g'(S\cup\{b\}):=g(S)+K-d(S)$ for $S\subseteq E$, and the function $g-d:S\mapsto g(S)-d(S)$.
--
--   **Formalization Note** The data $(g,m,\beta)$ reuse the instance structure, so marginals, level sets and $F^g_{\alpha,\theta}$ are those of the instance module. The new element $b$ is the extra point of an option type.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), App. B.6.1, p.28 (PDF p.29); Lemma B.11, p.33

import Mathlib
import Definitions.Def_PolyContract_QuadInstance

set_option autoImplicit false

namespace PolyContract

/-- The **full plane** `B(±)(g) := {y ∈ ℝ^E : y(S) ≤ g(S) for all S ⊆ E, y(E) = g(E)}`, the base
polyhedron of `g` without a sign constraint (Klimm, Lippke, Warode, arXiv:2611.04934, version of
November 3, 2026, sha256 18cfc0a5…, App. B.6.1, p.28). -/
def fullPlane {ι : Type} [Fintype ι] (g : Finset ι → ℝ) : Set (ι → ℝ) :=
  {y | (∀ S : Finset ι, setSum y S ≤ g S) ∧ setSum y Finset.univ = g Finset.univ}

namespace QuadInstance

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `y` is the **full-plane best response** `ξ^g(α)` of `g` for `m` and `β` at the share `α ∈ ℝ`
(arXiv:2611.04934, App. B.6.1, p.28): a maximizer of
`U_A(y | α) = α m⊤y − Σ_e β_e y_e²/2` over `B(±)(g)`.

**Formalization Note** The data `(g, m, β)` is a `QuadInstance` whose set function is `g`; no
monotonicity is assumed. The marginals `ρ^g(α) = αm − βξ^g(α)`, the level sets `A^g_θ(α)` and
`F^g_{α,θ}` are `marginal`, `levelSet` and `Ffun` evaluated at the full-plane best response. -/
def IsFullPlaneBR (I : QuadInstance ι) (α : ℝ) (y : ι → ℝ) : Prop :=
  y ∈ fullPlane I.f ∧ ∀ z ∈ fullPlane I.f, I.agentUtility α z ≤ I.agentUtility α y

/-- The reward `r(ξ^g(α)) = m⊤ξ^g(α)` of the full-plane best response (arXiv:2611.04934,
App. B.6.1, p.28), written as the `sSup` of the rewards of all full-plane best responses; the
full-plane best response is unique (p.28). -/
noncomputable def fpReward (I : QuadInstance ι) (α : ℝ) : ℝ :=
  sSup (I.reward '' {y | I.IsFullPlaneBR α y})

end QuadInstance

/-- The **translation extension** `g′ : 2^{E ∪ {b}} → ℝ` of `g` (arXiv:2611.04934, Lemma B.11,
p.33): `g′(S) := g(S)` and `g′(S ∪ {b}) := g(S) + K − d(S)` for `S ⊆ E`.

**Formalization Note** The new element `b` is `none : Option ι`, and `S ∩ E` is
`Finset.eraseNone S`. -/
def translationExt {ι : Type} [DecidableEq ι] (g : Finset ι → ℝ) (K : ℝ) (d : ι → ℝ) :
    Finset (Option ι) → ℝ :=
  fun S => g (Finset.eraseNone S) + if none ∈ S then K - setSum d (Finset.eraseNone S) else 0

/-- The function `g − d : S ↦ g(S) − d(S)` for a vector `d ∈ ℝ^E` (arXiv:2611.04934,
Lemma B.11(c), p.33). -/
def subModular {ι : Type} (g : Finset ι → ℝ) (d : ι → ℝ) : Finset ι → ℝ :=
  fun S => g S - setSum d S

end PolyContract


