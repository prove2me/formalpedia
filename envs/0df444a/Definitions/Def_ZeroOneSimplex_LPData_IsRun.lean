-- Prove2me | Definitions.Def_ZeroOneSimplex_LPData_IsRun
-- name    : ZeroOneSimplex_LPData_IsRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:37.597089+00:00
-- url     : https://prove2.me/theorems/ec4120cd-2f35-4202-b241-5b094c41e7c7
-- title:
--   Runs and lexicographic runs of the Ordered Shadow pivot rule
-- statement:
--   Let $B^0$ be a feasible basis with vertex $x^0$ and let $v$ be the Ordered Shadow vector for $x^0$. A **run** of the Ordered Shadow pivot rule is a sequence of bases $B_0=B^0,B_1,\dots,B_T$ with a switch time $t_0\le T$ such that
--
--   1. (Phase 1) for $t<t_0$, $B_t\to B_{t+1}$ is a degenerate pivot (any entering variable);
--   2. $B_{t_0}$ satisfies the slope condition: for each $z\in\mathcal C(B_{t_0})$, $c^\top z>0\Rightarrow v^\top z>0$;
--   3. (Phase 2) for $t_0\le t<T$, $B_t\to B_{t+1}$ is a pivot whose entering variable has an improving pivot direction of largest slope $c^\top z/v^\top z$.
--
--   A **lexicographic run** in addition fixes an ordering $e$ of $B_{t_0}$ and requires every $B_t$, $t_0\le t\le T$, to be feasible for the perturbed right-hand side $b'(\varepsilon)=b'+\sum_{i=1}^{m+p}\varepsilon^iA'_{e(i)}$ for all small $\varepsilon>0$: this is the lexicographic leaving rule. The number of **non-degenerate pivots** of a run is the number of $t<T$ at which the vertex changes.
--
--   **Formalization Note** The paper assembles the rule from Definition 5, Theorem 7, Lemma 6 and §3.4 ("the Ordered Shadow and Slim Shadow pivot rules can be implemented correctly using the lexicographic method", p.25). The lexicographic rule is encoded by right-hand-side perturbation, started at the Phase 2 basis.
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, Definition 5, p.16; Theorem 7, p.23; Lemma 6, p.24; §3.4, pp.24–25

import Mathlib
import Definitions.Def_ZeroOneSimplex_LPData_IsPivot
import Definitions.Def_ZeroOneSimplex_LPData_orderedShadowVec

set_option autoImplicit false

open Matrix

open Filter Topology

namespace ZeroOneSimplex

namespace LPData

variable {n m p : ℕ} (L : LPData n m p)

/-- **A run of the Ordered Shadow pivot rule** from the feasible basis `B⁰`
(arXiv:2111.14050v1, Definition 5, p.16; Theorem 7, p.23; Lemma 6, p.24; §3.4, pp.22–25).

Bases `B 0 = B⁰, B 1, …, B T` and a switch time `t₀ ≤ T`, where `x⁰` is the vertex of `B⁰` and
`v = orderedShadowVec x⁰` is the vector of Definition 5, such that
* **Phase 1** (`t < t₀`, Lemma 6): `B t → B (t+1)` is a degenerate pivot, with any entering
  variable;
* `B t₀` satisfies the condition of Theorem 7: for each `z ∈ 𝒞(B t₀)`, `cᵀz > 0 → vᵀz > 0`;
* **Phase 2** (`t₀ ≤ t < T`, Theorem 7): `B t → B (t+1)` is a pivot whose entering variable has
  an improving pivot direction of largest slope `cᵀz / vᵀz`.

The leaving variable is any one allowed by the ratio test. The run is *terminal* when `B T` is
an optimal basis.

**Formalization Note.** The paper assembles the rule from Definition 5, Theorem 7, Lemma 6 and
§3.4 and gives no single definition; this is that assembly, with the condition on the whole cone
as in the statements of Theorem 7 and Lemma 6. -/
def IsRun (B0 : Finset (Fin n ⊕ Fin p)) (T t0 : ℕ) (B : ℕ → Finset (Fin n ⊕ Fin p)) : Prop :=
  t0 ≤ T ∧ B 0 = B0 ∧ L.IsFeasibleBasis B0 ∧
    (∀ t < t0, L.IsDegeneratePivot (B t) (B (t + 1))) ∧
    L.IsReady (B t0) (L.orderedShadowVec (L.vertexOf B0)) ∧
    ∀ t, t0 ≤ t → t < T → ∃ j ℓ, L.IsPivot (B t) (B (t + 1)) j ℓ ∧
      L.IsShadowEntering (B t) (L.orderedShadowVec (L.vertexOf B0)) j

/-- The right-hand side `b'(ε) = b' + Σ_{i=1}^{m+p} εⁱ A'_{e(i)}` of the lexicographic
(perturbation) method, for an ordering `e` of the basis at which it starts. -/
def perturbedRhs (e : Fin (m + p) → Fin n ⊕ Fin p) (ε : ℝ) : Fin m ⊕ Fin p → ℝ :=
  fun r => L.stdb r + ∑ i : Fin (m + p), ε ^ (i.val + 1) * L.stdA r (e i)

/-- **A lexicographic run** (arXiv:2111.14050v1, §3.4, pp.24–25: "the Ordered Shadow and Slim
Shadow pivot rules can be implemented correctly using the lexicographic method"): a run in which
Phase 2 uses the lexicographic leaving rule. `e` lists the basis `B t₀` (a bijection
`{1, …, m+p} → B t₀`), and every basis `B t`, `t₀ ≤ t ≤ T`, is feasible for the perturbed
right-hand side `b'(ε)` for all sufficiently small `ε > 0`.

**Formalization Note.** The lexicographic rule is encoded by right-hand-side perturbation: a
pivot keeps feasibility for `b'(ε)`, for all small `ε > 0`, exactly when its leaving variable is
the lexicographic choice of the ratio test. The perturbation starts at the Phase 2 basis
`B t₀`; Phase 1 is finite by construction. -/
def IsLexRun (B0 : Finset (Fin n ⊕ Fin p)) (T t0 : ℕ) (B : ℕ → Finset (Fin n ⊕ Fin p))
    (e : Fin (m + p) → Fin n ⊕ Fin p) : Prop :=
  L.IsRun B0 T t0 B ∧ Function.Injective e ∧ (∀ i, e i ∈ B t0) ∧
    ∀ t, t0 ≤ t → t ≤ T → ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ L.basicSolFor (B t) (L.perturbedRhs e ε)

open Classical in
/-- The number of **non-degenerate pivots** among the first `T` pivots of the basis sequence
`B`: the steps `t < T` at which the vertex changes. -/
noncomputable def nonDegCount (B : ℕ → Finset (Fin n ⊕ Fin p)) (T : ℕ) : ℕ :=
  ((Finset.range T).filter (fun t => L.vertexOf (B (t + 1)) ≠ L.vertexOf (B t))).card

end LPData

end ZeroOneSimplex


