-- Prove2me | Definitions.Def_PolyContract_QuadInstance
-- name    : PolyContract_QuadInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:06.391371+00:00
-- url     : https://prove2.me/theorems/08fc3189-a3bd-439b-a30e-7f94c63e788c
-- title:
--   Contract instance with quadratic costs: best response, $U_P$, optimal contract, $\rho$, $A_\theta$, $F_{\alpha,\theta}$
-- statement:
--   An **instance** $(f,m,\beta)$ consists of a set function $f$ on a finite ground set $E$, rewards $m\in\mathbb R^E$ and curvatures $\beta\in\mathbb R^E$. It is **valid** when $f$ is a rank function, $m\ge 0$ and $\beta_e>0$ for all $e$. The agent picks $x\in P^{(+)}(f)$, earns the expected reward $r(x)=m^\top x$ and pays the quadratic cost $c(x)=\sum_e\beta_e x_e^2/2$. Under a linear contract with share $\alpha$, the utilities are
--   $$U_A(x\mid\alpha):=\alpha\,r(x)-c(x),\qquad U_P(x\mid\alpha):=(1-\alpha)\,r(x).$$
--
--   The module defines:
--
--   1. a **best response** to $\alpha$: a maximizer of $U_A(\cdot\mid\alpha)$ over $P^{(+)}(f)$;
--   2. the reward $r(x^\star(\alpha))$ under the best response with ties broken in favour of the principal, i.e. the largest reward over all best responses, and $U_P(\alpha):=(1-\alpha)\,r(x^\star(\alpha))$;
--   3. an **optimal contract**: a share $\alpha^\star\in[0,1]$ maximizing $U_P$ on $[0,1]$;
--   4. $t_e:=m_e/\beta_e$, the **marginals** $\rho_e(x):=\alpha m_e-\beta_e x_e$, the **level sets** $A_\theta(x):=\{e:\rho_e(x)\ge\theta\}$, and $F_{\alpha,\theta}(S):=f(S)-\alpha\,t(S)+\theta\,\beta^{-1}(S)$ with $\beta^{-1}(S)=\sum_{e\in S}1/\beta_e$;
--   5. **breakpoints**: shares $b>0$ at which $x^\star$ is not affine on any neighbourhood;
--   6. the **maximal minimizer** of a set function: a minimizer that contains every minimizer.
--
--   All statements of the mission are phrased with these notions.
--
--   **Formalization Note** The principal-favouring tie rule is a supremum over the set of best responses; for a valid instance and $\alpha\ge0$ the best response is unique (a milestone of the mission), so the supremum is the reward of that point. "Not affine on any neighbourhood" means that no $\varepsilon>0$ and vectors $u,v$ have every best response at every share within $\varepsilon$ of $b$ equal to $u+\alpha v$.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), §2, pp.5–6 (PDF pp.6–7); §3, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_PolyContract_IsRankFunction

set_option autoImplicit false

namespace PolyContract

/-- An **instance with quadratic costs** (Klimm, Lippke, Warode, *The Complexity of Continuous
Contract Design over Polymatroids*, arXiv:2611.04934, version of November 3, 2026, sha256
18cfc0a5…, §2, pp.5–6, and §3, p.6): a set function `f` on the ground set `E` (the finite type
`ι`), rewards `m ∈ ℝ^E` and curvatures `β ∈ ℝ^E`. The agent's cost is
`c(x) = Σ_e β_e x_e² / 2` and its expected reward is `r(x) = m⊤x`.

**Formalization Note** The structure carries only the data; the paper's standing hypotheses
(`f` a rank function, `m ≥ 0`, `β > 0`) are the predicate `QuadInstance.Valid`. The same data
type is reused for the full plane of App. B.6.1, where `f` is only submodular with `f(∅) = 0`. -/
structure QuadInstance (ι : Type) where
  /-- The set function `f : 2^E → ℝ`. -/
  f : Finset ι → ℝ
  /-- The rewards `m_e`. -/
  m : ι → ℝ
  /-- The curvatures `β_e`. -/
  β : ι → ℝ

namespace QuadInstance

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The standing hypotheses of an instance (arXiv:2611.04934, §2, p.5 and §3, p.6): `f` is a
rank function, `m ∈ ℝ^E_{≥0}`, and the curvatures are positive, `β_e > 0`. -/
def Valid (I : QuadInstance ι) : Prop :=
  IsRankFunction I.f ∧ (∀ e, 0 ≤ I.m e) ∧ ∀ e, 0 < I.β e

/-- The expected reward `r(x) := m⊤x` (arXiv:2611.04934, §2, p.5). -/
def reward (I : QuadInstance ι) (x : ι → ℝ) : ℝ := ∑ e, I.m e * x e

/-- The quadratic cost `c(x) = Σ_e β_e x_e²/2` (arXiv:2611.04934, §3, p.6). -/
noncomputable def cost (I : QuadInstance ι) (x : ι → ℝ) : ℝ := ∑ e, I.β e * x e ^ 2 / 2

/-- The agent's expected utility `U_A(x | α) := α r(x) − c(x)` (arXiv:2611.04934, §2, p.5). -/
noncomputable def agentUtility (I : QuadInstance ι) (α : ℝ) (x : ι → ℝ) : ℝ := α * I.reward x - I.cost x

/-- `x` is a **best response** to the share `α`: `x ∈ arg max_{x ∈ P(+)(f)} U_A(x | α)`
(arXiv:2611.04934, §2, p.5). -/
def IsBestResponse (I : QuadInstance ι) (α : ℝ) (x : ι → ℝ) : Prop :=
  x ∈ indepPoly I.f ∧ ∀ y ∈ indepPoly I.f, I.agentUtility α y ≤ I.agentUtility α x

/-- The reward `r(x⋆(α))` under the best response, with ties broken in favour of the principal
(arXiv:2611.04934, §2, pp.5–6): the largest reward over the set of best responses.

**Formalization Note** Written as `sSup` of the rewards of all best responses. For a valid
instance and `α ≥ 0` the best response exists and is unique (§3, p.7), so this is the reward of
that point; the tie rule only matters for the general cost functions of §2. -/
noncomputable def brReward (I : QuadInstance ι) (α : ℝ) : ℝ :=
  sSup (I.reward '' {x | I.IsBestResponse α x})

/-- The principal's utility `U_P(α) := U_P(x⋆(α) | α) = (1 − α) r(x⋆(α))`
(arXiv:2611.04934, §2, pp.5–6), with the principal-favouring tie rule of `brReward`. -/
noncomputable def principalUtility (I : QuadInstance ι) (α : ℝ) : ℝ :=
  (1 - α) * I.brReward α

/-- `a` is an **optimal contract**: `a ∈ arg max_{α ∈ [0,1]} U_P(α)` (arXiv:2611.04934, §2,
p.6). -/
def IsOptimalContract (I : QuadInstance ι) (a : ℝ) : Prop :=
  a ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ α ∈ Set.Icc (0 : ℝ) 1, I.principalUtility α ≤ I.principalUtility a

/-- `t_e := m_e / β_e` (arXiv:2611.04934, §3, p.7). -/
noncomputable def t (I : QuadInstance ι) (e : ι) : ℝ := I.m e / I.β e

/-- The marginal utility `ρ_e(x) := α m_e − β_e x_e` at the share `α` (arXiv:2611.04934, (3.1),
p.7). -/
def marginal (I : QuadInstance ι) (α : ℝ) (x : ι → ℝ) (e : ι) : ℝ := α * I.m e - I.β e * x e

open Classical in
/-- The upper level set `A_θ(x) := {e ∈ E : ρ_e(x) ≥ θ}` at the share `α` (arXiv:2611.04934,
§3, p.7). -/
noncomputable def levelSet (I : QuadInstance ι) (α : ℝ) (x : ι → ℝ) (θ : ℝ) : Finset ι :=
  Finset.univ.filter fun e => θ ≤ I.marginal α x e

/-- `F_{α,θ}(S) := f(S) − α t(S) + θ β⁻¹(S)` with `β⁻¹(S) := Σ_{e ∈ S} 1/β_e`
(arXiv:2611.04934, §3, p.7). -/
noncomputable def Ffun (I : QuadInstance ι) (α θ : ℝ) (S : Finset ι) : ℝ :=
  I.f S - α * setSum I.t S + θ * setSum (fun e => 1 / I.β e) S

/-- A share `b` is a **breakpoint** (arXiv:2611.04934, §3, p.7): `b > 0` and the best response
`x⋆` is not affine on any neighbourhood of `b`.

**Formalization Note** "`x⋆` is affine on a neighbourhood of `b`" reads: for some `ε > 0` and
vectors `u, v`, every best response at every share `α` with `|α − b| < ε` equals `u + α v`. The
best response is unique for valid instances and `α ≥ 0` (§3, p.7). -/
def IsBreakpoint (I : QuadInstance ι) (b : ℝ) : Prop :=
  0 < b ∧ ¬ ∃ ε > 0, ∃ u v : ι → ℝ, ∀ α : ℝ, |α - b| < ε →
    ∀ x, I.IsBestResponse α x → x = u + α • v

end QuadInstance

/-- `S` is the **maximal minimizer** of a set function `F` (arXiv:2611.04934, Theorem 3.3, p.7,
and Lemma B.9, p.27): `S` minimizes `F` over all subsets, and every minimizer is contained in `S`.
Such a set is unique when it exists. -/
def IsMaximalMinimizer {ι : Type} (F : Finset ι → ℝ) (S : Finset ι) : Prop :=
  (∀ T, F S ≤ F T) ∧ ∀ T, (∀ U, F T ≤ F U) → T ⊆ S

end PolyContract


