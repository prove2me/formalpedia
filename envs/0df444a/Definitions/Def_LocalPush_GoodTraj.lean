-- Prove2me | Definitions.Def_LocalPush_GoodTraj
-- name    : LocalPush_GoodTraj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:06:10.673839+00:00
-- url     : https://prove2.me/theorems/cce1806c-2461-4f67-94c2-fb5913bcd4dd
-- title:
--   Algorithm 3 (GeneralActiveSetPush): parameters, solver guarantee (6), good trajectories, $\Delta\psi(a,b)$
-- statement:
--   Algorithm 3 takes $\alpha\in(0,1)$, $\lambda>0$, $\eta>0$ and $0<\kappa\le0.4\alpha\eta^2$, sets $\mu:=0.01\alpha\min\{\lambda,\kappa\}$ and $\mathcal S_0:=\{s\}$, and in iteration $i$:
--
--   1. approximately solves $L_{\alpha,\mathcal S}x_{\mathcal S}=\alpha(e_s|_{\mathcal S}-\lambda d_{\mathcal S})$, the output $\tilde x$ satisfying
--   $$\|\tilde x_{\mathcal S}-L_{\alpha,\mathcal S}^{-1}b\|_{L_{\alpha,\mathcal S}}\le\mu\|L_{\alpha,\mathcal S}^{-1}b\|_{L_{\alpha,\mathcal S}};\tag{6}$$
--   2. returns if $\tilde r(v)\le(\lambda+\eta)d(v)$ for all $v\in\partial\mathcal S$;
--   3. otherwise adds $\{v\in\partial\mathcal S:\tilde r(v)>(\lambda+\kappa)d(v)\}$ to $\mathcal S$.
--
--   `Params` collects these parameter conditions together with the nontrivial case $(\lambda+\eta)d(s)<1$. A good trajectory reaching iterations $0,\dots,N$ is a sequence of sets $S_i$ and outputs $\tilde x_i$ (zero off $S_i$) such that every output satisfies (6), the stopping rule fails at $0,\dots,N-1$, and $S_{i+1}$ is the expansion of $S_i$. The exact states are $x_i=x^{(S_i)}$, $r_i=r(x_i)$, and $\Delta\psi(a,b):=\psi_\lambda(x_a)-\psi_\lambda(x_b)$.
--
--   These are the objects of the analysis of §5.1–5.2 on the good event $\mathcal G$.
--
--   **Formalization Note** Algorithm 3 is a relation over solver outputs: every output satisfying (6) is allowed. Line 7 computes $\tilde r$ on $\partial\mathcal S$ by eq. (10), which equals the residue $r(\tilde x)$ there, so the rules are written with $r(\tilde x)$.
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), Algorithm 3, p.18 (PDF p.18); eq. (6), p.15; §5.1, pp.17–18; §5.2, p.20

import Mathlib
import Definitions.Def_LocalPush_SDD
import Definitions.Def_LocalPush_ResidueSystem

open Finset Matrix

namespace LocalPush

/-!
# Algorithm 3 (GeneralActiveSetPush): parameters, solver guarantee (6), good trajectories

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), Algorithm 3, p.18 (PDF p.18);
eq. (6), p.15; the trajectory notation of §5.1, pp.17–18, and §5.2, p.20.

Algorithm 3 takes `α ∈ (0, 1)`, `λ > 0`, `η > 0`, `0 < κ ≤ 0.4αη²`, sets `µ := 0.01α min{λ, κ}` and
`𝒮 := {s}`, and repeats: solve `L_{α,𝒮} x_𝒮 = α(e_s|_𝒮 − λd_𝒮)` to accuracy `µ` (guarantee (6)); return if
`r̃(v) ≤ (λ + η)d(v)` on `∂𝒮`; else add `{v ∈ ∂𝒮 : r̃(v) > (λ + κ)d(v)}` to `𝒮`.

**Formalization Note.**
* `Params` collects the standing parameters of Algorithm 3 together with `(λ + η)d(s) < 1`, the nontrivial case
  ("For the remainder of the analysis, assume that (λ + η)d(s) < 1", p.20). The branch `(λ + η)d(s) ≥ 1`, which
  returns `0` on line 2, is not a trajectory.
* `SolveGood … S x̃` is guarantee (6) for the system of line 6: `‖x̃|_S − L_{α,S}⁻¹b‖_{L_{α,S}} ≤
  µ‖L_{α,S}⁻¹b‖_{L_{α,S}}` with `b = α(e_s|_S − λd_S)`.
* Line 7 computes `r̃(v) = ((1−α)/α)∑_{u∈N(v)∩𝒮} x̃_𝒮(u)` on `∂𝒮`. For `x̃` vanishing off `𝒮` and `s ∈ 𝒮` this
  equals the residue `r(x̃)(v)` of (8) (eq. (10), milestone `LocalPush.eq_9_10`), so the stopping rule and the
  expansion are written with `resid`.
* `GoodTraj … N S xt` is a run of Algorithm 3 that reaches iterations `0, …, N`, in which every solver output
  `xt i` (extended by zero outside `S i`) satisfies (6), and in which the stopping rule fails at iterations
  `0, …, N − 1`. It is the paper's trajectory on the good event `𝒢` (p.19), with `N` the number of expansions
  performed so far. A terminated run has `StopRule` at `N`; a good trajectory need not be terminated.
* Algorithm 3 is a relation over solver outputs here: every output satisfying (6) is allowed, not only exact
  solves. The exact state of iteration `i` is `exactX … i = x^(S_i)`, with residue `exactR … i = r(x_i)`.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The parameters of Algorithm 3 in its nontrivial case: `0 < α < 1`, `λ, η > 0`, `0 < κ ≤ 0.4αη²`, and
`(λ + η)d(s) < 1`. -/
structure Params (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α lam η κ : ℝ) : Prop where
  alpha_pos : 0 < α
  alpha_lt_one : α < 1
  lam_pos : 0 < lam
  eta_pos : 0 < η
  kappa_pos : 0 < κ
  kappa_le : κ ≤ 0.4 * α * η ^ 2
  nontrivial : (lam + η) * deg G s < 1

/-- The solver accuracy `µ := 0.01α min{λ, κ}` (line 3 of Algorithm 3). -/
noncomputable def mu (α lam κ : ℝ) : ℝ :=
  0.01 * α * min lam κ

/-- Guarantee (6) for the solve of line 6 on the set `S`: `‖x̃|_S − L_{α,S}⁻¹b‖_{L_{α,S}} ≤ µ‖L_{α,S}⁻¹b‖_{L_{α,S}}`
with `b = α(e_s|_S − λd_S)`. -/
def SolveGood (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α lam κ : ℝ) (S : Finset V)
    (xt : V → ℝ) : Prop :=
  enorm (LαS G α S) (restr S xt - (LαS G α S)⁻¹ *ᵥ bvec G s α lam S) ≤
    mu α lam κ * enorm (LαS G α S) ((LαS G α S)⁻¹ *ᵥ bvec G s α lam S)

/-- The stopping rule of line 8: `r̃(v) ≤ (λ + η)d(v)` for every `v ∈ ∂S`. -/
def StopRule (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α lam η : ℝ) (S : Finset V)
    (xt : V → ℝ) : Prop :=
  ∀ v ∈ bdry G S, resid G α s xt v ≤ (lam + η) * deg G v

open scoped Classical in
/-- The expansion of line 10: `S ∪ {v ∈ ∂S : r̃(v) > (λ + κ)d(v)}`. -/
noncomputable def expand (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α lam κ : ℝ) (S : Finset V)
    (xt : V → ℝ) : Finset V :=
  S ∪ (bdry G S).filter fun v => (lam + κ) * deg G v < resid G α s xt v

/-- A good trajectory of Algorithm 3 reaching iterations `0, …, N`: `S 0 = {s}`; for `i ≤ N` the solver output
`xt i` vanishes off `S i` and satisfies (6); for `i < N` the stopping rule fails and `S (i+1)` is the
expansion of line 10. -/
structure GoodTraj (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α lam η κ : ℝ) (N : ℕ)
    (S : ℕ → Finset V) (xt : ℕ → V → ℝ) : Prop where
  start : S 0 = {s}
  supp_sub : ∀ i ≤ N, ∀ v ∉ S i, xt i v = 0
  solve : ∀ i ≤ N, SolveGood G s α lam κ (S i) (xt i)
  no_stop : ∀ i < N, ¬ StopRule G s α lam η (S i) (xt i)
  next : ∀ i < N, S (i + 1) = expand G s α lam κ (S i) (xt i)

/-- The exact state `x_i := x^(S_i)` of iteration `i` (p.18). -/
noncomputable def exactX (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α lam : ℝ)
    (S : ℕ → Finset V) (i : ℕ) : V → ℝ :=
  xS G s α lam (S i)

/-- The exact residue `r_i := r(x_i)` of iteration `i` (p.18). -/
noncomputable def exactR (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α lam : ℝ)
    (S : ℕ → Finset V) (i : ℕ) : V → ℝ :=
  resid G α s (exactX G s α lam S i)

/-- The interval objective decrease `∆ψ(a, b) := ψ_λ(x_a) − ψ_λ(x_b)` (p.20); `∆ψ_i = ∆ψ(i, i+1)`. -/
noncomputable def dPsi (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α lam : ℝ)
    (S : ℕ → Finset V) (a b : ℕ) : ℝ :=
  psi G s α lam (exactX G s α lam S a) - psi G s α lam (exactX G s α lam S b)

end LocalPush


