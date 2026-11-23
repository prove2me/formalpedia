-- Prove2me | Definitions.Def_DriftVarCtrl_FixedLB_Supplement_FreeModel
-- name    : DriftVarCtrl_FixedLB_Supplement_FreeModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:35:01.121041+00:00
-- url     : https://prove2.me/theorems/cb3556a0-fd7d-4a3f-8ef1-42d2e1e1c3fc
-- title:
--   Definition 5 and (112)–(115), pp. EC-18–EC-19 — stopping k-interval policies, their value, optimality and early abandonment
-- statement:
--   The free-lower-boundary problem of §5 lets the entrepreneur stop at any level below the upper boundary. Fix the primitives of the base model: drifts $\mu_1,\mu_2>0$, volatilities $\sigma_1,\sigma_2>0$, running costs $h_1,h_2>0$, an upper boundary $U>0$ and the terminal cost $M<0$ paid on hitting $U$; stopping costs nothing.
--
--   1. **Stopping $k$-interval policy** (Definition 5). Breakpoints $z_0=S_0<S_1<\dots<S_k=U$ with $k\ge1$ and $z_0$ any real number below $U$ (negative values included), and controls $i_1,\dots,i_k\in\{1,2\}$ with $i_j\ne i_{j+1}$. Control $i_j$ is used on $[S_{j-1},S_j)$ and the entrepreneur stops as soon as $X\le z_0$. Two such policies are named: *use control $c$ on $[z,U)$, stop below* ($z<U$), and *use control 1 on $[z,s)$, control 2 on $[s,U)$, stop below* ($z<s<U$).
--   2. **Value of a policy.** A function $W:\mathbb R\to\mathbb R$ is a value of the policy when $W(x)=0$ for $x\le z_0$ and $W(U)=M$ (the boundary conditions (115)), $W$ is $C^1$ on $[z_0,U]$, and on every open piece $(S_{j-1},S_j)$ it is $C^2$ and
--   $$h_{i_j}+\mu_{i_j}W'(x)+\frac{\sigma_{i_j}^2}{2}W''(x)=0 .$$
--   3. **Optimality.** A policy is optimal when it has a value $V$ with $V(x)\le W(x)$ for every $x\le U$, every stopping interval policy (every stopping level, every number of intervals) and every value $W$ of it. This is minimization of the expected cost (112).
--   4. **Abandoning early.** It is optimal to abandon early when some optimal stopping interval policy has stopping level $z_0>0$, above the fixed lower boundary $0$.
--   5. For the quantities that vary the upper boundary (Lemmas 15–17), $\mathrm{withU}(p,\tilde U)$ is the model with the same drifts, volatilities, costs and $M$ and upper boundary $\tilde U>0$.
--
--   These objects state Theorems 3 and 4 and the verification Lemma 18.
--
--   **Formalization Note** The value is the analytic boundary-value system the paper writes for every policy it evaluates ((143)–(144), (151), (162)–(167)); the identity with the expected cost (112) (Dynkin's formula) is not formalized, because Mathlib has no stochastic integral. No smooth pasting is imposed at $z_0$: it characterizes the optimal level, not every policy.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. EC-18–EC-19, Definition 5, (112)–(115); p. 19, Theorem 3 ("abandon early"); pp. EC-23, EC-28 (Ũ-dependent quantities)

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model

namespace DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- The same primitives with the upper boundary replaced by `U' > 0` (Wang, Zenios, *New Venture
Creation: A Drift-Variance Diffusion Control Model*, SSRN 3667132 (working paper, sha256
2d7a57ba…), pp. EC-23 and EC-28: `h⁺(Ũ)`, `dᵁ₁(Ũ)`, `h*ᵢ(Ũ)` are the quantities of the model with
upper boundary `Ũ`). -/
def withU (p : Params) (U' : ℝ) (hU' : 0 < U') : Params :=
  { p with U := U', hU := hU' }

/-- A stopping `k`-interval policy (Definition 5, SSRN 3667132 p. EC-18): breakpoints
`z₀ = S₀ < S₁ < ⋯ < S_k = U`, with `z₀` any real number below `U` (negative values included: the
entrepreneur may continue after the process hits `0`), and controls `i₁, …, i_k` with adjacent
controls distinct. Control `ctrl j` is used on `[S j.castSucc, S j.succ)` (0-based `j`) and the
entrepreneur stops as soon as `X ≤ z₀`. The lower boundary is `z₀ = S 0`. -/
structure StopPolicy (p : Params) where
  k : ℕ
  one_le_k : 1 ≤ k
  ctrl : Fin k → Ctrl
  S : Fin (k + 1) → ℝ
  S_last : S (Fin.last k) = p.U
  S_strictMono : StrictMono S
  alt : ∀ (j : ℕ) (h : j + 1 < k), ctrl ⟨j, by omega⟩ ≠ ctrl ⟨j + 1, h⟩

/-- The lower (stopping) boundary `z₀` of a stopping interval policy. -/
def StopPolicy.z₀ {p : Params} (π : StopPolicy p) : ℝ := π.S 0

/-- The static stopping policy of Theorem 4 (a), (b) (SSRN 3667132 p. 21): use control `c` on
`[z, U)` and stop on `(−∞, z]`, for a level `z < U`. -/
def stopOne (p : Params) (c : Ctrl) (z : ℝ) (hz : z < p.U) : StopPolicy p where
  k := 1
  one_le_k := le_rfl
  ctrl := fun _ => c
  S := ![z, p.U]
  S_last := rfl
  S_strictMono := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    exact hz
  alt := fun j h => absurd h (by omega)

/-- The two-interval stopping policy of Theorem 4 (c) (SSRN 3667132 p. 22): use control 1 on
`[z, s)`, control 2 on `[s, U)` and stop on `(−∞, z]`, for levels `z < s < U`. -/
def stopOneTwo (p : Params) (z s : ℝ) (hzs : z < s) (hs : s < p.U) : StopPolicy p where
  k := 2
  one_le_k := by norm_num
  ctrl := ![.one, .two]
  S := ![z, s, p.U]
  S_last := rfl
  S_strictMono := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    · exact hzs
    · exact hs
  alt := by
    intro j h
    have hj : j = 0 := by omega
    subst hj
    simp

/-- `W` is the value of the stopping interval policy `π` (analytic encoding of the expected cost
(112) of `π`, SSRN 3667132 pp. EC-18–EC-19, with the boundary conditions (115)): `W x = 0` for
every `x ≤ z₀`, `W` is `C¹` on `[z₀, U]` (smooth pasting at every switch point), `W(U) = M`, and on
every open piece `(S_{j-1}, S_j)` it is `C²` and solves `h(i_j) + μ(i_j) W′ + σ(i_j)²/2 · W″ = 0`.
This is the system the paper writes for every policy it evaluates ((143)–(144), (151), (162)–(167)).

Formalization Note: as in the base model's `IsValue`, the identity "expected cost (112) of `π` =
this `W`" (Dynkin's formula) is not formalized; Mathlib has no stochastic integral. No smooth
pasting is imposed at `z₀`: it is a property of the optimal level, not of every policy. -/
def IsStopValue (p : Params) (π : StopPolicy p) (W : ℝ → ℝ) : Prop :=
  (∀ x ≤ π.S 0, W x = 0) ∧ ContDiffOn ℝ 1 W (Set.Icc (π.S 0) p.U) ∧ W p.U = p.M ∧
  ∀ (j : Fin π.k) (x : ℝ), x ∈ Set.Ioo (π.S j.castSucc) (π.S j.succ) →
    ContDiffAt ℝ 2 W x ∧
    p.cost (π.ctrl j) + p.mu (π.ctrl j) * deriv W x
      + p.sig (π.ctrl j) ^ 2 / 2 * deriv (deriv W) x = 0

/-- `π` is optimal for the free-lower-boundary problem (112) (SSRN 3667132 p. EC-18): it has a
value `V` lying below every value `W` of every stopping interval policy `π'` (every stopping level
`z₀'`, every length `k`) at every `x ≤ U`. Minimization, since (112) is a cost and the reward
enters as `M < 0`. -/
def IsStopOptimal (p : Params) (π : StopPolicy p) : Prop :=
  ∃ V, IsStopValue p π V ∧ ∀ (π' : StopPolicy p) (W : ℝ → ℝ), IsStopValue p π' W →
    ∀ x ≤ p.U, V x ≤ W x

/-- "It is optimal for the entrepreneur to abandon early" (Theorem 3, SSRN 3667132 p. 19; proof
p. EC-27): some optimal stopping interval policy stops at a level `z₀ > 0`, i.e. before the
process hits the fixed lower boundary `0`. -/
def AbandonsEarly (p : Params) : Prop :=
  ∃ π : StopPolicy p, IsStopOptimal p π ∧ 0 < π.z₀

end DriftVarCtrl.FixedLB.Supplement


