-- Prove2me | Definitions.Def_FKZAvg_WStar_Assumptions
-- name    : FKZAvg_WStar_Assumptions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:46.115608+00:00
-- url     : https://prove2.me/theorems/3a043695-7936-44d5-bb07-8b0a2552e160
-- title:
--   Assumptions (W*), (Wu), (B̲), optimal costs w and v_{n,α}, inequality (9), equalities (10), η of (14), u* and A_* of (15)–(17), u of (21), (22), A* of (26)
-- statement:
--   Let $\mathbb X$ and $\mathbb A$ be Borel subsets of Polish spaces, $A(x)\subseteq\mathbb A$ the nonempty set of actions available at $x$, with $\mathrm{Gr}(A)=\{(x,a): a\in A(x)\}$ Borel, $c(x,a)$ the one-step cost and $q(\cdot\mid x,a)$ the transition probability. For a policy $\pi$ let $v^\pi_{N,\alpha}(x)=\mathbb E^\pi_x\sum_{n<N}\alpha^n c(x_n,a_n)$, $v^\pi_\alpha=v^\pi_{\infty,\alpha}$ and $w^\pi(x)=\limsup_N \frac1N v^\pi_{N,1}(x)$. This item defines:
--
--   1. $v_{n,\alpha}(x)=\inf_\pi v^\pi_{n,\alpha}(x)$ and the optimal average cost $w(x)=\inf_\pi w^\pi(x)$ (infima over all policies); a stationary $\phi$ is average cost optimal if $w^\phi=w$.
--   2. Inequality (9), $\bar w+u(x)\ge c(x,\phi(x))+\int u(y)\,q(dy\mid x,\phi(x))$ for all $x$, and equalities (10), $w(x)=w^\phi(x)=\limsup_{\alpha\uparrow1}(1-\alpha)v_\alpha(x)=\bar w=w^*$ for all $x$, where $v_\alpha$ is the optimal discounted cost, $m_\alpha=\inf_x v_\alpha(x)$, $\bar w=\limsup_{\alpha\uparrow1}(1-\alpha)m_\alpha$ and $w^*=\inf_x w(x)$.
--   3. Assumption $(\underline{\mathrm B})$: $w^*<\infty$ and $\liminf_{\alpha\uparrow1}u_\alpha(x)<\infty$ for every $x$, with $u_\alpha=v_\alpha-m_\alpha$.
--   4. $\eta^\alpha_u(x,a)=c(x,a)+\alpha\int u(y)\,q(dy\mid x,a)$, $u^*(x)=\inf_{a\in A(x)}\eta^1_u(x,a)$, $A_*(x)=\{a\in A(x): u^*(x)=\eta^1_u(x,a)\}$ and $A_\alpha(x)=\{a\in A(x): v_\alpha(x)=\eta^\alpha_{v_\alpha}(x,a)\}$.
--   5. $U_\beta(x)=\inf_{\alpha\in[\beta,1)}u_\alpha(x)$.
--   6. Inf-compactness of $f$ on $U$: every level set $\{y\in U: f(y)\le\lambda\}$, $\lambda\in\mathbb R$, is compact; the class $L(\mathbb X)$ of lower semicontinuous, bounded below $\varphi$ with $\{\varphi<+\infty\}\neq\emptyset$.
--   7. Assumption $(\mathrm W^*)$: (i) $c$ is lower semicontinuous on $\mathrm{Gr}(A)$; (ii) if $x_n\to x$ in $\mathbb X$, $a_n\in A(x_n)$ and $\{c(x_n,a_n)\}$ is bounded above, then $\{a_n\}$ has a limit point $a\in A(x)$; (iii) $q(\cdot\mid x,a)$ is weakly continuous in $(x,a)\in\mathrm{Gr}(A)$. Assumption $(\mathrm{Wu})$: $c$ is inf-compact on $\mathrm{Gr}(A)$ and (iii) holds.
--   8. $u(x)=\liminf_{\alpha\uparrow1,\,y\to x}u_\alpha(y)$, the joint lower limit (21); $\underline u_\beta(x)=\liminf_{y\to x}U_\beta(y)$ (22); and $A^*(x)=\{a\in A(x): \bar w+u(x)\ge c(x,a)+\int u(y)\,q(dy\mid x,a)\}$ (26).
--
--   These are the objects of §§2–5 of the paper on which Theorem 3, the average cost optimality inequality, is stated.
--
--   **Formalization Note** The state and action spaces are types $\mathbb X$, $\mathbb A$ with a separable metrizable topology whose Borel $\sigma$-algebra is standard Borel; by the Lusin–Souslin theorem these are, up to homeomorphism, exactly the Borel subsets of Polish spaces of the paper. The model is the published `SchalAvg.AvgOpt.Model`: nonempty action sets $A(x)$ with measurable graph $\mathrm{Gr}(A)$, a Markov kernel $q$ on all of $\mathbb X\times\mathbb A$ (only its values on $\mathrm{Gr}(A)$ enter) and a cost $c$ with values in $[0,+\infty]$. The paper's cost is only bounded below; adding a constant to $c$ changes none of the statements (p. 595), so the nonnegative case is the general one. `HasSelector` is the paper's standing assumption (ii) of §2 (a measurable $\phi$ with $\phi(x)\in A(x)$). Optimal values are infima over all admissible (randomized, history-dependent) policies. Functions $u$ are $[0,+\infty]$-valued, so `InL` (the class $L(\mathbb X)$) and the operations $\eta$, $u^*$ are stated for nonnegative $u$; a bounded below $u$ reduces to this case by the same constant shift. `InfCompactOn` quantifies over levels $\lambda\ge0$, since negative levels of a nonnegative function give the empty set. `CondBLow` is not Schäl's condition (B), which bounds $\sup_\alpha u_\alpha$.
-- source:
--   Feinberg, Kasyanov & Zadoianchuk, Average Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, Math. Oper. Res. 37(4) 2012, pp. 592–600, §2 (1)–(2), Assumptions (G), (W), (Wu), (W*), (B̲), eqs. (9), (10), (14), (15), (17), (20), (21), (22), (26)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model

open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE SchalAvg.AvgOpt

namespace FKZAvg.WStar

/-! Feinberg, Kasyanov & Zadoianchuk (2012), §§2–5. The model is Schäl's `Model` (published
definition `SchalAvg_AvgOpt_Model`): action sets `A(x)` nonempty with measurable graph, the
one-step cost in `[0, ∞]` (the paper's bounded-below cost shifted by a constant, p. 595), and a
Markov kernel `q`. `Admissible` policies, `vβ` (= v_α), `mβ` (= m_α), `wβ` (= u_α),
`gUpper` (= w̄), `gStar` (= w*) and `GeneralAssumption` (= (G)) are reused from it. -/

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-- Assumption (ii) of §2 (p. 592): there exists a measurable `φ : 𝕏 → 𝔸` with `φ(x) ∈ A(x)`
for all `x`. -/
def HasSelector (M : Model X A) : Prop :=
  ∃ φ : X → A, IsStationary M φ

/-- The optimal `n`-horizon discounted cost `v_{n,α}(x) = inf_{π ∈ Π} v^π_{n,α}(x)` ((1), p. 593),
the infimum over all admissible policies. -/
noncomputable def vNOpt (M : Model X A) (n : ℕ) (α : ℝ) (x : X) : ℝ≥0∞ :=
  ⨅ π : {π : Policy X A // Admissible M π}, vN M.toMDP π.1 n α x

/-- The optimal average cost `w(x) = inf_{π ∈ Π} w^π(x)` ((2), p. 593), the infimum over all
admissible policies. -/
noncomputable def wAvg (M : Model X A) (x : X) : ℝ≥0∞ :=
  ⨅ π : {π : Policy X A // Admissible M π}, Phi M π.1 x

/-- A stationary policy `φ ∈ 𝔽` is average cost optimal: `w^φ(x) = w(x)` for all `x` (p. 593). -/
def IsAvgOpt (M : Model X A) {φ : X → A} (hφ : IsStationary M φ) : Prop :=
  ∀ x, Phi M (statPolicy hφ) x = wAvg M x

/-- Inequality (9) (p. 594) for a function `u` and a map `φ`:
`w̄ + u(x) ≥ c(x, φ(x)) + ∫ u(y) q(dy | x, φ(x))` for all `x`. -/
def Ineq9 (M : Model X A) (u : X → ℝ≥0∞) (φ : X → A) : Prop :=
  ∀ x, M.toMDP.cost x (φ x) + ∫⁻ y, u y ∂(M.toMDP.q (x, φ x)) ≤ gUpper M + u x

/-- Equalities (10) (p. 594) for the stationary policy `φ`, every one of them, for all `x`:
`w(x) = w^φ(x) = limsup_{α ↑ 1} (1 − α) v_α(x) = w̄ = w*`. -/
def Eq10 (M : Model X A) {φ : X → A} (hφ : IsStationary M φ) : Prop :=
  ∀ x, wAvg M x = Phi M (statPolicy hφ) x ∧
    Phi M (statPolicy hφ) x =
      limsup (fun α : ℝ => ENNReal.ofReal (1 - α) * vβ M α x) (𝓝[<] 1) ∧
    limsup (fun α : ℝ => ENNReal.ofReal (1 - α) * vβ M α x) (𝓝[<] 1) = gUpper M ∧
    gUpper M = gStar M

/-- Assumption (B̲) (p. 599): (i) Assumption (G) holds, and (ii) `liminf_{α ↑ 1} u_α(x) < ∞`
for all `x`. (Not Schäl's (B), which bounds the supremum over `α`.) -/
def CondBLow (M : Model X A) : Prop :=
  GeneralAssumption M ∧ ∀ x, liminf (fun α : ℝ => wβ M α x) (𝓝[<] 1) < ⊤

/-- The operation (14) (p. 596): `η^α_u(x, a) = c(x, a) + α ∫ u(y) q(dy | x, a)`, for `α ≥ 0`;
only its values on `Gr(A)` are used. -/
noncomputable def eta (M : Model X A) (u : X → ℝ≥0∞) (α : ℝ) (x : X) (a : A) : ℝ≥0∞ :=
  M.toMDP.cost x a + ENNReal.ofReal α * ∫⁻ y, u y ∂(M.toMDP.q (x, a))

/-- The function (15) (p. 597): `u*(x) = inf_{a ∈ A(x)} [c(x, a) + ∫ u(y) q(dy | x, a)]`. -/
noncomputable def uStar (M : Model X A) (u : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ⨅ a ∈ M.Aset x, eta M u 1 x a

/-- The sets (17) (p. 597):
`A_*(x) = {a ∈ A(x) : u*(x) = c(x, a) + ∫ u(y) q(dy | x, a)}`. -/
def AsubStar (M : Model X A) (u : X → ℝ≥0∞) (x : X) : Set A :=
  {a | a ∈ M.Aset x ∧ uStar M u x = eta M u 1 x a}

/-- The sets of Theorem 2(iv) (p. 599): `A_α(x) = {a ∈ A(x) : v_α(x) = η^α_{v_α}(x, a)}`. -/
noncomputable def AAlpha (M : Model X A) (α : ℝ) (x : X) : Set A :=
  {a | a ∈ M.Aset x ∧ vβ M α x = eta M (vβ M α) α x a}

/-- `U_β(x) = inf_{α ∈ [β, 1)} u_α(x)` ((22), p. 600). -/
noncomputable def UInf (M : Model X A) (β : ℝ) (x : X) : ℝ≥0∞ :=
  ⨅ α ∈ Set.Ico β 1, wβ M α x

section Topology

variable [TopologicalSpace X] [TopologicalSpace A]

/-- Inf-compactness on `U` (p. 595): every level set `{y ∈ U : f(y) ≤ λ}`, `λ ∈ ℝ`, is compact.
For a `[0, ∞]`-valued `f` the levels `λ < 0` give the empty set, so levels `λ ≥ 0` suffice. -/
def InfCompactOn {Y : Type*} [TopologicalSpace Y] (f : Y → ℝ≥0∞) (U : Set Y) : Prop :=
  ∀ l : ℝ≥0, IsCompact {y | y ∈ U ∧ f y ≤ (l : ℝ≥0∞)}

/-- The class `L(𝕏)` (p. 596) for `[0, ∞]`-valued functions: `φ` is lower semicontinuous (bounded
below is automatic) and `dom φ = {x : φ(x) < +∞}` is nonempty. -/
def InL (φ : X → ℝ≥0∞) : Prop :=
  LowerSemicontinuous φ ∧ ∃ x, φ x ≠ ⊤

/-- Assumption (W(i)) = (W*(i)) (p. 595): `c` is lower semicontinuous (and bounded below) on
`Gr(A)`. -/
def CondWStar_i (M : Model X A) : Prop :=
  LowerSemicontinuousOn (fun p : X × A => M.toMDP.cost p.1 p.2) (graphA M)

/-- Assumption (W*(ii)) (p. 595): if `x_n → x` in `𝕏`, `a_n ∈ A(x_n)`, and `{c(x_n, a_n)}` is
bounded above (by a finite constant), then `{a_n}` has a limit point `a ∈ A(x)`. -/
def CondWStar_ii (M : Model X A) : Prop :=
  ∀ (xs : ℕ → X) (x : X) (as : ℕ → A), Tendsto xs atTop (𝓝 x) →
    (∀ n, as n ∈ M.Aset (xs n)) → (∃ C : ℝ≥0, ∀ n, M.toMDP.cost (xs n) (as n) ≤ (C : ℝ≥0∞)) →
    ∃ a ∈ M.Aset x, MapClusterPt a atTop as

/-- Assumption (W(iii)) = (W*(iii)) (p. 595): `q(· | x, a)` is weakly continuous in
`(x, a) ∈ Gr(A)`. -/
def CondWStar_iii (M : Model X A) : Prop :=
  ∀ f : X →ᵇ ℝ, ContinuousOn (fun p : X × A => ∫ y, f y ∂(M.toMDP.q p)) (graphA M)

/-- Assumption (W*) (p. 595): (i), (ii) and (iii). -/
def CondWStar (M : Model X A) : Prop :=
  CondWStar_i M ∧ CondWStar_ii M ∧ CondWStar_iii M

/-- Assumption (Wu) (p. 595): (i) `c` is inf-compact on `Gr(A)`; (ii) Assumption (W(iii)). -/
def CondWu (M : Model X A) : Prop :=
  InfCompactOn (fun p : X × A => M.toMDP.cost p.1 p.2) (graphA M) ∧ CondWStar_iii M

/-- The function (21) (p. 600): `u(x) = liminf_{α ↑ 1, y → x} u_α(y)`, the joint lower limit. -/
noncomputable def uAvg (M : Model X A) (x : X) : ℝ≥0∞ :=
  liminf (fun p : ℝ × X => wβ M p.1 p.2) ((𝓝[<] (1 : ℝ)) ×ˢ 𝓝 x)

/-- `u̲_β(x) = liminf_{y → x} U_β(y)` ((22), p. 600). -/
noncomputable def uLow (M : Model X A) (β : ℝ) (x : X) : ℝ≥0∞ :=
  liminf (fun y => UInf M β y) (𝓝 x)

/-- The sets (26) (p. 600):
`A*(x) = {a ∈ A(x) : w̄ + u(x) ≥ c(x, a) + ∫ u(y) q(dy | x, a)}`, with `u` of (21). -/
def AsupStar (M : Model X A) (x : X) : Set A :=
  {a | a ∈ M.Aset x ∧
    M.toMDP.cost x a + ∫⁻ y, uAvg M y ∂(M.toMDP.q (x, a)) ≤ gUpper M + uAvg M x}

end Topology

end FKZAvg.WStar


