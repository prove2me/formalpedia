-- Prove2me | Definitions.Def_FracMPGA_IsMPGARun
-- name    : FracMPGA_IsMPGARun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:40:53.513921+00:00
-- url     : https://prove2.me/theorems/a6fcb570-08a5-43de-9918-269875dea655
-- title:
--   Runs of Algorithm 1 (MPGA), CMPGA and CMPGA$_{\rm ML}$
-- statement:
--   A run of the **multi-proximity gradient algorithm** with parameters $0<\underline\alpha\le\bar\alpha$, $\sigma>0$, $0<\gamma<1$, memory $M\ge0$ and index sequence $(i_{(0)},i_{(1)},\dots)$ with $i_{(t)}\in\{0,1,\dots,N\}$ is a sequence $(x^{(t)},y^{(t)})$ with step sizes $\alpha_{(t)}$ such that $x^{(0)}\in\operatorname{dom}F$, $y^{(0)}\in\partial g(x^{(0)})$, and for every $t$:
--
--   1. with $Q_{(l(t))}=\max\{Q(x^{(s)},y^{(s)}):[t-M]_+\le s\le t\}$;
--   2. if $i_{(t)}=0$: $x^{(t+1)}=x^{(t)}$ and $y^{(t+1)}=\operatorname{prox}_{\alpha g^*}(y^{(t)}+\alpha x^{(t)})$ with $\alpha=\alpha_{(t)}\in[\underline\alpha,\bar\alpha]$;
--   3. if $i_{(t)}=i\ge1$: $y^{(t+1)}=y^{(t)}$; starting from $\tilde\alpha_{(t)}\in[\underline\alpha,\bar\alpha]$, trial points $x_i^{(t)}(\alpha)\in\operatorname{prox}_{\alpha f_i}\big(x_i^{(t)}-\alpha\nabla_ih(x^{(t)})+\alpha Q_{(t)}y_i^{(t)}\big)$ are computed for $\alpha=\tilde\alpha_{(t)}\gamma^k$, $k=0,1,\dots$, until the first one with
--   $$
--   \zeta(x^{(t),i}(\alpha))+\tfrac\sigma2\|x^{(t),i}(\alpha)-x^{(t)}\|_2^2\le Q_{(l(t))}\,\eta(x^{(t),i}(\alpha),y^{(t)}),
--   $$
--   where $x^{(t),i}(\alpha)$ is $x^{(t)}$ with block $i$ replaced by $x_i^{(t)}(\alpha)$; then $x^{(t+1)}=x^{(t),i}(\alpha)$ and $\alpha_{(t)}=\alpha$.
--
--   **CMPGA** is the cyclic choice $i_{(t)}=t\bmod(N+1)$, and **CMPGA$_{\rm ML}$** is CMPGA with $M=0$ (the monotone line search).
--
--   **Formalization Note** The $y$-step size may vary with $t$ (Algorithm 1 writes one $\tilde\alpha_Y$; §5.1 (39) writes "some $\alpha_{(k,0)}\in[\underline\alpha,\bar\alpha]$"). Each prox evaluation is a membership in the argmin set. $Q_{(t)}$ enters the prox argument as a real number; it is finite along every run. The line search records its failed trials.
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §4, p.14, Algorithm 1; §5.1, p.20 (CMPGA); §6, p.25 (CMPGA_ML)

import Mathlib
import Definitions.Def_fenchelConjugate
import Definitions.Def_FracMPGA_proxSet
import Definitions.Def_ProxAlg_FixedPoint_Basic
import Definitions.Def_FracMPGA_Problem

namespace FracMPGA

namespace Problem

variable {n N : ℕ} (P : Problem n N)

/-- The prox argument of Step 2-X of Algorithm 1 (Zhou, Zhang, Li, arXiv:2311.00957v2, p.14) for
block `i` and step size `α` at the point `(x, y)`:
`x_i − α ∇_i h(x) + α Q(x, y) y_i`.

**Formalization Note** `∇_i h(x)` is the `i`-th block of `gradient h x`, and `Q(x, y)` enters as
the real number `(Q x y).toReal`; Algorithm 1 only evaluates it on `dom(Q)` (Theorem 4.6(ii)). -/
noncomputable def xStepInput (x y : Vec n) (i : Fin N) (α : ℝ) :
    EuclideanSpace ℝ {j // P.blk j = i} :=
  P.block x i - α • P.block (gradient P.h x) i + (α * (P.Q x y).toReal) • P.block y i

/-- The reference value `Q_(l(t)) = max{Q_(s) : [t − M]₊ ≤ s ≤ t}` of Step 1 of Algorithm 1
(p.14), `Q_(s) = Q(x⁽ˢ⁾, y⁽ˢ⁾)`, computed in `EReal`. Natural-number subtraction `t - M` is
exactly `[t − M]₊`. The index `l(t)` itself is not needed: only `Q_(l(t))` enters the algorithm and
the statements. -/
noncomputable def Qwin (M : ℕ) (x y : ℕ → Vec n) (t : ℕ) : EReal :=
  ⨆ s ∈ Finset.Icc (t - M) t, P.Q (x s) (y s)

/-- The line-search test of Step 2-X (p.14) at the trial point `x'` from `(x, y)` with reference
value `c`: `ζ(x') + σ/2 ‖x' − x‖₂² ≤ c η(x', y)`, computed in `EReal`. With `c = Q_(l(t))` it is
the acceptance test of Algorithm 1; with a real `c` it is inequality (23) of Lemma 4.5. -/
def lsTest (σ : ℝ) (c : EReal) (x y x' : Vec n) : Prop :=
  P.zeta x' + ((σ / 2 * ‖x' - x‖ ^ 2 : ℝ) : EReal) ≤ c * P.eta x' y

/-- **A run of Algorithm 1 (MPGA)** of Zhou, Zhang, Li, arXiv:2311.00957v2, p.14, with
parameters `α̲ = αlo`, `ᾱ = αhi`, `σ`, `γ`, memory `M` and index sequence
`I∞ = (i(0), i(1), …)` given by `I`, producing iterates `(x⁽ᵗ⁾, y⁽ᵗ⁾) = (x t, y t)` and the
recorded step sizes `α(t) = α t`. Line by line:

* **Step 0.** `x⁽⁰⁾ ∈ dom(F)`, `y⁽⁰⁾ ∈ ∂g(x⁽⁰⁾)`, `0 < α̲ ≤ ᾱ`, `σ > 0`, `0 < γ < 1`, `M ≥ 0`.
* **Step 1.** `Q_(l(t)) = max{Q_(s) : [t − M]₊ ≤ s ≤ t}` is `Qwin M x y t`.
* **Step 2.** The picked index is `I t : Fin (N+1)`: `0` is the paper's `i = 0` (Step 2-Y), and
  `r.succ` (`r : Fin N`) is the paper's block `i = r + 1 ∈ ℕ_N` (Step 2-X).
* **Step 2-Y.** With `α := α̃_Y ∈ [α̲, ᾱ]`: `y⁽ᵗ⁺¹⁾ = prox_{αg*}(y⁽ᵗ⁾ + α x⁽ᵗ⁾)`,
  `x⁽ᵗ⁺¹⁾ = x⁽ᵗ⁾`; the recorded step is `α(t) = α`.
* **Step 2-X.** Starting from `α̃(t) ∈ [α̲, ᾱ]`, the trial steps are `α̃(t) γᵏ`, `k = 0, 1, …`. For
  each trial a point `p k ∈ prox_{α̃(t)γᵏ f_i}(x_i − α̃(t)γᵏ ∇_i h(x) + α̃(t)γᵏ Q_(t) y_i)` is
  computed (any element of the possibly set-valued prox); the test fails for `k < j` and holds at
  `k = j`; then `x⁽ᵗ⁺¹⁾` is `x⁽ᵗ⁾` with block `i` replaced by `p j`, `y⁽ᵗ⁺¹⁾ = y⁽ᵗ⁾`, and the
  recorded step is `α(t) = α̃(t) γʲ`.
* **Step 3.** `t ← t + 1`.

**Formalization Note** The y-step size `α̃_Y` may differ between iterations (the paper writes a
single `α̃_Y`, and its §5.1 (39) "with some `α(k,0) ∈ [α̲, ᾱ]`"); a constant `α̃_Y` is the special
case. Each prox evaluation is a membership in the argmin set `proxSet`; `g*` is
`ConvexOptimization.fenchelConjugate P.g`. `Q_(t)` enters the prox argument as a real number
(`xStepInput`). -/
def IsMPGARun (αlo αhi σ γ : ℝ) (M : ℕ) (I : ℕ → Fin (N + 1)) (x y : ℕ → Vec n)
    (α : ℕ → ℝ) : Prop :=
  (P.F (x 0) ≠ ⊤ ∧ y 0 ∈ ProxAlg.FixedPoint.subdifferential (fun z => (P.g z : EReal)) (x 0) ∧
    0 < αlo ∧ αlo ≤ αhi ∧ 0 < σ ∧ 0 < γ ∧ γ < 1) ∧
  ∀ t : ℕ,
    (I t = 0 →
      x (t + 1) = x t ∧ αlo ≤ α t ∧ α t ≤ αhi ∧
      y (t + 1) ∈ proxSet (α t) (ConvexOptimization.fenchelConjugate P.g) (y t + α t • x t)) ∧
    (∀ r : Fin N, I t = r.succ →
      y (t + 1) = y t ∧
      ∃ α₀ : ℝ, αlo ≤ α₀ ∧ α₀ ≤ αhi ∧
      ∃ j : ℕ, ∃ p : ℕ → EuclideanSpace ℝ {k // P.blk k = r},
        (∀ k ≤ j, p k ∈ proxSet (α₀ * γ ^ k) (P.fb r) (P.xStepInput (x t) (y t) r (α₀ * γ ^ k))) ∧
        (∀ k < j, ¬ P.lsTest σ (P.Qwin M x y t) (x t) (y t) (P.blockUpdate (x t) r (p k))) ∧
        P.lsTest σ (P.Qwin M x y t) (x t) (y t) (P.blockUpdate (x t) r (p j)) ∧
        x (t + 1) = P.blockUpdate (x t) r (p j) ∧
        α t = α₀ * γ ^ j)

/-- The cyclic index rule of CMPGA (p.20): "the index `i` … at the `t`-th iteration is chosen by
`i := t mod (N + 1)`". -/
def cyclicIdx (N t : ℕ) : Fin (N + 1) := ⟨t % (N + 1), Nat.mod_lt _ N.succ_pos⟩

/-- A run of **CMPGA** (cyclic MPGA, §5.1, p.20): Algorithm 1 with `I t = t mod (N + 1)`. -/
def IsCMPGARun (αlo αhi σ γ : ℝ) (M : ℕ) (x y : ℕ → Vec n) (α : ℕ → ℝ) : Prop :=
  P.IsMPGARun αlo αhi σ γ M (cyclicIdx N) x y α

/-- A run of **CMPGA_ML** (§6, p.25: "CMPGA with the parameter `M = 0`"), the cyclic algorithm
with the monotone line search. -/
def IsCMPGAMLRun (αlo αhi σ γ : ℝ) (x y : ℕ → Vec n) (α : ℕ → ℝ) : Prop :=
  P.IsCMPGARun αlo αhi σ γ 0 x y α

end Problem

end FracMPGA


