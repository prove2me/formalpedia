-- Prove2me | Definitions.Def_AdaptiveEM_Infinite_Assumptions
-- name    : AdaptiveEM_Infinite_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:05.822867+00:00
-- url     : https://prove2.me/theorems/192ed079-2ef6-4f1e-b51d-1268d4ecb8a7
-- title:
--   Assumptions 3, 7, 8, 9 and conditions (7), (14) of Fang–Giles (2020)
-- statement:
--   Let $f:\mathbb R^m\to\mathbb R^m$, $g:\mathbb R^m\to\mathbb R^{m\times d}$ and $h:\mathbb R^m\to\mathbb R$, with the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm on $\mathbb R^m$ and the Frobenius norm on matrices.
--
--   1. **Local Lipschitz condition (7).** For every $R>0$ there is $C_R$ with $\|f(x)-f(y)\|+\|g(x)-g(y)\|\le C_R\|x-y\|$ whenever $\|x\|,\|y\|\le R$.
--   2. **Assumption 7 (dissipative condition)** with constants $\alpha,\beta>0$: (7) holds, and for all $x$,
--   $$\langle x,f(x)\rangle\le-\alpha\|x\|^2+\beta\quad(17),\qquad \|g(x)\|^2\le\beta\quad(18).$$
--   3. **Assumption 8 (adaptive timestep for the infinite interval)** with constants $h_{\max},\alpha,\beta>0$: $h$ is continuous, $0<h(x)\le h_{\max}$ for all $x$, and
--   $$\langle x,f(x)\rangle+\tfrac12h(x)\|f(x)\|^2\le-\alpha\|x\|^2+\beta\quad(19).$$
--   4. **Polynomial growth Lipschitz condition (14)** with $\gamma,\mu,q>0$: $\|f(x)-f(y)\|\le(\gamma(\|x\|^q+\|y\|^q)+\mu)\|x-y\|$.
--   5. **Assumption 9 (contractive Lipschitz properties)** with $p^*\in(2,\infty)$ and $\lambda,\eta>0$: for all $x,y$,
--   $$\langle x-y,f(x)-f(y)\rangle+\frac{p^*-1}2\|g(x)-g(y)\|^2\le-\lambda\|x-y\|^2\quad(20),\qquad \|g(x)-g(y)\|^2\le\eta\|x-y\|^2\quad(21),$$
--   and $f$ satisfies (14).
--   6. **Assumption 3** for one value $\delta$ and a constant $T$: a timestep function $h^\delta$ satisfies $\delta\min(T,h(x))\le h^\delta(x)\le\min(\delta T,h(x))$ for all $x$ (11).
--
--   These are the hypotheses of the infinite-time stability and convergence results: Assumption 7 drives the solution towards a bounded region, Assumption 8 makes the adaptive timestep small enough to preserve that drift on the discrete level, Assumption 9 makes two solutions contract towards each other, and Assumption 3 describes the refined timestep $h^\delta$ whose limit $\delta\to0$ is studied.
--
--   **Formalization Note** The source also calls $g$ "nondegenerate" in Assumption 7; this word is never defined in the paper and is not used by Lemma 3, Theorem 5 or Theorem 6, so it is not encoded. Assumption 8's "bounded" is the bound $h\le h_{\max}$. The constants of each assumption are explicit arguments, and Assumptions 7 and 8 have independent $\alpha,\beta$. Powers $\|x\|^q$ are real powers. `lam` stands for $\lambda$. In the infinite-time setting $T$ in Assumption 3 is a fixed positive constant, not a time horizon.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 528, (7); p. 530, Assumption 3 (11) and (14); p. 532, Assumption 7 (17), (18); p. 533, Assumption 8 (19), Assumption 9 (20), (21)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace AdaptiveEM.Infinite

open EthierKurtz

/-- Fang–Giles (2020), p. 528, (7): `f` and `g` are locally Lipschitz: for every `R > 0`
there is `C_R` with `‖f x − f y‖ + ‖g x − g y‖ ≤ C_R ‖x − y‖` whenever `‖x‖, ‖y‖ ≤ R`. -/
def LocallyLipschitz7 {m d : ℕ} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ C : ℝ, ∀ x y : SDEState m, ‖x‖ ≤ R → ‖y‖ ≤ R →
    ‖f x - f y‖ + ‖g x - g y‖ ≤ C * ‖x - y‖

/-- Fang–Giles (2020), p. 532, Assumption 7 (dissipative condition), with constants
`α, β > 0`: (7), `⟨x, f(x)⟩ ≤ −α‖x‖² + β` (17) and `‖g(x)‖² ≤ β` (18) for all `x`.
The word "nondegenerate" of the source is not encoded (it is never defined in the paper). -/
def Assumption7 {m d : ℕ} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (α β : ℝ) : Prop :=
  LocallyLipschitz7 f g ∧ 0 < α ∧ 0 < β ∧
    (∀ x : SDEState m, inner ℝ x (f x) ≤ -α * ‖x‖ ^ 2 + β) ∧
    ∀ x : SDEState m, ‖g x‖ ^ 2 ≤ β

/-- Fang–Giles (2020), p. 533, Assumption 8 (adaptive timestep for infinite time interval):
`h : ℝ^m → (0, h_max]` is continuous, `0 < h_max < ∞`, and with constants `α, β > 0`,
`⟨x, f(x)⟩ + ½ h(x) ‖f(x)‖² ≤ −α‖x‖² + β` (19) for all `x`. -/
def Assumption8 {m : ℕ} (f : SDEState m → SDEState m) (h : SDEState m → ℝ)
    (hmax α β : ℝ) : Prop :=
  Continuous h ∧ 0 < hmax ∧ (∀ x : SDEState m, 0 < h x ∧ h x ≤ hmax) ∧ 0 < α ∧ 0 < β ∧
    ∀ x : SDEState m, inner ℝ x (f x) + 1 / 2 * h x * ‖f x‖ ^ 2 ≤ -α * ‖x‖ ^ 2 + β

/-- Fang–Giles (2020), p. 530, (14): the polynomial growth Lipschitz condition
`‖f(x) − f(y)‖ ≤ (γ(‖x‖^q + ‖y‖^q) + μ)‖x − y‖` with `γ, μ, q > 0` (real powers). -/
def PolyLipschitz14 {m : ℕ} (f : SDEState m → SDEState m) (γ μ q : ℝ) : Prop :=
  0 < γ ∧ 0 < μ ∧ 0 < q ∧ ∀ x y : SDEState m,
    ‖f x - f y‖ ≤ (γ * (‖x‖ ^ q + ‖y‖ ^ q) + μ) * ‖x - y‖

/-- Fang–Giles (2020), p. 533, Assumption 9 (contractive Lipschitz properties), with
`p* ∈ (2, ∞)` and `λ, η > 0` (`lam` is the source's `λ`):
`⟨x − y, f(x) − f(y)⟩ + (p* − 1)/2 ‖g(x) − g(y)‖² ≤ −λ‖x − y‖²` (20),
`‖g(x) − g(y)‖² ≤ η‖x − y‖²` (21), and `f` satisfies (14) with constants `γ, μ, q > 0`. -/
def Assumption9 {m d : ℕ} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (pstar lam η γ μ q : ℝ) : Prop :=
  2 < pstar ∧ 0 < lam ∧ 0 < η ∧
    (∀ x y : SDEState m,
      inner ℝ (x - y) (f x - f y) + (pstar - 1) / 2 * ‖g x - g y‖ ^ 2 ≤ -lam * ‖x - y‖ ^ 2) ∧
    (∀ x y : SDEState m, ‖g x - g y‖ ^ 2 ≤ η * ‖x - y‖ ^ 2) ∧
    PolyLipschitz14 f γ μ q

/-- Fang–Giles (2020), p. 530, Assumption 3, (11), for one value `δ` of the refinement
parameter: `δ min(T, h(x)) ≤ h^δ(x) ≤ min(δT, h(x))` for all `x`. -/
def Assumption3 {m : ℕ} (h : SDEState m → ℝ) (T δ : ℝ) (hδ : SDEState m → ℝ) : Prop :=
  ∀ x : SDEState m, δ * min T (h x) ≤ hδ x ∧ hδ x ≤ min (δ * T) (h x)

end AdaptiveEM.Infinite


