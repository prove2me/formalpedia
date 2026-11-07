-- Prove2me | Definitions.Def_CtxSearchTSR_Algorithm2
-- name    : CtxSearchTSR_Algorithm2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:23.732345+00:00
-- url     : https://prove2.me/theorems/9f92318f-770d-4cd4-9ab7-5769d9c7f98d
-- title:
--   Algorithm 2 (Adversarial Contextual Search): state $(\mathbf m,R)$, price (9), update (10), and its run
-- statement:
--   **Algorithm 2** keeps a mean proxy $\mathbf m\in\mathbb R^d$ and a scale matrix $R\in\mathbb R^{d\times d}$, initialized as
--
--   $$\mathbf m_1=0,\qquad R_1=\tfrac{1}{\sqrt d}\,I_d. \tag{8}$$
--
--   At a round with context $x$ it computes $m=x^\top\mathbf m$, $u=Rx$, $a=x^\top u$ and $r=\|u\|_2$, draws a fresh uniform sign $\varepsilon\in\{-1,1\}$ and posts
--
--   $$P=m+\tfrac r2\,\varepsilon. \tag{9}$$
--
--   After observing $Y$ it updates
--
--   $$\mathbf m_{+}=\mathbf m+\frac{Y r}{a(3-\varepsilon Y)}\,u,\qquad R_{+}=R+\frac{\varepsilon Y}{a(3-\varepsilon Y)}\,u u^\top. \tag{10}$$
--
--   The module defines the state, the quantities $u,a,r$, the price (9), the update (10) for an arbitrary sign $e$ and answer $Y$, one round of the algorithm (where $Y=\operatorname{sign}(x^\top z-P)$), and the **run** of the algorithm against a target $z$ and an adaptive context strategy $X$ under a sequence of learner signs: the state before round $t$.
--
--   **Formalization Note** Rounds are $0$-based: the run's state at index $t$ is the paper's $(\mathbf m_{t+1},R_{t+1})$, and index $0$ is (8). At $x=0$ one has $u=0$ and $a=0$; Lean's convention $c/0=0$ makes the update the identity, matching the paper's remark that for $x_t=0$ nothing changes.
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), §2.2, Algorithm 2, p.10, (8)–(10)

import Mathlib
import Definitions.Def_CtxSearchTSR_Protocol

open Matrix

namespace CtxSearchTSR

/-!
# Algorithm 2 (Adversarial Contextual Search)

Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, *Contextual Search and Bilateral Trade with a
Trace-Square-Root Potential*, STOC 2027 submission (manuscript sha256 70eeb0d1…),
§2.2, Algorithm 2, p.10, equations (8)–(10):

* initialize m₁ = 0, R₁ = (1/√d) I_d (8);
* at round t, receive x_t, compute m_t = x_tᵀm_t, u_t = R_t x_t, a_t = x_tᵀu_t, r_t = ‖u_t‖₂;
* draw a fresh uniform sign ε_t ∈ {−1, 1} and post P_t = m_t + (r_t/2) ε_t (9);
* observe Y_t and update m_{t+1} = m_t + Y_t r_t / (a_t(3 − ε_tY_t)) u_t,
  R_{t+1} = R_t + ε_tY_t / (a_t(3 − ε_tY_t)) u_t u_tᵀ (10).

**Formalization Note.** The state is the pair (m, R) ∈ ℝ^d × ℝ^{d×d}. `update` is the closed form
(10) for arbitrary reals `e` (the sign) and `Y` (the answer); `step` feeds it the algorithm's own
answer Y = sign(xᵀz − P) with sign(0) = 1. Rounds are 0-based: `run z X ε t` is the paper's state
(m_{t+1}, R_{t+1}), and `run z X ε 0` is (8). At x = 0 one has u = 0 and a = 0, and Lean's
`r / 0 = 0` makes the update the identity (the paper: "for x_t = 0, the loss and potential change
are both zero", App. C.3, p.21).
-/

/-- The algorithm's state: the mean proxy **m** and the scale matrix R. -/
structure State (d : ℕ) where
  /-- The mean proxy **m**. -/
  m : Fin d → ℝ
  /-- The scale matrix R. -/
  R : Matrix (Fin d) (Fin d) ℝ

/-- The initial state (8): **m**₁ = 0 and R₁ = (1/√d) I_d. -/
noncomputable def State.init (d : ℕ) : State d :=
  ⟨0, (Real.sqrt (d : ℝ))⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)⟩

/-- **u** = R**x**. -/
def dirU {d : ℕ} (R : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : Fin d → ℝ := R *ᵥ x

/-- a = **x**ᵀ**u** = **x**ᵀR**x**. -/
def quadA {d : ℕ} (R : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : ℝ := x ⬝ᵥ dirU R x

/-- r = ‖**u**‖₂ = ‖R**x**‖₂ (Euclidean norm). -/
noncomputable def radius {d : ℕ} (R : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : ℝ :=
  eucNorm (dirU R x)

/-- The posted price (9): P = **x**ᵀ**m** + (r/2) e, for the sign `e`. -/
noncomputable def price {d : ℕ} (s : State d) (x : Fin d → ℝ) (e : ℝ) : ℝ :=
  x ⬝ᵥ s.m + radius s.R x / 2 * e

/-- The update (10) with sign `e` and answer `Y`:
**m**' = **m** + Y r / (a(3 − eY)) **u**, R' = R + eY / (a(3 − eY)) **u****u**ᵀ. -/
noncomputable def update {d : ℕ} (s : State d) (x : Fin d → ℝ) (e Y : ℝ) : State d :=
  ⟨s.m + (Y * radius s.R x / (quadA s.R x * (3 - e * Y))) • dirU s.R x,
   s.R + (e * Y / (quadA s.R x * (3 - e * Y))) • vecMulVec (dirU s.R x) (dirU s.R x)⟩

/-- One round of Algorithm 2 at state `s` and context `x` with the learner's sign `b`: post the
price (9), receive the answer Y = sign(xᵀz − P) (sign(0) = 1), and apply (10). -/
noncomputable def step {d : ℕ} (z : Fin d → ℝ) (s : State d) (x : Fin d → ℝ) (b : Bool) :
    State d :=
  update s x (signOf b) (feedback z x (price s x (signOf b)))

/-- The run of Algorithm 2 against the target `z` and the context strategy `X`, with the learner's
sign sequence `ε`: `run z X ε t` is the state before round `t` (0-based). Round `t` uses the
context `X t (ε 0, …, ε (t-1))` and the sign `ε t`. -/
noncomputable def run {d : ℕ} (z : Fin d → ℝ) (X : ContextStrategy d) (ε : ℕ → Bool) :
    ℕ → State d
  | 0 => State.init d
  | t + 1 => step z (run z X ε t) (X t (fun i => ε i.val)) (ε t)

end CtxSearchTSR


