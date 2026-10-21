-- Prove2me | Definitions.Def_ProxBundle_GPB_Model
-- name    : ProxBundle_GPB_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:46.096992+00:00
-- url     : https://prove2.me/theorems/75f2c7c7-d1a6-4b63-978c-2a6bf483f259
-- title:
--   §1.1–§3.2, pp. 4–9 — HCCO instance, BU and GPB runs
-- statement:
--   The model fixes a hybrid convex composite problem on $\mathbb R^n$: minimize $\phi=f+h$ over $D=\operatorname{dom}h$, where $h$ is $\mu$-convex and lower semicontinuous, and the selected subgradient oracle $f'$ obeys the hybrid condition. Its objects include the cut $\ell_f(u;x)$, the closest minimizer $x_0^*$, and the pair $(\bar M_f,\bar L_f)$ minimizing $M^2+\bar\varepsilon L$ among admissible hybrid bounds.
--
--   $$
--   \ell_f(u;x)=f(x)+\langle f'(x),u-x\rangle,\qquad \|f'(x)-f'(y)\|\le 2M+L\|x-y\|.
--   $$
--
--   An infinite GPB run chooses at each step either a serious update (30) or a null update through the existential BU blackbox (17)–(18), then computes the proximal minimizer and the best point seen so far. The definitions also fix $\lambda_\mu$, $\bar t$, $\tau$ of (38), and the serious-step bound with its $\mu=0$ convention. This interface supports all the paper's GPB variants.
--
--   **Formalization Note** Functions are real-valued on $D$ and extended by $+\infty$ off $D$ for lower semicontinuity. The oracle inequality is relative to $D$; lower semicontinuity of $f$ and of the auxiliary BU model $\bar\Gamma$ is omitted. The abstract serious-iterate predicate explicitly keeps $\hat y_k\in D$.
-- source:
--   Liang & Monteiro, arXiv:2110.01084v3, pp. 4–9, §1.1, §2.1, (A1)–(A3), (6), (8), (9), BU (17)–(18), GPB (28)–(32); (44) p. 13, (58) p. 16, (38) p. 11

import Mathlib

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

namespace ProxBundle.GPB

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The data `(f, f′; h)` of (1), with `D = dom h`. -/
structure Instance (n : ℕ) where
  D : Set (E n)
  f : E n → ℝ
  f' : E n → E n
  h : E n → ℝ

namespace Instance

variable {n : ℕ} (P : Instance n)

/-- Objective `φ = f + h` on `D`. -/
def φ (x : E n) : ℝ := P.f x + P.h x

/-- The affine cut `ℓ_f(u; x)` of (6). -/
def ellf (u x : E n) : ℝ := P.f x + ⟪P.f' x, u - x⟫

/-- Extended-valued function with effective domain `D`. -/
noncomputable def ext (g : E n → ℝ) : E n → EReal :=
  fun x => by
    classical
    exact if x ∈ P.D then (g x : EReal) else ⊤

/-- The paper's proper lower semicontinuous μ-convex functions with domain `D`. -/
def ConvBar (μ : ℝ) (g : E n → ℝ) : Prop :=
  StrongConvexOn P.D μ g ∧ LowerSemicontinuous (P.ext g)

/-- (A1): convexity, lower semicontinuity of `h`, and a subgradient oracle on `D`. -/
def A1 (μ : ℝ) : Prop :=
  P.D.Nonempty ∧ ConvexOn ℝ P.D P.f ∧ P.ConvBar μ P.h ∧
    ∀ x ∈ P.D, ∀ z ∈ P.D, P.ellf z x ≤ P.f z

/-- The hybrid oracle condition (A3). -/
def A3 (M L : ℝ) : Prop :=
  ∀ x ∈ P.D, ∀ y ∈ P.D, ‖P.f' x - P.f' y‖ ≤ 2 * M + L * ‖x - y‖

/-- The minimizing pair (9), chosen among all nonnegative pairs satisfying (A3). -/
def IsMinPair (ε Mbar Lbar : ℝ) : Prop :=
  0 ≤ Mbar ∧ 0 ≤ Lbar ∧ P.A3 Mbar Lbar ∧
    ∀ M L, 0 ≤ M → 0 ≤ L → P.A3 M L →
      Mbar ^ 2 + ε * Lbar ≤ M ^ 2 + ε * L

/-- A minimizer of (1), representing an attained finite `φ*`. -/
def IsOpt (x : E n) : Prop := x ∈ P.D ∧ ∀ y ∈ P.D, P.φ x ≤ P.φ y

/-- A nearest optimal point `x₀*` to `x₀`, as in (8). -/
def IsNearestOpt (x0 x0s : E n) : Prop :=
  P.IsOpt x0s ∧ ∀ y, P.IsOpt y → ‖x0 - x0s‖ ≤ ‖x0 - y‖

/-- A point minimizing the proximal objective of (2)/(31) over `D`. -/
def IsProxMin (g : E n → ℝ) (xc : E n) (lam : ℝ) (x : E n) : Prop :=
  x ∈ P.D ∧ ∀ u ∈ P.D,
    g x + ‖x - xc‖ ^ 2 / (2 * lam) ≤
      g u + ‖u - xc‖ ^ 2 / (2 * lam)

/-- The existential BU output condition (17)–(18). -/
def BU (μ lam τ : ℝ) (xc x : E n) (Γ Γp : E n → ℝ) : Prop :=
  P.ConvBar μ Γp ∧ (∀ u ∈ P.D, Γp u ≤ P.φ u) ∧
    ∃ Γbar : E n → ℝ,
      StrongConvexOn P.D μ Γbar ∧ Γbar x = Γ x ∧
      P.IsProxMin Γbar xc lam x ∧
      ∀ u ∈ P.D,
        τ * Γbar u + (1 - τ) * (P.ellf u x + P.h u) ≤ Γp u

end Instance

/-- One infinite family of GPB iterates. Index zero is the initialization. -/
structure Run (n : ℕ) where
  x : ℕ → E n
  y : ℕ → E n
  xc : ℕ → E n
  Γ : ℕ → E n → ℝ

namespace Run

variable {n : ℕ} (R : Run n)

/-- Model minimum `m_j` in (32). -/
def m (lam : ℝ) (j : ℕ) : ℝ :=
  R.Γ j (R.x j) + ‖R.x j - R.xc j‖ ^ 2 / (2 * lam)

/-- Model gap `t_j` in (32), with the specified initialization `t₀ = 0`. -/
def t (P : Instance n) (lam : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else P.φ (R.y j) - R.m lam j

end Run

/-- Steps 0–2 of GPB, including both branches of the bundle update and best-so-far (28). -/
def IsRun {n : ℕ} (P : Instance n) (μ lam ε τ : ℝ) (x0 : E n) (R : Run n) : Prop :=
  R.x 0 = x0 ∧ R.y 0 = x0 ∧
    ∀ j : ℕ, 1 ≤ j →
      (R.t P lam (j - 1) ≤ ε / 2 →
        R.xc j = R.x (j - 1) ∧ P.ConvBar μ (R.Γ j) ∧
          ∀ u ∈ P.D,
            P.ellf u (R.x (j - 1)) + P.h u ≤ R.Γ j u ∧ R.Γ j u ≤ P.φ u) ∧
      (ε / 2 < R.t P lam (j - 1) →
        R.xc j = R.xc (j - 1) ∧
          P.BU μ lam τ (R.xc (j - 1)) (R.x (j - 1)) (R.Γ (j - 1)) (R.Γ j)) ∧
      P.IsProxMin (R.Γ j) (R.xc j) lam (R.x j) ∧
      (∃ i ≤ j, R.y j = R.x i) ∧
      (∀ i ≤ j, P.φ (R.y j) ≤ P.φ (R.x i))

/-- The adjusted stepsize (44). -/
def lamMu (μ lam : ℝ) : ℝ := lam / (1 + lam * μ)

/-- The bound `t̄` in (58), with `d₀` as an argument. -/
def tbar (Mbar Lbar lam d0 : ℝ) : ℝ :=
  Mbar ^ 2 + 4 * (Lbar + 2) * (max 1 (2 * lam * Lbar) * d0 + lam * Mbar) ^ 2

/-- The specified choice of τ in (38). -/
def tau38 (μ lam ε Mf Lf : ℝ) : ℝ :=
  (1 + (1 + lam * μ) * ε / (8 * lam * (Mf ^ 2 + ε * Lf)))⁻¹

/-- The input condition (29), with `T² = Mbar² + ε Lbar`. -/
def Cond29 (μ lam ε τ Mbar Lbar : ℝ) : Prop :=
  8 * lam * (Mbar ^ 2 + ε * Lbar) / ((1 + lam * μ) * ε) ≤ τ / (1 - τ)

/-- The serious iteration bound, including the θ = 1 / μ = 0 convention of Corollary B.2. -/
noncomputable def serBound (μ lam ε r : ℝ) : ℝ :=
  if μ = 0 then r / (lam * ε)
  else min (r / (lam * ε))
    (1 / (μ * lamMu μ lam) * Real.log (μ * r / ε + 1))

/-- The three conditions of Lemma 4.1 for abstract serious-iterate sequences. -/
def IsHat {n : ℕ} (P : Instance n) (μ lam ε : ℝ) (x0 : E n)
    (xh yh : ℕ → E n) (Γh : ℕ → E n → ℝ) : Prop :=
  xh 0 = x0 ∧ ∀ k : ℕ, 1 ≤ k →
    P.ConvBar μ (Γh k) ∧ (∀ u ∈ P.D, Γh k u ≤ P.φ u) ∧
      P.IsProxMin (Γh k) (xh (k - 1)) lam (xh k) ∧
      yh k ∈ P.D ∧
      P.φ (yh k) -
        (Γh k (xh k) + ‖xh k - xh (k - 1)‖ ^ 2 / (2 * lam)) ≤ ε / 2

end ProxBundle.GPB


