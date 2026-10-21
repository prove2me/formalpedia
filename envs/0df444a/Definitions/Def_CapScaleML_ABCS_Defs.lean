-- Prove2me | Definitions.Def_CapScaleML_ABCS_Defs
-- name    : CapScaleML_ABCS_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:47.645235+00:00
-- url     : https://prove2.me/theorems/26d8b01e-1e04-403f-911f-d14e00eee7f2
-- title:
--   Fluid capacity-scaling model, AP, ABCS, and competitive-ratio constants
-- statement:
--   Fix a horizon $T>0$, a nonnegative arrival rate $\lambda$, and a nonnegative server schedule $m$ that starts at zero. The workload $q$ follows the one-sided queue equation
--   $$
--   q(t)=\int_0^t(\lambda(s)-m(s))\mathbf 1\{q(s)>0\text{ or }\lambda(s)\ge m(s)\}\,ds.
--   $$
--   The cost is waiting weight $\omega$ times the integral of $q$, activation price $\beta$ times the limiting sum of positive increments of $m$, and operating rate $\theta$ times the integral of $m$. The offline optimum is the infimum of this cost over feasible schedules and their workloads.
--
--   Mean absolute prediction error, $\eta$-accuracy, the underprediction process $\Delta\lambda$, AP's offline-plus-online advice, and ABCS's rate-switching trajectory follow Definitions 3.1–3.3 and Algorithms 2–3. The constants $c_1,\ldots,c_6$, OCR, and PCR are exactly those in equation (4.14). These definitions form the shared interface for the goal and its milestones.
--
--   **Formalization Note** Costs lie in $\mathbb R_{\ge0}\cup\{\infty\}$; workload and trajectory equations require integrable integrands. The final switching interval is clipped at $t$, and AP's online correction starts at zero. Real division in OCR and PCR is used only with positive $r_1,r_2$ in the theorems.
-- source:
--   Rutten & Mukherjee, Online Capacity Scaling Augmented With Unreliable Machine Learning Predictions, arXiv:2101.12160v2, p. 7–16, (2.1)–(2.3), Definitions 3.1–3.3, Algorithms 2–3, (4.14)

import Mathlib

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace CapScaleML.ABCS

/-- Equation (2.1): the queue workload, with an integrable right-hand side. -/
def IsWorkload (T : ℝ) (lam m q : ℝ → ℝ) : Prop :=
  IntervalIntegrable (fun s => if 0 < q s ∨ m s ≤ lam s then lam s - m s else 0) volume 0 T ∧
  ∀ t ∈ Icc 0 T, q t = ∫ s in (0:ℝ)..t,
    (if 0 < q s ∨ m s ≤ lam s then lam s - m s else 0)

/-- Feasible capacity schedules in (2.1). -/
def Admissible (T : ℝ) (m : ℝ → ℝ) : Prop :=
  m 0 = 0 ∧ (∀ t ∈ Ioc 0 T, 0 ≤ m t) ∧ IntervalIntegrable m volume 0 T

/-- The positive server activations in the mesh sum of (2.2), clipped at `t`. -/
noncomputable def switchSum (t δ : ℝ) (m : ℝ → ℝ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (⌊t / δ⌋₊ + 1),
    ENNReal.ofReal (m (min ((i + 1) * δ) t) - m (i * δ))

/-- The right-hand limsup of the switching sums. -/
noncomputable def switching (t : ℝ) (m : ℝ → ℝ) : ℝ≥0∞ :=
  limsup (fun δ => switchSum t δ m) (𝓝[>] 0)

/-- Equation (2.2), with `q` the workload of `m` under the given arrival process. -/
noncomputable def cost (ω β θ t : ℝ) (m q : ℝ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ω * ∫⁻ s in Icc 0 t, ENNReal.ofReal (q s)
    + ENNReal.ofReal β * switching t m
    + ENNReal.ofReal θ * ∫⁻ s in Icc 0 t, ENNReal.ofReal (m s)

/-- Equation (2.3), the infimum over feasible schedules and their workloads. -/
noncomputable def opt (ω β θ T : ℝ) (lam : ℝ → ℝ) : ℝ≥0∞ :=
  ⨅ (m : ℝ → ℝ) (q : ℝ → ℝ) (_ : Admissible T m ∧ IsWorkload T lam m q),
    cost ω β θ T m q

/-- An offline optimizer, as used in Algorithm 2 and Proposition 2.2. -/
def IsOfflineOpt (ω β θ T : ℝ) (lam m q : ℝ → ℝ) : Prop :=
  Admissible T m ∧ IsWorkload T lam m q ∧ cost ω β θ T m q = opt ω β θ T lam

/-- Definition 3.1, the mean absolute prediction error. -/
noncomputable def mae (T : ℝ) (f g : ℝ → ℝ) : ℝ :=
  T⁻¹ * ∫ t in (0:ℝ)..T, |f t - g t|

/-- Definition 3.2, with an extended-real optimum. -/
def IsEtaAccurate (ω β θ T η : ℝ) (lam lamHat : ℝ → ℝ) : Prop :=
  ENNReal.ofReal (mae T lamHat lam) ≤
    ENNReal.ofReal η * opt ω β θ T lam / ENNReal.ofReal T

/-- The positive underprediction, extended by zero to negative time. -/
noncomputable def deltaLam (lam lamHat : ℝ → ℝ) (t : ℝ) : ℝ :=
  if 0 ≤ t then max (lam t - lamHat t) 0 else 0

/-- The integrated equation (4.7), with the initial value `m₂(0) = 0`. -/
noncomputable def apOnline (ω β : ℝ) (lam lamHat : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..t, Real.sqrt (ω / (2 * β)) *
    (deltaLam lam lamHat s - deltaLam lam lamHat (s - Real.sqrt (2 * β / ω)))

/-- Algorithm 2, as an offline optimizer plus the online correction. -/
def IsAPAdvice (ω β θ T : ℝ) (lam lamHat mAdv : ℝ → ℝ) : Prop :=
  ∃ m₁ q₁ : ℝ → ℝ, IsOfflineOpt ω β θ T lamHat m₁ q₁ ∧
    ∀ t ∈ Icc 0 T, mAdv t = m₁ t + apOnline ω β lam lamHat t

/-- The upward coefficient in (4.12). -/
noncomputable def rateUp (ω β r₁ R₁ : ℝ) (m q mAdv qAdv : ℝ) : ℝ :=
  if m - mAdv > max (q - qAdv) 0 * Real.sqrt (ω / (2 * β)) then r₁ else R₁

/-- The downward coefficient in (4.12). -/
noncomputable def rateDown (r₂ R₂ : ℝ) (m q mAdv qAdv : ℝ) : ℝ :=
  if mAdv < m ∧ q ≤ qAdv then R₂ else r₂

/-- The right-hand side of (4.11). -/
noncomputable def abcsDrift (ω β θ r₁ r₂ R₁ R₂ : ℝ)
    (mAdv qAdv m q : ℝ → ℝ) (s : ℝ) : ℝ :=
  (rateUp ω β r₁ R₁ (m s) (q s) (mAdv s) (qAdv s) * ω * q s -
    rateDown r₂ R₂ (m s) (q s) (mAdv s) (qAdv s) * θ * m s) / β

/-- Algorithm 3, understood as any integrated trajectory of (4.11)–(4.12). -/
def IsABCS (ω β θ T r₁ r₂ R₁ R₂ : ℝ)
    (lam mAdv qAdv m q : ℝ → ℝ) : Prop :=
  IsWorkload T lam m q ∧
  IntervalIntegrable (abcsDrift ω β θ r₁ r₂ R₁ R₂ mAdv qAdv m q) volume 0 T ∧
  ∀ t ∈ Icc 0 T, m t = ∫ s in (0:ℝ)..t,
    abcsDrift ω β θ r₁ r₂ R₁ R₂ mAdv qAdv m q s

/-- Constants from (4.14). -/
noncomputable def c1 (r₁ R₂ : ℝ) : ℝ := 1 + 1 / r₁ + 1 / R₂
noncomputable def c3 (R₁ R₂ : ℝ) : ℝ := 1 + 1 / R₁ + 1 / R₂
noncomputable def c2 (r₁ R₁ R₂ : ℝ) : ℝ :=
  (c1 r₁ R₂ * Real.sqrt (1 + 2 * r₁) - c1 r₁ R₂ + c3 R₁ R₂) /
    Real.sqrt (1 + 2 * R₁)
noncomputable def c4 (r₁ r₂ R₁ R₂ : ℝ) : ℝ :=
  1 + r₂ + r₂ / R₁ + c2 r₁ R₁ R₂ * r₂
noncomputable def c5 (r₁ r₂ : ℝ) : ℝ := 1 + 1 / r₁ + 1 / r₂
noncomputable def c6 (r₁ r₂ R₁ : ℝ) : ℝ := c5 r₁ r₂ * Real.sqrt (R₁ / r₁)
noncomputable def OCR (r₁ r₂ R₁ R₂ : ℝ) : ℝ :=
  max (max (c1 r₁ R₂ * r₁) (c2 r₁ R₁ R₂ * R₁ / Real.sqrt (1 + 2 * R₁)))
    (max (c2 r₁ R₁ R₂ + c3 R₁ R₂) (c4 r₁ r₂ R₁ R₂))
noncomputable def PCR (r₁ r₂ R₁ R₂ : ℝ) : ℝ :=
  max (c5 r₁ r₂ * R₁)
    (max (2 * c6 r₁ r₂ R₁) (2 * c6 r₁ r₂ R₁ * R₂ + 1 - R₂ / r₂))

end CapScaleML.ABCS


