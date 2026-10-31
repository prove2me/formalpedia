-- Prove2me | Definitions.Def_SpiderDiameter_GeneralProcess
-- name    : SpiderDiameter_GeneralProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:49.260655+00:00
-- url     : https://prove2.me/theorems/a4ab12ac-e30c-4a57-bcac-a74dbffcad4a
-- title:
--   General-start process $(X,Y,Z)$ on the state space $\mathcal D$, and its filtrations
-- statement:
--   The **state space** is $\mathcal D=\{(x,y,z): z\le0\le y,\ z\le x\le y,\ y+z\ge0\}$.
--
--   For the spider, $Y_t$ is the longest rib, $-Z_t$ the second longest rib (so that $D_t=Y_t-Z_t$), and $X_t$ is the signed distance of $S_t$ from the origin: $|X_t|$ is the distance, and $X_t\ge0$ exactly when $S_t$ lies on the running longest rib. The process $X$ is a $(1-\tfrac1n)$-skew Brownian motion that jumps from $-Y_t$ to $Y_t$ when the second longest rib becomes the longest.
--
--   To start from $(x,y,z)\in\mathcal D$, the spider is realized on the noise $(B,\theta)$ as follows: its distance from the origin is $\big||x|+B_t\big|$; until $|x|+B$ first hits $0$ it stays on a fixed ray (ray $0$, carrying the longest rib, if $x\ge0$; ray $1$, carrying the second longest rib, if $x<0$), and afterwards each excursion goes to the ray $\theta_m$ of its number $m$; the initial ribs are $y$ on ray $0$, $-z$ on ray $1$ and $0$ on the other rays. Each rib is the larger of its initial length and the farthest distance reached on its ray; $Y$, $Z$ and $X$ are read off as above, a ray becoming the running longest rib at the moment its rib reaches the current maximum. The law of $(X,Y,Z)$ so constructed is $P_{x,y,z}$.
--
--   Also defined: the natural filtration of the position of this spider, the natural filtration $\sigma(X_s:s\le t)$ of $X$, the corresponding stopping times ($\{\tau\le t\}$ convention), and evaluation of a process at a random time.
--
--   **Formalization Note** Rays are natural numbers. At $(-y,y,-y)$ with $y>0$ the construction starts from the identified point $(y,y,-y)$, in agreement with Remark 3.7. At $(x,y,z)=(0,0,0)$ the position process is the spider $S$ of §1. A process evaluated at $\tau=\infty$ takes its time-$0$ value; this convention is only applied where $\tau<\infty$ almost surely.
-- source:
--   Bednarz–Ernst–Osękowski, On the Diameter of the Stopped Spider Process, arXiv:2105.15202v2, §3 Step 1, pp.10–11 (X, Y, Z; skew Brownian motion with jumps) and Step 2, p.11 (state space D, P_(x,y,z))

import Mathlib
import Definitions.Def_SpiderDiameter_Noise
import Definitions.Def_SpiderDiameter_Spider

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option warn.classDefReducibility false

namespace SpiderDiameter

/-! A family of tightly coupled definitions: the state space `𝒟` and the process `(X, Y, Z)` of
§3 Steps 1–2 started from a point `(x, y, z)`, built on the same noise `(B, θ)` as the spider, and
its filtrations. The law of `(X, Y, Z)` under the construction with parameters `(x, y, z)` is the
paper's `P_{x,y,z}`. -/

/-- **The state space** `𝒟 = {(x, y, z) : z ≤ 0 ≤ y, z ≤ x ≤ y, y + z ≥ 0}`.
Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, §3 Step 2, p.11. -/
def stateSpace : Set (ℝ × ℝ × ℝ) :=
  {p | p.2.2 ≤ 0 ∧ 0 ≤ p.2.1 ∧ p.2.2 ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ 0 ≤ p.2.1 + p.2.2}

/-- The radial driver `|x| + B_t`, a Brownian motion started at `|x|`. -/
def driver {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  |x| + N.B t ω

/-- **Distance from the origin** `|X_t| = ||x| + B_t|`, a reflecting Brownian motion started at
`|x|` (p.10: "|X_t| [is] the distance of the spider process S_t from the origin"). -/
def radius {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  |driver N x t ω|

/-- **The ray carrying the spider at time `t`.** Before the first zero of the driver the spider is
on the fixed ray `0` (the initial longest rib) if `x ≥ 0`, and on the fixed ray `1` (the initial
second longest rib) if `x < 0`; afterwards each excursion of the driver away from `0` is sent to
the ray `θ_m` of its number `m`, as for the spider of §1.

**Formalization Note.** Rays are natural numbers; the `θ_m` take values in `{0, …, n − 1}`. -/
noncomputable def curRay {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x : ℝ) (t : ℝ≥0) (ω : Ω) : ℕ := by
  classical
  exact if ∀ s ≤ t, 0 < driver N x s ω then (if 0 ≤ x then 0 else 1)
    else (N.θ (excIndex (fun s => driver N x s ω) t) ω : ℕ)

/-- Initial rib lengths: `y` on ray `0`, `−z` on ray `1`, `0` on the other rays. -/
def initRib (y z : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then y else if k = 1 then -z else 0

/-- **Rib length on ray `k` at time `t`**: the larger of the initial rib and the farthest distance
reached on ray `k` during `[0, t]`. -/
noncomputable def ribG {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x y z : ℝ) (k : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  max (initRib y z k)
    (⨆ s : Set.Iic t, if curRay N x s ω = k then radius N x s ω else 0)

/-- **The longest rib** `Y_t = max_{1 ≤ j ≤ n} |T_t ∩ R_j|`.
Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, §3 Step 1, p.10. -/
noncomputable def Yg {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x y z : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ⨆ k : Fin n, ribG N x y z k t ω

/-- **The diameter** of the general-start spider: the largest sum of two ribs on distinct rays
(as in (1.5)), so that `D_t = Y_t − Z_t` (p.10). -/
noncomputable def Dg {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x y z : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ⨆ p : {p : Fin n × Fin n // p.1 ≠ p.2}, ribG N x y z p.1.1 t ω + ribG N x y z p.1.2 t ω

/-- **Minus the second longest rib**, `Z_t = −(second longest rib) = Y_t − D_t`.
Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, §3 Step 1, p.10 ("let −Z_t (note the minus sign) be
the corresponding second longest rib, so that D_t = Y_t − Z_t"). -/
noncomputable def Zg {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x y z : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Yg N x y z t ω - Dg N x y z t ω

/-- **The running longest rib's ray.** The ray occupied by the spider at the last time
`s ≤ t` at which the spider is at the tip of a longest rib (`0 < |X_s| = Y_s`); ray `0` if there
is no such time.

**Formalization Note (tie rule).** A ray becomes the running longest rib at the moment its rib
reaches the current maximum `Y`: this is the jump of p.11 ("if … its left limit X_{t−} equals
−Y_t, then X_t changes its sign, moving to Y_t"). At time `0` this identifies the start
`(−y, y, −y)` with `(y, y, −y)`, as in Remark 3.7. -/
noncomputable def longestRay {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x y z : ℝ) (t : ℝ≥0) (ω : Ω) : ℕ := by
  classical
  exact
    let L : Set ℝ≥0 := {s | s ≤ t ∧ 0 < radius N x s ω ∧ radius N x s ω = Yg N x y z s ω}
    if L.Nonempty then curRay N x (sSup L) ω else 0

/-- **The process `X`**: `|X_t|` is the distance of the spider from the origin, and `X_t ≥ 0`
iff the spider is on the running longest rib.
Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, §3 Step 1, p.10: "we copy the running longest rib on
the positive half-line, while all the remaining ribs are glued together and copied on (−∞, 0]".
`X` is a `(1 − 1/n)`-skew Brownian motion with a jump from `−Y_t` to `Y_t` (p.11).

**Formalization Note.** `(X, Y, Z)` built from the parameters `(x, y, z) ∈ 𝒟` on the noise
`(B, θ)` has the law `P_{x,y,z}` of p.11: `X_0 = x`, `Y_0 = y`, `Z_0 = z`, except at
`(−y, y, −y)` with `y > 0`, which starts from the identified point `(y, y, −y)` (tie rule of
`longestRay`). -/
noncomputable def Xg {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x y z : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if curRay N x t ω = longestRay N x y z t ω then radius N x t ω else -radius N x t ω

/-- **Position of the general-start spider** in the plane: distance `|X_t|` on the ray
`curRay`. For `x = 0` this is the spider process `S` of §1. -/
noncomputable def genPos {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x : ℝ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  ((radius N x t ω : ℝ) : ℂ) * rayDir n (curRay N x t ω)

/-- The natural filtration `σ(position_s : s ≤ t)` of the general-start spider (raw, as a family
of σ-algebras). It contains the natural filtration of `(X, Y, Z)`. -/
noncomputable def genSigma {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x : ℝ) (t : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ (s : ℝ≥0) (_ : s ≤ t), MeasurableSpace.comap (genPos N x s) inferInstance

/-- Stopping time (`{τ ≤ t}` convention) of the general-start spider's natural filtration. -/
def IsGenStoppingTime {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x : ℝ) (τ : Ω → ℝ≥0∞) : Prop :=
  ∀ t : ℝ≥0, MeasurableSet[genSigma N x t] {ω | τ ω ≤ (t : ℝ≥0∞)}

/-- The natural filtration `σ(X_s : s ≤ t)` of the process `X` (raw, as a family of σ-algebras). -/
noncomputable def XSigma {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x y z : ℝ) (t : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ (s : ℝ≥0) (_ : s ≤ t), MeasurableSpace.comap (Xg N x y z s) inferInstance

/-- **Stopping time of `X`** (`{τ ≤ t}` convention), the class in (3.3), p.13. -/
def IsXStoppingTime {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x y z : ℝ) (τ : Ω → ℝ≥0∞) : Prop :=
  ∀ t : ℝ≥0, MeasurableSet[XSigma N x y z t] {ω | τ ω ≤ (t : ℝ≥0∞)}

/-- Evaluation of a process at a random time; at `τ = ∞` the value at time `0` is used (a
convention, only ever applied where `τ < ∞` almost surely). -/
def atTime {Ω : Type*} (F : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞) (ω : Ω) : ℝ :=
  F (τ ω).toNNReal ω

end SpiderDiameter


