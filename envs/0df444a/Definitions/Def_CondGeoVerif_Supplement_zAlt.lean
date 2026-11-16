-- Prove2me | Definitions.Def_CondGeoVerif_Supplement_zAlt
-- name    : CondGeoVerif_Supplement_zAlt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:11:40.49281+00:00
-- url     : https://prove2.me/theorems/dadecff7-3c3c-4813-bbcf-4b00631aef1f
-- title:
--   Soundness on a family of laws, and the localized alternatives $P_v$ of §H.2 with constants $J_a,H_a,\theta_a,\varepsilon_a,C_a,L_a$
-- statement:
--   An interactive verifier is **sound on a family $L$ of laws** if the published arbitrary-label soundness holds for every law in $L$ (rather than every Gaussian-marginal law).
--
--   **The construction of §H.2.** Let $d\ge2$, $X=(T,Z)\sim N(0,I_d)$, $h_0(X)=\mathrm{sign}(T)$ and $0<a<a_c$. Put $\eta_a=(1-a)/2$, $k_a=\Phi^{-1}((1+a)/2)$, $q(u)=\bar\Phi(u)$, $g_a(u)=\min\{q(u),1-a-q(u)\}$, $J_a=\int_0^\infty g_a$. An **admissible cutoff** is $M\ge\max\{1,k_a\}$ with $(1+a)\int_M^\infty q\le J_a/4$. Then
--   $$H_a=\int_0^Mu^2|g_a(u)|\,du,\quad \theta_a=\min\Big\{\frac\pi4,\arctan\sqrt{\frac{J_a}{2H_a}}\Big\},\quad \varepsilon_a=\frac{\phi_0J_a\theta_a}4,\quad C_a=\frac{16M}{J_a},\quad L_a=1+\log(24)\Big(8C_a+\frac83\Big).$$
--   For $0<\varepsilon\le\varepsilon_a$ let $\theta=4\varepsilon/(\phi_0J_a)$ and $b=M\tan\theta$. For $v\in S^{d-2}$ the tilted halfspace is $h_v(T,Z)=\mathrm{sign}(T+\tan\theta\,v\cdot Z)$. Inside the strip $|T|\le b$, with $q=\Phi(-|T|\cot\theta)$ and $D=1\{h_v\ne h_0\}$, the label differs from $h_0$ with probability
--   $$z_v=\frac{\eta_a}{q}D\ \ (q\ge\eta_a),\qquad z_v=D+\frac{\eta_a-q}{1-q}(1-D)\ \ (q<\eta_a),$$
--   and outside the strip with probability $\eta_a$. The null $Q$ has regression $r_0=ah_0$, and $P_v$ has regression $r_v=h_0(1-2z_v)$.
--
--   **Formalization Note** $v\in S^{d-2}$ is a unit $w\in\mathbb R^d$ with $w_1=0$, so $v\cdot Z=w\cdot x$. The laws are given through the published `IsLabelLaw` with base rule $h_0$ and the error probability $z_v$.
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §H.1–H.2, pp.64–65 (PDF pp.67–68), Lemma H.1, (H.1); Theorem H.4, p.67 (PDF p.70)

import Mathlib
import Definitions.Def_CondGeoVerif_IVerifier
import Definitions.Def_CondGeoVerif_Mprog
import Definitions.Def_CondGeoVerif_Supplement_critA
import Definitions.Def_CondGeoVerif_Supplement_boolComp

set_option autoImplicit false

namespace CondGeoVerif.Supplement

noncomputable section

open MeasureTheory ProbabilityTheory Cohen2019.Robust CondGeoVerif
open scoped Matrix

/-- **Soundness on a family of laws** for an interactive verifier (Chen, *The Conditional Geometry
of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, Theorem H.4, p.67 = PDF
p.70: "for every displayed P_v and every prover strategy is sound with probability at least 2/3"):
the published `ISound` restricted to the laws in `L`. -/
def ISoundOn {d : ℕ} (V : IVerifier d) (L : Set (ProbabilityMeasure (Vec d × Bool)))
    (H : Set (Vec d → Bool)) (ε δ : ℝ) : Prop :=
  ∀ P ∈ L, ∀ σ : Strategy V, σ.IsMeasurable →
    ((sampleLaw P V.m).prod (V.coins : Measure V.Ω))
        {sω | ∃ h, outcome V σ sω.1 sω.2 = some h ∧
          risk (P : Measure (Vec d × Bool)) h > opt (P : Measure (Vec d × Bool)) H + ε}
      ≤ ENNReal.ofReal δ

/-! ### The construction of §H.1–H.2 (Chen, Oct. 2026, pp.64–65 = PDF pp.67–68)

Fix `0 < a < a_c`. `η_a = (1 − a)/2`, `k_a = Φ⁻¹((1 + a)/2)`, `q(u) = Φ̄(u)`,
`g_a(u) = min{q(u), 1 − a − q(u)}`, `J_a = ∫₀^∞ g_a`. -/

/-- `η_a = (1 − a)/2`. -/
noncomputable def etaA (a : ℝ) : ℝ := (1 - a) / 2

/-- `k_a = Φ⁻¹((1 + a)/2)`. -/
noncomputable def kA (a : ℝ) : ℝ := PhiInvReal ((1 + a) / 2)

/-- `g_a(u) = min{Φ̄(u), 1 − a − Φ̄(u)}`. -/
noncomputable def gA (a u : ℝ) : ℝ := min (Phibar u) (1 - a - Phibar u)

/-- `J_a = ∫₀^∞ g_a(u) du` (equal to `2ϕ(k_a) − ϕ₀` by (H.1)). -/
noncomputable def JA (a : ℝ) : ℝ := ∫ u in Set.Ioi (0 : ℝ), gA a u

/-- The admissible cutoffs `M` of §H.2 (p.65): `M ≥ max{1, k_a}` and
`(1 + a)∫_M^∞ q(u) du ≤ J_a/4` ("Choose a finite M = M_a ≥ max{1, k_a} so large that …"). -/
def IsAdmissibleM (a M : ℝ) : Prop :=
  max 1 (kA a) ≤ M ∧ (1 + a) * ∫ u in Set.Ioi M, Phibar u ≤ JA a / 4

/-- `H_a = ∫₀^M u²|g_a(u)| du`. -/
noncomputable def HA (a M : ℝ) : ℝ := ∫ u in (0 : ℝ)..M, u ^ 2 * |gA a u|

/-- `θ_a = min{π/4, arctan √(J_a/(2H_a))}`. -/
noncomputable def thetaA (a M : ℝ) : ℝ :=
  min (Real.pi / 4) (Real.arctan (Real.sqrt (JA a / (2 * HA a M))))

/-- `ε_a = ϕ₀ J_a θ_a / 4`, `ϕ₀ = ϕ(0)`. -/
noncomputable def epsA (a M : ℝ) : ℝ := phi 0 * JA a * thetaA a M / 4

/-- `C_a = 16M/J_a` (Lemma H.2, p.65). -/
noncomputable def CA (a M : ℝ) : ℝ := 16 * M / JA a

/-- `L_a = 1 + log(24)(8C_a + 8/3)` (Theorem H.4, p.67). -/
noncomputable def LA (a M : ℝ) : ℝ := 1 + Real.log 24 * (8 * CA a M + 8 / 3)

/-- The tilt angle `θ = 4ε/(ϕ₀J_a)` (§H.2, p.65). -/
noncomputable def thetaEps (a ε : ℝ) : ℝ := 4 * ε / (phi 0 * JA a)

/-- The first coordinate `T = x₁` of `x = (T, Z) ∈ ℝ × ℝ^{d−1}`. -/
noncomputable def firstCoord {d : ℕ} (x : Vec d) : ℝ := (matVec (coordFrame d 1)ᵀ x) 0

/-- The anchor `h₀(X) = sign(T)`, i.e. the halfspace of the first coordinate vector. -/
noncomputable def h0 (d : ℕ) : Vec d → Bool := frameRule halfRule (coordFrame d 1)

/-- The tilted halfspace `h_v(T, Z) = sign(T + tan θ·v·Z)` for `v ∈ S^{d−2}`, encoded by a unit
`w ∈ ℝᵈ` with `w₁ = 0` (so that `v·Z = w·x`). -/
noncomputable def tiltRule {d : ℕ} (a ε : ℝ) (w : Vec d) : Vec d → Bool :=
  fun x => sgn (firstCoord x + Real.tan (thetaEps a ε) * inner ℝ w x)

/-- **The conditional error allocation of the alternative `P_v`** (Chen, Oct. 2026, Lemma H.1,
p.64, and §H.2, p.65): inside the strip `|T| ≤ b`, `b = M tan θ`, with `q = Φ(−|T| cot θ)`,
`D = 1{h_v ≠ h₀}` and `η = η_a`, the probability that the label differs from `h₀` is
`z = (η/q)D` if `q ≥ η` and `z = D + ((η − q)/(1 − q))(1 − D)` if `q < η`; outside the strip it is
`η_a` (the null). The regression is `r_v = h₀(1 − 2z)`. -/
noncomputable def zAlt {d : ℕ} (a M ε : ℝ) (w : Vec d) (x : Vec d) : ℝ :=
  if |firstCoord x| ≤ M * Real.tan (thetaEps a ε) then
    (if etaA a ≤ Phi (-|firstCoord x| * Real.cot (thetaEps a ε)) then
      etaA a / Phi (-|firstCoord x| * Real.cot (thetaEps a ε)) *
        ind (decide (tiltRule a ε w x ≠ h0 d x))
    else
      ind (decide (tiltRule a ε w x ≠ h0 d x)) +
        (etaA a - Phi (-|firstCoord x| * Real.cot (thetaEps a ε))) /
          (1 - Phi (-|firstCoord x| * Real.cot (thetaEps a ε))) *
          (1 - ind (decide (tiltRule a ε w x ≠ h0 d x))))
  else etaA a

/-- The alternative regression `r_v = h₀(1 − 2z_v)` (as a real function). -/
noncomputable def rAlt {d : ℕ} (a M ε : ℝ) (w : Vec d) (x : Vec d) : ℝ :=
  sgnR (firstCoord x) * (1 - 2 * zAlt a M ε w x)

end

end CondGeoVerif.Supplement


