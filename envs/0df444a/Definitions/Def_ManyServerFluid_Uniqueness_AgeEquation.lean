-- Prove2me | Definitions.Def_ManyServerFluid_Uniqueness_AgeEquation
-- name    : ManyServerFluid_Uniqueness_AgeEquation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:52.961997+00:00
-- url     : https://prove2.me/theorems/e3d8ce04-901f-4d06-8910-cbdf6ea9630f
-- title:
--   The age equation (4.2), the bound (4.1), Radon paths on [0, M), BV_0 integrals, |·|_TV, C_b^1, and ψ_ℓ of (4.45)–(4.46)
-- statement:
--   This file adds the objects of Section 4 of Kaspi and Ramanan on top of the fluid model.
--
--   1. **Radon measures on $[0,M)$**, $\mathcal M[0,M)$: measures carried by $[0,M)$ and finite on every $[0,m]$ with $m < M$; they may have infinite total mass.
--   2. $\mathcal C_c[0,M)$: functions continuous on $[0,M)$ that vanish on $[0,M)$ beyond some $m < M$.
--   3. **Vaguely càdlàg paths** $\{\bar\nu_s\}_{s\ge0} \in \mathcal D_{\mathcal M[0,M)}[0,\infty)$: every $\bar\nu_s$ is a Radon measure on $[0,M)$ and $s \mapsto \langle f, \bar\nu_s\rangle$ is càdlàg for every $f \in \mathcal C_c[0,M)$.
--   4. **The bound (4.1)**: for every $m < M$ and $T$ there is $C(m,T) < \infty$ with
--   $$\Big|\int_0^\infty\langle\varphi(\cdot,s)h(\cdot),\bar\nu_s\rangle ds\Big| \le C(m,T)\,\|\varphi\|_\infty$$
--   for every $\varphi$ continuous on $[0,M)\times[0,\infty)$ vanishing there outside $[0,m]\times[0,T]$.
--   5. **$BV_0$ integrals.** A càdlàg function $Z$ of bounded variation on bounded intervals with $Z(0) = 0$ is written $Z = Z_1 - Z_2$ with $Z_1, Z_2 \in \mathcal I_0[0,\infty)$, and $\int_A\varphi\,dZ = \int_A\varphi\,dZ_1 - \int_A\varphi\,dZ_2$.
--   6. **The age equation (4.2)** for $\upsilon_0 \in \mathcal M[0,M)$ and $Z \in BV_0[0,\infty)$: for every $\varphi \in \mathcal C_c^{1,1}([0,M)\times\mathbb R_+)$ and $t \ge 0$,
--   $$\langle\varphi(\cdot,t),\bar\nu_t\rangle = \langle\varphi(\cdot,0),\upsilon_0\rangle + \int_0^t\langle\varphi_x+\varphi_s,\bar\nu_s\rangle ds - \int_0^t\langle h\varphi(\cdot,s),\bar\nu_s\rangle ds + \int_{[0,t]}\varphi(0,s)\,dZ(s).$$
--   7. **The representation (4.3)**, as a function of $f$ and $t$:
--   $$\int_{[0,M)} f(x+t)\frac{1-G(x+t)}{1-G(x)}\upsilon_0(dx) + \int_{[0,t]} f(t-s)(1-G(t-s))\,dZ(s).$$
--   8. **$|\Delta\upsilon_0|_{TV}$**, the total variation on $[0,M)$ of the difference of two Radon measures (p. 53), possibly $+\infty$.
--   9. $\mathcal C_b^1(\mathbb R_+)$: continuously differentiable functions with $f$ and $f'$ bounded on $[0,\infty)$.
--   10. For $\ell \in L^1_{loc}[0,M)$, $\psi_\ell(x,t) = \exp(r_\ell(x,t))$ (4.45) with
--   $$r_\ell(x,t) = \begin{cases}-\int_{x-t}^x\ell(u)\,du, & 0\le t\le x<M,\\ -\int_0^x\ell(u)\,du, & 0\le x\le t,\ x<M,\\ 0, & \text{otherwise}\end{cases}\qquad(4.46).$$
--
--   The age equation is the fluid equation (3.5) with an arbitrary Radon measure $\upsilon_0$ and an arbitrary $Z$ in place of $\bar\nu_0$ and $\bar K$ (Remark 4.2); it is the object of Theorem 4.1 and Lemma 4.5.
--
--   **Formalization Note.** The vague topology is the initial topology of the maps $\mu\mapsto\langle f,\mu\rangle$, $f\in\mathcal C_c[0,M)$, and on Radon measures scalar left limits for every such $f$ define a Radon left limit (Riesz), so item 3 is càdlàg in the vague topology. In item 4 the bound is applied to $|\varphi|$ (same support, same sup norm) inside a lower integral, which is equivalent to the paper's bound and makes the integral absolutely convergent; $\|\varphi\|_\infty \le c$ is a pointwise bound and $C \ge 0$. Every càdlàg $BV_0$ function is such a difference (Jordan decomposition with right-continuous parts), and every integral depends only on $Z_1 - Z_2$, so quantifying over pairs is quantifying over $BV_0$. The total variation is computed as the supremum over $m < M$ and measurable $A$ of $\mu(A\cap[0,m]) - \mu(A^c\cap[0,m])$, $\mu = \upsilon^2 - \upsilon^1$ (Hahn), in $[0,\infty]$. A $\mathcal C_b^1(\mathbb R_+)$ function is represented by a $C^1$ function on $\mathbb R$; only its values on $[0,\infty)$ are read. Interval integrals of $\ell$ are Lean's `intervalIntegral`.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), pp. 36–37 (§1.2), p. 51 (Theorem 4.1, (4.1)–(4.3), Remark 4.2), p. 53 (|μ|_TV), p. 67 ((4.45)–(4.46))

import Mathlib
import Definitions.Def_ManyServerFluid_Uniqueness_Model

namespace ManyServerFluid.Uniqueness

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- ∫_A φ dZ for Z = Z₁ − Z₂ ∈ BV_0[0, ∞) written as a difference of two I_0 paths:
∫_A φ dZ₁ − ∫_A φ dZ₂ (Lebesgue–Stieltjes integrals through `stieltjes`). The value depends only on
Z₁ − Z₂ when Z₁, Z₂ are I_0 paths (the Stieltjes measures are additive). -/
noncomputable def bvInt (Z₁ Z₂ : ℝ → ℝ) (A : Set ℝ) (φ : ℝ → ℝ) : ℝ :=
  ∫ s in A, φ s ∂(stieltjes Z₁) - ∫ s in A, φ s ∂(stieltjes Z₂)

/-- C_b^1(R₊): continuously differentiable, with f and f′ bounded on [0, ∞). A function on R₊ that
is C¹ (one-sided at 0) with f, f′ bounded extends to such a function on ℝ, and only values on
[0, ∞) are ever read. -/
def IsCb1 (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ ∃ C : ℝ, ∀ x, 0 ≤ x → |f x| ≤ C ∧ |deriv f x| ≤ C

namespace ServiceLaw
variable (S : ServiceLaw)

/-- M[0, M): a (possibly infinite) Radon measure on [0, M), i.e. carried by [0, M) and finite on
every [0, m] with m < M. -/
def IsRadonAges (υ : Measure ℝ) : Prop :=
  υ S.Agesᶜ = 0 ∧ ∀ m : ℝ, ENNReal.ofReal m < S.M → υ (Icc 0 m) < ⊤

/-- C_c[0, M) (p. 36): continuous on [0, M) and vanishing on [0, M) beyond some m < M (compact
support relative to [0, M); f need not vanish at 0). -/
def IsCcAges (f : ℝ → ℝ) : Prop :=
  ContinuousOn f S.Ages ∧ ∃ m : ℝ, ENNReal.ofReal m < S.M ∧ ∀ x ∈ S.Ages, m < x → f x = 0

/-- D_{M[0,M)}[0, ∞): every ν_t (t ≥ 0) is a Radon measure on [0, M), and t ↦ ⟨f, ν_t⟩ is càdlàg on
[0, ∞) for every f ∈ C_c[0, M). The vague topology on M[0, M) is the initial topology of the maps
μ ↦ ⟨f, μ⟩, f ∈ C_c[0, M), and scalar left limits for every such f define a Radon left limit (Riesz),
so this is càdlàg in the vague topology. -/
def IsVagueCadlag (ν : ℝ → Measure ℝ) : Prop :=
  (∀ t, 0 ≤ t → S.IsRadonAges (ν t)) ∧
  ∀ f, S.IsCcAges f → IsCadlag (fun t => ∫ x, f x ∂(ν t))

/-- (4.1), p. 51: for every m ∈ [0, M) and T there is C(m, T) < ∞ with
|∫_0^∞ ⟨φ(·, s) h(·), ν_s⟩ ds| ≤ C(m, T) ‖φ‖_∞ for every φ continuous on [0, M) × [0, ∞) vanishing
there outside [0, m] × [0, T]. Stated with |φ| in a lower integral (apply (4.1) to |φ|, which has the
same support and sup norm), so the integral is a genuine absolutely convergent one; ‖φ‖_∞ ≤ c is
written as a pointwise bound. -/
def HazardBound (ν : ℝ → Measure ℝ) : Prop :=
  ∀ m T : ℝ, ENNReal.ofReal m < S.M → ∃ C : ℝ, 0 ≤ C ∧
    ∀ φ : ℝ × ℝ → ℝ, ContinuousOn φ (S.Ages ×ˢ Ici 0) →
      (∀ p ∈ S.Ages ×ˢ Ici (0 : ℝ), (m < p.1 ∨ T < p.2) → φ p = 0) →
      ∀ c : ℝ, (∀ p ∈ S.Ages ×ˢ Ici (0 : ℝ), |φ p| ≤ c) →
        ∫⁻ s in Ici 0, ∫⁻ x, ENNReal.ofReal (|φ (x, s)| * S.h x) ∂(ν s) ≤ ENNReal.ofReal (C * c)

/-- The age equation (4.2), p. 51, for υ_0 ∈ M[0, M) and Z = Z₁ − Z₂ ∈ BV_0[0, ∞): for every
φ ∈ C_c^{1,1}([0, M) × R₊) and t ≥ 0,
⟨φ(·,t), ν_t⟩ = ⟨φ(·,0), υ_0⟩ + ∫_0^t ⟨φ_x + φ_s, ν_s⟩ ds − ∫_0^t ⟨hφ(·,s), ν_s⟩ ds + ∫_[0,t] φ(0,s) dZ(s).
υ_0 is not required to be ν_0. -/
def AgeEq (υ0 : Measure ℝ) (Z₁ Z₂ : ℝ → ℝ) (ν : ℝ → Measure ℝ) : Prop :=
  ∀ φ Dφ, S.IsTestFn φ Dφ → ∀ t, 0 ≤ t →
    ∫ x, φ (x, t) ∂(ν t) =
      ∫ x, φ (x, 0) ∂υ0
      + ∫ s in Icc 0 t, ∫ x, Dφ (x, s) ∂(ν s)
      - ∫ s in Icc 0 t, ∫ x, S.h x * φ (x, s) ∂(ν s)
      + bvInt Z₁ Z₂ (Icc 0 t) (fun s => φ (0, s))

/-- The right-hand side of (4.3), p. 51:
∫_[0,M) f(x + t) (1 − G(x + t))/(1 − G(x)) υ_0(dx) + ∫_[0,t] f(t − s)(1 − G(t − s)) dZ(s). -/
noncomputable def ageRep (υ0 : Measure ℝ) (Z₁ Z₂ : ℝ → ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, f (x + t) * ((1 - S.G (x + t)) / (1 - S.G x)) ∂υ0
  + bvInt Z₁ Z₂ (Icc 0 t) (fun s => f (t - s) * (1 - S.G (t - s)))

/-- |υ² − υ¹|_TV (p. 53), the total variation on [0, M) of the difference of two Radon measures on
[0, M): the supremum over m < M of the total variation on [0, m], computed by the Hahn formula
|μ|([0, m]) = sup_A (μ(A ∩ [0, m]) − μ(Aᶜ ∩ [0, m])). In ℝ≥0∞; it may be +∞. -/
noncomputable def tvDiff (υ1 υ2 : Measure ℝ) : ℝ≥0∞ :=
  ⨆ (m : ℝ) (_ : ENNReal.ofReal m < S.M) (A : Set ℝ) (_ : MeasurableSet A),
    ENNReal.ofReal (((υ2 (A ∩ Icc 0 m)).toReal - (υ1 (A ∩ Icc 0 m)).toReal)
      - ((υ2 (Aᶜ ∩ Icc 0 m)).toReal - (υ1 (Aᶜ ∩ Icc 0 m)).toReal))

end ServiceLaw

/-- (4.46), p. 67: r_ℓ(x, t) = −∫_{x−t}^x ℓ if 0 ≤ t ≤ x < M; −∫_0^x ℓ if 0 ≤ x ≤ t, x < M; 0
otherwise. (At x = t both formulas agree.) -/
noncomputable def ServiceLaw.rEll (S : ServiceLaw) (ℓ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := by
  classical
  exact if 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ ENNReal.ofReal p.1 < S.M then -∫ u in (p.1 - p.2)..p.1, ℓ u
    else if 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ ENNReal.ofReal p.1 < S.M then -∫ u in (0 : ℝ)..p.1, ℓ u
    else 0

/-- (4.45), p. 67: ψ_ℓ(x, t) = exp(r_ℓ(x, t)). -/
noncomputable def ServiceLaw.psiEll (S : ServiceLaw) (ℓ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (S.rEll ℓ p)

end ManyServerFluid.Uniqueness


