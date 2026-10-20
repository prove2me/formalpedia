-- Prove2me | Definitions.Def_DynkinAsymInfo_Linear_ClosedForms
-- name    : DynkinAsymInfo_Linear_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:25.869227+00:00
-- url     : https://prove2.me/theorems/9a704586-8e74-42b9-86ea-7943d8512ebc
-- title:
--   §6.3 — free boundaries, explicit value functions, and reflecting control
-- statement:
--   Let $\beta_1\in(0,1)$ and $\beta_2<0$ be the two roots of $\omega^2\beta(\beta-1)/2+\sigma\omega\beta+\mu_0=0$. Let $\delta\in(0,1)$ solve (90), define $B$ by (93), and set $A=\delta B$. The constants $C_1,C_2,D_1,D_2$ are those of (89) and (91); they determine piecewise functions $V_1,V$, extended according to (94)–(97). Finally $V_0(\phi)=V(\phi)-\phi V_1(\phi)$.
--
--   The reflecting control has the explicit running-maximum form
--   $$\Gamma^B_t=\max\left\{0,1-\frac{B}{\max_{s\le t}\Phi_s}\right\},\qquad \Phi^B_t=\Phi_t(1-\Gamma^B_t),\qquad \tau_A=\inf\{t:\Phi^B_t\le A\}.$$
--   The candidate informed strategy uses the pair $(0,\Gamma^B)$. A second GBM realises the tilted likelihood law used in Lemma 6.5.
--
--   **Formalization Note.** $\delta$ is the infimum of the root set; Lemma 6.9 makes it a singleton. The running maximum is over the compact interval $[0,t]$. The tilted law is represented at the level of the likelihood path.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, pp. 19–24, (65), (74)–(77), (89)–(97)

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinAsymInfo.Linear
set_option autoImplicit false
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The two indicial roots in §6.3, p. 23, (89). -/
noncomputable def quadA (p : Params) : ℝ := signalNoise p ^ 2 / 2
noncomputable def quadB (p : Params) : ℝ := p.sigma * signalNoise p - signalNoise p ^ 2 / 2
noncomputable def discr (p : Params) : ℝ := quadB p ^ 2 - 4 * quadA p * p.mu0
noncomputable def beta1 (p : Params) : ℝ :=
  (-quadB p + Real.sqrt (discr p)) / (2 * quadA p)
noncomputable def beta2 (p : Params) : ℝ :=
  (-quadB p - Real.sqrt (discr p)) / (2 * quadA p)

/-- The left side of equation (90), minus its right side, p. 23. -/
noncomputable def rootEq (p : Params) (eps z : ℝ) : ℝ :=
  (1 - beta2 p) * z ^ (beta1 p - 1) +
    (beta1 p - 1) * z ^ (beta2 p - 1) -
      (beta1 p - beta2 p) / (1 + eps)

/-- The unique root `δ=A/B` of (90), p. 23. The root set is a singleton under
Assumption 6.2 and `eps>0` (Lemma 6.9). -/
noncomputable def delta (p : Params) (eps : ℝ) : ℝ :=
  sInf {z : ℝ | z ∈ Set.Ioo 0 1 ∧ rootEq p eps z = 0}

/-- The upper free boundary (93), p. 24. -/
noncomputable def Bb (p : Params) (eps : ℝ) : ℝ :=
  let d := delta p eps
  let b1 := beta1 p
  let b2 := beta2 p
  b1 * b2 * (d ^ (-b2) - d ^ (-b1)) /
    ((1 + eps) * (b1 - b2) - b2 * (b1 - 1) * d ^ (1 - b2) +
      b1 * (b2 - 1) * d ^ (1 - b1))

/-- The lower free boundary `A=δB`, p. 24. -/
noncomputable def Ab (p : Params) (eps : ℝ) : ℝ := delta p eps * Bb p eps

/-- The four coefficients of (89) and (91), pp. 23–24. -/
noncomputable def C1 (p : Params) (eps : ℝ) : ℝ :=
  (1 - beta2 p) * (1 + eps) / (beta1 p - beta2 p) * Bb p eps ^ (1 - beta1 p)
noncomputable def C2 (p : Params) (eps : ℝ) : ℝ :=
  (beta1 p - 1) * (1 + eps) / (beta1 p - beta2 p) * Bb p eps ^ (1 - beta2 p)
noncomputable def D1 (p : Params) (eps : ℝ) : ℝ :=
  Ab p eps ^ (-beta1 p) / (beta1 p - beta2 p) *
    (-beta2 p + (1 - beta2 p) * Ab p eps)
noncomputable def D2 (p : Params) (eps : ℝ) : ℝ :=
  Ab p eps ^ (-beta2 p) / (beta1 p - beta2 p) *
    (beta1 p + (beta1 p - 1) * Ab p eps)

/-- The informed type's piecewise candidate value (89), (96), (97), pp. 23–24. -/
noncomputable def V1 (p : Params) (eps phi : ℝ) : ℝ :=
  if phi ≤ Ab p eps then 1
  else if Bb p eps ≤ phi then 1 + eps
  else C1 p eps * phi ^ (beta1 p - 1) + C2 p eps * phi ^ (beta2 p - 1)

/-- The scaled value (91), (94), (95), p. 24. -/
noncomputable def V (p : Params) (eps phi : ℝ) : ℝ :=
  if phi ≤ Ab p eps then 1 + phi
  else if Bb p eps ≤ phi then
    D1 p eps * Bb p eps ^ beta1 p + D2 p eps * Bb p eps ^ beta2 p +
      (1 + eps) * (phi - Bb p eps)
  else D1 p eps * phi ^ beta1 p + D2 p eps * phi ^ beta2 p

/-- The type-zero value, §6.3, p. 23. -/
noncomputable def V0 (p : Params) (eps phi : ℝ) : ℝ := V p eps phi - phi * V1 p eps phi

/-- Running maximum of the likelihood ratio up to time `t`, the explicit
Skorokhod representation underlying (71)–(75), pp. 20–21. -/
noncomputable def runMax (p : Params) (st : Setting Ω) (x pi : ℝ)
    (t : ℝ≥0) (a : Ω) : ℝ :=
  sSup ((fun s => Phi p st x pi s a) '' Set.Icc (0 : ℝ≥0) t)

/-- The control `Γ^B`, equivalent to (74) under the reflected likelihood law. -/
noncomputable def GammaB (p : Params) (st : Setting Ω) (x pi B : ℝ)
    (t : ℝ≥0) (a : Ω) : ℝ :=
  max 0 (1 - B / runMax p st x pi t a)

/-- The adjusted likelihood `(75)`, p. 20. -/
noncomputable def PhiB (p : Params) (st : Setting Ω) (x pi B : ℝ)
    (t : ℝ≥0) (a : Ω) : ℝ :=
  Phi p st x pi t a * (1 - GammaB p st x pi B t a)

/-- The Skorokhod regulator recovered from the explicit control, (74), p. 20. -/
noncomputable def regulatorB (p : Params) (st : Setting Ω) (x pi B : ℝ)
    (t : ℝ≥0) (a : Ω) : ℝ :=
  -B * Real.log ((1 - GammaB p st x pi B t a) /
    (1 - GammaB p st x pi B 0 a))

/-- The observation stopping time `(76)`, p. 21; infimum of the empty set is infinity. -/
noncomputable def tauA (p : Params) (st : Setting Ω) (x pi A B : ℝ)
    (a : Ω) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : PhiB p st x pi B t a ≤ A), (t : WithTop ℝ≥0)

/-- The type-contingent control `Γ*=(0,Γ^B)` of Theorem 6.10, p. 24. -/
noncomputable def GammaStar (p : Params) (st : Setting Ω) (x pi B : ℝ) :
    ℝ≥0 → Ω → ℝ :=
  mixControl st pi (fun _ _ => 0) (GammaB p st x pi B)

/-- Law-level realisation of the likelihood under `P̃⁰`, (65), p. 19. -/
noncomputable def PhiTilde (p : Params) (st : Setting Ω) (phi : ℝ)
    (t : ℝ≥0) (a : Ω) : ℝ :=
  phi * Real.exp (signalNoise p * st.W t a +
    (p.sigma * signalNoise p - signalNoise p ^ 2 / 2) * (t : ℝ))

noncomputable def runMaxTilde (p : Params) (st : Setting Ω) (phi : ℝ)
    (t : ℝ≥0) (a : Ω) : ℝ :=
  sSup ((fun s => PhiTilde p st phi s a) '' Set.Icc (0 : ℝ≥0) t)

noncomputable def PhiBTilde (p : Params) (st : Setting Ω) (phi B : ℝ)
    (t : ℝ≥0) (a : Ω) : ℝ :=
  PhiTilde p st phi t a * (1 - max 0 (1 - B / runMaxTilde p st phi t a))

noncomputable def tauATilde (p : Params) (st : Setting Ω) (phi A B : ℝ)
    (a : Ω) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : PhiBTilde p st phi B t a ≤ A), (t : WithTop ℝ≥0)

/-- The discounted hitting payoff under the law-level tilted representation, (77),
p. 21, with `e^{mu0·∞}=0`. -/
noncomputable def discountedHit (p : Params) (st : Setting Ω) (phi A B : ℝ) : ℝ≥0∞ :=
  ∫⁻ a, if tauATilde p st phi A B a = ⊤ then 0 else
    ENNReal.ofReal (Real.exp (p.mu0 * ((tauATilde p st phi A B a).untopA : ℝ))) ∂st.P

end DynkinAsymInfo.Linear


