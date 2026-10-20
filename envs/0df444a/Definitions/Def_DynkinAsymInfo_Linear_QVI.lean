-- Prove2me | Definitions.Def_DynkinAsymInfo_Linear_QVI
-- name    : DynkinAsymInfo_Linear_QVI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:18.944641+00:00
-- url     : https://prove2.me/theorems/4eb325b5-ccab-4633-aecb-bf4dff50be1f
-- title:
--   §5 — candidate regions, generators, adjusted odds, and localisation
-- statement:
--   For candidate type values $u^0,u^1$ on $(0,\infty)^2$, set $u(x,\phi)=u^0(x,\phi)+\phi u^1(x,\phi)$. The continuation regions are $C=\{u>(1+\phi)f(x)\}$ and $C^i=\{u^i<g(x)\}$, each inside $(0,\infty)^2$; their relative complements are $S,S^i$. The two differential generators $\mathcal L^0,\mathcal L^1$ of the GBM and likelihood process are defined with their full $x$ factors.
--
--   For type controls $\Gamma^0,\Gamma^1$, adjusted odds are $\Phi^*_t=\Phi_t(1-\Gamma^1_t)/(1-\Gamma^0_t)$. The localisation integral $I(h)$ and capped hitting times $\tau_n(h)=\inf\{t:I(h)_t\ge n\}\wedge n$ are the printed expressions in §5.
--
--   These objects state the verification theorem precisely and can also serve other two-type stopping games.
--
--   **Formalization Note.** Closures are relative to $(0,\infty)^2$. At time zero the left odds are the initial odds, and the left control value is zero. The printed $I(h)$ uses one factor of $\Phi^*_{s-}$ in its second summand.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, pp. 13–14, (40)–(41) and Theorem 5.1

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_Game

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace DynkinAsymInfo.Linear
set_option autoImplicit false
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The open GBM state domain `I × (0,∞)`, with `I=(0,∞)`, §6. -/
def stateDomain : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2}

/-- Relative closure in the state domain, as specified just before Theorem 5.1, p. 14. -/
noncomputable def relativeClosure (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  closure S ∩ stateDomain

/-- The scaled value is constructed from the two type values, §5, p. 13. -/
def combinedValue (u0 u1 : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  u0 q + q.2 * u1 q

/-- The continuation and contact regions in Theorem 5.1, p. 14. -/
def C (u : ℝ × ℝ → ℝ) (f : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {q ∈ stateDomain | (1 + q.2) * f q.1 < u q}
def Ci (ui : ℝ × ℝ → ℝ) (g : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {q ∈ stateDomain | ui q < g q.1}
def S (u : ℝ × ℝ → ℝ) (f : ℝ → ℝ) : Set (ℝ × ℝ) :=
  stateDomain \ C u f
def Si (ui : ℝ × ℝ → ℝ) (g : ℝ → ℝ) : Set (ℝ × ℝ) :=
  stateDomain \ Ci ui g

/-- First partial derivatives of a candidate value in the GBM instance, p. 13. -/
noncomputable def dx (u : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  fderiv ℝ u q (1, 0)
noncomputable def dphi (u : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  fderiv ℝ u q (0, 1)
noncomputable def dxx (u : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  fderiv ℝ (dx u) q (1, 0)
noncomputable def dphiphi (u : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  fderiv ℝ (dphi u) q (0, 1)
noncomputable def dxphi (u : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  fderiv ℝ (dphi u) q (1, 0)

/-- The type-zero generator `L⁰` in the GBM instance, p. 13. -/
noncomputable def L0 (p : Params) (u : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  (signalNoise p ^ 2 * q.2 ^ 2 * dphiphi u q +
    p.sigma ^ 2 * q.1 ^ 2 * dxx u q +
    2 * p.sigma * signalNoise p * q.1 * q.2 * dxphi u q) / 2 +
    p.mu0 * q.1 * dx u q

/-- The type-one generator `L¹` in the GBM instance, p. 13. -/
noncomputable def L1 (p : Params) (u : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  (signalNoise p ^ 2 * q.2 ^ 2 * dphiphi u q +
    p.sigma ^ 2 * q.1 ^ 2 * dxx u q +
    2 * p.sigma * signalNoise p * q.1 * q.2 * dxphi u q) / 2 +
    p.mu1 * q.1 * dx u q + signalNoise p ^ 2 * q.2 * dphi u q

/-- The adjusted likelihood `Φ*`, (40), p. 13. -/
noncomputable def PhiStar (p : Params) (st : Setting Ω) (x pi : ℝ)
    (G0 G1 : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (a : Ω) : ℝ :=
  Phi p st x pi t a * (1 - G1 t a) / (1 - G0 t a)

/-- Left limit of `Φ*`; its left value at zero is the initial odds, as (40)
and the zero-time jump convention require. -/
noncomputable def PhiStarLeft (p : Params) (st : Setting Ω) (x pi : ℝ)
    (G0 G1 : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (a : Ω) : ℝ :=
  if t = 0 then pi / (1 - pi)
  else Function.leftLim (fun s => PhiStar p st x pi G0 G1 s a) t

/-- Jump of a control, with `Γ_{0-}=0`, pp. 4, 14. -/
noncomputable def controlJump (G : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (a : Ω) : ℝ :=
  if t = 0 then G 0 a else G t a - Function.leftLim (fun s => G s a) t

/-- The printed localisation integral `I(h)`, p. 13. Its second summand contains
one power of `Φ*_{s-}`, exactly as printed, rather than its square. -/
noncomputable def localI (p : Params) (st : Setting Ω) (x pi : ℝ)
    (G0 G1 : ℝ≥0 → Ω → ℝ) (h : ℝ × ℝ → ℝ)
    (t : ℝ≥0) (a : Ω) : ℝ≥0∞ :=
  ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
    let r : ℝ≥0 := ⟨max s 0, le_max_right s 0⟩
    ENNReal.ofReal (p.sigma ^ 2 * X p st x pi r a ^ 2 *
      dx h (X p st x pi r a, PhiStarLeft p st x pi G0 G1 r a) ^ 2 +
      signalNoise p ^ 2 * PhiStarLeft p st x pi G0 G1 r a *
      dphi h (X p st x pi r a, PhiStarLeft p st x pi G0 G1 r a) ^ 2)

/-- The localising time `τ_n(h)`, (41), p. 14, capped at n. -/
noncomputable def localTau (p : Params) (st : Setting Ω) (x pi : ℝ)
    (G0 G1 : ℝ≥0 → Ω → ℝ) (h : ℝ × ℝ → ℝ)
    (n : ℕ) (a : Ω) : WithTop ℝ≥0 :=
  (⨅ (t : ℝ≥0) (_ : (n : ℝ≥0∞) ≤ localI p st x pi G0 G1 h t a),
    (t : WithTop ℝ≥0)) ⊓ ((n : ℝ≥0) : WithTop ℝ≥0)

/-- First exit of `(X,Φ*)` from the candidate continuation region, p. 14. -/
noncomputable def exitTime (p : Params) (st : Setting Ω) (x pi : ℝ)
    (G0 G1 : ℝ≥0 → Ω → ℝ) (u : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (a : Ω) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : (X p st x pi t a, PhiStar p st x pi G0 G1 t a) ∉ C u f),
    (t : WithTop ℝ≥0)

/-- The transversality limit (49), p. 14, under the conditional type-i law
at the given starting point. -/
def Transverse (p : Params) (st : Setting Ω) (x pi i : ℝ)
    (G0 G1 : ℝ≥0 → Ω → ℝ) (u ui h : ℝ × ℝ → ℝ)
    (f : ℝ → ℝ) : Prop :=
  Tendsto (fun n : ℕ =>
    ∫⁻ a, if exitTime p st x pi G0 G1 u f a >
          localTau p st x pi G0 G1 h n a then
      ENNReal.ofReal (ui (X p st x pi (localTau p st x pi G0 G1 h n a).untopA a,
        PhiStar p st x pi G0 G1 (localTau p st x pi G0 G1 h n a).untopA a))
    else 0 ∂(Ptype st pi i)) atTop (nhds (0 : ℝ≥0∞))

end DynkinAsymInfo.Linear


