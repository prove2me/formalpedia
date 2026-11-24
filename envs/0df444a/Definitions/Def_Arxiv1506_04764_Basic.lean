-- Prove2me | Definitions.Def_Arxiv1506_04764_Basic
-- name    : Arxiv1506_04764_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T13:55:59.320159+00:00
-- url     : https://prove2.me/theorems/87bc9105-97fe-44a4-a94b-e87e63299aa9
-- title:
--   Far fields, Lorentz transformation and correlation functions for an observer moving relative to sources
-- statement:
--   Objects of Sections 2-3 of Braun, Monjid, Rougé and Kerr (2015).
--
--   1. **Vectors.** Points, velocities and current densities are vectors of $\mathbb{R}^3$ with the dot product $x\cdot y$, the cross product $x\times y$ and the Euclidean length $|x|=\sqrt{x\cdot x}$. The unit vector in the direction of $x\neq0$ is $\hat e_x=x/|x|$ (set to $0$ at $x=0$, a point the paper never uses). For a source point $r''$ and a field point $r$, $\mathbf R=r-r''$, $R=|\mathbf R|$, $\hat R=\hat e_{r-r''}$.
--   2. **Satellite motion.** The satellite frame $\mathcal R'$ moves with constant velocity $v_s$ relative to the Earth frame $\mathcal R$; $\beta=v_s/c$ and $\gamma=1/\sqrt{1-\beta\cdot\beta}$.
--   3. **Far fields (eqs. 3-4).** For a charge density $\rho(r'',s)$ and a current density $j(r'',s)$, with $\partial_t\rho,\partial_tj$ their time derivatives evaluated at the retarded time $t-R/c$,
--   $$E(r,t)=\frac{1}{4\pi\epsilon_0}\int d^3r''\Big\{\frac{\hat R}{cR}\partial_t\rho-\frac{1}{c^2R}\partial_tj\Big\},\qquad B(r,t)=-\frac{\mu_0}{4\pi}\int d^3r''\,\frac{\hat R}{R}\times\frac1c\partial_tj.$$
--   4. **Lorentz transformation (eqs. 5, 8, 9).** $E'=\gamma(E+c\beta\times B)-\frac{\gamma^2}{\gamma+1}\beta(\beta\cdot E)$. The event $(r',t')$ of $\mathcal R'$ has Earth-frame coordinates $t=\gamma(t'+\beta\cdot r'/c)$ and $r=r'+\frac{\gamma-1}{\beta^2}(r'\cdot\beta)\beta+\gamma\beta ct'$.
--   5. **Eq. (7).** $E'(r,t)=-\frac{\gamma\mu_0}{4\pi}\int\frac{d^3r''}{R}\Big[\partial_t(j-c\hat R\rho)+(\beta\cdot\partial_tj)\hat R-(\beta\cdot\hat R)\partial_tj-\frac{\gamma}{\gamma+1}\big(\beta\cdot\partial_t(j-c\hat R\rho)\big)\beta\Big]$, all source quantities at $(r'',t-R/c)$.
--   6. **Correlation function.** $S(r'')=\langle|\tilde J(r'',\omega_0)|^2\rangle\ge0$ is the source strength at the centre frequency $\omega_0$; $l_c,T_c$ are the correlation length and time; $w$ is the receiver filter; $r_1',r_2'$ are the antenna positions, $\Delta r=r_2'-r_1'$, $\Delta t=t_2'-t_1'$, $\hat e=\hat e_{r_1'-r''}$. Eq. (25) with the flat-spectrum replacement $\omega^2\langle|\tilde J(r'',\omega)|^2\rangle\to\omega_0^2S(r'')$ is
--   $$\frac{l_c^3}{2\pi T_c}\Big(\frac{\mu_0}{4\pi}\Big)^2\int d^3r''\frac{\omega_0^2S(r'')}{|r_1'-r''||r_2'-r''|}\int d\omega\,|w(\omega(1-\hat e\cdot\beta))|^2e^{-i\omega\Delta t+i\frac{\omega}{c}(\Delta r+\Delta t\,v_s)\cdot\hat e},$$
--   and eq. (27) is $\frac{l_c^3}{2\pi T_c}(\frac{\mu_0}{4\pi})^2\int d\omega\,\omega_0^2|w(\omega)|^2\int d^3r''\frac{S(r'')}{|r_1'-r''||r_2'-r''|}e^{-i\omega\Delta t+i\frac{\omega}{c}\Delta r\cdot\hat e}$.
--   7. **Eqs. (28)-(29).** The rectangular filter is $w=1$ on $[\omega_0-b/2,\omega_0+b/2]$ and $0$ elsewhere; $K=l_c^3b\omega_0^2\mu_0^2/(32\pi^3T_c)$; $\tau=-\Delta t+\Delta r\cdot\hat e/c$; $\operatorname{sinc}x=\sin x/x$ with $\operatorname{sinc}0=1$.
--   $$C_{28}=K\int d^3r''\frac{S(r'')\,e^{i\omega_0\tau}\operatorname{sinc}(b\tau/2)}{|r_1'-r''||r_2'-r''|},\qquad C_{VCZ}=K\int d^3r''\frac{S(r'')\,e^{i\omega_0\Delta r\cdot\hat e/c}}{|r_1'-r''||r_2'-r''|}.$$
--
--   **Formalization Note** Vectors are `Fin 3 → ℝ` and the Euclidean length is defined explicitly (the default norm on `Fin 3 → ℝ` is the sup norm). The time derivatives are `deriv` of $s\mapsto\rho(r'',s)$ and $s\mapsto j(r'',s)$ at the retarded time. The paper's correlation function is an ensemble average obtained through a chain of approximations; the definitions are the explicit right-hand sides of eqs. (25), (27), (28) and (29), which are what the statements relate. In the definition of eq. (25) the source integral is written outside the frequency integral.
-- source:
--   Braun, Monjid, Rougé and Kerr, Generalization of the Van Cittert-Zernike theorem: observers moving with respect to sources, arXiv:1506.04764v1 (2015), Sec. 2.1 (eqs. (3)-(9)), Sec. 2.4 (eqs. (25)-(28)), Sec. 3 (eq. (29))

import Mathlib

/-!
D. Braun, Y. Monjid, B. Rougé and Y. Kerr, *Generalization of the Van Cittert–Zernike theorem:
observers moving with respect to sources*, arXiv:1506.04764v1 (2015): the far fields of
Section 2.1 (eqs. (3)-(4)), the Lorentz transformation of fields and coordinates (eqs. (5), (8),
(9)), the field (7) in the satellite frame, and the correlation-function expressions
(25)-(29) of Sections 2.4 and 3.

Vectors of ℝ³ are `Fin 3 → ℝ` with the dot product `dotProduct` and the cross product
`crossProduct`; their Euclidean length is `len` (the sup norm of `Fin 3 → ℝ` is never used).
-/

open MeasureTheory Complex

noncomputable section

namespace Arxiv1506_04764

/-- Section 2: points `r, r', r''`, velocities `v_s`, `β` and current densities `j` are vectors of
ℝ³ (components `(x₁, x₂, x₃)`, Sec. 2, p. 3). -/
abbrev V3 := Fin 3 → ℝ

/-- Section 2.1: the Euclidean length `|x| = √(x · x)` (e.g. `R = |R|` after eq. (2)). -/
def len (x : V3) : ℝ := Real.sqrt (dotProduct x x)

/-- Section 2.1 (after eq. (2)) and eq. (13): the unit vector `ê_x = x / |x|` in the direction of
`x` (the paper's `R̂` for `x = r - r''` and `ê_{r'-r''}`). At `x = 0` it is `0`; the paper never
uses that point. -/
def unitVec (x : V3) : V3 := (len x)⁻¹ • x

/-- After eq. (6): `β = v_s / c`. -/
def betaVec (c : ℝ) (vs : V3) : V3 := c⁻¹ • vs

/-- After eq. (6): the Lorentz factor `γ = 1 / √(1 - β²)`. -/
def lorentzGamma (beta : V3) : ℝ := 1 / Real.sqrt (1 - dotProduct beta beta)

/-- Eqs. (1)-(4): the time derivative `∂_t ρ(r'', s)` of the charge density at source point `r''`
and time `s`. -/
def rhoDot (rho : V3 → ℝ → ℝ) (r'' : V3) (s : ℝ) : ℝ := deriv (rho r'') s

/-- Eqs. (1)-(4): the time derivative `∂_t j(r'', s)` of the current density at source point `r''`
and time `s`. -/
def jDot (j : V3 → ℝ → V3) (r'' : V3) (s : ℝ) : V3 := deriv (j r'') s

/-- Eqs. (1)-(4): the retarded time `t - R/c`, with `R = |r - r''|`. -/
def retTime (c : ℝ) (r r'' : V3) (t : ℝ) : ℝ := t - len (r - r'') / c

/-- Eq. (3): the integrand of the far electric field in the Earth frame,
`(R̂/(cR)) ∂_t ρ(r'', t - R/c) - (1/(c²R)) ∂_t j(r'', t - R/c)`, `R = r - r''`. -/
def farEIntegrand (c : ℝ) (rho : V3 → ℝ → ℝ) (j : V3 → ℝ → V3) (r : V3) (t : ℝ) (r'' : V3) :
    V3 :=
  ((1 / (c * len (r - r''))) * rhoDot rho r'' (retTime c r r'' t)) • unitVec (r - r'') -
    (1 / (c ^ 2 * len (r - r''))) • jDot j r'' (retTime c r r'' t)

/-- Eq. (3): the far (radiation) electric field `E(r, t)` in the Earth frame `𝓡`,
`E(r,t) = (1/(4πε₀)) ∫ d³r'' {…}`. -/
def farE (eps0 c : ℝ) (rho : V3 → ℝ → ℝ) (j : V3 → ℝ → V3) (r : V3) (t : ℝ) : V3 :=
  (1 / (4 * Real.pi * eps0)) • ∫ r'', farEIntegrand c rho j r t r''

/-- Eq. (4): the integrand of the far magnetic induction, `(R̂/R) × (1/c) ∂_t j(r'', t - R/c)`. -/
def farBIntegrand (c : ℝ) (j : V3 → ℝ → V3) (r : V3) (t : ℝ) (r'' : V3) : V3 :=
  (1 / len (r - r'')) •
    crossProduct (unitVec (r - r'')) ((1 / c) • jDot j r'' (retTime c r r'' t))

/-- Eq. (4): the far (radiation) magnetic induction `B(r, t) = -(μ₀/4π) ∫ d³r'' (R̂/R) × (1/c) ∂_t j`
in the Earth frame. -/
def farB (mu0 c : ℝ) (j : V3 → ℝ → V3) (r : V3) (t : ℝ) : V3 :=
  (-(mu0 / (4 * Real.pi))) • ∫ r'', farBIntegrand c j r t r''

/-- Eq. (5): the Lorentz transformation of the electric field to the frame `𝓡'` moving with
velocity `c β`: `E' = γ(E + c β × B) - (γ²/(γ+1)) β (β · E)`. -/
def lorentzE (c : ℝ) (beta E B : V3) : V3 :=
  lorentzGamma beta • (E + c • crossProduct beta B) -
    (lorentzGamma beta ^ 2 / (lorentzGamma beta + 1) * dotProduct beta E) • beta

/-- Eq. (7): the bracket of the integrand of `E'(r, t)`,
`∂_t(j - cR̂ρ) + (β·∂_t j) R̂ - (β·R̂) ∂_t j - (γ/(γ+1)) (β·∂_t(j - cR̂ρ)) β`, with `ρ, j` (and their
time derivatives) taken at `(r'', t - R/c)`. Since `R̂` does not depend on `t`,
`∂_t(j - cR̂ρ) = ∂_t j - c (∂_t ρ) R̂`. -/
def eq7Bracket (c : ℝ) (beta : V3) (rho : V3 → ℝ → ℝ) (j : V3 → ℝ → V3) (r : V3) (t : ℝ)
    (r'' : V3) : V3 :=
  let jd := jDot j r'' (retTime c r r'' t)
  let Jd := jd - (c * rhoDot rho r'' (retTime c r r'' t)) • unitVec (r - r'')
  Jd + dotProduct beta jd • unitVec (r - r'') - dotProduct beta (unitVec (r - r'')) • jd -
    (lorentzGamma beta / (lorentzGamma beta + 1) * dotProduct beta Jd) • beta

/-- Eq. (7): the right-hand side `-(γμ₀/4π) ∫ (d³r''/R) [ … ]`, the electric field in the satellite
frame `𝓡'` as a function of Earth-frame coordinates `(r, t)`. -/
def eq7Field (mu0 c : ℝ) (beta : V3) (rho : V3 → ℝ → ℝ) (j : V3 → ℝ → V3) (r : V3) (t : ℝ) :
    V3 :=
  (-(lorentzGamma beta * mu0 / (4 * Real.pi))) •
    ∫ r'', (1 / len (r - r'')) • eq7Bracket c beta rho j r t r''

/-- Eq. (8): the Earth-frame time `t = γ (t' + β·r'/c)` of the event `(r', t')` of `𝓡'`. -/
def earthTime (c : ℝ) (beta r' : V3) (t' : ℝ) : ℝ :=
  lorentzGamma beta * (t' + dotProduct beta r' / c)

/-- Eq. (9): the Earth-frame position `r = r' + ((γ-1)/β²)(r'·β) β + γ β c t'` of the event
`(r', t')` of `𝓡'`. -/
def earthPos (c : ℝ) (beta r' : V3) (t' : ℝ) : V3 :=
  r' + ((lorentzGamma beta - 1) / dotProduct beta beta * dotProduct r' beta) • beta +
    (lorentzGamma beta * c * t') • beta

/-- Section 2.4, eq. (25) after the paper's flat-spectrum assumption
`ω² ⟨|J̃(r'',ω)|²⟩ ≃ ω₀² S(r'')`, `S(r'') = ⟨|J̃(r'',ω₀)|²⟩`:
`(l_c³/(2πT_c)) (μ₀/4π)² ∫ d³r'' ω₀² S(r'')/(|r₁'-r''||r₂'-r''|) ∫ dω |w(ω(1 - ê·β))|²
 exp[-iωΔt + i(ω/c)(Δr + Δt v_s)·ê]`, with `ê = ê_{r₁'-r''}`, `Δr = r₂' - r₁'`, `β = v_s/c`.
The source integral is written outside the frequency integral. -/
def corrEq25Flat (lc Tc mu0 omega0 c : ℝ) (S : V3 → ℝ) (w : ℝ → ℂ) (vs r1 r2 : V3)
    (dt : ℝ) : ℂ :=
  ((lc ^ 3 / (2 * Real.pi * Tc) * (mu0 / (4 * Real.pi)) ^ 2 : ℝ) : ℂ) *
    ∫ r'', ((omega0 ^ 2 * S r'' / (len (r1 - r'') * len (r2 - r'')) : ℝ) : ℂ) *
      ∫ omega : ℝ,
        ((‖w (omega * (1 - dotProduct (unitVec (r1 - r'')) (betaVec c vs)))‖ ^ 2 : ℝ) : ℂ) *
          Complex.exp (-(I * omega * dt) +
            I * (omega / c : ℝ) * (dotProduct (r2 - r1 + dt • vs) (unitVec (r1 - r'')) : ℝ))

/-- Eq. (27): `(l_c³/(2πT_c)) (μ₀/4π)² ∫ dω ω₀² |w(ω)|² ∫ d³r'' S(r'')/(|r₁'-r''||r₂'-r''|)
exp[-iωΔt + i(ω/c) Δr·ê_{r₁'-r''}]`, `S(r'') = ⟨|J̃(r'',ω₀)|²⟩`, `Δr = r₂' - r₁'`. -/
def corrEq27 (lc Tc mu0 omega0 c : ℝ) (S : V3 → ℝ) (w : ℝ → ℂ) (r1 r2 : V3) (dt : ℝ) : ℂ :=
  ((lc ^ 3 / (2 * Real.pi * Tc) * (mu0 / (4 * Real.pi)) ^ 2 : ℝ) : ℂ) *
    ∫ omega : ℝ, ((omega0 ^ 2 * ‖w omega‖ ^ 2 : ℝ) : ℂ) *
      ∫ r'', ((S r'' / (len (r1 - r'') * len (r2 - r'')) : ℝ) : ℂ) *
        Complex.exp (-(I * omega * dt) +
          I * (omega / c : ℝ) * (dotProduct (r2 - r1) (unitVec (r1 - r'')) : ℝ))

/-- Section 2.4 (before eq. (28)): the rectangular filter `w(ω) = 1` for
`ω₀ - b/2 ≤ ω ≤ ω₀ + b/2` and `0` elsewhere. -/
def rectFilter (omega0 b : ℝ) (omega : ℝ) : ℂ :=
  if omega0 - b / 2 ≤ omega ∧ omega ≤ omega0 + b / 2 then 1 else 0

/-- After eq. (28): the constant `K = l_c³ b ω₀² μ₀² / (32 π³ T_c)`. -/
def constK (lc b omega0 mu0 Tc : ℝ) : ℝ :=
  lc ^ 3 * b * omega0 ^ 2 * mu0 ^ 2 / (32 * Real.pi ^ 3 * Tc)

/-- Eq. (28): the time argument `τ = -Δt + (1/c) Δr·ê_{r₁'-r''}` of the phase and of the sinc. -/
def tauEq28 (c : ℝ) (r1 r2 r'' : V3) (dt : ℝ) : ℝ :=
  -dt + dotProduct (r2 - r1) (unitVec (r1 - r'')) / c

/-- Eq. (28), the paper's main result: `K ∫ d³r'' S(r'') exp[iω₀τ] sinc[(b/2)τ] /
(|r₁'-r''||r₂'-r''|)`, with `τ` as in `tauEq28` and `sinc x = sin x / x` (`Real.sinc`, with value
`1` at `0`). -/
def corrEq28 (K omega0 b c : ℝ) (S : V3 → ℝ) (r1 r2 : V3) (dt : ℝ) : ℂ :=
  (K : ℂ) * ∫ r'', ((S r'' / (len (r1 - r'') * len (r2 - r'')) : ℝ) : ℂ) *
    Complex.exp (I * (omega0 * tauEq28 c r1 r2 r'' dt : ℝ)) *
      ((Real.sinc (b / 2 * tauEq28 c r1 r2 r'' dt) : ℝ) : ℂ)

/-- Eq. (29): the standard Van Cittert–Zernike form
`C_VCZ = K ∫ d³r'' S(r'') exp[iω₀ (1/c) Δr·ê_{r₁'-r''}] / (|r₁'-r''||r₂'-r''|)`. -/
def corrVCZ (K omega0 c : ℝ) (S : V3 → ℝ) (r1 r2 : V3) : ℂ :=
  (K : ℂ) * ∫ r'', ((S r'' / (len (r1 - r'') * len (r2 - r'')) : ℝ) : ℂ) *
    Complex.exp (I * (omega0 * (dotProduct (r2 - r1) (unitVec (r1 - r'')) / c) : ℝ))

end Arxiv1506_04764


