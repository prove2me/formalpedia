-- Prove2me | Definitions.Def_OTCChain_Equilibrium_ClosedForm
-- name    : OTCChain_Equilibrium_ClosedForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:56.055285+00:00
-- url     : https://prove2.me/theorems/311bce69-a468-4cb6-ae44-508a2f2623d0
-- title:
--   (20)–(21), (55)–(66), (77)–(84), pp. 13, 37–41 — closed forms: N_s, N_b, the cutoff equations, c*, the equilibrium densities and value functions
-- statement:
--   The closed-form objects of Theorem 1 of Shen, Wei and Yan and of its proof, for the model `OTCChain.Equilibrium.Model`. Write $k = \kappa/\lambda$.
--
--   1. **Populations** (64), (66): as functions of $y \in [0,1]$,
--   $$N_s(y) = \tfrac12\sqrt{(k + N - X - Ny)^2 + 4\tfrac{\kappa X}{\lambda}y} - \tfrac12(k + N - X - Ny),$$
--   $$N_b(y) = \tfrac12(N - Ny - X - k) + \tfrac12\sqrt{(N - Ny - X - k)^2 + 4k(N-X)(1-y)}.$$
--   2. **Cutoff equations** (20), (21): the right-hand sides as functions of the cutoff $\delta$,
--   $$\mathrm{rhs}_{20}(\delta) = \frac{\lambda\kappa\eta X}{[\kappa + r + \lambda N_b(F(\delta))(1-\eta)](\kappa + \lambda N_b(F(\delta)))}\int_0^\delta F(x)\,dx,$$
--   $$\mathrm{rhs}_{21}(\delta) = \frac{\lambda\kappa(1-\eta)(N-X)}{(\kappa + r + \lambda\eta N_s(F(\delta)))(\kappa + \lambda N_s(F(\delta)))}\int_\delta^{\bar\Delta}[1 - F(x)]\,dx.$$
--   3. **Threshold** (84): $\delta^* = \inf\{\delta \in [0,\bar\Delta] : \mathrm{rhs}_{21}(\delta) \le \mathrm{rhs}_{20}(\delta)\}$ and $c^* = \mathrm{rhs}_{20}(\delta^*)$. The paper defines $c^*$ by $\Delta_b(c^*) = \Delta_s(c^*)$, where $\Delta_b(c)$, $\Delta_s(c)$ solve (20), (21); since $\mathrm{rhs}_{20}$ increases and $\mathrm{rhs}_{21}$ decreases, this is the common value at their crossing. The set contains $\bar\Delta$, so the infimum is a genuine one.
--   4. **Candidate densities** (55)–(63) for cutoffs $\Delta_b < \Delta_s$, with $N_b = N_b(F(\Delta_b))$, $N_s = N_s(F(\Delta_s))$: on $[0,\Delta_b)$, $\mu_b = \mu_h = 0$, $\mu_n = \frac{\kappa(N-X) + \lambda N_b N}{\kappa + \lambda N_b} f$, $\mu_s = \frac{\kappa X}{\kappa + \lambda N_b} f$; on $[\Delta_b, \Delta_s)$, $\mu_n = \mu_h = 0$ and, with $A = N - NF - X - k$ and $R = \sqrt{A^2 + 4k(N-X)(1-F)}$,
--   $$\mu_b = \frac{Nf}{2}\Big[1 + \frac{A + 2\kappa(N-X)/(\lambda N)}{R}\Big], \qquad \mu_s = Nf - \mu_b;$$
--   on $[\Delta_s, \bar\Delta]$, $\mu_n = \mu_s = 0$, $\mu_b = \frac{\kappa(N-X)}{\kappa + \lambda N_s} f$, $\mu_h = \frac{\kappa X + \lambda N_s N}{\kappa + \lambda N_s} f$.
--   5. **Slopes** (77)–(78), for densities $\mu$ with $F_s(\Delta) = \int_0^\Delta\mu_s$, $F_b(\Delta) = \int_0^\Delta \mu_b$ and $D(\Delta) = \kappa + r + \lambda(1-\eta)[N_b - F_b(\Delta)] + \lambda\eta F_s(\Delta)$: on $(\Delta_b,\Delta_s)$, $V_s' = \frac{1}{\kappa+r}\frac{\kappa + r + \lambda\eta F_s}{D}$ and $V_b' = \frac{1}{\kappa+r}\frac{\lambda\eta F_s}{D}$; $V_s' = \frac{1}{\kappa + r + \lambda(1-\eta)N_b}$ on $[0,\Delta_b)$; $V_b' = \frac{1}{\kappa+r}\frac{\lambda\eta N_s}{\kappa + r + \lambda\eta N_s}$ on $(\Delta_s,\bar\Delta]$.
--   6. **Values** (79)–(82), computed from the candidate densities:
--   $$V_n = \frac{\kappa}{r}\int_{\Delta_b}^{\Delta_s} V_b'(z)[1-F(z)]\,dz + \frac{\kappa}{r}\frac{1}{\kappa+r}\frac{\lambda\eta N_s}{\kappa+r+\lambda\eta N_s}\int_{\Delta_s}^{\bar\Delta}[1-F(z)]\,dz,$$
--   $$V_h(\Delta_s) = \frac{1+\Delta_s}{r} - \frac{\kappa}{r}\frac{\int_0^{\Delta_b}F}{\kappa + r + \lambda N_b(1-\eta)} - \frac{\kappa}{r}\int_{\Delta_b}^{\Delta_s}V_s'(z)F(z)\,dz + \frac{\kappa}{r}\frac{\int_{\Delta_s}^{\bar\Delta}[1-F]}{\kappa + r},$$
--   $V_s(\Delta_b) = V_h(\Delta_s) - \int_{\Delta_b}^{\Delta_s}V_s'$. Then $V(0,\Delta)$ is $V_n$ on $[0,\Delta_b]$, $V_n + \int_{\Delta_b}^\Delta V_b'$ on $[\Delta_b,\Delta_s]$ and $V_n + \int_{\Delta_b}^{\Delta_s}V_b' + V_b'|_{(\Delta_s,\bar\Delta]}(\Delta - \Delta_s)$ beyond; $V(1,\Delta)$ is $V_s(\Delta_b) + \frac{\Delta - \Delta_b}{\kappa + r + \lambda N_b(1-\eta)}$ on $[0,\Delta_b]$, $V_s(\Delta_b) + \int_{\Delta_b}^\Delta V_s'$ on $[\Delta_b,\Delta_s]$ and $V_h(\Delta_s) + \frac{\Delta-\Delta_s}{\kappa+r}$ beyond. The four candidate value functions are $V_h(\Delta) = V_h(\Delta_s) + \frac{\Delta - \Delta_s}{\kappa + r}$, $V_n$, $V_s = V(1,\cdot)$ on $[0,\Delta_s]$ and $V_b = V(0,\cdot)$ on $[\Delta_b,\bar\Delta]$, completed elsewhere by the right-hand sides of (9) and (11).
--
--   These are the objects that Theorem 1 asserts every equilibrium equals.
--
--   **Formalization Note** The printed (59)–(60) lack the term $2\kappa(N-X)/(\lambda N)$ and violate (18) and $N_b = \int\mu_b$; the corrected form is the derivative of $-N_b(F(\Delta))$, i.e. $\int_\Delta^{\bar\Delta}\mu_b = N_b(F(\Delta))$ on the middle region. The branches of (80) and (82) are labelled "for $z \in$" on the page where $\Delta$ is meant, and the brace is added to the constant in front of it; $V(1,\cdot)$ on $[\Delta_s,\bar\Delta]$ is read from (81). The radicands of the square roots are positive under the standing assumptions. The values of the candidate densities at $\Delta_b$, $\Delta_s$ are a convention: the steady state does not constrain them.
-- source:
--   Shen, Wei & Yan, Financial Intermediation Chains in an OTC Market, MPRA Paper No. 74925 (version of October 29, 2016), p. 13 (PDF 16) (20)–(21); pp. 37–38 (PDF 40–41) (55)–(66); p. 40 (PDF 43) (77)–(82); p. 41 (PDF 44) (84)

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model

namespace OTCChain.Equilibrium

open MeasureTheory Set

/-- (64), p. 38: the seller population as a function of `y = F(∆s)`,
`N_s = ½ √([κ/λ + N − X − N y]² + 4 (κX/λ) y) − ½ [κ/λ + N − X − N y]`. -/
noncomputable def NsOf (M : Params) (y : ℝ) : ℝ :=
  Real.sqrt ((M.κ / M.lam + M.N - M.X - M.N * y) ^ 2 + 4 * (M.κ * M.X / M.lam) * y) / 2
    - (M.κ / M.lam + M.N - M.X - M.N * y) / 2

/-- (66), p. 38: the buyer population as a function of `y = F(∆b)`,
`N_b = (N − N y − X − κ/λ)/2 + ½ √([N − N y − X − κ/λ]² + 4 (κ/λ)(N − X)(1 − y))`. -/
noncomputable def NbOf (M : Params) (y : ℝ) : ℝ :=
  (M.N - M.N * y - M.X - M.κ / M.lam) / 2
    + Real.sqrt ((M.N - M.N * y - M.X - M.κ / M.lam) ^ 2
      + 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - y)) / 2

/-- The right-hand side of (20), p. 13, as a function of the cutoff `δ`, with `N_b` from (66):
`λκηX / ([κ + r + λ N_b (1 − η)](κ + λ N_b)) · ∫₀^δ F(x) dx`. -/
noncomputable def rhs20 (M : Params) (δ : ℝ) : ℝ :=
  M.lam * M.κ * M.η * M.X /
      ((M.κ + M.r + M.lam * NbOf M (M.F δ) * (1 - M.η)) * (M.κ + M.lam * NbOf M (M.F δ)))
    * ∫ x in (0:ℝ)..δ, M.F x

/-- The right-hand side of (21), p. 13, as a function of the cutoff `δ`, with `N_s` from (64):
`λκ(1 − η)(N − X) / ((κ + r + λη N_s)(κ + λ N_s)) · ∫_δ^∆̄ [1 − F(x)] dx`. -/
noncomputable def rhs21 (M : Params) (δ : ℝ) : ℝ :=
  M.lam * M.κ * (1 - M.η) * (M.N - M.X) /
      ((M.κ + M.r + M.lam * M.η * NsOf M (M.F δ)) * (M.κ + M.lam * NsOf M (M.F δ)))
    * ∫ x in δ..M.Δbar, (1 - M.F x)

/-- The crossing point of the cutoff curves: the least `δ ∈ [0, ∆̄]` with
`rhs21 δ ≤ rhs20 δ`. The set contains `∆̄` (where `rhs21 = 0 ≤ rhs20`) and is bounded below,
so the infimum is a genuine one. -/
noncomputable def δStar (M : Params) : ℝ :=
  sInf {δ : ℝ | δ ∈ Icc 0 M.Δbar ∧ rhs21 M δ ≤ rhs20 M δ}

/-- (84), p. 41: the threshold search cost `c*`, the common value of both sides of (20) and (21)
at the cutoff `δ*` where `∆b(c*) = ∆s(c*)`. -/
noncomputable def cStar (M : Params) : ℝ := rhs20 M (δStar M)

/-- The densities of Step I of the proof of Theorem 1 (p. 37) for cutoffs `∆b < ∆s`, with
`N_b = NbOf(F ∆b)` and `N_s = NsOf(F ∆s)`:
* on `[0, ∆b)` (55)–(57): `μb = μh = 0`, `μn = (κ(N − X) + λ N_b N)/(κ + λ N_b) f`,
  `μs = κX/(κ + λ N_b) f`;
* on `[∆b, ∆s)` (58) and (59)–(60) **corrected**: `μn = μh = 0`,
  `μb = (N f/2)[1 + (A + 2κ(N − X)/(λN))/R]`, `μs = N f − μb`, where
  `A = N − N F − X − κ/λ` and `R = √(A² + 4(κ/λ)(N − X)(1 − F))`
  (the printed (59)–(60) lack the term `2κ(N − X)/(λN)` and violate (18));
* on `[∆s, …)` (61)–(63): `μn = μs = 0`, `μb = κ(N − X)/(κ + λ N_s) f`,
  `μh = (κX + λ N_s N)/(κ + λ N_s) f`.
The values at `∆b` and `∆s` themselves are a convention (the steady state leaves them free). -/
noncomputable def candDensities (M : Params) (Δb Δs : ℝ) : Densities :=
  let Nb := NbOf M (M.F Δb)
  let Ns := NsOf M (M.F Δs)
  let A : ℝ → ℝ := fun Δ => M.N - M.N * M.F Δ - M.X - M.κ / M.lam
  let R : ℝ → ℝ := fun Δ =>
    Real.sqrt (A Δ ^ 2 + 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - M.F Δ))
  let midB : ℝ → ℝ := fun Δ =>
    M.N * M.f Δ / 2 * (1 + (A Δ + 2 * M.κ * (M.N - M.X) / (M.lam * M.N)) / R Δ)
  { μb := fun Δ => if Δ < Δb then 0 else if Δ < Δs then midB Δ
      else M.κ * (M.N - M.X) / (M.κ + M.lam * Ns) * M.f Δ
    μs := fun Δ => if Δ < Δb then M.κ * M.X / (M.κ + M.lam * Nb) * M.f Δ
      else if Δ < Δs then M.N * M.f Δ - midB Δ else 0
    μn := fun Δ => if Δ < Δb then
        (M.κ * (M.N - M.X) + M.lam * Nb * M.N) / (M.κ + M.lam * Nb) * M.f Δ else 0
    μh := fun Δ => if Δ < Δs then 0
      else (M.κ * M.X + M.lam * Ns * M.N) / (M.κ + M.lam * Ns) * M.f Δ }

/-- `F_s(∆) = ∫₀^∆ μs` (p. 38). -/
noncomputable def Densities.Fs (μ : Densities) (Δ : ℝ) : ℝ := ∫ x in (0:ℝ)..Δ, μ.μs x

/-- `F_b(∆) = ∫₀^∆ μb` (p. 38). -/
noncomputable def Densities.Fb (μ : Densities) (Δ : ℝ) : ℝ := ∫ x in (0:ℝ)..Δ, μ.μb x

/-- (77), middle branch, p. 40: the slope of `Vs` on `(∆b, ∆s)`,
`(1/(κ + r)) (κ + r + λη F_s(∆)) / (κ + r + λ(1 − η)[N_b − F_b(∆)] + λη F_s(∆))`. -/
noncomputable def slopeVsMid (M : Params) (μ : Densities) (Δ : ℝ) : ℝ :=
  1 / (M.κ + M.r) * ((M.κ + M.r + M.lam * M.η * μ.Fs Δ) /
    (M.κ + M.r + M.lam * (1 - M.η) * (μ.Nb M - μ.Fb Δ) + M.lam * M.η * μ.Fs Δ))

/-- (78), middle branch, p. 40: the slope of `Vb` on `(∆b, ∆s)`,
`(1/(κ + r)) λη F_s(∆) / (κ + r + λ(1 − η)[N_b − F_b(∆)] + λη F_s(∆))`. -/
noncomputable def slopeVbMid (M : Params) (μ : Densities) (Δ : ℝ) : ℝ :=
  1 / (M.κ + M.r) * (M.lam * M.η * μ.Fs Δ /
    (M.κ + M.r + M.lam * (1 - M.η) * (μ.Nb M - μ.Fb Δ) + M.lam * M.η * μ.Fs Δ))

/-- (77), first branch: the slope `1/(κ + r + λ(1 − η) N_b)` of `Vs` on `[0, ∆b)`. -/
noncomputable def slopeVsLow (M : Params) (μ : Densities) : ℝ :=
  1 / (M.κ + M.r + M.lam * (1 - M.η) * μ.Nb M)

/-- (78), second branch: the slope `(1/(κ + r)) λη N_s/(κ + r + λη N_s)` of `Vb` on `(∆s, ∆̄]`. -/
noncomputable def slopeVbHigh (M : Params) (μ : Densities) : ℝ :=
  1 / (M.κ + M.r) * (M.lam * M.η * μ.Ns M / (M.κ + M.r + M.lam * M.η * μ.Ns M))

/-- (79), p. 40: the constant `Vn`, computed from the candidate densities. -/
noncomputable def candVn (M : Params) (Δb Δs : ℝ) : ℝ :=
  let μ := candDensities M Δb Δs
  M.κ / M.r * (∫ z in Δb..Δs, slopeVbMid M μ z * (1 - M.F z))
    + M.κ / M.r * slopeVbHigh M μ * (∫ z in Δs..M.Δbar, (1 - M.F z))

/-- The constant `Vh(∆s)` printed under (82), p. 40. -/
noncomputable def candVhAtS (M : Params) (Δb Δs : ℝ) : ℝ :=
  let μ := candDensities M Δb Δs
  (1 + Δs) / M.r
    - M.κ / M.r * ((∫ z in (0:ℝ)..Δb, M.F z) / (M.κ + M.r + M.lam * μ.Nb M * (1 - M.η)))
    - M.κ / M.r * (∫ z in Δb..Δs, slopeVsMid M μ z * M.F z)
    + M.κ / M.r * ((∫ z in Δs..M.Δbar, (1 - M.F z)) / (M.κ + M.r))

/-- The constant `Vs(∆b) = Vh(∆s) − ∫_{∆b}^{∆s} dVs` printed under (82), p. 40. -/
noncomputable def candVsAtB (M : Params) (Δb Δs : ℝ) : ℝ :=
  candVhAtS M Δb Δs - ∫ z in Δb..Δs, slopeVsMid M (candDensities M Δb Δs) z

/-- `V(0, ·)` from (79)–(80), p. 40: `Vn` on `[0, ∆b]`, `Vn + ∫_{∆b}^∆ dVb` on `[∆b, ∆s]`, and
`Vn + ∫_{∆b}^{∆s} dVb + (78)·(∆ − ∆s)` on `[∆s, ∆̄]`. -/
noncomputable def candV0 (M : Params) (Δb Δs : ℝ) (Δ : ℝ) : ℝ :=
  let μ := candDensities M Δb Δs
  if Δ ≤ Δb then candVn M Δb Δs
  else if Δ ≤ Δs then candVn M Δb Δs + ∫ z in Δb..Δ, slopeVbMid M μ z
  else candVn M Δb Δs + (∫ z in Δb..Δs, slopeVbMid M μ z) + slopeVbHigh M μ * (Δ - Δs)

/-- `V(1, ·)` from (81)–(82), p. 40: `Vs(∆b) + (∆ − ∆b)/(κ + r + λ N_b (1 − η))` on `[0, ∆b]`,
`Vs(∆b) + ∫_{∆b}^∆ dVs` on `[∆b, ∆s]`, and `Vh(∆s) + (∆ − ∆s)/(κ + r)` on `[∆s, ∆̄]`. -/
noncomputable def candV1 (M : Params) (Δb Δs : ℝ) (Δ : ℝ) : ℝ :=
  let μ := candDensities M Δb Δs
  if Δ ≤ Δb then candVsAtB M Δb Δs + (Δ - Δb) / (M.κ + M.r + M.lam * μ.Nb M * (1 - M.η))
  else if Δ ≤ Δs then candVsAtB M Δb Δs + ∫ z in Δb..Δ, slopeVsMid M μ z
  else candVhAtS M Δb Δs + (Δ - Δs) / (M.κ + M.r)

/-- The four candidate value functions of Step II–III (pp. 39–42): `Vh` linear (81) everywhere,
`Vn` the constant (79), `Vs = V(1, ·)` on `[0, ∆s]` and `Vb = V(0, ·)` on `[∆b, ∆̄]`; off those
pieces `Vs` and `Vb` are completed by the right-hand sides of (9) and (11) evaluated at the
candidate `V(0, ·)`, `V(1, ·)` (with `S⁺` and the corrected readings of `IsBellman`). -/
noncomputable def candValues (M : Params) (Δb Δs : ℝ) : Values :=
  let μ := candDensities M Δb Δs
  let V0 := candV0 M Δb Δs
  let V1 := candV1 M Δb Δs
  { Vh := fun Δ => candVhAtS M Δb Δs + (Δ - Δs) / (M.κ + M.r)
    Vs := fun Δ => if Δ ≤ Δs then V1 Δ else
      (1 + Δ - M.c + M.lam * (1 - M.η) *
          (∫ x in (0:ℝ)..M.Δbar, max (V1 x + V0 Δ - (V0 x + V1 Δ)) 0 * μ.μb x)
        + M.κ * M.E V1) / (M.κ + M.r)
    Vn := fun _ => candVn M Δb Δs
    Vb := fun Δ => if Δb ≤ Δ then V0 Δ else
      (-M.c + M.lam * M.η *
          (∫ x in (0:ℝ)..M.Δbar, max (V1 Δ + V0 x - (V0 Δ + V1 x)) 0 * μ.μs x)
        + M.κ * M.E V0) / (M.κ + M.r) }

end OTCChain.Equilibrium


