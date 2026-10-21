-- Prove2me | Definitions.Def_HedgeContract_OPE_Model
-- name    : HedgeContract_OPE_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:16.78398+00:00
-- url     : https://prove2.me/theorems/d2fd7357-3b20-45d6-9dc6-a39176bece92
-- title:
--   §2 and §6.6 — reduced principal control problem (21), (24), (56)–(58)
-- statement:
--   The principal's reduced problem has parameters $\mu,\psi,\rho,\kappa,b,r,m,\sigma,\gamma,\delta,\Phi$ and compact intervals $\mathcal A=[\underline A,\overline A]$, $\mathcal Z=[\underline Z,\overline Z]$, $\Gamma=[\underline\Gamma,\overline\Gamma]$. Effort has cost $h(A)=\kappa A^2/2+bA$, and $A^*(Z)$ minimizes $h(A)-ZA$ on $\mathcal A$ as in (56). Define
--
--   $$g(Z,\zeta)=\frac{r\gamma}{2}\psi^2(1-\rho^2)Z^2+h(A^*(Z))+(m-r)\zeta,\qquad \Sigma(Z,\zeta)=(1-\rho^2)\psi^2Z^2+\sigma^2\zeta^2.$$
--
--   An admissible contract chooses progressive $Z\in\mathcal Z$, $\zeta\in\Gamma$ and an adapted, right-continuous nondecreasing cumulative payment $I$; its state satisfies (21) with independent Brownian shocks $B$ and $B^\perp$. Liquidation occurs at $\tau=\inf\{t\ge0:Y_t\le0\}$, including $\tau=\infty$ if the state never reaches zero. The contract obeys transversality (57). Its expected payoff is
--
--   $$\mathbb E\left[\delta\int_{[0,\tau)}e^{-\delta t}(\mu+A^*(Z_t))\,dt-\delta\int_{[0,\tau]}e^{-\delta t}\,dI_t+\delta e^{-\delta\tau}\Phi\,\mathbf1_{\{\tau<\infty\}}\right].$$
--
--   The feasible payoff set consists of these values for contracts from initial promise $y\ge0$; its least upper bound is the principal's value $W(y)$. The definition also records the six clauses of Assumption 6.2, the HJB Hamiltonian, the bounds $\underline W,\overline W$, and the payment boundary $\bar y=\sup\{y\ge0:W(y)<\widetilde W(y)\}$.
--
--   This model is reusable for the paper's value bounds, HJB regularity, and optimal-contract theorem.
--
--   **Formalization Note.** This is the reduced problem (24); the agent's Lemma 2.2 and output/market processes are outside scope. Coordinate zero of the published two-dimensional Brownian motion is $B$, coordinate one is $B^\perp$. The filtration is its natural filtration; Itô integrals are required on every finite horizon. The Stieltjes payment measure charges a lump sum at time zero. The added positivity and $|\rho|<1$ assumptions make the square root and diffusion nondegenerate. Payoff and payment integrability exclude Lean's zero value for nonintegrable real integrals.
-- source:
--   Huang, Ju & Xing, Optimal Contracting with Unobservable Managerial Hedging, working paper (Nov. 14, 2017), pp. 5–13, 32–34 (PDF 7–15, 34–36), §2.1–2.5, §6.6, (2), (21), (24), (56)–(58), Assumption 6.2

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
set_option autoImplicit false

namespace HedgeContract.OPE
open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal NNReal
noncomputable section

structure Params where
  mu : ℝ
  ψ : ℝ
  ρ : ℝ
  κ : ℝ
  b : ℝ
  Alo : ℝ
  Ahi : ℝ
  r : ℝ
  m : ℝ
  σ : ℝ
  γ : ℝ
  δ : ℝ
  Φ : ℝ
  Zlo : ℝ
  Zhi : ℝ
  Γlo : ℝ
  Γhi : ℝ

def Params.Standing (P : Params) : Prop :=
  0 < P.σ ∧ 0 < P.ψ ∧ -1 < P.ρ ∧ P.ρ < 1 ∧ 0 < P.γ ∧ 0 < P.δ ∧
  P.Alo ≤ P.Ahi ∧ P.Zlo ≤ P.Zhi ∧ P.Γlo ≤ P.Γhi ∧ 0 < P.κ ∧ 0 < P.b

def h (P : Params) (A : ℝ) : ℝ := P.κ / 2 * A ^ 2 + P.b * A

def Astar (P : Params) (Z : ℝ) : ℝ :=
  if Z ≤ P.κ * P.Alo + P.b then P.Alo
  else if P.κ * P.Ahi + P.b ≤ Z then P.Ahi
  else (Z - P.b) / P.κ

def g (P : Params) (Z ζ : ℝ) : ℝ :=
  P.r * P.γ / 2 * P.ψ ^ 2 * (1 - P.ρ ^ 2) * Z ^ 2 +
    h P (Astar P Z) + (P.m - P.r) * ζ

def Sig (P : Params) (Z ζ : ℝ) : ℝ :=
  (1 - P.ρ ^ 2) * P.ψ ^ 2 * Z ^ 2 + P.σ ^ 2 * ζ ^ 2

def box (P : Params) : Set (ℝ × ℝ) :=
  Set.Icc P.Zlo P.Zhi ×ˢ Set.Icc P.Γlo P.Γhi

def netSup (P : Params) : ℝ :=
  sSup ((fun z : ℝ × ℝ => Astar P z.1 - g P z.1 z.2) '' box P)

def Wbar (P : Params) (y : ℝ) : ℝ := P.mu - P.δ * y + netSup P
def Wlow (P : Params) (y : ℝ) : ℝ := P.δ * P.Φ - P.δ * y
def Wtil (P : Params) (y : ℝ) : ℝ := P.mu - P.r * y + netSup P

def Ham (P : Params) (y p q Z ζ : ℝ) : ℝ :=
  P.δ * (P.mu + Astar P Z) + (P.r * y + g P Z ζ) * p + Sig P Z ζ / 2 * q

def hamSup (P : Params) (y p q : ℝ) : ℝ :=
  sSup ((fun z : ℝ × ℝ => Ham P y p q z.1 z.2) '' box P)

def ctrlObj (P : Params) (p q Z ζ : ℝ) : ℝ :=
  P.δ * Astar P Z + g P Z ζ * p + Sig P Z ζ / 2 * q

def IsMaximizer (P : Params) (p q Z ζ : ℝ) : Prop :=
  (Z, ζ) ∈ box P ∧
    ∀ z ∈ box P, ctrlObj P p q z.1 z.2 ≤ ctrlObj P p q Z ζ

structure Assumption62 (P : Params) : Prop where
  part1 : P.δ < P.r
  part2 : 0 ≤ netSup P
  part3 : ∀ z ∈ box P,
    (∀ w ∈ box P, Astar P w.1 - g P w.1 w.2 ≤ Astar P z.1 - g P z.1 z.2) →
      0 ≤ g P z.1 z.2
  part4 : P.Alo = 0 ∧ P.Zlo = P.b ∧ P.Zhi = P.κ * P.Ahi + P.b
  part5 : 0 < P.κ ∧ 0 < P.b
  part6 : P.δ * P.Φ ≤ P.mu

structure Contract (Ω : Type*) where
  Z : ℝ≥0 → Ω → ℝ
  ζ : ℝ≥0 → Ω → ℝ
  I : ℝ≥0 → Ω → ℝ
  Y : ℝ≥0 → Ω → ℝ
  J₀ : ℝ≥0 → Ω → ℝ
  J₁ : ℝ≥0 → Ω → ℝ

def Contract.τ {Ω : Type*} (C : Contract Ω) (ω : Ω) : ℝ≥0∞ :=
  sInf ((fun t : ℝ≥0 => (t : ℝ≥0∞)) '' {t | C.Y t ω ≤ 0})

def Contract.paymentPath {Ω : Type*} (C : Contract Ω) (ω : Ω) (t : ℝ) : ℝ :=
  if t < 0 then 0 else C.I t.toNNReal ω

def Contract.paymentMeasure {Ω : Type*} (C : Contract Ω) (ω : Ω) : Measure ℝ :=
  if hm : Monotone (C.paymentPath ω) then hm.stieltjesFunction.measure else 0

def Contract.payment {Ω : Type*} (P : Params) (C : Contract Ω) (ω : Ω) : ℝ :=
  ∫ t in {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t ≤ C.τ ω},
    Real.exp (-P.δ * t) ∂(C.paymentMeasure ω)

def Contract.pathPayoff {Ω : Type*} (P : Params) (C : Contract Ω) (ω : Ω) : ℝ :=
  P.δ * (∫ t in {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < C.τ ω},
      Real.exp (-P.δ * t) * (P.mu + Astar P (C.Z t.toNNReal ω)))
    - P.δ * C.payment P ω +
    (if C.τ ω < ⊤ then P.δ * Real.exp (-P.δ * (C.τ ω).toReal) * P.Φ else 0)

def Contract.payoff {Ω : Type*} [MeasurableSpace Ω] (P : Params) (P₀ : Measure Ω)
    (C : Contract Ω) : ℝ :=
  ∫ ω, C.pathPayoff P ω ∂P₀

def Contract.Admissible {Ω : Type*} [MeasurableSpace Ω] (C : Contract Ω)
    (P : Params) (P₀ : Measure Ω) (B : ℝ≥0 → Ω → Fin 2 → ℝ)
    (hB : Peng1990.SMP.IsStdBrownian P₀ B) (y : ℝ) : Prop :=
  let 𝓕 := Peng1990.SMP.brownianFiltration hB
  IsStronglyProgressive 𝓕 C.Z ∧ IsStronglyProgressive 𝓕 C.ζ ∧
  (∀ t ω, (C.Z t ω, C.ζ t ω) ∈ box P) ∧
  StronglyAdapted 𝓕 C.I ∧ StronglyAdapted 𝓕 C.Y ∧
  (∀ ω, Monotone (C.paymentPath ω)) ∧
  (∀ ω t, ContinuousWithinAt (fun s : ℝ≥0 => C.I s ω) (Set.Ici t) t) ∧
  (∀ ω, 0 ≤ C.I 0 ω) ∧
  (∀ T, Peng1990.SMP.IsItoIntegral 𝓕 P₀ T (fun t ω => B t ω 0)
    (fun t ω => P.σ * C.ζ t ω) C.J₀) ∧
  (∀ T, Peng1990.SMP.IsItoIntegral 𝓕 P₀ T (fun t ω => B t ω 1)
    (fun t ω => Real.sqrt (1 - P.ρ ^ 2) * P.ψ * C.Z t ω) C.J₁) ∧
  (∀ᵐ ω ∂P₀, Continuous (fun t => C.J₀ t ω) ∧ Continuous (fun t => C.J₁ t ω) ∧
    ∀ t : ℝ≥0,
      IntegrableOn (fun s : ℝ => P.r * C.Y s.toNNReal ω +
        g P (C.Z s.toNNReal ω) (C.ζ s.toNNReal ω)) (Set.Icc 0 (t : ℝ)) ∧
      C.Y t ω = y + (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        P.r * C.Y s.toNNReal ω + g P (C.Z s.toNNReal ω) (C.ζ s.toNNReal ω)) -
        C.I t ω + C.J₀ t ω + C.J₁ t ω) ∧
  (∀ T : ℝ≥0, Integrable (fun ω => Real.exp (-P.δ * (T : ℝ)) * C.Y T ω *
      (if (T : ℝ≥0∞) ≤ C.τ ω then (1 : ℝ) else 0)) P₀) ∧
  Tendsto (fun T : ℝ≥0 => ∫ ω, Real.exp (-P.δ * (T : ℝ)) * C.Y T ω *
      (if (T : ℝ≥0∞) ≤ C.τ ω then (1 : ℝ) else 0) ∂P₀) atTop (𝓝 0) ∧
  (∀ᵐ ω ∂P₀, IntegrableOn (fun t : ℝ => Real.exp (-P.δ * t))
      {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t ≤ C.τ ω} (C.paymentMeasure ω)) ∧
  Integrable (fun ω => C.payment P ω) P₀ ∧
  Integrable (fun ω => C.pathPayoff P ω) P₀

def valueSet (P : Params) {Ω : Type*} [MeasurableSpace Ω] (P₀ : Measure Ω)
    (B : ℝ≥0 → Ω → Fin 2 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P₀ B)
    (y : ℝ) : Set ℝ :=
  {v | ∃ C : Contract Ω, C.Admissible P P₀ B hB y ∧ v = C.payoff P P₀}

def IsValue (P : Params) {Ω : Type*} [MeasurableSpace Ω] (P₀ : Measure Ω)
    (B : ℝ≥0 → Ω → Fin 2 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P₀ B)
    (W : ℝ → ℝ) : Prop :=
  ∀ y : ℝ, 0 ≤ y → IsLUB (valueSet P P₀ B hB y) (W y)

def ybar (P : Params) (W : ℝ → ℝ) : ℝ :=
  sSup {y : ℝ | 0 ≤ y ∧ W y < Wtil P y}

end
end HedgeContract.OPE


