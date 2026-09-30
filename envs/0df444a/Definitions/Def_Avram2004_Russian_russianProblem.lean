-- Prove2me | Definitions.Def_Avram2004_Russian_russianProblem
-- name    : Avram2004_Russian_russianProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:04:56.309625+00:00
-- url     : https://prove2.me/theorems/a7b2526a-c677-482f-823d-d06def251500
-- title:
--   The Russian optimal stopping problem (28): admissible times, payoff e^{−ατ+Y_τ}, value w^R, level κ* of (30), and u(z) = e^z Z^(q)(κ* − z)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbf F,\mathbb P)$ be a filtered probability space carrying a spectrally negative Lévy process $X$, let $\mathbb P^1$ be the Esscher measure, and let $Y$ be the reflected process under $\mathbb P^1_{-z}$ (so $Y_0=z\ge0$). Fix $\alpha>0$.
--
--   1. **Admissible exercise rules.** The admissible times are the $\mathbf F$-stopping times $\tau$ with values in $[0,\infty]$ that are $\mathbb P^1$-almost surely finite.
--   2. **Payoff.** For such $\tau$ the payoff is $e^{-\alpha\tau+Y_\tau}$ (set to $0$ on the null event $\{\tau=\infty\}$).
--   3. **Value function (28).**
--   $$w^R(z)=\sup_\tau\ \mathbb E^1_{-z}\big[e^{-\alpha\tau+Y_\tau}\big],$$
--   the supremum over all admissible $\tau$.
--   4. **Optimal level (30).** For $q\ge0$, with the scale functions $W^{(q)}$, $Z^{(q)}$ of $(X,\mathbb P)$,
--   $$\kappa^*=\inf\{x\in\mathbb R:\ Z^{(q)}(x)\le qW^{(q)}(x)\}.$$
--   5. **Candidate value (Theorem 2).** $u(z)=e^{z}Z^{(q)}(\kappa^*-z)$.
--
--   In the paper $q=\alpha+r$ with $r=\psi(1)$, and Theorem 2 asserts $w^R=u$ with optimal time $\tau_{\kappa^*}$. The value $w^R(z)$ of this problem gives the price of the perpetual Russian option: $V_r(M_0,S_0)=S_0\,w^R(\log(M_0/S_0))$.
--
--   **Formalization Note** The expectation is the integral of a nonnegative function taking values in $[0,\infty]$, and the supremum is taken in $[0,\infty]$, so neither an integrability side condition nor a junk value of a real supremum enters. The admissible class is every $\mathbb P^1$-a.s. finite stopping time of the given filtration; it is not restricted to passage times. For $x\le0$ one has $Z^{(q)}(x)=1>0=qW^{(q)}(x)$, so the set in (30) lies in $(0,\infty)$; that it is nonempty (so that the real infimum is the paper's) is the content of Lemma 2 and is not assumed. $\kappa^*$ is defined by the infimum (30), not by a choice among roots of $Z^{(q)}=qW^{(q)}$.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 227, §5, Eq. (27) and the sentence after it; p. 228, §6, Eq. (28); p. 229, Eq. (30) and Theorem 2 (definition of u)

import Mathlib
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Shared_reflected

open MeasureTheory
open scoped NNReal ENNReal

namespace Avram2004.Russian

/-- The admissible exercise rules of (27)–(28): the `𝓕`-stopping times that are almost surely finite
under `Q` (= `ℙ^1`). -/
def Admissible {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m) (Q : Measure Ω) :
    Set (Ω → WithTop ℝ≥0) :=
  {τ | IsStoppingTime 𝓕 τ ∧ ∀ᵐ ω ∂Q, τ ω ≠ ⊤}

/-- The payoff `e^{-ατ + Y_τ}` of (28) under `ℙ^1_{-z}` (so `Y = refl 0 (-z) X`, `Y_0 = z`), as an
extended nonnegative real, with the value `0` on `{τ = ∞}`. -/
noncomputable def rpayoff {Ω : Type*} (α z : ℝ) (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  match τ ω with
  | none => 0
  | some t => ENNReal.ofReal (Real.exp (-α * (t : ℝ) + Shared.refl 0 (-z) X t ω))

/-- The value function of the Russian optimal stopping problem (28):
`w^R(z) = sup_τ 𝔼^1_{-z}[e^{-ατ + Y_τ}]`, the supremum over all `Q`-almost surely finite `𝓕`-stopping
times, computed in `[0, ∞]`. -/
noncomputable def valueR {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (Q : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (α z : ℝ) : ℝ≥0∞ :=
  ⨆ τ ∈ Admissible 𝓕 Q, ∫⁻ ω, rpayoff α z X τ ω ∂Q

/-- The optimal level (30): `κ* = inf {x : Z^{(q)}(x) ≤ q W^{(q)}(x)}`, with the scale functions of
`(X, P)`. -/
noncomputable def kappaStar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (q : ℝ) : ℝ :=
  sInf {x : ℝ | Shared.Z P X 0 q x ≤ q * Shared.W P X 0 q x}

/-- Theorem 2: `u(z) = e^z Z^{(q)}(κ* - z)`. -/
noncomputable def uR {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (q z : ℝ) : ℝ :=
  Real.exp z * Shared.Z P X 0 q (kappaStar P X q - z)

end Avram2004.Russian


