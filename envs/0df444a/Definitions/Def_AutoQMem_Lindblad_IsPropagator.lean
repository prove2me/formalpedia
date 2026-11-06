-- Prove2me | Definitions.Def_AutoQMem_Lindblad_IsPropagator
-- name    : AutoQMem_Lindblad_IsPropagator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:08.679337+00:00
-- url     : https://prove2.me/theorems/ef841f2e-0b46-48ab-85ce-94cb546989ae
-- title:
--   Propagators: $\mathcal W_*(t,0)$ of $\mathcal L(t)$ and backward transition operators $M(t,0)$
-- statement:
--   1. The **Schrödinger propagator** $\mathcal W_*(t,0)$ solves $\frac{d}{dt}\mathcal W_*(t,0)=\mathcal L(t)\mathcal W_*(t,0)$, $\mathcal W_*(0,0)=\mathrm{id}$, so that $\rho(t)=\mathcal W_*(t,0)\rho(0)$. A family $\mathcal W$ is called a propagator of $\mathcal L$ when, for every $t\ge0$ and every matrix $\rho$,
--   $$\mathcal W(t)\rho=\rho+\int_0^t\mathcal L(s)\bigl(\mathcal W(s)\rho\bigr)\,ds .$$
--   2. For a time-dependent Markov generator $G(t)$ on a finite set, the **backward transition operator** $M(t,0)$, $(M(t,0)h)(e)=\mathbb E[h(\chi_t)\mid\chi_0=e]$, solves Kolmogorov's forward equation $\frac{d}{dt}M(t,0)=M(t,0)G(t)$, $M(0,0)=I$; in integrated form
--   $$M(t)=I+\int_0^tM(s)G(s)\,ds,\qquad t\ge0 .$$
--
--   **Formalization Note** Both equations are taken entrywise in integrated form, with the integrand required to be integrable on $[0,t]$ (this only excludes junk values of the integral). Under the time regularity of Reading R1 each equation has exactly one solution, the paper's propagator. The Heisenberg propagator $\mathcal W^*(t,0)$ is the trace-pairing adjoint of $\mathcal W(t)$.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), eq. (40), p. 21 (PDF p. 23); Definition 2.30, eqs. (50)–(51), p. 23 (PDF p. 25)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_SyndromeLindbladian_gen
open Matrix

namespace AutoQMem.Lindblad

/-- **Schrödinger-picture propagator `W_*(t, 0)` of `L(t)`.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), §2.2.1, eq. (40), p. 21
(PDF 23): "d/dt W_*(t, t′) = L(t) W_*(t, t′), W_*(t′, t′) = id, so that ρ(t) = W_*(t, t′)ρ(t′)."

**Formalization Note (Reading R1).** `W t` is `W_*(t, 0)`. Eq. (40) with `t′ = 0` is taken in
integrated form, entrywise: for every `t ≥ 0` and every matrix `ρ`, the integrand
`s ↦ L(s)(W s ρ)` is interval integrable on `[0, t]` and
`W t ρ = ρ + ∫₀ᵗ L(s)(W s ρ) ds`. Under R1 (measurable, locally bounded `L(t)`) this linear
Volterra equation has exactly one solution, the paper's propagator. The integrability clause only
excludes junk values of the Bochner integral. The Heisenberg propagator `W^*(t, 0)` (eq. (43)) is
`hsAdj (W t)`. -/
def IsPropagator {n mX mZ : ℕ} {C : CSSCode n mX mZ} {ι : Type} [Fintype ι]
    (L : SyndromeLindbladian C ι) (W : ℝ → Op n → Op n) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ (ρ : Op n) (x y : Fin n → ZMod 2),
    IntervalIntegrable (fun s => L.gen s (W s ρ) x y) MeasureTheory.volume 0 t ∧
      W t ρ x y = ρ x y + ∫ s in (0 : ℝ)..t, L.gen s (W s ρ) x y

/-- **Backward transition operator `M(t, 0)` of a time-dependent Markov generator.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03),
Definition 2.30, eq. (51), p. 23 (PDF 25): "It satisfies, for t ≥ t′, d/dt M^{(X)}(t, t′) =
M^{(X)}(t, t′) G_X(t), M^{(X)}(t′, t′) = I, which is Kolmogorov's forward equation for the transition
matrix of a Markov chain with time-dependent generator".

**Formalization Note (Reading R1).** `M t` is `M(t, 0)`, a real matrix with
`(M(t,0) h)(e) = Σ_y M t e y h(y) = E[h(χ_t) | χ_0 = e]` (eq. (50)), so `M t e y` is the
transition probability from `e` to `y`. Eq. (51) with `t′ = 0` is taken in integrated form,
entrywise, with the integrand interval integrable on `[0, t]`: `M t = I + ∫₀ᵗ M s G s ds`.
This is the transition matrix of the CTMC built from the rates in the standard way ([YZ13, §2.3–2.4,
Thm. 2.5(c)]), unique under R1. -/
def IsBackwardPropagator {Ω : Type} [Fintype Ω] [DecidableEq Ω] (G M : ℝ → Matrix Ω Ω ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x y : Ω,
    IntervalIntegrable (fun s => (M s * G s) x y) MeasureTheory.volume 0 t ∧
      M t x y = (if x = y then 1 else 0) + ∫ s in (0 : ℝ)..t, (M s * G s) x y

end AutoQMem.Lindblad


