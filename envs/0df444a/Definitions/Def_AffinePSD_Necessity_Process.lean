-- Prove2me | Definitions.Def_AffinePSD_Necessity_Process
-- name    : AffinePSD_Necessity_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:23.729367+00:00
-- url     : https://prove2.me/theorems/fcb73ac8-a0b7-4b60-8376-ae6ca66edf37
-- title:
--   Affine process on $S_d^+$, regularity, the Feller property, generator and Riccati equations (Definitions 2.1–2.2)
-- statement:
--   This file fixes the process-level notions of §2.
--
--   A **transition family** on $S_d^+$ is a family of sub-stochastic kernels $p_t(x, d\xi)$, $t \ge 0$, with $p_t(x, S_d^+) \le 1$, $p_0(x,\cdot) = \delta_x$, and the Chapman–Kolmogorov equations $p_{s+t}(x,\cdot) = \int p_s(x,dy)\, p_t(y,\cdot)$. The missing mass $1 - p_t(x,S_d^+)$ is the probability of having been sent to the cemetery $\Delta$. The semigroup is $P_t f(x) = \int f(\xi)\, p_t(x,d\xi)$, with the convention $f(\Delta) = 0$.
--
--   **Definition 2.1.** The process is **affine** if it is stochastically continuous, i.e. $p_s(x,\cdot) \to p_t(x,\cdot)$ weakly on $S_d^+$ as $s \to t$, and there are $\varphi : \mathbb R_+ \times S_d^+ \to \mathbb R_+$ and $\psi : \mathbb R_+ \times S_d^+ \to S_d^+$ with
--   $$\int_{S_d^+} e^{-\langle u,\xi\rangle}\, p_t(x,d\xi) = e^{-\varphi(t,u) - \langle \psi(t,u), x\rangle} \qquad (2.1)$$
--   for all $t \ge 0$ and $u, x \in S_d^+$.
--
--   **Definition 2.2.** The affine process is **regular** if the right derivatives $F(u) = \partial_t\varphi(t,u)|_{t=0+}$ and $R(u) = \partial_t\psi(t,u)|_{t=0+}$ exist for every $u \in S_d^+$ and are continuous at $u = 0$.
--
--   The process has the **Feller property** if $(P_t)$ restricts to a strongly continuous contraction semigroup on $C_0(S_d^+)$. A function $f$ is in the domain of the generator $A$ with $Af = g$ if $(P_tf - f)/t \to g$ uniformly on $S_d^+$ as $t \downarrow 0$.
--
--   Finally, $(\varphi, \psi)$ **solve the generalized Riccati equations** with right-hand sides $F, R$ if, for every $u \in S_d^+$,
--   $$\partial_t \varphi(t,u) = F(\psi(t,u)),\quad \varphi(0,u) = 0, \qquad \partial_t \psi(t,u) = R(\psi(t,u)),\quad \psi(0,u) = u,$$
--   for all $t \ge 0$ (one-sided at $t = 0$), with $\psi(t,u) \in S_d^+$.
--
--   **Formalization Note.** Transition families are indexed by $t \in \mathbb R$; only $t \ge 0$ is constrained, and limits are taken within $[0,\infty)$ or from the right. Weak convergence on $S_d^+$ means convergence of integrals of bounded continuous functions. The exponents are functions on $\mathbb R \times M_d$ constrained only at $t \ge 0$ and positive semidefinite arguments. The Feller property uses the platform definition `EthierKurtz.IsStronglyContinuousContractionSemigroup` for a family of bounded operators on $C_0(S_d^+)$ agreeing with $P_t$ for $t \ge 0$. The generator is the sup-norm limit; pointwise convergence would be a weaker, different notion.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §2, p. 7 (transition function), Definition 2.1, p. 7, Definition 2.2, p. 8; Theorem 2.4 and (2.14)–(2.15), p. 9

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Cone
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction ZeroAtInfty

namespace AffinePSD.Necessity

/-- `p` is a (sub-stochastic, time-homogeneous) Markov transition family on `S_d^+` (§2, p. 7):
`p_t(x, S_d^+) ≤ 1` (the deficit `1 − p_t(x, S_d^+)` is the mass sent to the cemetery `Δ`), `p_0 = id`,
and the Chapman–Kolmogorov equations `p_{s+t}(x, ·) = ∫ p_s(x, dy) p_t(y, ·)`.
Only `t ≥ 0` matters; values at negative times are unconstrained. -/
def IsTransition {d : ℕ} (p : ℝ → Kernel (Cone d) (Cone d)) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ x, p t x Set.univ ≤ 1) ∧
  p 0 = Kernel.id ∧
  (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → p (s + t) = p t ∘ₖ p s)

/-- Definition 2.1(i) (p. 7): stochastic continuity, `lim_{s→t} p_s(x, ·) = p_t(x, ·)` weakly on
`S_d^+`, for every `t ≥ 0` and `x ∈ S_d^+` (the limit taken over `s ≥ 0`). -/
def IsStochCont {d : ℕ} (p : ℝ → Kernel (Cone d) (Cone d)) : Prop :=
  ∀ (x : Cone d) (t : ℝ), 0 ≤ t → ∀ f : Cone d →ᵇ ℝ,
    Tendsto (fun s => ∫ ξ, f ξ ∂(p s x)) (𝓝[Set.Ici 0] t) (𝓝 (∫ ξ, f ξ ∂(p t x)))

/-- The semigroup `P_t f(x) = ∫_{S_d^+} f(ξ) p_t(x, dξ)` (§2, p. 7), with the convention `f(Δ) = 0`
built in (the kernel lives on the cone). -/
noncomputable def Pt {d : ℕ} (p : ℝ → Kernel (Cone d) (Cone d)) (t : ℝ) (f : Cone d → ℝ)
    (x : Cone d) : ℝ :=
  ∫ ξ, f ξ ∂(p t x)

/-- Definition 2.1 (p. 7) with the exponents named: `p` is a stochastically continuous transition family
and (2.1) `∫ e^{−⟨u,ξ⟩} p_t(x, dξ) = e^{−φ(t,u) − ⟨ψ(t,u), x⟩}` holds for all `t ≥ 0` and `u, x ∈ S_d^+`,
with `φ(t,u) ≥ 0` and `ψ(t,u) ∈ S_d^+`.

**Formalization Note.** `φ : ℝ → M_d → ℝ` and `ψ : ℝ → M_d → M_d` are only constrained at `t ≥ 0` and
PSD `u`, which is the paper's `φ : ℝ_+ × S_d^+ → ℝ_+`, `ψ : ℝ_+ × S_d^+ → S_d^+`. -/
def IsAffineWith {d : ℕ} (p : ℝ → Kernel (Cone d) (Cone d)) (φ : ℝ → Mat d → ℝ)
    (ψ : ℝ → Mat d → Mat d) : Prop :=
  IsTransition p ∧ IsStochCont p ∧
  (∀ t : ℝ, 0 ≤ t → ∀ u : Cone d, 0 ≤ φ t u ∧ PSD (ψ t u)) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ u x : Cone d,
    ∫ ξ, Real.exp (- tr (u : Mat d) (ξ : Mat d)) ∂(p t x) =
      Real.exp (- φ t u - tr (ψ t u) (x : Mat d)))

/-- Definition 2.1 (p. 7): the Markov process with transition family `p` is affine. -/
def IsAffine {d : ℕ} (p : ℝ → Kernel (Cone d) (Cone d)) : Prop :=
  ∃ (φ : ℝ → Mat d → ℝ) (ψ : ℝ → Mat d → Mat d), IsAffineWith p φ ψ

/-- Definition 2.2 (p. 8): the affine process is regular, i.e. the right derivatives
`F(u) = ∂_t φ(t,u)|_{t=0+}` and `R(u) = ∂_t ψ(t,u)|_{t=0+}` (2.2) exist for every `u ∈ S_d^+` and are
continuous at `u = 0` (within `S_d^+`). -/
def IsRegular {d : ℕ} (φ : ℝ → Mat d → ℝ) (ψ : ℝ → Mat d → Mat d) : Prop :=
  ∃ (Fr : Mat d → ℝ) (Rr : Mat d → Mat d),
    (∀ u : Mat d, PSD u →
      HasDerivWithinAt (fun t => φ t u) (Fr u) (Set.Ici 0) 0 ∧
      HasDerivWithinAt (fun t => ψ t u) (Rr u) (Set.Ici 0) 0) ∧
    ContinuousWithinAt Fr {u | PSD u} 0 ∧ ContinuousWithinAt Rr {u | PSD u} 0

/-- The Feller property (Theorem 2.4, p. 9; Proposition 3.4, p. 17): `(P_t)_{t ≥ 0}` restricts to a
strongly continuous contraction semigroup on `C_0(S_d^+)`.

**Formalization Note.** Uses the platform definition
`EthierKurtz.IsStronglyContinuousContractionSemigroup` (`T 0 = id`, semigroup law and `‖T t‖ ≤ 1` for
`t ≥ 0`, strong right-continuity at `0`) for a family `T` of bounded operators on `C_0(S_d^+)` that agrees
with `P_t` for `t ≥ 0`. -/
def IsFeller {d : ℕ} (p : ℝ → Kernel (Cone d) (Cone d)) : Prop :=
  ∃ T : ℝ → C₀(Cone d, ℝ) →L[ℝ] C₀(Cone d, ℝ),
    (∀ t : ℝ, 0 ≤ t → ∀ (f : C₀(Cone d, ℝ)) (x : Cone d), T t f x = Pt p t f x) ∧
    EthierKurtz.IsStronglyContinuousContractionSemigroup T

/-- `f ∈ D(A)` and `A f = g` for the infinitesimal generator `A` of `(P_t)` on `C_0(S_d^+)`:
`(P_t f − f)/t → g` uniformly on `S_d^+` as `t ↓ 0`.

**Formalization Note.** The generator of a Feller semigroup is the limit in the sup norm of `C_0`; it is
used here only for `f, g ∈ C_0(S_d^+)`. Pointwise convergence would be a different, weaker notion. -/
def HasGenerator {d : ℕ} (p : ℝ → Kernel (Cone d) (Cone d)) (f g : Cone d → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x : Cone d, |(Pt p t f x - f x) / t - g x| ≤ ε

/-- `(φ, ψ)` solve the generalized Riccati equations (2.14)–(2.15) (p. 9) with right-hand sides `Fr`,
`Rr`: for every `u ∈ S_d^+`, `φ(0,u) = 0`, `ψ(0,u) = u`, and for all `t ≥ 0`, `ψ(t,u) ∈ S_d^+`,
`∂_t φ(t,u) = Fr(ψ(t,u))` and `∂_t ψ(t,u) = Rr(ψ(t,u))` (one-sided at `t = 0`). -/
def SolvesRiccati {d : ℕ} (Fr : Mat d → ℝ) (Rr : Mat d → Mat d) (φ : ℝ → Mat d → ℝ)
    (ψ : ℝ → Mat d → Mat d) : Prop :=
  ∀ u : Mat d, PSD u →
    φ 0 u = 0 ∧ ψ 0 u = u ∧
    ∀ t : ℝ, 0 ≤ t →
      PSD (ψ t u) ∧
      HasDerivWithinAt (fun s => φ s u) (Fr (ψ t u)) (Set.Ici 0) t ∧
      HasDerivWithinAt (fun s => ψ s u) (Rr (ψ t u)) (Set.Ici 0) t

end AffinePSD.Necessity


