-- Prove2me | Definitions.Def_HollandsSanders_CFTBound_Entanglement
-- name    : HollandsSanders_CFTBound_Entanglement
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:44:30.98342+00:00
-- url     : https://prove2.me/theorems/0157502a-b0b7-4471-a0be-5b41088f8737
-- title:
--   §3.1, §3.4–3.6, pp. 24–47 — normal functionals, separable states, relative entropy, E_R, E_N, the 1-nuclear norm and E_M for two von Neumann algebras
-- statement:
--   Let $\mathcal H$ be a complex Hilbert space and let $\mathfrak A_A,\mathfrak A_B\subseteq B(\mathcal H)$ be von Neumann algebras. Their **join** $\mathfrak A_A\vee\mathfrak A_B=(\mathfrak A_A\cup\mathfrak A_B)''$ is the von Neumann algebra they generate. This file fixes the entanglement measures of Hollands and Sanders, §3, for such a pair.
--
--   1. A **positive normal functional** on a von Neumann algebra $\mathfrak M$ is a map of the form $\varphi(a)=\sum_n\langle\xi_n,a\,\xi_n\rangle$ ($a\in\mathfrak M$) with $\sum_n\|\xi_n\|^2<\infty$; a **normal state** is one with $\varphi(1)=1$. A (not necessarily positive) **normal functional** is $\varphi(a)=\sum_n\langle\xi_n,a\,\eta_n\rangle$ with $\sum_n\|\xi_n\|\,\|\eta_n\|<\infty$, and its norm is $\|\varphi\|=\sup\{|\varphi(a)|:a\in\mathfrak M,\ \|a\|\le1\}$. A positive functional $\sigma$ **dominates** $\omega$, $\sigma\geqslant\omega$, if $\sigma-\omega$ is positive.
--   2. (Definition 7, read on the join as in Theorem 2 c.) A normal state $\sigma$ on $\mathfrak A_A\vee\mathfrak A_B$ is **separable** if
--   $$\sigma(ab)=\sum_j\varphi_j(a)\,\psi_j(b)\qquad(a\in\mathfrak A_A,\ b\in\mathfrak A_B)$$
--   for positive normal functionals $\varphi_j$ on $\mathfrak A_A$ and $\psi_j$ on $\mathfrak A_B$ with $\sum_j\varphi_j(1)\psi_j(1)<\infty$. A **separable positive functional** is $r\sigma$ with $\sigma$ a separable state and $r\ge0$.
--   3. (Definition 10.) **Araki's relative entropy** $H(\omega,\sigma)$ of positive normal functionals on a von Neumann algebra $\mathfrak M$, in **Kosaki's variational form**:
--   $$H(\omega,\sigma)=\sup_{n\ge1}\ \sup_{x(\cdot)}\Big\{\omega(1)\ln n-\int_{1/n}^{\infty}\Big(\omega\big(y(t)^*y(t)\big)+t^{-1}\sigma\big(x(t)x(t)^*\big)\Big)\frac{dt}{t}\Big\},$$
--   where $x(\cdot)$ runs over step functions $[1/n,\infty)\to\mathfrak M$ with finitely many steps, equal to $1$ for large $t$, and $y(t)=1-x(t)$. The integral is evaluated in closed form on each step. The value lies in $(-\infty,+\infty]$.
--   4. (Definition 11.) The **relative entanglement entropy** $E_R(\omega)=\inf\{H(\omega,\sigma):\sigma\text{ a separable state}\}$, which is $+\infty$ when no separable state exists.
--   5. (Definition 12.) The **logarithmic dominance** $E_N(\omega)=\inf\{\ln\|\sigma\|:\sigma\geqslant\omega,\ \sigma\text{ separable}\}$, with $\|\sigma\|=\sigma(1)$, and $+\infty$ when no dominating separable functional exists.
--   6. (Definition 5.) The **1-nuclear norm** $\|T\|_1=\inf\sum_j\|f_j\|\,\|y_j\|$ over all representations $T(x)=\sum_j f_j(x)\,y_j$ by continuous linear functionals $f_j$ and vectors $y_j$; it is $+\infty$ when there is none.
--   7. (Eq. (105), (106), Definition 13.) For a unit vector $\Omega$ that is cyclic and separating for $\mathfrak A_B'$ and $\mathfrak A_A'$, with modular operators $\Delta_{\mathfrak A_B'}$ and $\Delta_{\mathfrak A_A'}$, the maps $\Psi^A(a)=\Delta_{\mathfrak A_B'}^{1/4}a\Omega$ on $\mathfrak A_A$ and $\Psi^B(b)=\Delta_{\mathfrak A_A'}^{1/4}b\Omega$ on $\mathfrak A_B$ define the **modular entanglement measure**
--   $$E_M(\omega)=\ln\min\big(\|\Psi^A\|_1,\|\Psi^B\|_1\big),$$
--   which is $+\infty$ when neither map is nuclear. The file also fixes the **statistical independence** assumption of §3 in the form used below: every product $\varphi(a)\psi(b)$ of positive normal functionals extends to a positive normal functional on the join.
--
--   These are the objects of all entanglement estimates of the paper: $E_R\le E_N\le E_M$ (Theorems 3 and 4) is how the paper bounds $E_R$ of the vacuum.
--
--   **Formalization Note.** Functionals are functions $B(\mathcal H)\to\mathbb C$ of which only the values on the relevant algebra matter. Modular operators come from the published definition `BoundedRecovery` (`StandardModularData`, whose field `D` is the spectral calculus of $\log\Delta$); $\Delta^{1/4}x$ is the limit of $\exp(\min(n,\log\Delta)/4)\,x$, and its graph is `quarterGraph`. The 1-nuclear norm of a map on $\mathfrak A_A$ is taken over functionals on all of $B(\mathcal H)$; by Hahn–Banach this is the same infimum. $H$, $E_R$, $E_N$, $E_M$ are `EReal`-valued and the norms `ℝ≥0∞`-valued, so empty infima are $+\infty$. Kosaki's form is used because it defines $H(\omega,\sigma)$ for every pair of positive normal functionals, faithful or not.
-- source:
--   Hollands & Sanders, Entanglement measures and their properties in quantum field theory, arXiv:1702.04924v3, pp. 24–47: Definition 5 (p. 24), Definition 7 (p. 35), Theorem 2 c) (p. 25), Definition 10 and its extension (pp. 40–41), Definition 11 (93) (p. 42), Definition 12 (104) (p. 45), (105)–(106) and Definition 13 (pp. 46–47); Kosaki's variational formula: H. Kosaki, Comm. Math. Phys. 87 (1986); Ohya–Petz, Quantum Entropy and Its Use, Thm 5.11

import Mathlib
import Definitions.Def_BoundedRecovery

namespace HollandsSanders.CFTBound

/-!
Hollands & Sanders, *Entanglement measures and their properties in quantum field theory*,
arXiv:1702.04924v3, §3.1, §3.4–3.6 (pp. 34–47), Definitions 5, 7, 10–13.

The general layer: a Hilbert space `H`, two von Neumann algebras `AA`, `AB` on `H`, normal
functionals on them and on their join, Araki's relative entropy (in Kosaki's variational form),
the relative entanglement entropy `E_R`, the logarithmic dominance `E_N`, the 1-nuclear norm, the
maps `Ψ^A`, `Ψ^B` and the modular entanglement measure `E_M`.
-/

open OAI.BoundedRecovery
open Filter Topology
open scoped InnerProductSpace ENNReal NNReal

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The commutant `s'` of (the star closure of) a set `s` of bounded operators, as a von Neumann
algebra. -/
def commutantOf (s : Set (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ s
  centralizer_centralizer' := Set.centralizer_centralizer_centralizer (s ∪ star s)

/-- The join `𝔄_A ∨ 𝔄_B`: the von Neumann algebra generated by `𝔄_A ∪ 𝔄_B`, i.e. its
bicommutant. -/
def join (AA AB : VonNeumannAlgebra H) : VonNeumannAlgebra H :=
  commutantOf (commutantOf ((AA : Set (H →L[ℂ] H)) ∪ AB) : Set (H →L[ℂ] H))

/-- The vector functional `a ↦ ⟨ξ, a ξ⟩` (the vector state of a unit vector `ξ`). -/
def vecState (xi : H) : (H →L[ℂ] H) → ℂ := fun a => ⟪xi, a xi⟫_ℂ

/-- `φ` is a positive normal functional on `M`: `φ(a) = Σₙ ⟨ξₙ, a ξₙ⟩` for all `a ∈ M`, with
`Σₙ ‖ξₙ‖² < ∞`. Only the values of `φ` on `M` matter. -/
def IsPosNormal (M : Set (H →L[ℂ] H)) (φ : (H →L[ℂ] H) → ℂ) : Prop :=
  ∃ ξ : ℕ → H, Summable (fun n => ‖ξ n‖ ^ 2) ∧
    ∀ a ∈ M, HasSum (fun n => ⟪ξ n, a (ξ n)⟫_ℂ) (φ a)

/-- `φ` is a normal state on `M`: a positive normal functional with `φ(1) = 1`. -/
def IsNormalState (M : Set (H →L[ℂ] H)) (φ : (H →L[ℂ] H) → ℂ) : Prop :=
  IsPosNormal M φ ∧ φ 1 = 1

/-- `φ` is a (not necessarily positive) normal functional on `M`:
`φ(a) = Σₙ ⟨ξₙ, a ηₙ⟩` for all `a ∈ M`, with `Σₙ ‖ξₙ‖ ‖ηₙ‖ < ∞`. -/
def IsNormalFunctional (M : Set (H →L[ℂ] H)) (φ : (H →L[ℂ] H) → ℂ) : Prop :=
  ∃ ξ η : ℕ → H, Summable (fun n => ‖ξ n‖ * ‖η n‖) ∧
    ∀ a ∈ M, HasSum (fun n => ⟪ξ n, a (η n)⟫_ℂ) (φ a)

/-- The norm of a functional on `M`: `‖φ‖ = sup {|φ(a)| : a ∈ M, ‖a‖ ≤ 1}`, in `ℝ≥0∞`. -/
def funcNorm (M : Set (H →L[ℂ] H)) (φ : (H →L[ℂ] H) → ℂ) : ℝ≥0∞ :=
  ⨆ a ∈ M, ⨆ (_ : ‖a‖ ≤ 1), (‖φ a‖₊ : ℝ≥0∞)

/-- `σ` dominates `ω` on `M` (`σ ⩾ ω`): `σ - ω` is positive on `M`. -/
def Dominates (M : Set (H →L[ℂ] H)) (σ ω : (H →L[ℂ] H) → ℂ) : Prop :=
  ∀ a ∈ M, (ω (star a * a)).re ≤ (σ (star a * a)).re

/-- Definition 7 (p. 35), read on the join as in Theorem 2 c) (p. 25): a normal state `σ` on
`𝔄_A ∨ 𝔄_B` is separable if `σ(ab) = Σⱼ φⱼ(a) ψⱼ(b)` for all `a ∈ 𝔄_A`, `b ∈ 𝔄_B`, with positive
normal functionals `φⱼ` on `𝔄_A` and `ψⱼ` on `𝔄_B` and `Σⱼ ‖φⱼ‖ ‖ψⱼ‖ = Σⱼ φⱼ(1) ψⱼ(1) < ∞`. -/
def IsSeparableState (AA AB : VonNeumannAlgebra H) (σ : (H →L[ℂ] H) → ℂ) : Prop :=
  IsNormalState (join AA AB : Set (H →L[ℂ] H)) σ ∧
    ∃ φ ψ : ℕ → (H →L[ℂ] H) → ℂ,
      (∀ j, IsPosNormal (AA : Set (H →L[ℂ] H)) (φ j)) ∧
      (∀ j, IsPosNormal (AB : Set (H →L[ℂ] H)) (ψ j)) ∧
      Summable (fun j => (φ j 1).re * (ψ j 1).re) ∧
      ∀ a ∈ AA, ∀ b ∈ AB, HasSum (fun j => φ j a * ψ j b) (σ (a * b))

/-- p. 45: a separable positive linear functional is `σ = r ω'` on the join, with `ω'` a separable
state and `r ⩾ 0`. -/
def IsSeparablePos (AA AB : VonNeumannAlgebra H) (σ : (H →L[ℂ] H) → ℂ) : Prop :=
  ∃ r : ℝ, 0 ≤ r ∧ ∃ σ' : (H →L[ℂ] H) → ℂ, IsSeparableState AA AB σ' ∧
    ∀ x ∈ join AA AB, σ x = (r : ℂ) * σ' x

/-- The standing assumption of statistical independence of §3 (p. 35, `𝔄_A ∨ 𝔄_B ≅ 𝔄_A ⊗ 𝔄_B`),
in the form the proofs use it: every product of positive normal functionals on `𝔄_A` and `𝔄_B`
is a positive normal functional on the join. -/
def IsStatIndependent (AA AB : VonNeumannAlgebra H) : Prop :=
  ∀ φ ψ : (H →L[ℂ] H) → ℂ, IsPosNormal (AA : Set (H →L[ℂ] H)) φ →
    IsPosNormal (AB : Set (H →L[ℂ] H)) ψ →
    ∃ χ : (H →L[ℂ] H) → ℂ, IsPosNormal (join AA AB : Set (H →L[ℂ] H)) χ ∧
      ∀ a ∈ AA, ∀ b ∈ AB, χ (a * b) = φ a * ψ b

/-- The quantity inside Kosaki's variational formula for the step function `x(·)` that equals
`x i` on `[t (i-1), t i)` (`i = 1, …, m`) and `1` on `[t m, ∞)`, with `y = 1 - x`:
`ω(1) ln n − ∫_{1/n}^∞ (ω(y(t)* y(t)) + t⁻¹ σ(x(t) x(t)*)) dt/t`, integrated in closed form. -/
def kosakiValue (ω σ : (H →L[ℂ] H) → ℂ) (n m : ℕ) (t : ℕ → ℝ) (x : ℕ → H →L[ℂ] H) : ℝ :=
  (ω 1).re * Real.log n
    - ∑ i ∈ Finset.Icc 1 m,
        ((ω (star (1 - x i) * (1 - x i))).re * Real.log (t i / t (i - 1))
          + (σ (x i * star (x i))).re * (1 / t (i - 1) - 1 / t i))
    - (σ 1).re / t m

/-- Definition 10 (pp. 40–41): Araki's relative entropy `H(ω, σ)` of positive normal functionals
on a von Neumann algebra `M`, in Kosaki's variational form: the supremum over `n ⩾ 1`, partitions
`1/n = t₀ < t₁ < … < tₘ` and `x₁, …, xₘ ∈ M` of `kosakiValue`. Valued in `EReal`. -/
def relEntropy (M : Set (H →L[ℂ] H)) (ω σ : (H →L[ℂ] H) → ℂ) : EReal :=
  ⨆ (n : ℕ) (_ : 1 ≤ n) (m : ℕ) (t : ℕ → ℝ) (_ : t 0 = 1 / (n : ℝ) ∧ ∀ i < m, t i < t (i + 1))
    (x : ℕ → H →L[ℂ] H) (_ : ∀ i, x i ∈ M), ((kosakiValue ω σ n m t x : ℝ) : EReal)

/-- Definition 11 (p. 42, (93)): the relative entanglement entropy
`E_R(ω) = inf {H(ω, σ) | σ a separable state}`; `⊤` if there is no separable state. -/
def ER (AA AB : VonNeumannAlgebra H) (ω : (H →L[ℂ] H) → ℂ) : EReal :=
  ⨅ (σ : (H →L[ℂ] H) → ℂ) (_ : IsSeparableState AA AB σ),
    relEntropy (join AA AB : Set (H →L[ℂ] H)) ω σ

/-- Definition 12 (p. 45, (104)): the logarithmic dominance
`E_N(ω) = inf {ln ‖σ‖ | σ ⩾ ω, σ separable}` (for positive `σ`, `‖σ‖ = σ(1)`); `⊤` if no
dominating separable functional exists. -/
def EN (AA AB : VonNeumannAlgebra H) (ω : (H →L[ℂ] H) → ℂ) : EReal :=
  ⨅ (σ : (H →L[ℂ] H) → ℂ)
    (_ : IsSeparablePos AA AB σ ∧ Dominates (join AA AB : Set (H →L[ℂ] H)) σ ω),
    ((Real.log (σ 1).re : ℝ) : EReal)

/-- Definition 5 (p. 24): the 1-nuclear norm of a map `T` defined on a subset `M` of a Banach
space `E`: `inf Σⱼ ‖fⱼ‖ ‖yⱼ‖` over representations `T(x) = Σⱼ fⱼ(x) yⱼ` (`x ∈ M`) with
`fⱼ ∈ E*`; `⊤` if there is none. -/
def nuclearNorm1 {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (M : Set E) (T : E → Y) : ℝ≥0∞ :=
  ⨅ (f : ℕ → E →L[ℂ] ℂ) (y : ℕ → Y) (_ : ∀ x ∈ M, HasSum (fun j => f j x • y j) (T x)),
    ∑' j, (‖f j‖₊ : ℝ≥0∞) * ‖y j‖₊

/-- The cut-off `u ↦ exp(min(n, u)/4)`, a bounded continuous function. -/
def quarterExponentialCutoff (n : ℕ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => (Real.exp (min (n : ℝ) u / 4) : ℂ))
    (by fun_prop) (Real.exp ((n : ℝ) / 4)) (by
      intro u
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)))

/-- The graph of `Δ^{1/4}` for modular data `S` (whose `D` is the calculus of `log Δ`):
`(x, y)` with `exp(min(n, log Δ)/4) x → y`. -/
def quarterGraph (S : StandardModularData H) : Set (H × H) :=
  {p | Tendsto (fun n : ℕ => S.D.calculus (quarterExponentialCutoff n) p.1) atTop (𝓝 p.2)}

/-- `Δ^{1/4} x`, as the limit of the cut-offs (meaningful for `x` in the domain of `Δ^{1/4}`). -/
def quarterPow (S : StandardModularData H) (x : H) : H :=
  limUnder atTop (fun n : ℕ => S.D.calculus (quarterExponentialCutoff n) x)

/-- The map `a ↦ Δ^{1/4} a ξ` of (105) (p. 46), for modular data `S` with vector `ξ = S.xi`.
With `S` the modular data of `𝔄′_B` this is `Ψ^A` on `𝔄_A`; with those of `𝔄′_A`, `Ψ^B`. -/
def quarterMap (S : StandardModularData H) : (H →L[ℂ] H) → H :=
  fun a => quarterPow S (a S.xi)

/-- (106) and Definition 13 (p. 47): `E_M(ω) = ln min(‖Ψ^A‖₁, ‖Ψ^B‖₁)`, `⊤` when neither is
nuclear. `SB` is the modular data of `𝔄′_B` and `SA` that of `𝔄′_A` at the vector representative
of `ω` (pinned by hypotheses where used). -/
def EM (AA AB : VonNeumannAlgebra H) (SA SB : StandardModularData H) : EReal :=
  ENNReal.log (min (nuclearNorm1 (AA : Set (H →L[ℂ] H)) (quarterMap SB))
    (nuclearNorm1 (AB : Set (H →L[ℂ] H)) (quarterMap SA)))

end

end HollandsSanders.CFTBound


