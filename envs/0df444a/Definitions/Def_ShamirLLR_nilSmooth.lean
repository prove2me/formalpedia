-- Prove2me | Definitions.Def_ShamirLLR_nilSmooth
-- name    : ShamirLLR_nilSmooth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:29.408337+00:00
-- url     : https://prove2.me/theorems/a4a1baed-cf72-4296-89a3-1a65f20cadf2
-- title:
--   Directional derivatives, $C^R$ norms and Lipschitz norms on $G/\Gamma$
-- statement:
--   For a function $F$ on $G/\Gamma$ and $X\in\mathrm{Lie}(G)$, the directional derivative is
--   $$
--   D_XF(x\Gamma)=\frac{d}{dt}F(\exp(tX)x\Gamma)\Big|_{t=0}.
--   $$
--   $F\in C^R(G/\Gamma)$ when it is $R$ times continuously differentiable, and
--   $$
--   \|F\|_{C^R(X)}=\max_{0\le j\le R}\ \max_{X_{i_1},\dots,X_{i_j}\in X}\bigl\|D_{X_{i_1}}\cdots D_{X_{i_j}}F\bigr\|_\infty .
--   $$
--   The Lipschitz norm is $\|F\|_{\mathrm{Lip}(X)}=\|F\|_\infty+\sup_{x\Gamma\neq y\Gamma}|F(x\Gamma)-F(y\Gamma)|/d_{G/\Gamma}(x\Gamma,y\Gamma)$, where $d_{G/\Gamma}$ is the quotient of the largest right-invariant metric $d_X$ with $d_X(g,\mathrm{id})\le\|\psi(g)\|_\infty$.
--
--   These norms define the smooth class $G_{p,3}$ and the complexity of nilsequences.
--
--   **Formalization Note** Functions on $G/\Gamma$ are right-$\Gamma$-invariant functions on $G$; $C^R$ is measured in Mal'cev coordinates. Norm bounds are stated as bounds (not as real suprema): $\|F\|_{C^R}\le Q$ bounds every iterated derivative of order $\le R$; $\|F\|_{\mathrm{Lip}}\le K$ is $A+L\le K$ with $A$ a sup bound and $L\ge0$ a Lipschitz constant for the published quotient metric `G.distQ`.
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), §3.1, p.19; §4.1, pp.24–25 (PDF pp.20, 25–26)

import Mathlib
import Definitions.Def_LSSNil

set_option autoImplicit false

namespace ShamirLLR

/-- A function on `G` is right-`Γ`-invariant on `G`, i.e. a function on `G/Γ` (§3.1). -/
def IsRightΓInv {E : Type*} (G : LSS.Nilmanifold 2) (F : G.Mat → E) : Prop :=
  ∀ x γ : G.Mat, G.Mem x → G.MemΓ γ → F (x * γ) = F x

/-- The directional derivative `D_X F(xΓ) = d/dt F(exp(tX)xΓ)|_{t=0}`, §4.1, p.24.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
§4.1, pp.24–25.

**Formalization Note.** `exp(tX)` is the matrix exponential `LSS.mexp (t • X)` of the strictly
upper triangular matrix `tX`. -/
noncomputable def lieDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : LSS.Nilmanifold 2) (X : G.Mat) (F : G.Mat → E) : G.Mat → E :=
  fun x => deriv (fun t : ℝ => F (LSS.mexp (t • X) * x)) 0

/-- The iterated derivative `D_{X_{i₁}} ⋯ D_{X_{i_j}} F` along a word `(i₁, …, i_j)` of basis
directions (§4.1, p.25); the empty word gives `F`. -/
noncomputable def lieDerivWord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : LSS.Nilmanifold 2) (w : List (Fin G.d)) (F : G.Mat → E) : G.Mat → E :=
  w.foldr (fun i F' => lieDeriv G (G.X i) F') F

/-- `F ∈ C^R(G/Γ)`: `F` is a function on `G/Γ` that is `R` times continuously differentiable
(§4.1, p.25).

**Formalization Note.** `G/Γ`-functions are right-`Γ`-invariant functions on `G`; smoothness is
measured in Mal'cev coordinates (`F ∘ G.malcev` is `C^R` on `ℝ^{d_G}`), which is equivalent since
the coordinate map is a diffeomorphism onto `G`. -/
def IsCR {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : LSS.Nilmanifold 2) (R : ℕ)
    (F : G.Mat → E) : Prop :=
  IsRightΓInv G F ∧ ContDiff ℝ R (F ∘ G.malcev)

/-- `‖F‖_{C^R(X)} ≤ Q` (§4.1, p.25): `F` and all its iterated directional derivatives
`D_{X_{i₁}} ⋯ D_{X_{i_j}} F` of order `j ≤ R` along basis vectors are bounded in absolute value
by `Q` on `G`.

**Formalization Note.** Stated as a bound rather than as a real supremum, so that no junk value
of an unbounded supremum can enter. -/
def CRNormLE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : LSS.Nilmanifold 2)
    (R : ℕ) (Q : ℝ) (F : G.Mat → E) : Prop :=
  ∀ w : List (Fin G.d), w.length ≤ R → ∀ x : G.Mat, G.Mem x → ‖lieDerivWord G w F x‖ ≤ Q

/-- `‖F‖_{Lip(X)} ≤ K` (§3.1, p.19), where
`‖F‖_{Lip(X)} = ‖F‖_∞ + sup_{xΓ ≠ yΓ} |F(xΓ) − F(yΓ)| / d_{G/Γ}(xΓ, yΓ)` and `d_{G/Γ}` is the
quotient of the right-invariant metric `d_X`.

**Formalization Note.** `F` is right-`Γ`-invariant on `G`; the quotient metric is the published
`G.distQ` (Green–Tao's metric). The norm bound is written as `A + L ≤ K` with `A` a sup bound
and `L ≥ 0` a Lipschitz constant, which is equivalent and avoids real suprema. -/
def LipNormLE {E : Type*} [NormedAddCommGroup E] (G : LSS.Nilmanifold 2) (F : G.Mat → E)
    (K : ℝ) : Prop :=
  IsRightΓInv G F ∧ ∃ A L : ℝ, 0 ≤ L ∧ A + L ≤ K ∧ (∀ x : G.Mat, G.Mem x → ‖F x‖ ≤ A) ∧
    ∀ x y : G.Mat, G.Mem x → G.Mem y → ‖F x - F y‖ ≤ L * G.distQ x y

end ShamirLLR


