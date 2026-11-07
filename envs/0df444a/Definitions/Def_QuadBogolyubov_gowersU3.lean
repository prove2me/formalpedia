-- Prove2me | Definitions.Def_QuadBogolyubov_gowersU3
-- name    : QuadBogolyubov_gowersU3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:38.350856+00:00
-- url     : https://prove2.me/theorems/3b6d2fc3-b93e-43e4-8063-2e2beac505b4
-- title:
--   Gowers $U^2$, $U^3$ norms and the local norm $\|f\|_{U^3(W)}$
-- statement:
--   For $f:\mathbb F_2^n\to\mathbb C$,
--   $$\|f\|_{U^2}^4=\mathbb E_{x,h_1,h_2}\prod_{\epsilon\in\{0,1\}^2}\mathcal C^{|\epsilon|}f(x+\epsilon\cdot h),\qquad \|f\|_{U^3}^8=\mathbb E_{x,h_1,h_2,h_3}\prod_{\epsilon\in\{0,1\}^3}\mathcal C^{|\epsilon|}f(x+\epsilon\cdot h),$$
--   where $\mathcal Cf=\overline f$. For a non-empty quadratic variety $W$, the **local norm** is
--   $$\|f\|_{U^3(W)}=\frac{\|f\mathbf 1_W\|_{U^3}}{\|\mathbf 1_W\|_{U^3}}.$$
--   The module also defines the indicator $\mathbf 1_S$ of a finite set, with values in $\mathbb R$ or $\mathbb C$.
--
--   The local norm measures quadratic uniformity relative to a variety.
--
--   **Formalization Note** The cube averages are non-negative reals; the norms are the real $1/4$-th and $1/8$-th powers of their real parts. $f$ is defined on all of $\mathbb F_2^n$ and only its values on $W$ enter. The paper defines the local norm for non-empty $W$ only; for empty $W$ the Lean value is $0/0=0$.
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Definitions 3.3, 3.4, p.10

import Mathlib
import Definitions.Def_QuadBogolyubov_QuadVariety

set_option autoImplicit false

open scoped BigOperators

namespace QuadBogolyubov

/-- The indicator function `1_S` of a finite set `S`, valued in a ring `R` (`ℝ` or `ℂ`). -/
noncomputable def ind {α R : Type} [Zero R] [One R] (S : Finset α) (x : α) : R :=
  open Classical in if x ∈ S then 1 else 0

/-- `‖f‖⁴_{U²} = 𝔼_{x,h₁,h₂ ∈ G} ∏_{ε ∈ {0,1}²} 𝒞^{|ε|} f(x + ε · h)`, as a complex number. -/
noncomputable def gowersU2Pow4 {n : ℕ} (f : (Fin n → ZMod 2) → ℂ) : ℂ :=
  𝔼 x, 𝔼 h : Fin 2 → (Fin n → ZMod 2),
    ∏ ε : Fin 2 → ZMod 2, (starRingEnd ℂ)^[∑ i, (ε i).val] (f (x + ∑ i, ε i • h i))

/-- `‖f‖⁸_{U³} = 𝔼_{x,h₁,h₂,h₃ ∈ G} ∏_{ε ∈ {0,1}³} 𝒞^{|ε|} f(x + ε · h)`, as a complex number. -/
noncomputable def gowersU3Pow8 {n : ℕ} (f : (Fin n → ZMod 2) → ℂ) : ℂ :=
  𝔼 x, 𝔼 h : Fin 3 → (Fin n → ZMod 2),
    ∏ ε : Fin 3 → ZMod 2, (starRingEnd ℂ)^[∑ i, (ε i).val] (f (x + ∑ i, ε i • h i))

/-- The **Gowers `U²` norm** `‖f‖_{U²}` of `f : 𝔽₂ⁿ → ℂ`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…),
Definition 3.3, p.10: "Given f : G → C, define ∥f∥⁴_{U2} = E_{x,h1,h2∈G} ∏_{ϵ∈{0,1}²} C^{|ϵ|}f(x + ϵ · h),
and ∥f∥⁸_{U3} = E_{x,h1,h2,h3∈G} ∏_{ϵ∈{0,1}³} C^{|ϵ|}f(x + ϵ · h), where Cf = f̄ and ϵ · h
denotes the standard dot product."

**Formalization Note.** `G = 𝔽₂ⁿ = Fin n → ZMod 2`; `ε ∈ {0,1}^k` is `Fin k → ZMod 2`, so
`ε · h = ∑ᵢ εᵢ hᵢ` and `|ε| = ∑ᵢ εᵢ` (as natural numbers); `𝒞` is complex conjugation. The average
is a non-negative real number; the norm is the real fourth root of its real part. -/
noncomputable def gowersU2 {n : ℕ} (f : (Fin n → ZMod 2) → ℂ) : ℝ :=
  (gowersU2Pow4 f).re ^ ((1 : ℝ) / 4)

/-- The **Gowers `U³` norm** `‖f‖_{U³}` of `f : 𝔽₂ⁿ → ℂ` (Definition 3.3, p.10; see
`gowersU2`). The norm is the real eighth root of the real part of `gowersU3Pow8 f`. -/
noncomputable def gowersU3 {n : ℕ} (f : (Fin n → ZMod 2) → ℂ) : ℝ :=
  (gowersU3Pow8 f).re ^ ((1 : ℝ) / 8)

/-- The **local Gowers `U³` norm** relative to a quadratic variety `W`:
`‖f‖_{U³(W)} = ‖f 1_W‖_{U³} / ‖1_W‖_{U³}`.

Definition 3.4, p.10: "For a non-empty quadratic variety W ⊆ G and a function f : W → C, define
∥f∥_{U3(W)} = ∥f1W∥_{U3} / ∥1W∥_{U3}, where f1W denotes the extension of f by zero on G \ W."

**Formalization Note.** `f` is a function on all of `𝔽₂ⁿ`; only its values on `W` enter. The
paper defines the norm for non-empty `W` only; every statement using it assumes `W` non-empty
(for empty `W` the Lean value is `0 / 0 = 0`). -/
noncomputable def localU3 {n : ℕ} (W : QuadVariety n) (f : (Fin n → ZMod 2) → ℂ) : ℝ :=
  gowersU3 (fun x => f x * ind W.carrier x) / gowersU3 (ind W.carrier)

end QuadBogolyubov


