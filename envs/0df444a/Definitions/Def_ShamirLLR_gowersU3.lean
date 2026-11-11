-- Prove2me | Definitions.Def_ShamirLLR_gowersU3
-- name    : ShamirLLR_gowersU3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:25:59.729165+00:00
-- url     : https://prove2.me/theorems/e87c6692-0289-4f7b-8eb1-5d7d41ed384c
-- title:
--   Gowers $U^3$ norm and normalized $L^2$ norm on a finite abelian group
-- statement:
--   For a finite abelian group $A$ and $h:A\to\mathbb C$, the **Gowers $U^3$ norm** is defined by
--   $$
--   \|h\|_{U^3(A)}^8=\mathbb E_{x,u_1,u_2,u_3\in A}\prod_{\omega\in\{0,1\}^3}\mathcal C^{|\omega|}h(x+\omega_1u_1+\omega_2u_2+\omega_3u_3),
--   $$
--   where $\mathcal C$ is complex conjugation and $|\omega|=\omega_1+\omega_2+\omega_3$. The normalized $L^2$ norm is $\|f\|_2=(\mathbb E_{z\in A}|f(z)|^2)^{1/2}$.
--
--   The $U^3$ norm measures quadratic uniformity; one-bit leakage functions are approximated in it by nilsequences.
--
--   **Formalization Note** The cube average is a nonnegative real number, so the norm is the real $1/8$-th power of its absolute value (equal to the average itself). Real functions enter through $\mathbb R\to\mathbb C$.
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Eq. (8), p.13; §2.3, p.17 (PDF pp.14, 18)

import Mathlib

set_option autoImplicit false

namespace ShamirLLR

/-- The Gowers `U³` norm on a finite abelian group `A`, Eq. (8), p.13:
`‖h‖_{U³(A)}^8 = 𝔼_{x, u₁, u₂, u₃ ∈ A} ∏_{ω ∈ {0,1}³} 𝒞^{|ω|} h(x + ω₁u₁ + ω₂u₂ + ω₃u₃)`,
where `𝒞` is complex conjugation and `|ω| = ω₁ + ω₂ + ω₃`.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
Eq. (8), p.13 ("the normalized convention in [GT10, Appendix B, p. 1816]").

**Formalization Note.** `ω ∈ {0,1}³` is `Fin 3 → Bool`, `|ω|` the number of `true` entries, and
`𝒞^{|ω|}` the `|ω|`-fold iterate of `starRingEnd ℂ`. The cube average is a nonnegative real
number, so taking its complex absolute value before the real `1/8`-th power changes nothing; it
avoids a real power of a possibly negative real part. Real functions enter through `ℝ → ℂ`. -/
noncomputable def gowersU3 {A : Type*} [AddCommGroup A] [Fintype A] (h : A → ℂ) : ℝ :=
  ‖((Fintype.card A : ℂ) ^ 4)⁻¹ * ∑ x : A, ∑ u : Fin 3 → A,
      ∏ ω : Fin 3 → Bool, (starRingEnd ℂ)^[(Finset.univ.filter (fun j => ω j = true)).card]
        (h (x + ∑ j, if ω j then u j else 0))‖ ^ ((1 : ℝ) / 8)

/-- The normalized `L²` norm `‖f‖₂ = (𝔼_{z ∈ A} |f(z)|²)^{1/2}` on a finite group (§2.3, p.17:
"all averages … use the Haar probability measure; on a finite group, it is the uniform
measure"). -/
noncomputable def l2norm {A : Type*} [Fintype A] (f : A → ℂ) : ℝ :=
  Real.sqrt ((Fintype.card A : ℝ)⁻¹ * ∑ z : A, ‖f z‖ ^ 2)

end ShamirLLR


