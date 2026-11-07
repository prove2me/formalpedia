-- Prove2me | Definitions.Def_ApproxGKR_lagrangeBasis
-- name    : ApproxGKR_lagrangeBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:47.753324+00:00
-- url     : https://prove2.me/theorems/a04f542a-e56a-44bf-a8db-154946a3f4f9
-- title:
--   Lagrange basis $L_a$ on $\Omega_h$, $\chi_g$, the extension $\widetilde V$, $\mathrm{eq}_H$ and $\Psi$
-- statement:
--   Fix $h\ge1$ and let $H=\Omega_h$. For a label coordinate $a\in H$ (given by its index) the **Lagrange basis polynomial** is
--   $$L_a(z)=\frac1h\sum_{t=0}^{h-1}(z/a)^t ,$$
--   and for a label $g\in H^m$, $\chi_g(z)=\prod_j L_{g_j}(z_j)$. The **extension** of a function $f$ on the labels $H^m$ is
--   $$\widetilde f(z)=\sum_{g\in H^m} f(g)\,\chi_g(z)$$
--   (eq. (C.1); for $f=V_i$ this is $\widetilde V_i$). The module also defines
--   $$\mathrm{eq}_H(\rho,z)=\sum_{a\in H}L_a(\rho)L_a(z),\qquad \mathrm{eq}(\rho,g)=\prod_j\mathrm{eq}_H(\rho_j,g_j),\qquad \Psi(g)=c_0\,\mathrm{eq}(\rho_0,g)+c_1\,\mathrm{eq}(\rho_1,g)$$
--   (eqs. (C.3)–(C.4)), the last two as polynomials in $g$ for fixed points $\rho,\rho_0,\rho_1\in\mathbb C^m$ and coefficients $c_0,c_1$.
--
--   These are the algebraic objects by which the protocol reduces a claim about one layer of the circuit to a sum over the next.
--
--   **Formalization Note** A label coordinate is an index $a\in\{0,\dots,h-1\}$ standing for $\exp(2\pi i a/h)$, and $z/a$ is written $a^{-1}z$.
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.1, eq. (C.1), p.30; eqs. (C.3)–(C.4), p.31

import Mathlib
import Definitions.Def_ApproxGKR_root

namespace ApproxGKR

/-- The Lagrange basis polynomial `L_a(z) = h⁻¹ Σ_{t=0}^{h−1} (z/a)^t` on `H = Ω_h`, for the label
coordinate with index `a`, i.e. the root `a = exp(2πia/h)` (equation (C.1)).

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.1, eq. (C.1), p.30.

**Formalization Note** `z/a` is written `a⁻¹ · z`; the label coordinate is the index
`a : Fin h`, standing for the root `root h a`. -/
noncomputable def lagrangeBasis (h : ℕ) (a : Fin h) : Polynomial ℂ :=
  Polynomial.C ((h : ℂ)⁻¹) *
    ∑ t ∈ Finset.range h, (Polynomial.C (root h a.val)⁻¹ * Polynomial.X) ^ t

/-- The point of `ℂ^m` represented by a label `g ∈ H^m` given by its indices. -/
noncomputable def labelPoint {h m : ℕ} (g : Fin m → Fin h) : Fin m → ℂ :=
  fun j => root h (g j).val

/-- `χ_g(z) = Π_j L_{g_j}(z_j)` (eq. (C.1), p.30), as a polynomial in `m` variables. -/
noncomputable def chi {h m : ℕ} (g : Fin m → Fin h) : MvPolynomial (Fin m) ℂ :=
  ∏ j, Polynomial.aeval (MvPolynomial.X j) (lagrangeBasis h (g j))

/-- The extension `Ṽ(z) = Σ_{g ∈ H^m} f(g) χ_g(z)` of a function `f` on the labels `H^m`
(eq. (C.1), p.30; there `f = V_i`, the exact gate values of layer `i`). -/
noncomputable def extension {h m : ℕ} (f : (Fin m → Fin h) → ℂ) : MvPolynomial (Fin m) ℂ :=
  ∑ g, MvPolynomial.C (f g) * chi g

/-- `eq_H(ρ, z) = Σ_{a ∈ H} L_a(ρ) L_a(z)` (eq. (C.3), p.31), as a function of two complex
numbers. -/
noncomputable def eqH (h : ℕ) (ρ z : ℂ) : ℂ :=
  ∑ a : Fin h, (lagrangeBasis h a).eval ρ * (lagrangeBasis h a).eval z

/-- `eq(ρ, ·) = Π_j eq_H(ρ_j, ·_j)` (eq. (C.4), p.31) as a polynomial in the second argument
`g ∈ ℂ^m`, for a fixed point `ρ ∈ ℂ^m`. -/
noncomputable def eqMv (h : ℕ) {m : ℕ} (ρ : Fin m → ℂ) : MvPolynomial (Fin m) ℂ :=
  ∏ j, ∑ a : Fin h, MvPolynomial.C ((lagrangeBasis h a).eval (ρ j)) *
    Polynomial.aeval (MvPolynomial.X j) (lagrangeBasis h a)

/-- `Ψ(g) = Σ_{b=0}^{1} c_b eq(ρ_b, g)` (eq. (C.4), p.31), for evaluation points `ρ₀, ρ₁ ∈ ℂ^m`
and coefficients `c₀, c₁ ∈ ℂ`, as a polynomial in `g`. -/
noncomputable def Psi (h : ℕ) {m : ℕ} (ρ0 ρ1 : Fin m → ℂ) (c0 c1 : ℂ) :
    MvPolynomial (Fin m) ℂ :=
  MvPolynomial.C c0 * eqMv h ρ0 + MvPolynomial.C c1 * eqMv h ρ1

end ApproxGKR


