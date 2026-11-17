-- Prove2me | Definitions.Def_ImpuritySim_Supplement_Interaction
-- name    : ImpuritySim_Supplement_Interaction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:31:29.729597+00:00
-- url     : https://prove2.me/theorems/75a9e77b-ca37-4da6-9695-dacecf035c9c
-- title:
--   The imaginary-time interaction-picture expansion $D_r$, $G_K$ of $e^{-\beta(H_{\mathrm{ref}}+V)}$
-- statement:
--   Let $H=H_{\mathrm{ref}}+V$ act on a finite-dimensional Hilbert space, with $V=\sum_{a=1}^R v_aU_a$, $v_a\in\mathbb R$, and $W=\sum_a|v_a|$ (C.1). For $r\ge1$ the **ordered simplex** is
--   $$\Omega_r(\beta)=\{(\tau_1,\dots,\tau_r):\beta\ge\tau_1\ge\cdots\ge\tau_r\ge0\}\subseteq\mathbb R^r,$$
--   and $V_I(\tau)=e^{\tau H_{\mathrm{ref}}}Ve^{-\tau H_{\mathrm{ref}}}$. The terms of the expansion are $D_0=e^{-\beta H_{\mathrm{ref}}}$ and, for $r\ge1$,
--   $$D_r=(-1)^r e^{-\beta H_{\mathrm{ref}}}\int_{\Omega_r(\beta)}V_I(\tau_1)\cdots V_I(\tau_r)\,d\tau_1\cdots d\tau_r,$$
--   and the truncation at order $K$ is $G_K=\sum_{r=0}^K D_r$.
--
--   These are the objects of continuous-time quantum Monte Carlo: truncating the expansion at $G_K$ is what Theorem C.1 controls.
--
--   **Formalization Note** The integral is against Lebesgue measure on $\mathbb R^r$ and is taken entrywise; the integrand is continuous on the compact set $\Omega_r(\beta)$, so every entry is integrable. The matrix exponential is Mathlib's `NormedSpace.exp`.
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), (C.1), p.59; Ω_r(β), V_I, (C.2)–(C.3), D_r, G_K, p.60

import Mathlib

open MeasureTheory

namespace ImpuritySim.Supplement

/-!
# The imaginary-time interaction-picture expansion of Appendix C.1

J. Jiang, N. Ju, O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation
of quantum impurity models*, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2): (C.1),
p.59; the ordered simplex, `V_I(τ)`, (C.2)–(C.3), `D_r` and `G_K`, p.60.

**Formalization Note.**
* Operators are square complex matrices on a finite index type `ι` (a finite-dimensional Hilbert
  space with a fixed orthonormal basis). `e^X` is Mathlib's matrix exponential `NormedSpace.exp`.
* `Vop v U = V = Σ_{a=1}^R v_a U_a` and `Wsum v = W = Σ_a |v_a|` (C.1), with `a : Fin R`.
* `orderedSimplex β r = Ω_r(β) = {τ ∈ ℝ^r : β ≥ τ_1 ≥ ⋯ ≥ τ_r ≥ 0}` (coordinates 0-based: `τ 0`
  is the page's `τ_1`); for `r = 0` it is the one point of `ℝ^0`.
* `VI Href V t = V_I(t) = e^{t H_ref} V e^{−t H_ref}`.
* `Dterm Href V β r = D_r`: `D_0 = e^{−β H_ref}`, and for `r ≥ 1`
  `D_r = (−1)^r e^{−β H_ref} ∫_{Ω_r(β)} V_I(τ_1) ⋯ V_I(τ_r) dτ_1 ⋯ dτ_r`, the product in the order
  `τ_1, …, τ_r` and the integral against Lebesgue measure on `ℝ^r`. The integral of a matrix-valued
  function is taken entrywise (the `(i, j)` entry of `D_r` is the integral of the `(i, j)` entry
  of the integrand); the integrand is continuous and `Ω_r(β)` is compact, so every entry is
  integrable and this is the Bochner integral of the page.
* `GK Href V β K = G_K = Σ_{r=0}^K D_r`.
-/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `V = Σ_{a=1}^R v_a U_a` (C.1). -/
noncomputable def Vop {R : ℕ} (v : Fin R → ℝ) (U : Fin R → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ a, ((v a : ℝ) : ℂ) • U a

/-- `W = Σ_{a=1}^R |v_a|` (C.1). -/
def Wsum {R : ℕ} (v : Fin R → ℝ) : ℝ := ∑ a, |v a|

/-- The ordered simplex `Ω_r(β) = {(τ_1, …, τ_r) : β ≥ τ_1 ≥ ⋯ ≥ τ_r ≥ 0}`. -/
def orderedSimplex (β : ℝ) (r : ℕ) : Set (Fin r → ℝ) :=
  {τ | Antitone τ ∧ ∀ k, 0 ≤ τ k ∧ τ k ≤ β}

/-- `V_I(t) = e^{t H_ref} V e^{−t H_ref}`. -/
noncomputable def VI (Href V : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  NormedSpace.exp ((t : ℂ) • Href) * V * NormedSpace.exp (-(t : ℂ) • Href)

/-- `D_0 = e^{−βH_ref}` and `D_r = (−1)^r e^{−βH_ref} ∫_{Ω_r(β)} V_I(τ_1) ⋯ V_I(τ_r) dτ` (`r ≥ 1`),
the integral entrywise against Lebesgue measure on `ℝ^r`. -/
noncomputable def Dterm (Href V : Matrix ι ι ℂ) (β : ℝ) (r : ℕ) : Matrix ι ι ℂ :=
  if r = 0 then NormedSpace.exp (-(β : ℂ) • Href)
  else fun i j => (-1 : ℂ) ^ r *
    ∫ τ in orderedSimplex β r,
      (NormedSpace.exp (-(β : ℂ) • Href) * (List.ofFn fun k : Fin r => VI Href V (τ k)).prod) i j

/-- `G_K = Σ_{r=0}^K D_r`. -/
noncomputable def GK (Href V : Matrix ι ι ℂ) (β : ℝ) (K : ℕ) : Matrix ι ι ℂ :=
  ∑ r ∈ Finset.range (K + 1), Dterm Href V β r

end ImpuritySim.Supplement


