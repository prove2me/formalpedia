-- Prove2me | Definitions.Def_WildeQIT_fidelity
-- name    : WildeQIT_fidelity
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T06:40:28.445744+00:00
-- url     : https://prove2.me/theorems/3067fb0e-8bf5-4083-b4e0-de1085edb3d3
-- title:
--   Fidelity $F(\rho,\sigma) = \|\sqrt{\rho}\sqrt{\sigma}\|_1^2$ and root fidelity $\sqrt{F}$
-- statement:
--   **Fidelity of two states (Wilde §9.2.3, eq. (9.99)/(9.100)).** For density operators $\rho, \sigma \in \mathcal{D}(\mathcal{H})$ the fidelity is
--
--   $$
--   F(\rho, \sigma) = \left\| \sqrt{\rho}\, \sqrt{\sigma} \right\|_1^2 ,
--   $$
--
--   and the **root fidelity** is $\sqrt{F}(\rho, \sigma) = \|\sqrt{\rho}\sqrt{\sigma}\|_1$. By Uhlmann's theorem (Theorem 9.2.1) this equals the maximum squared overlap of purifications (Definition 9.2.3); it is the expression the book uses in Exercises 9.2.4–9.2.8, Property 9.2.1 and Lemma 9.2.1, and the two quantities are related by $F = (\sqrt F)^2$.
--
--   **Formalization Note.** `WildeQIT.rootFidelity ρ σ := traceNorm (CFC.sqrt ρ * CFC.sqrt σ)` and `WildeQIT.fidelity ρ σ := rootFidelity ρ σ ^ 2`, with the square relation recorded as `fidelity_eq_rootFidelity_sq` (definitional). `CFC.sqrt` is the positive square root of a positive semidefinite matrix (junk value $0$ otherwise, so for non-PSD inputs both functions return $0$); `traceNorm` is Definition 9.1.1.
-- source:
--   Wilde, *Quantum Information Theory*, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), §9.2.3 "Uhlmann Fidelity", eq. (9.99)–(9.100) (fidelity as $\|\sqrt{\rho}\sqrt{\sigma}\|_1^2$) and Remark 9.2.1.

import Definitions.Def_WildeQIT_traceNorm

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §9.2.3, eq. (9.99)/(9.100) ("fidelity-l1"):
the fidelity of two density operators is `F(ρ, σ) = ‖√ρ √σ‖₁²`, the root fidelity is
`√F(ρ, σ) = ‖√ρ √σ‖₁`. By Uhlmann's theorem (Theorem 9.2.1) this equals the maximum overlap of
purifications (Definition 9.2.3), and it is the definition used in Exercises 9.2.4–9.2.8,
Property 9.2.1 and Lemma 9.2.1.
-/

open Matrix
open scoped MatrixOrder

namespace WildeQIT

/-- **Root fidelity** `√F(ρ, σ) = ‖√ρ √σ‖₁`, with `√·` Mathlib's positive square root
`CFC.sqrt` and `‖·‖₁` the trace norm (Definition 9.1.1). -/
noncomputable def rootFidelity {n : Type} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ) : ℝ :=
  traceNorm (CFC.sqrt ρ * CFC.sqrt σ)

/-- **Fidelity** `F(ρ, σ) = ‖√ρ √σ‖₁²` (Wilde eq. "fidelity-l1", §9.2.3). -/
noncomputable def fidelity {n : Type} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ) : ℝ :=
  rootFidelity ρ σ ^ 2

/-- The square relation between fidelity and root fidelity, `F = (√F)²`. -/
theorem fidelity_eq_rootFidelity_sq {n : Type} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ) :
    fidelity ρ σ = rootFidelity ρ σ ^ 2 := rfl

end WildeQIT


