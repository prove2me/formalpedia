-- Prove2me | Definitions.Def_KallMayerSLP_ProbConstr_realizationSet
-- name    : KallMayerSLP_ProbConstr_realizationSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:26.326981+00:00
-- url     : https://prove2.me/theorems/63c060c4-54a1-4727-a06a-02e90a94e2e0
-- title:
--   The realized feasible set $\{x \mid T(\hat\xi)x\ge h(\hat\xi)\}$ (the sets $K_j$)
-- statement:
--   For a fixed realization $\hat\xi\in\mathbb R^r$ of the random vector, the set of decisions satisfying the realized linear system is
--   $$
--   \{x\in\mathbb R^n \mid T(\hat\xi)x\ge h(\hat\xi)\}.
--   $$
--   For the atoms $\hat\xi^j$ of a finite discrete distribution these are the sets
--   $$
--   K_j=\{x \mid T(\hat\xi^j)x\ge h(\hat\xi^j)\},\qquad j=1,\dots,N,
--   $$
--   and for an event $A$ the intersection $\bigcap_{\xi\in A}\{x\mid T(\xi)x\ge h(\xi)\}$ is the inner set of the representation (2.13) of the feasible set $\mathcal B(\alpha)$.
--
--   **Formalization Note** The inequality is componentwise; $T$ and $h$ are arbitrary functions of the realization.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Chapter 2, (2.13), p.96 (PDF 106); definition of K_j, §2.2, p.98 (PDF 108)

import Mathlib

open Matrix

namespace KallMayerSLP.ProbConstr

/-- For a fixed realization `ξ̂` of the random vector, the set of decisions satisfying the
realized linear system, `{x | T(ξ̂)x ≥ h(ξ̂)}`. For the atoms `ξ̂^j` of a finite discrete
distribution this is the book's `K_j = {x | T(ξ̂^j)x ≥ h(ξ̂^j)}`, and `⋂_{ξ ∈ A}` of these sets is
the inner set of the representation (2.13).

Kall & Mayer 2005, Chapter 2, (2.13), p.96 (PDF 106), and the definition of `K_j`, §2.2, p.98
(PDF 108).

**Formalization Note.** Componentwise inequality `h ξ ≤ T ξ *ᵥ x` on `Fin m → ℝ`; `T`, `h` are
arbitrary functions of the realization (the book's affine data are a special case). -/
def realizationSet {r m n : ℕ} (T : (Fin r → ℝ) → Matrix (Fin m) (Fin n) ℝ)
    (h : (Fin r → ℝ) → Fin m → ℝ) (ξ : Fin r → ℝ) : Set (Fin n → ℝ) :=
  {x | h ξ ≤ T ξ *ᵥ x}

end KallMayerSLP.ProbConstr


