-- Prove2me | Definitions.Def_KatyushaNs_Fobj
-- name    : KatyushaNs_Fobj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:45:27.14352+00:00
-- url     : https://prove2.me/theorems/656c804f-b3f9-408b-9f6f-612028379782
-- title:
--   Composite objective $F = f + \psi$
-- statement:
--   For $f_1,\dots,f_n : \mathbb{R}^d \to \mathbb{R}$ and $\psi$, the composite objective of Problem (1.1) is
--   $$F(x) = f(x) + \psi(x) = \frac1n\sum_{i=1}^n f_i(x) + \psi(x).$$
--
--   **Formalization Note** The paper's $\psi$ may take the value $+\infty$; it is encoded by its effective domain $D$ and real values on $D$. $F$ is only evaluated at points of $D$ in the theorems of this mission.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Problem (1.1), p. 1

import Mathlib
import Definitions.Def_KatyushaNs_favg

namespace KatyushaNs

/-- **The composite objective `F = f + ψ` of Problem (1.1).**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, Problem (1.1), p. 1 (PDF p. 2): "min_{x∈Rd} { F(x) def= f(x) + ψ(x) def=
(1/n) Σ_{i=1}^n fi(x) + ψ(x) }".

`Fobj fi ψ x = favg fi x + ψ x`.

**Formalization Note.** The paper's `ψ` may take the value `+∞`. It is encoded by a set `D` (its
effective domain) and real values `ψ : ℝᵈ → ℝ` on `D`; `Fobj fi ψ x` is the paper's `F(x)` for
`x ∈ D` and is never used at points outside `D` by the theorems of this mission. -/
noncomputable def Fobj {d n : ℕ} (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => favg fi x + ψ x

end KatyushaNs


