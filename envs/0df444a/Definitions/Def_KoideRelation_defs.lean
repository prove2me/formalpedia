-- Prove2me | Definitions.Def_KoideRelation_defs
-- name    : KoideRelation_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T14:14:54.772645+00:00
-- url     : https://prove2.me/theorems/af122bd0-9ca8-4182-a6e7-847adde09ade
-- title:
--   Koide splitting parameter $q$, degeneracy angle $\psi$, and pseudo-masses $\tilde m_i$
-- statement:
--   Four notions used throughout the mission, for a family of $n$ real "masses" $m = (m_1,\dots,m_n)$.
--
--   **Koide splitting parameter.** $q(m) = \dfrac{\sum_i m_i}{\left(\sum_i \sqrt{m_i}\right)^2}$. Koide's relation for the charged leptons is $q(m_e, m_\mu, m_\tau) = \tfrac{2}{3}$ (eq. (3.1) of the source with $q^l = \tfrac23$).
--
--   **Degeneracy cosine.** With $S = (\sqrt{m_1},\dots,\sqrt{m_n})$ and $\mathbf 1 = (1,\dots,1)$, $\cos\psi = \dfrac{\langle S, \mathbf 1\rangle}{\lVert S\rVert\,\lVert \mathbf 1\rVert} = \dfrac{\sum_i \sqrt{m_i}}{\sqrt{\sum_i (\sqrt{m_i})^2}\,\sqrt n}$, written out as an explicit quotient of sums (eq. (3.5)).
--
--   **Degeneracy angle.** $\psi = \arccos(\cos\psi)$, the angle between the square-root-mass vector and the democratic direction $(1,\dots,1)$ (Fig. 3.1).
--
--   **Pseudo-masses.** For a complex mixing matrix $U$, $\tilde m_i = \left|\sum_j U_{ij} m_j\right|$ (eq. (3.32)).
--
--   All four are total functions: they use Lean's conventions $\sqrt{x} = 0$ for $x < 0$ and $x/0 = 0$, so nonnegativity and nondegeneracy are imposed as hypotheses on each theorem rather than built into the definitions.
-- source:
--   Goffinet, François, "A bottom-up approach to fermion masses", PhD thesis, Université catholique de Louvain, December 2008, http://hdl.handle.net/2078.1/20873, Chapter 3 "A Mass Relation", pp. 60-62 (eqs. (3.1), (3.5), Fig. 3.1), p. 73 (eq. (3.32))

import Mathlib

namespace KoideRelation

open Finset

/-- The Koide splitting parameter of a family of `n` masses `m : Fin n → ℝ`:
`q = (∑ i, m i) / (∑ i, √(m i))ᐟ²`.  Koide's relation for the charged leptons is the
statement that this parameter equals `2/3` for `(mₑ, m_μ, m_τ)`. -/
noncomputable def koideRatio {n : ℕ} (m : Fin n → ℝ) : ℝ :=
  (∑ i, m i) / (∑ i, Real.sqrt (m i)) ^ 2

/-- The cosine of the angle `ψ` between the vector of square-root masses
`S = (√m₁, …, √mₙ)` and the "degeneracy" direction `(1, …, 1)`. -/
noncomputable def koideCos {n : ℕ} (m : Fin n → ℝ) : ℝ :=
  (∑ i, Real.sqrt (m i)) /
    (Real.sqrt (∑ i, Real.sqrt (m i) ^ 2) * Real.sqrt (n : ℝ))

/-- The angle `ψ` between the square-root-mass vector and the degeneracy direction
`(1, …, 1)`, in radians. -/
noncomputable def koideAngle {n : ℕ} (m : Fin n → ℝ) : ℝ :=
  Real.arccos (koideCos m)

/-- The "pseudo-masses" `m̃ᵢ = |∑ⱼ (U_L)ᵢⱼ mⱼ|` built from a flavour mixing matrix `U`
and the physical masses `m`. -/
noncomputable def pseudoMass {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (m : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  ‖∑ j, U i j * (m j : ℂ)‖

end KoideRelation


