-- Prove2me | Definitions.Def_LogConcaveLattice_Lift_UniformQuotient
-- name    : LogConcaveLattice_Lift_UniformQuotient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:06.324923+00:00
-- url     : https://prove2.me/theorems/67eb68ae-da77-4b0b-9429-f0bd3d72173c
-- title:
--   §2.5 — the uniform probability measure on the torus $\mathbb R^n/\Lambda$
-- statement:
--   Let $\Lambda\subseteq\mathbb R^n$ be a full-rank lattice with basis $B=(b_1,\dots,b_n)$ and fundamental parallelepiped $F=B[0,1)^n$. The **uniform probability measure on $\mathbb R^n/\Lambda$** is the law of $U+\Lambda$ where $U$ is uniform on $F$:
--   $$\nu_\Lambda=\pi_\#\Big(\tfrac{1}{\operatorname{Vol}_n(F)}\operatorname{Vol}_n|_F\Big),\qquad \pi(x)=x+\Lambda .$$
--   It does not depend on the choice of fundamental domain, and $\operatorname{Vol}_n(F)=\det\Lambda$. For a random vector $X$ on $\mathbb R^n$, "$X+\Lambda$ is uniform on $\mathbb R^n/\Lambda$" means that the push-forward of the law of $X$ under $\pi$ is $\nu_\Lambda$.
--
--   This is the target law of the lattice lift of Theorem 1.1 and the object of Lemma 2.6.
--
--   **Formalization Note** The quotient is `V n ⧸ Λ.toAddSubgroup` with Mathlib's quotient σ-algebra (a set is measurable iff its preimage is), for which the quotient map is measurable; the basis is a chosen $\mathbb Z$-basis of $\Lambda$, viewed as an $\mathbb R$-basis of $\mathbb R^n$.
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, §2.5 p. 8 (uniform probability measure on R^n/Λ, push-forward π_# μ); fundamental parallelepiped p. 7 and proof of Lemma 2.6 p. 9

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice

open MeasureTheory

namespace LogConcaveLattice.Lift

variable {n : ℕ}

/-- The fundamental parallelepiped `F = B[0,1)ⁿ` of a full-rank lattice `Λ` for a chosen basis
`B` (p. 7, proof of Lemma 2.6). -/
noncomputable def fundParallelepiped (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] : Set (V n) :=
  ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ)

/-- The **uniform probability measure on `ℝⁿ/Λ`** (p. 8): the law of `U + Λ` with `U` uniform on
a fundamental domain `F` (here the parallelepiped above), i.e. the push-forward under the
quotient map `x ↦ x + Λ` of the normalized Lebesgue measure `vol(F)⁻¹ · vol|_F`. The quotient
carries the quotient σ-algebra, for which the quotient map is measurable. -/
noncomputable def uniformQuot (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    Measure (V n ⧸ Λ.toAddSubgroup) :=
  Measure.map (QuotientAddGroup.mk : V n → V n ⧸ Λ.toAddSubgroup)
    ((volume (fundParallelepiped Λ))⁻¹ • volume.restrict (fundParallelepiped Λ))

end LogConcaveLattice.Lift


