-- Prove2me | Definitions.Def_LevyExtrema_SBA_negTriplet
-- name    : LevyExtrema_SBA_negTriplet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:39:16.692914+00:00
-- url     : https://prove2.me/theorems/23005b62-4f48-4007-9f29-12507cfaab68
-- title:
--   The generating triplet of $-X$: $(\sigma^2,\nu\circ(-\cdot)^{-1},-b)$
-- statement:
--   If $X$ is a Lévy process with generating triplet $(\sigma^2,\nu,b)$ for the cutoff $\mathbb 1_{\{|x|<1\}}$, then $-X$ is a Lévy process with triplet
--
--   $$(\sigma^2,\ \nu(-\,\cdot\,),\ -b),$$
--
--   i.e. the same Gaussian coefficient, the reflected Lévy measure $A\mapsto\nu(-A)$ and the negated drift. The paper uses it through the constant $C_p(-X)$ in the definition (4.23) of $C^*_p(X)$.
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, (4.23), p. 25 (C_p(−X))

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy

open MeasureTheory

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **The generating triplet of −X.**
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, (4.23), p. 25 uses `C_p(−X)`, the
constant of Corollary 3 computed from the characteristics of the dual process −X. If X has
triplet (σ², ν, b) for the cutoff 1{|x|<1}, then −X has triplet (σ², ν∘(−·)⁻¹, −b): the drift is
negated, the Lévy measure is reflected, σ is unchanged. -/
noncomputable def negTriplet (Tr : Triplet) : Triplet :=
  ⟨-Tr.γ, Tr.σ, Tr.levyMeasure.map Neg.neg⟩

end LevyExtrema.SBA


