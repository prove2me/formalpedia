-- Prove2me | Definitions.Def_JonesUnknot_jones
-- name    : JonesUnknot_jones
-- status  : Definition
-- author  : @Lucas
-- created : 2026-11-17T00:31:51.084468+00:00
-- url     : https://prove2.me/theorems/18e59643-1ba2-4d84-ade4-914b040219b9
-- title:
--   Kauffman bracket and normalized Jones polynomial
-- statement:
--   The Kauffman bracket and the normalized Jones polynomial of a PD code, valued in the Laurent polynomial ring $\mathbb Z[A,A^{-1}]$ (represented as `AddMonoidAlgebra ℤ ℤ`).
--
--   A **state** $s$ assigns to each of the $n$ crossings one of its two Kauffman smoothings; the $A$-smoothing pairs positions $(0,1)$ and $(2,3)$, the $B$-smoothing pairs $(0,3)$ and $(1,2)$. Writing $a(s)$ and $b(s)$ for the numbers of $A$- and $B$-smoothings and $\mathrm{loops}(s)$ for the number of circles of the smoothed diagram, the **Kauffman bracket** is
--   $$\langle D\rangle=\sum_{s} A^{\,a(s)-b(s)}\,\delta^{\,\mathrm{loops}(s)-1},\qquad \delta=-A^2-A^{-2}.$$
--   The circle count reuses the existing `PD.stateGraph` connected components.
--
--   With $w(D)$ the writhe, the **normalized bracket** is
--   $$f_D(A)=(-A^3)^{-w(D)}\,\langle D\rangle.$$
--   For a knot $K$ presented by $D$, $f_D(A)=V_K(A^{-4})$, where $V_K$ is the Jones polynomial; because the exponents of $f_D$ are multiples of $4$, $f_D=1$ if and only if $V_K=1$. The empty diagram has $f_D=1$.
--
--   **Formalization Note.** The state sum ranges over `Fin D.numCrossings → Bool` (definitionally `PD.State`); `numTrue` and `stateGraph` are imported from the platform's Lee layer. The sign factor $(-1)^{w}$ is written via `Even (writhe D)` to avoid integer `zpow`.
-- source:
--   Epoch AI FrontierMath, The Jones Unknot Conjecture, https://epoch.ai/frontiermath/open-problems/jones-unknot ; L. H. Kauffman, State models and the Jones polynomial, Topology 26 (1987), 395-407.

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD
import Definitions.Def_ManolescuPiccirillo_Lee1
import Definitions.Def_JonesUnknot_planar

open Classical
noncomputable section

namespace JonesUnknot
open ManolescuPiccirillo

/-- The Laurent polynomial ring `ℤ[A, A⁻¹]`, represented as `ℤ[ℤ]`. -/
abbrev LP := AddMonoidAlgebra ℤ ℤ

/-- The Kauffman loop value `δ = -A² - A⁻²`. -/
def delta : LP := -AddMonoidAlgebra.single 2 1 - AddMonoidAlgebra.single (-2) 1

/-- The number of circles of the smoothed diagram in state `s`. -/
def stateLoops (D : PD) (s : Fin D.numCrossings → Bool) : ℕ :=
  if D.crossings = [] then 1 else Fintype.card (D.stateGraph s).ConnectedComponent

/-- The Kauffman bracket `⟨D⟩ = Σ_s A^{a(s)-b(s)} δ^{loops(s)-1}`. -/
def kauffmanBracket (D : PD) : LP :=
  ∑ s : Fin D.numCrossings → Bool,
    AddMonoidAlgebra.single ((2 * D.numTrue s : ℤ) - D.numCrossings) 1 *
      delta ^ (stateLoops D s - 1)

/-- The normalized bracket `(-A³)^{-w(D)} ⟨D⟩`, which equals `V_K(A⁻⁴)` for a knot `K`. -/
def jonesA (D : PD) : LP :=
  AddMonoidAlgebra.single (-3 * writhe D) (if Even (writhe D) then 1 else -1) *
    kauffmanBracket D

end JonesUnknot


