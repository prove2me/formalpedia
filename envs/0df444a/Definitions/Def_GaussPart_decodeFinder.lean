-- Prove2me | Definitions.Def_GaussPart_decodeFinder
-- name    : GaussPart_decodeFinder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:14.84269+00:00
-- url     : https://prove2.me/theorems/a89bd392-2167-49f2-b6b5-b6504ddaafa6
-- title:
--   Output format of the finder programs
-- statement:
--   A finder outcome is Reject, None, or a direction $w\in\mathbb R^d$. For a halted run of a finder program, register $r_0=0$ means Reject, $r_0=1$ None, and $r_0=2$ a direction: memory from the address in pointer $1$ then holds a nonzero vector $\hat w$, and the returned unit direction is $\hat w/\|\hat w\|$. Anything else is malformed. The inputs are $k,\Delta,V,H$ (Proposition 3.3) or $k,\Delta,V,H,\beta$ (Corollary C.1) in memory from cell $0$.
--
--   **Formalization Note** An arithmetic program cannot take square roots, so "returns a unit direction" is encoded by returning a nonzero vector whose normalization is the direction.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Proposition 3.3, p.15 (PDF p.17); Corollary C.1, p.73

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_Cell

namespace GaussPart

/-- An output of the moment discrepancy finder: Reject, None, or a unit direction (Proposition 3.3,
p.15). -/
inductive FinderOutcome (d : ℕ) where
  | reject
  | none
  | dir (w : Vec d)

open Classical in
/-- The output of a halted state of a finder program (Proposition 3.3, p.15, PDF p.17, of
arXiv:2611.05264, sha256 7e0ca6d4…): register `r[0]` is `0` for Reject, `1` for None and `2` for a
direction; in that last case memory from `p[1]` holds a nonzero vector `ŵ ∈ ℝᵈ`, and the direction
is `ŵ/‖ŵ‖`. Anything else decodes to `none`.

**Formalization Note.** A program on the arithmetic machine cannot take a square root, so "returns
a unit direction" is encoded as returning a nonzero vector; its normalization is the unit
direction. -/
noncomputable def decodeFinder (d : ℕ) (s : GaussMixHH.State) : Option (FinderOutcome d) :=
  if s.core.regs 0 = 0 then some .reject
  else if s.core.regs 0 = 1 then some .none
  else if s.core.regs 0 = 2 then
    let w : Vec d := WithLp.toLp 2 fun i : Fin d => s.core.mem (s.core.ptrs 1 + (i : ℕ))
    if w = 0 then Option.none else some (.dir ((‖w‖)⁻¹ • w))
  else Option.none

/-- The input of a finder program, in memory from cell `0`: `k, Δ, V, H`. -/
noncomputable def finderInput (k : ℕ) (Δ V H : ℝ) : List ℝ := [(k : ℝ), Δ, V, H]

/-- The input of an amplified finder program, in memory from cell `0`: `k, Δ, V, H, β`. -/
noncomputable def amplifiedInput (k : ℕ) (Δ V H β : ℝ) : List ℝ := [(k : ℝ), Δ, V, H, β]

end GaussPart


