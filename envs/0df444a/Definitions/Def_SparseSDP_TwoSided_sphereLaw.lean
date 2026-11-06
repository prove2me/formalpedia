-- Prove2me | Definitions.Def_SparseSDP_TwoSided_sphereLaw
-- name    : SparseSDP_TwoSided_sphereLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:14.609602+00:00
-- url     : https://prove2.me/theorems/65b486f6-6ca1-4794-911f-af4215b62c59
-- title:
--   $\mathrm{Unif}(S^{d-1})$ and the rank-one response $P_u(H)$, $\bar P(H)$
-- statement:
--   The law $\mathrm{Unif}(S^{d-1})$ is taken as the law of $g/\|g\|_2$ for $g$ with i.i.d. $N(0,1)$ coordinates, and `drawSphere` draws it from the tape at cost $O(d)$.
--
--   For real symmetric $H$ and a real unit vector $u$,
--   $$
--   P_u(H)=\frac{e^{H/2}uu^\top e^{H/2}}{u^\top e^Hu},\qquad \bar P(H)=\mathbb E_{u\sim\mathrm{Unif}(S^{d-1})}[P_u(H)],
--   $$
--   Eq. (228). $P_u(H)$ is the rank-one projector obtained by normalizing $e^{H/2}u$; in general $\bar P(H)\ne e^H/\operatorname{Tr}e^H$.
--
--   **Formalization Note** $\bar P$ is an entrywise Bochner integral of bounded measurable functions; the map $g\mapsto g/\|g\|_2$ is measurable, so `sphereLaw` is a probability measure (proved in the verification file). The point $g=0$ is a null event for $d\ge1$.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Eq. (228), p. 45; p. 62

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Prog

open MeasureTheory ProbabilityTheory Matrix

namespace SparseSDP.TwoSided

variable {d : ℕ}

/-- `g ↦ g/‖g‖₂`. -/
noncomputable def sphereNormalize (g : Vec d) : Vec d := (1 / l2 g) • g

/-- `Unif(S^{d−1})` as the law of `g/‖g‖₂` for `g` with i.i.d. `N(0,1)` coordinates.

**Formalization Note.** `g = 0` is a null event for `d ≥ 1`. The map is measurable, so the law is a
genuine probability measure (checked in the verification file). -/
noncomputable def sphereLaw (d : ℕ) : Measure (Vec d) :=
  (Measure.pi fun _ : Fin d => gaussianReal 0 1).map sphereNormalize

/-- Draw `u ∼ Unif(S^{d−1})` from the tape: `d` Gaussians, then normalize. Cost `O(d)` (p. 62). -/
noncomputable def drawSphere (d : ℕ) : Prog (Vec d) := do
  let mut g : Vec d := 0
  for i in List.finRange d do
    tick 1
    let x ← drawGauss
    g ← op 1 (Function.update g i x)
  let nu ← nrm g
  let inv ← op 1 (1 / nu)
  scale inv g

/-- The matrix exponential. -/
noncomputable def expM (H : Mat d) : Mat d := NormedSpace.exp H

/-- `P_u(H) = e^{H/2} u uᵀ e^{H/2} / (uᵀ e^H u)`, Eq. (228), p. 45. -/
noncomputable def Pu (H : Mat d) (u : Vec d) : Mat d :=
  (1 / (u ⬝ᵥ (expM H *ᵥ u))) •
    (expM ((1 / 2 : ℝ) • H) * vecMulVec u u * expM ((1 / 2 : ℝ) • H))

/-- `P̄(H) = E_{u ∼ Unif(S^{d−1})}[P_u(H)]`, Eq. (228), p. 45, entrywise.

**Formalization Note.** Entries of `P_u(H)` are bounded on the sphere (the matrix is a projector),
so each Bochner integral is of a bounded measurable function. -/
noncomputable def Pbar (H : Mat d) : Mat d :=
  fun i j => ∫ u, Pu H u i j ∂(sphereLaw d)

end SparseSDP.TwoSided


