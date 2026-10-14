-- Prove2me | Definitions.Def_KerrBL_CoordGeometry
-- name    : KerrBL_CoordGeometry
-- status  : Definition
-- author  : @He Wang
-- created : 2026-09-09T09:25:50.404315+00:00
-- url     : https://prove2.me/theorems/bbec007a-159a-4623-916d-f1cafab3e353
-- title:
--   Generic coordinate Christoffel symbols and Ricci tensor on $\mathbb{R}^4$
-- statement:
--   This bundle is the specification layer of the mission: it fixes what *partial derivative*, *Christoffel symbol* and *Ricci tensor* mean for a matrix of real-valued functions on $\mathbb R^4$. No manifold, chart or signature is involved.
--
--   A point is a function $x:\{0,1,2,3\}\to\mathbb R$ (`Pt`). For $f:\mathbb R^4\to\mathbb R$ the coordinate partial derivative is the one-variable Mathlib derivative of the slice through $x$ along coordinate $i$:
--
--   $$\partial_i f(x) := \frac{d}{du}\Big|_{u=x_i} f\big(x[i\mapsto u]\big).$$
--
--   Given two $4\times 4$ matrices of functions $g$ and $\hat g$ (a metric and a candidate inverse, both taken as data), the Christoffel symbols and the Ricci tensor are the standard coordinate formulas
--
--   $$\Gamma^a_{bc} := \tfrac12\sum_{k}\hat g^{ak}\big(\partial_c g_{kb}+\partial_b g_{kc}-\partial_k g_{bc}\big),$$
--
--   $$R_{bd} := \sum_{i}\Big(\partial_i\Gamma^i_{bd}-\partial_d\Gamma^i_{bi}+\sum_{j}\big(\Gamma^i_{ij}\Gamma^j_{bd}-\Gamma^i_{dj}\Gamma^j_{bi}\big)\Big),$$
--
--   and `ricciOf g ĝ` composes the two.
--
--   Together with the metric transcription in `KerrBL_Kerr_Metric`, these 45 lines are the trusted computing base of the mission: every later statement about Kerr is a statement about these definitions. The index placement and contraction pattern mirror the SymPy verifier of the parent project (`knads_verifier.py`).
--
--   **Formalization Note** Mathlib's `deriv` returns $0$ where a slice is not differentiable. The mission therefore proves explicit `HasDerivAt` statements for every slice it differentiates, so no such junk value is ever used. The inverse $\hat g$ is a free argument rather than `Matrix.inv`; the mission certifies separately that the chosen $\hat g$ is a left inverse of $g$.
-- source:
--   R. P. Kerr, Gravitational field of a spinning mass as an example of algebraically special metrics, Phys. Rev. Lett. 11 (1963) 237-238, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer and R. W. Lindquist, Maximal analytic extension of the Kerr metric, J. Math. Phys. 8 (1967) 265-281, https://doi.org/10.1063/1.1705193, Sec. 2 (Boyer-Lindquist form of the Kerr line element); metric components transcribed token-for-token from the project certificate EinsteinSolver/certificate/kerr/metric.json (sha256 d729883d95fd7d3cf84d9c971c6725f847155562cc4e88660535b8d0bd0be336); design record LEAN/kerr-formalization/mission/DESIGN.md, definition bundle D1 (hand-written)

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Coordinate differential geometry on ℝ⁴ (hand-written specification layer)

Coordinates are indexed by `Fin 4` with the fixed meaning `0 = t, 1 = r, 2 = θ, 3 = φ`.
A metric is a matrix of real functions on coordinate points; nothing here is a manifold.

Conventions (mirroring `pipeline/knads_verifier.py` of the exact_bh repository, functions
`christoffel_symbols_symbolic` and `ricci_tensor_symbolic`, verbatim index order):

* `Γ^a_{bc} = (Σ_d g^{ad} (∂_c g_{db} + ∂_b g_{dc} − ∂_d g_{bc})) / 2`
* `R_{bd} = Σ_a ( ∂_a Γ^a_{bd} − ∂_d Γ^a_{ba} + Σ_c ( Γ^a_{ac} Γ^c_{bd} − Γ^a_{dc} Γ^c_{ba} ) )`

Partial derivatives are Mathlib's `deriv` of the one-variable slice obtained by
`Function.update`; at non-differentiable points `deriv` returns the junk value `0`,
so every theorem about these objects carries explicit regularity hypotheses.
-/

namespace KerrBL

/-- A coordinate point `(t, r, θ, φ)` of ℝ⁴, indexed by `Fin 4`. -/
abbrev Pt := Fin 4 → ℝ

/-- Partial derivative `∂_i f` at `x`: the derivative of the slice `u ↦ f (x with x_i := u)`. -/
noncomputable def pd (i : Fin 4) (f : Pt → ℝ) (x : Pt) : ℝ :=
  deriv (fun u : ℝ => f (Function.update x i u)) (x i)

/-- Coordinate Christoffel symbols `Γ^a_{bc}` built from a metric `g` and a candidate
inverse `ginv` by the standard formula (index order mirrors `knads_verifier.py`). -/
noncomputable def christoffel (g ginv : Fin 4 → Fin 4 → Pt → ℝ) (a b c : Fin 4) (x : Pt) : ℝ :=
  (∑ k : Fin 4, ginv a k x * (pd c (g k b) x + pd b (g k c) x - pd k (g b c) x)) / 2

/-- Coordinate Ricci tensor `R_{bd}` from Christoffel symbols
(sign and contraction convention mirrors `knads_verifier.ricci_tensor_symbolic`). -/
noncomputable def ricci (Γ : Fin 4 → Fin 4 → Fin 4 → Pt → ℝ) (b d : Fin 4) (x : Pt) : ℝ :=
  ∑ i : Fin 4, (pd i (Γ i b d) x - pd d (Γ i b i) x
    + ∑ j : Fin 4, (Γ i i j x * Γ j b d x - Γ i d j x * Γ j b i x))

/-- Ricci tensor of a metric `g` with candidate inverse `ginv`. -/
noncomputable def ricciOf (g ginv : Fin 4 → Fin 4 → Pt → ℝ) : Fin 4 → Fin 4 → Pt → ℝ :=
  ricci (christoffel g ginv)

end KerrBL


