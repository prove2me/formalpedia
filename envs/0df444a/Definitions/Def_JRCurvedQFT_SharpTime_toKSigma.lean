-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_toKSigma
-- name    : JRCurvedQFT_SharpTime_toKSigma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:43.419206+00:00
-- url     : https://prove2.me/theorems/b653624d-4718-42db-ba5d-e39829c9ef54
-- title:
--   A function on $\Sigma$ as a vector of $\mathcal K_\Sigma$
-- statement:
--   A complex function $u$ that is square integrable for $\nu$ defines its class in $L^2(\nu;\mathbb C)$; for $\nu=\sqrt{\mathcal G}\,dx$ this is a vector of $\mathcal K_\Sigma=L^2(\Sigma,\sqrt{\mathcal G}\,dx)$ of (4.6).
--
--   **Formalization Note** Functions that are not square integrable are sent to $0$; every use is on continuous functions with compact support on $\Sigma$.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, Eq. (4.6), p. 21

import Mathlib

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

/-- A function on the slice as a vector of `𝒦_Σ = L²(Σ, √𝒢 dx; ℂ)` (or of any `L²(ν; ℂ)`).

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, (4.6), p. 21: `𝒦_Σ := L²(Σ, √𝒢 dx)`.

**Formalization Note** Returns the `L²` class of `u` when `u ∈ L²(ν)` and the junk `0` otherwise;
every use applies it to functions that are in `L²` (continuous with compact support on `Σ`). -/
noncomputable def toKSigma {X : Type} [MeasurableSpace X] (ν : Measure X) (u : X → ℂ) :
    Lp ℂ 2 ν :=
  open Classical in
  if h : MemLp u 2 ν then h.toLp u else 0

end JRCurvedQFT.SharpTime


