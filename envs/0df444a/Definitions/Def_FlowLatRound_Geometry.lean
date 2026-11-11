-- Prove2me | Definitions.Def_FlowLatRound_Geometry
-- name    : FlowLatRound_Geometry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:05.525195+00:00
-- url     : https://prove2.me/theorems/3baeb340-8dbf-413f-8aae-e8dff5b85b87
-- title:
--   §2, p.4 — volume, surface area (Minkowski content), circumradius and the normalized boundary $\Phi(K)=R(K)S(K)/V(K)$
-- statement:
--   For a set $K$ in a finite-dimensional real inner product space $E$ of dimension $r$ (in this mission $E$ is the flow space $H_G\subseteq\mathbb R^m$):
--
--   1. $V(K)$ is its $r$-dimensional volume: the Lebesgue measure of its image under orthonormal coordinates $E\cong\mathbb R^r$;
--   2. $S(K)$ is its surface area, defined as the Minkowski content
--   $$S(K)=\lim_{s\downarrow0}\frac{V(K+sB)-V(K)}{s},$$
--   where $K+sB$ is the closed $s$-neighbourhood of $K$;
--   3. $R(K)=\sup_{x\in K}\|x\|$ is the circumradius;
--   4. $\Phi(K)=R(K)\,S(K)/V(K)$ is the normalized boundary.
--
--   These are the quantities of §2 and of Theorem 1.1. For a convex body the Minkowski content is the surface area (Steiner formula), and the volume does not depend on the orthonormal basis.
--
--   **Formalization Note** Mathlib's Hausdorff measure is not used for $S$: it is not normalized like Lebesgue measure. For the segment $[-\tfrac12,\tfrac12]\subset\mathbb R$ these definitions give $V=1$, $S=2$ (checked in the mission's verification file). `limUnder` and `sSup` take default values when the limit does not exist or the set is unbounded; the cells of this mission are nonempty polytopes.
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), §2 Notation, p.4 (PDF 6); Φ(K), p.1 (PDF 3); Steiner formula, proof of Lemma B.2, p.19 (PDF 21)

import Mathlib

namespace FlowLatRound

open MeasureTheory Filter Topology

/-! # Volume, surface area, circumradius and the normalized boundary Φ

Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027
submission, sha256 35bd3e4b…aeac), §2 Notation, p.4 (PDF 6); Φ(K) = R(K)S(K)/V(K), p.1 (PDF 3);
the Steiner formula S(K) = lim_{s↓0} (V(K + sB) − V(K))/s, proof of Lemma B.2, p.19 (PDF 21).

**Formalization Note.** A convex body lives in a finite-dimensional real inner product space `E`
(in this mission `E` is the flow space `H_G`, a subspace of `ℝ^m`). Its volume is the Lebesgue
measure of its image under the coordinate isometry `E ≃ₗᵢ ℝ^r` of `stdOrthonormalBasis`; this
does not depend on the orthonormal basis (isometries of `ℝ^r` preserve Lebesgue measure), and
the unit cube of an orthonormal frame has volume `1`. The surface area is the **Minkowski
content** `lim_{s↓0} (V(K_s) − V(K))/s`, `K_s` the closed `s`-thickening, which is the surface
area for convex bodies (Steiner formula). Mathlib's Hausdorff measure `μH[r-1]` is deliberately
not used: it is not normalized like Lebesgue measure, and a dimension-dependent constant would
change Φ. Junk values: `limUnder` is a default when the limit does not exist and `sSup` is `0`
on unbounded or empty sets; the bodies of this mission are nonempty polytopes, for which the
limit exists and the supremum is a maximum. -/

/-- The `r`-dimensional volume `V(K)` of a set `K` in a finite-dimensional real inner product
space `E` of dimension `r`: the Lebesgue measure of its image under the orthonormal coordinates
`stdOrthonormalBasis ℝ E`, as a real number (§2 Notation, p.4). -/
noncomputable def cellVol {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E) : ℝ :=
  (volume ((stdOrthonormalBasis ℝ E).repr '' K)).toReal

/-- The surface area `S(K)` as the Minkowski content
`lim_{s↓0} (V(K + sB) − V(K))/s` (Steiner formula, proof of Lemma B.2, p.19), where
`K + sB = Metric.cthickening s K` is the closed `s`-neighbourhood of `K` in `E`. -/
noncomputable def cellSurf {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun s => (cellVol (Metric.cthickening s K) - cellVol K) / s)

/-- The circumradius `R(K) = max_{x ∈ K} ‖x‖` (§2 Notation, p.4), as a supremum. -/
noncomputable def circumradius {E : Type*} [Norm E] (K : Set E) : ℝ :=
  sSup ((fun x => ‖x‖) '' K)

/-- The normalized boundary `Φ(K) = R(K) S(K) / V(K)` (p.1). -/
noncomputable def Phi {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E) : ℝ :=
  circumradius K * cellSurf K / cellVol K

end FlowLatRound


