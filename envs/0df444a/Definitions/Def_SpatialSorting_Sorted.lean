-- Prove2me | Definitions.Def_SpatialSorting_Sorted
-- name    : SpatialSorting_Sorted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:00.268715+00:00
-- url     : https://prove2.me/theorems/298c33c9-7d30-434f-8596-9596997320c4
-- title:
--   The Sorted$(\alpha,\delta)$ event
-- statement:
--   For $\sigma\in\Omega_{\Lambda^L,\rho}$, $\mathsf{Sorted}(\alpha,\delta)$ holds when there is a comparison colouring $\tau:D_L\to\{0,1,\dots,q-1\}$ with $\tau|_{B_L}=0$ whose parts $R_i=\{v\in I_L:\tau_v=i\}$ satisfy
--
--   1. $|\{v\in R_i:\sigma_v\ne i\}|\le\delta|R_i|$ for every $i\in\{0,1,\dots,q-1\}$;
--   2. $H_{\Lambda^L}(\tau)\le\alpha H_*(L,\rho)$.
--
--   The energy is a sum over all heterogeneous edges, including free–boundary ones. The interior counts of $\tau$ need not be those prescribed by $\rho$, and its parts need not be connected.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 1.1, p. 6 (PDF p. 7)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_I
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_HV
import Definitions.Def_SpatialSorting_Hstar
open Classical Filter Topology

namespace SpatialSorting

/-- Definition 1.1: `σ` is `(α, δ)`-sorted when some comparison colouring `τ` with `τ|_{B_L} = 0` has parts `R_i` with at most `δ|R_i|` sites where `σ ≠ i`, and `H(τ) ≤ α H_*(L, ρ)`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 1.1, p. 6 (PDF p. 7). -/
def Sorted {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (ρ : Fin q → ℝ) (L : ℕ)
    (α δ : ℝ) (σ : Coloring q L) : Prop :=
  ∃ τ : Coloring q L,
    (∀ i : Fin q,
      ((((I L).filter (fun v => extendBy 0 (I L) τ v = i ∧ extendBy 0 (I L) σ v ≠ i)).card : ℝ)
        ≤ δ * (((I L).filter (fun v => extendBy 0 (I L) τ v = i)).card : ℝ))) ∧
    HV A (D L) (extendBy 0 (I L) τ) ≤ α * Hstar A ρ L

end SpatialSorting


