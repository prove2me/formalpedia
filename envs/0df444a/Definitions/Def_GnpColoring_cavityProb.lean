-- Prove2me | Definitions.Def_GnpColoring_cavityProb
-- name    : GnpColoring_cavityProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:49.039028+00:00
-- url     : https://prove2.me/theorems/ec779ba5-1859-4e0d-ade9-9336058862fc
-- title:
--   The cavity probability $p^\sigma_\rho(c)$ (Definition 3.8)
-- statement:
--   $p^\sigma_\rho(c)=\mathbb P_\mu[\sigma_\rho=c\mid\sigma_{V\setminus B}]$: the probability that the port $\rho$ gets colour $c$ given the colours outside the block $B$.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Definition 3.8, p.18

import Mathlib
import Definitions.Def_SpinGirth5_heatBath

open scoped Classical
open Finset

namespace GnpColoring

/-- **The cavity probability** `p^σ_ρ(c) = P_µ[σ_ρ = c | σ_{V∖B}]` (Definition 3.8).

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Definition 3.8, p.18. -/
noncomputable def cavityProb {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (B : Finset (Fin n)) (ρ : Fin n)
    (c : Fin q) (σ : Fin n → Fin q) : ℝ :=
  SpinGirth5.condExp μ (univ \ B) (fun y => if y ρ = c then 1 else 0) σ

end GnpColoring


