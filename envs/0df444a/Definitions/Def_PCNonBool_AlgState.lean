-- Prove2me | Definitions.Def_PCNonBool_AlgState
-- name    : PCNonBool_AlgState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:02.14802+00:00
-- url     : https://prove2.me/theorems/2ba5bf4a-d2b4-4797-83a3-591bc9678d02
-- title:
--   State of Algorithm 1
-- statement:
--   A **state** of Algorithm 1 after round $\ell$ records the current sequence of polynomials $\pi_\ell$, the remaining pigeons $U_\ell$ and holes $V_\ell$, so that the current graph is $G_\ell=G[U_\ell\sqcup V_\ell]$, and the set $C_\ell=\bigcup_{\ell'\le\ell}S_{\ell'}$ of pigeons removed by the matchings so far.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Algorithm 1 and Proposition 5.12, p.30 (PDF p.33)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var

namespace PCNonBool

/-- A state of Algorithm 1 (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.30 (PDF p.33)) after some round `ℓ`: the current
sequence `π_ℓ`, the remaining pigeons `U_ℓ` and holes `V_ℓ` (so `G_ℓ = G[U_ℓ ⊔ V_ℓ]`), and the
set `C_ℓ = ⋃_{ℓ' ≤ ℓ} S_{ℓ'}` of pigeons matched so far (Proposition 5.12). The cumulative
restriction `ρ_ℓ` has already been applied to `π_ℓ`. -/
structure AlgState {F : Type*} [Field F] {U V : Type*} (G : BipGraph U V) where
  /-- the current sequence `π_ℓ` -/
  π : List (MvPolynomial (Var G) F)
  /-- the remaining pigeons `U_ℓ` -/
  Ua : Finset U
  /-- the remaining holes `V_ℓ` -/
  Va : Finset V
  /-- the matched pigeons `C_ℓ = ⋃_{ℓ' ≤ ℓ} S_ℓ'` -/
  C : Finset U

end PCNonBool


