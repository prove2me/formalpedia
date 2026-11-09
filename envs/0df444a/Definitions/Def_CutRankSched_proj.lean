-- Prove2me | Definitions.Def_CutRankSched_proj
-- name    : CutRankSched_proj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:26.938739+00:00
-- url     : https://prove2.me/theorems/1d42c9df-69ff-4ff7-bc2e-0188264c1b38
-- title:
--   Coordinate deletion $\rho_k$
-- statement:
--   The map $\rho_k : \mathbb F_2^{\,n-k} \to \mathbb F_2^{\,n-k-1}$ **deletes the first coordinate**, the column of the event $i = k+1$ being processed. It is linear, and $\rho_k(U)$ denotes the image of a whole subspace $U$.
--
--   **Formalization Note** In the zero-padded encoding of the signatures, $\rho_k$ is the linear map on $\mathbb F_2^n$ that sets the coordinate of event $i$ to $0$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 5.3, p.9

import Mathlib

set_option autoImplicit false

namespace CutRankSched

/-- The coordinate deletion `ρ_k : 𝔽₂^{n−k} → 𝔽₂^{n−k−1}` of §5.3 (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §5.3, p.9), which
deletes the first coordinate (the column of event `i = k + 1`).

**Formalization Note** In the zero-padded encoding of `signature` it is the linear map on
`𝔽₂^n` that sets coordinate `k` (0-based, the column of the 0-based event `k`) to `0`. -/
def proj (n k : ℕ) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  LinearMap.pi fun c : Fin n =>
    if c.val = k then (0 : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) else LinearMap.proj c

end CutRankSched


