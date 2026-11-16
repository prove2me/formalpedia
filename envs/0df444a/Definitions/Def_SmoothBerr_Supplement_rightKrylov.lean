-- Prove2me | Definitions.Def_SmoothBerr_Supplement_rightKrylov
-- name    : SmoothBerr_Supplement_rightKrylov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:53:46.770798+00:00
-- url     : https://prove2.me/theorems/a19c0529-470c-42f4-821a-5cb1280e8c1d
-- title:
--   Krylov subspace $K_k(M,v)$ and right-side Krylov subspace $R_k(A,b)$
-- statement:
--   The **Krylov subspace of degree $k$** of a matrix $M$ and a vector $v$ is
--   $$
--   K_k(M,v):=\operatorname{span}\{v,Mv,M^2v,\dots,M^kv\},
--   $$
--   spanned by $k+1$ vectors. The **right-side Krylov subspace** of $A$ and $b$ is the Krylov subspace of the normal equations $A^\top Ax=A^\top b$:
--   $$
--   R_k(A,b):=K_k(A^\top A,A^\top b).
--   $$
--   Building $R_k(A,b)$ takes $2k+1$ matvecs with $A$ or $A^\top$. It is the space a Krylov method on the normal equations searches.
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), §3, p.5 (K_t(A, b)); §6, p.16 (R_k(A, b) := K_k(A^⊤A, A^⊤b))

import Mathlib

open Matrix

namespace SmoothBerr.Supplement

/-- The **Krylov subspace of degree `k`**, `K_k(M, v) := span{v, Mv, M²v, …, M^k v}` (`k + 1`
generators) (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The
power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, §3, p.5). -/
noncomputable def krylov {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (k : ℕ) :
    Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ (Set.range fun j : Fin (k + 1) => (M ^ (j : ℕ)) *ᵥ v)

/-- The **right-side Krylov subspace** `R_k(A, b) := K_k(AᵀA, Aᵀb)` (manuscript of 3 Nov 2026,
§6, p.16), the Krylov subspace of the normal equations `AᵀA x = Aᵀb`; building it takes
`2k + 1` matvecs with `A` or `Aᵀ`. -/
noncomputable def rightKrylov {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (k : ℕ) :
    Submodule ℝ (Fin n → ℝ) :=
  krylov (Aᵀ * A) (Aᵀ *ᵥ b) k

end SmoothBerr.Supplement


