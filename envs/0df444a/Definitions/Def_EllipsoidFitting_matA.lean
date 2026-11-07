-- Prove2me | Definitions.Def_EllipsoidFitting_matA
-- name    : EllipsoidFitting_matA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:10.61749+00:00
-- url     : https://prove2.me/theorems/5df15c98-32a8-4c65-a7f5-d49cd2fc97dd
-- title:
--   The matrices $M_\alpha$, $M_\beta$, $M_D$, $A$ and $B$
-- statement:
--   For points $v_1,\dots,v_m\in\mathbb R^d$:
--
--   1. $M_\alpha$ has zero diagonal and $M_\alpha[i,j]=\sum_{a\ne b\in[d]}v_i[a]v_i[b]v_j[a]v_j[b]$ for $i\ne j$;
--   2. $M_\beta$ has zero diagonal and $M_\beta[i,j]=\sum_{a\in[d]}\bigl(v_i[a]^2-\tfrac1d\bigr)\bigl(v_j[a]^2-\tfrac1d\bigr)$ for $i\ne j$;
--   3. $M_D$ is diagonal with $M_D[i,i]=\|v_i\|_2^4-\tfrac2d\|v_i\|_2^2-1$;
--   4. $A=\bigl(1+\tfrac1d\bigr)I_m+M_\alpha+M_\beta+M_D$;
--   5. $B=\tfrac1dJ_m+\tfrac1d\bigl(\mathbf 1_m\eta^\top+\eta\mathbf 1_m^\top\bigr)$, $J_m$ the all-ones matrix.
--
--   $A$ behaves like a Wishart matrix with aspect ratio $\gamma$ and $B$ has rank at most $2$; the decomposition $M=A+B$ reduces inverting $M$ to inverting $A$.
--
--   **Formalization Note** "Off-diagonal" and "diagonal" (p.17) are encoded by zero entries. $\|v_i\|_2^2$ is the dot product $v_i\cdot v_i$.
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), §2.3, eq. (2)–(5), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_EllipsoidFitting_perturbR

set_option autoImplicit false

namespace EllipsoidFitting

open Matrix

/-- **The matrices `M_α`, `M_β`, `M_D`, `A`, `B` of the decomposition `M = A + B`.**
de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase Transition for Ellipsoid Fitting*,
arXiv:2608.12415 (version of Nov 3, 2026), §2.3, eq. (2)–(5), p.17.

`Malpha v` is `M_α`: zero on the diagonal and, for `i ≠ j`,
`M_α[i, j] = ∑_{a ≠ b ∈ [d]} v_i[a] v_i[b] v_j[a] v_j[b]` (eq. (3), first expression).

**Formalization Note** "Mα and Mβ are off-diagonal … matrices" and "MD is diagonal" (p.17): the
entries not given by (3)–(5) are `0`. -/
def Malpha {m d : ℕ} (v : Fin m → Fin d → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if i = j then 0 else ∑ a, ∑ b, if a = b then 0 else v i a * v i b * v j a * v j b

/-- `Mbeta v` is `M_β`: zero on the diagonal and, for `i ≠ j`,
`M_β[i, j] = ∑_{a ∈ [d]} (v_i[a]² − 1/d)(v_j[a]² − 1/d)` (eq. (4)). -/
noncomputable def Mbeta {m d : ℕ} (v : Fin m → Fin d → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if i = j then 0 else ∑ a, (v i a ^ 2 - 1 / (d : ℝ)) * (v j a ^ 2 - 1 / (d : ℝ))

/-- `MD v` is the diagonal matrix `M_D` with `M_D[i, i] = ‖v_i‖₂⁴ − (2/d)‖v_i‖₂² − 1` (eq. (5)).

**Formalization Note** `‖v_i‖₂²` is written `v i ⬝ᵥ v i` (the Euclidean norm; Lean's default
norm on `Fin d → ℝ` is the sup norm and is not used). -/
noncomputable def MD {m d : ℕ} (v : Fin m → Fin d → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if i = j then (v i ⬝ᵥ v i) ^ 2 - (2 / (d : ℝ)) * (v i ⬝ᵥ v i) - 1 else 0

/-- `matA v` is `A := (1 + 1/d) I_m + M_α + M_β + M_D` (eq. (2)). -/
noncomputable def matA {m d : ℕ} (v : Fin m → Fin d → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (1 + 1 / (d : ℝ)) • (1 : Matrix (Fin m) (Fin m) ℝ) + Malpha v + Mbeta v + MD v

/-- `matB v` is `B := (1/d) J_m + (1/d)(1_m ηᵀ + η 1_mᵀ)` (eq. (2)), `J_m` the all-ones matrix. -/
noncomputable def matB {m d : ℕ} (v : Fin m → Fin d → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (1 / (d : ℝ)) • (Matrix.of fun _ _ => (1 : ℝ)) +
    (1 / (d : ℝ)) • (vecMulVec (fun _ => (1 : ℝ)) (eta v) + vecMulVec (eta v) (fun _ => (1 : ℝ)))

end EllipsoidFitting


