-- Prove2me | Definitions.Def_IntADSat_Supplement_IsPointedIntertwiner
-- name    : IntADSat_Supplement_IsPointedIntertwiner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:44:01.35634+00:00
-- url     : https://prove2.me/theorems/50f9fa6c-cac3-48c3-8404-0d1318d72ca6
-- title:
--   Rational orthogonal pointed AD intertwiner
-- statement:
--   Let $G$ be a graph on $n$ vertices and $H$ a graph on $m$ vertices. An $m\times n$ rational matrix $Q$ is a **rational orthogonal pointed AD intertwiner** from $G$ to $H$ if
--   $$Q^{\mathsf T}Q=I_n,\qquad QQ^{\mathsf T}=I_m,\qquad Qe=e,\qquad QA_G=A_HQ,\qquad QD_G=D_HQ .$$
--   Orthogonality forces $m=n$. Such matrices are the subject of Theorem A.8 (condition 3), Lemma S4.1 and Theorem S4.2.
--
--   **Formalization Note** The integer adjacency and degree matrices are cast entrywise to $\mathbb Q$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorem A.8 (3), p.13 (PDF 14); Lemma S4.1, p.39 (PDF 40)

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat.Supplement

/-- `Q` is a **rational orthogonal pointed AD intertwiner** from `G` to `H`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Theorem A.8 (3), p.13 (PDF 14); Lemma S4.1, p.39 (PDF 40)): a rational orthogonal matrix with
`Qe = e`, `QA_G = A_HQ` and `QD_G = D_HQ`.

**Formalization Note** `Q` is an `m × n` rational matrix (rows indexed by the vertices of `H`, columns
by those of `G`); orthogonality is `QᵀQ = I_n` and `QQᵀ = I_m`, which forces `m = n`. The integer
adjacency and degree matrices are cast entrywise to `ℚ`. -/
def IsPointedIntertwiner {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
    (Q : Matrix (Fin m) (Fin n) ℚ) : Prop :=
  Q.transpose * Q = 1 ∧ Q * Q.transpose = 1 ∧ Q.mulVec (fun _ => 1) = (fun _ => 1) ∧
    Q * (adjacency G).map (Int.cast : ℤ → ℚ) = (adjacency H).map (Int.cast : ℤ → ℚ) * Q ∧
    Q * (degreeMatrix G).map (Int.cast : ℤ → ℚ) = (degreeMatrix H).map (Int.cast : ℤ → ℚ) * Q

end IntADSat.Supplement


