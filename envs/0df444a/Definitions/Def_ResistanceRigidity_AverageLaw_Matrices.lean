-- Prove2me | Definitions.Def_ResistanceRigidity_AverageLaw_Matrices
-- name    : ResistanceRigidity_AverageLaw_Matrices
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:05:40.20889+00:00
-- url     : https://prove2.me/theorems/3f7fd60f-9236-4e60-b49a-b237438ef947
-- title:
--   The matrices $Q = L^+$, $z = \mathrm{diag}(Q)$, $P = I - J/N$ and the resistance matrix $R$ (§2)
-- statement:
--   Let $V$ be a finite set of $N$ vertices and let $c : V \times V \to \mathbb R$ be the conductance function of a weighted graph: symmetric, nonnegative and zero on the diagonal, with $c(u,v) > 0$ exactly on the edges (the published `IncrementalER.IsGraph`). Write $L$ for its Laplacian, $L_{uu} = \sum_{w \ne u} c(u,w)$ and $L_{uv} = -c(u,v)$ for $u \ne v$ (the published `IncrementalER.lap`). This definition introduces the four matrices of §2 of the paper:
--
--   - $Q = L^+$, the Moore–Penrose pseudoinverse of $L$ (`pinvLap`);
--   - $z = \mathrm{diag}(Q)$, the vector $z_u = Q_{uu}$ (`diagPinv`);
--   - $P = I - \tfrac1N J$, the orthogonal projection onto the vectors with zero sum, where $J$ is the all-ones matrix (`projOnes`);
--   - the resistance matrix $R$, with entries the effective resistances
--   $$R_{uv} = (e_u - e_v)^\top Q\,(e_u - e_v)$$
--   (`resMat`, built from the published `IncrementalER.reff`); its diagonal is zero.
--
--   These are the objects in which the paper writes the identities $R = z\mathbf 1^\top + \mathbf 1 z^\top - 2Q$ (eq. (1)) and $LR = (Lz)\mathbf 1^\top - 2P$ (eq. (8)).
--
--   **Formalization Note.** $R$ is defined on all pairs of vertices from the pseudoinverse; on a connected graph, the paper's setting, these are the effective resistances.
-- source:
--   Tianlang Chen, A Sharp Rigidity Law for Effective Resistance, STOC 2027 submission (manuscript, sha256 3846da8c…1e8b), p. 5, §2

import Mathlib
import Definitions.Def_IncrementalER_lap

open Matrix

namespace ResistanceRigidity.AverageLaw

/-!
# The matrices Q = L⁺, z = diag(Q), P = I − J/N and the resistance matrix R

Tianlang Chen, *A Sharp Rigidity Law for Effective Resistance*, STOC 2027 submission
(manuscript, sha256 3846da8c…1e8b), §2, p. 5.

A weighted graph is a conductance function `c : V → V → ℝ` (`IncrementalER.IsGraph`), its
Laplacian is `IncrementalER.lap c` and its effective resistance is `IncrementalER.reff c`,
defined with the Moore–Penrose pseudoinverse.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Q = L⁺`, the Moore–Penrose pseudoinverse of the Laplacian. -/
noncomputable def pinvLap (c : V → V → ℝ) : Matrix V V ℝ :=
  IncrementalER.pinvMat (IncrementalER.lap c)

/-- `z = diag(Q)`, the vector of diagonal entries of `Q = L⁺`. -/
noncomputable def diagPinv (c : V → V → ℝ) : V → ℝ :=
  fun u => pinvLap c u u

/-- `P = I − (1/N) J`, the projection orthogonal to the all-ones vector, `N = card V`. -/
noncomputable def projOnes (V : Type*) [Fintype V] [DecidableEq V] : Matrix V V ℝ :=
  1 - ((Fintype.card V : ℝ)⁻¹) • Matrix.of (fun _ _ => (1 : ℝ))

/-- The resistance matrix `R`, with entries `R u v = (e_u − e_v)ᵀ L⁺ (e_u − e_v)`
(zero on the diagonal). -/
noncomputable def resMat (c : V → V → ℝ) : Matrix V V ℝ :=
  Matrix.of fun u v => IncrementalER.reff c u v

end ResistanceRigidity.AverageLaw


