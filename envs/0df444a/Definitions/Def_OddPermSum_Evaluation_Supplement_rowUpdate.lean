-- Prove2me | Definitions.Def_OddPermSum_Evaluation_Supplement_rowUpdate
-- name    : OddPermSum_Evaluation_Supplement_rowUpdate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:37:10.946877+00:00
-- url     : https://prove2.me/theorems/4995cb8e-f6fe-4c4a-b6af-29e6e3a2fc04
-- title:
--   Rank-one row increments and the fixed Boolean border
-- statement:
--   For an index $i$ and a row $\rho$, define $A'=A+e_i\rho$. For a stored inverse $B$, put $\eta=1+(\rho B)_i$. The candidate updated inverse is
--   $$B+\eta^{-1}(Be_i)(\rho B).$$
--   Here $\eta^{-1}$ is the ring inverse and is used as an inverse only when $\eta$ is a unit. The border $M_b(X)$ is the published border with one new last index, row and column basis vector $e_u$, and bottom-right entry $b$.
--
--   These definitions construct the source's matrices rather than assuming arbitrary objects with their desired properties.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 19–20, Eqs. (6.8), (6.11), (6.12)

import Definitions.Def_OddPermSum_Evaluation_border

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

noncomputable def rowUpdate {R : Type*} [CommRing R] {s : ℕ}
    (A : Matrix (Fin s) (Fin s) R) (i : Fin s) (ρ : Fin s → R) : Matrix (Fin s) (Fin s) R :=
  fun p j => A p j + if p = i then ρ j else 0

noncomputable def updateEta {R : Type*} [CommRing R] {s : ℕ}
    (B : Matrix (Fin s) (Fin s) R) (i : Fin s) (ρ : Fin s → R) : R :=
  1 + ∑ j, ρ j * B j i

noncomputable def inverseUpdate {R : Type*} [CommRing R] {s : ℕ}
    (B : Matrix (Fin s) (Fin s) R) (i : Fin s) (ρ : Fin s → R) : Matrix (Fin s) (Fin s) R :=
  fun p q => B p q + Ring.inverse (updateEta B i ρ) * B p i * (∑ j, ρ j * B j q)

noncomputable def fixedBorder {R : Type*} [CommRing R] {n : ℕ}
    (u : Fin n) (X : Matrix (Fin n) (Fin n) R) (b : R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  border (fun _ : Fin 1 => u) (fun _ : Fin 1 => u) X (fun _ => b)

end OddPermSum.Evaluation.Supplement


