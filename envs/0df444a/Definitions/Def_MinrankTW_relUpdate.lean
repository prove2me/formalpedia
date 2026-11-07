-- Prove2me | Definitions.Def_MinrankTW_relUpdate
-- name    : MinrankTW_relUpdate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:51.081042+00:00
-- url     : https://prove2.me/theorems/f68ecf9e-0df8-496d-aefc-b1a5cd25e94b
-- title:
--   Relation updates of the one-entry recursion
-- statement:
--   The relation-update table of Section 3.2 gives the new linear relation $R'$ from the child relation $R$:
--
--   1. introduce a row: $\{(x,(y,0)) : (x,y)\in R\}$;
--   2. introduce a column: $\{((x,v),y) : (x,y)\in R,\ v\in\mathbb F_q\}$;
--   3. assign value $\alpha$ to entry $(i,j)$: $\{(x,y+\alpha x_je_i) : (x,y)\in R\}$;
--   4. forget row $i$: $\{(x,y_{-i}) : (x,y)\in R,\ y_i=0\}$;
--   5. forget column $j$: $\{(x_{-j},y) : (x,y)\in R\}$.
--
--   Here $e_i$ is the unit vector of row coordinate $i$ and a subscript $-i$ deletes coordinate $i$.
--
--   **Formalization Note** In ambient coordinates appending a zero coordinate and deleting a coordinate both set that coordinate to $0$, and appending a free coordinate adds the line spanned by $(e_j,0)$.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 3.2, p.11, relation-update table

import Mathlib

namespace MinrankTW

/-!
# The relation updates of the one-entry recursion

Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §3.2, p.11, the relation-update table: from the child relation `R`,
introduce row: `{(x, (y, 0)) : (x, y) ∈ R}`; introduce column: `{((x, v), y) : (x, y) ∈ R,
v ∈ F_q}`; assign entry `(i, j)` with value `α`: `{(x, y + α x_j e_i) : (x, y) ∈ R}`;
forget row `i`: `{(x, y_{−i}) : (x, y) ∈ R, y_i = 0}`; forget column `j`:
`{(x_{−j}, y) : (x, y) ∈ R}`.

**Formalization Note** Ambient coordinates (as in `relOfPartial`): `x ∈ F^n`, `y ∈ F^m`.
Appending a coordinate with value `0` and deleting a coordinate are both setting that coordinate
to `0` (`zeroAt`); appending a free coordinate `v` adds the line spanned by `(e_j, 0)`.
-/

variable {F : Type*} [Field F] {m n : ℕ}

/-- The linear map setting coordinate `k` to `0`. -/
def zeroAt {ι : Type*} [DecidableEq ι] (k : ι) : (ι → F) →ₗ[F] (ι → F) :=
  LinearMap.pi fun l => if l = k then 0 else LinearMap.proj l

/-- Introduce row `i`: `{(x, (y, 0)) : (x, y) ∈ R}`. -/
def introRowRel (i : Fin m) (R : Submodule F ((Fin n → F) × (Fin m → F))) :
    Submodule F ((Fin n → F) × (Fin m → F)) :=
  R.map (LinearMap.prodMap LinearMap.id (zeroAt i))

/-- Introduce column `j`: `{((x, v), y) : (x, y) ∈ R, v ∈ F}`. -/
def introColRel (j : Fin n) (R : Submodule F ((Fin n → F) × (Fin m → F))) :
    Submodule F ((Fin n → F) × (Fin m → F)) :=
  R.map (LinearMap.prodMap (zeroAt j) LinearMap.id) ⊔
    Submodule.span F {((Pi.single j 1 : Fin n → F), (0 : Fin m → F))}

/-- Assign value `α` to entry `(i, j)`: `{(x, y + α x_j e_i) : (x, y) ∈ R}`. -/
def assignRel (i : Fin m) (j : Fin n) (α : F) (R : Submodule F ((Fin n → F) × (Fin m → F))) :
    Submodule F ((Fin n → F) × (Fin m → F)) :=
  R.map ((LinearMap.fst F (Fin n → F) (Fin m → F)).prod
    (LinearMap.snd F (Fin n → F) (Fin m → F) +
      (LinearMap.single F (fun _ : Fin m => F) i).comp
        ((α • LinearMap.proj j).comp (LinearMap.fst F (Fin n → F) (Fin m → F)))))

/-- Forget row `i`: `{(x, y_{−i}) : (x, y) ∈ R, y_i = 0}`. -/
def forgetRowRel (i : Fin m) (R : Submodule F ((Fin n → F) × (Fin m → F))) :
    Submodule F ((Fin n → F) × (Fin m → F)) :=
  (R ⊓ LinearMap.ker ((LinearMap.proj i).comp (LinearMap.snd F (Fin n → F) (Fin m → F)))).map
    (LinearMap.prodMap LinearMap.id (zeroAt i))

/-- Forget column `j`: `{(x_{−j}, y) : (x, y) ∈ R}`. -/
def forgetColRel (j : Fin n) (R : Submodule F ((Fin n → F) × (Fin m → F))) :
    Submodule F ((Fin n → F) × (Fin m → F)) :=
  R.map (LinearMap.prodMap (zeroAt j) LinearMap.id)

end MinrankTW


