-- Prove2me | Definitions.Def_BarelyTestable_LowerBound_Loads
-- name    : BarelyTestable_LowerBound_Loads
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:22:11.105712+00:00
-- url     : https://prove2.me/theorems/2267b416-dd62-4071-a6e2-649b3a888952
-- title:
--   Balanced centers, repair residuals and exact ordered load counts
-- statement:
--   A selector chooses one coordinate in each control block. A set is balanced when each block size lies in the real interval $[m/4+1,3m/4-1]$; both endpoints are inclusive. Balanced centers satisfy this in both halves. For fixed $Y$, the load $L_Y(U)$ counts ordered triples $(X,\Gamma,\Gamma')$ with $(X,Y)$ a center and
--
--   $$U=X\cup\Gamma\quad\text{or}\quad U=X\setminus\Gamma\quad\text{or}\quad U=(X\mathbin\triangle\Gamma)\cup\Gamma'.$$
--
--   A triple is counted once even if several alternatives hold. The exchanged load fixes $X$ and varies the other half. Total squared load is $2\sum_{X,Y}(L_Y(X)^2+L_X(Y)^2)$. For each actual submodular repair $G$, residuals are computed as $G-F^{(-1)}$ on the relevant slice, with the opposite half fixed. No global submodularity of a residual is assumed.
--
--   Within one block, $\gamma_j(X_i,U_i)$ counts ordered coordinate pairs producing $U_i$ by the $j$th operation. The functions $s_j$ and $t_j$ sum these counts and their squares over the prescribed parity class. They are computed from the operations, not supplied as arbitrary numbers satisfying identities. The propagated-pair count records nonzero residuals at at least one of the three candidate sets.
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Definition 3.5, Definition 3.7, residuals and block counts, p. 13–14, 20–21 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Construction

set_option autoImplicit false

namespace BarelyTestable.LowerBound

abbrev Selector (m : ℕ) := Fin m → Fin m

def selected {m : ℕ} (γ : Selector m) : HalfSet m :=
  Finset.univ.image (fun i => (i, γ i))

def xorSet {ι : Type} [DecidableEq ι] (X Y : Cube ι) : Cube ι := (X \ Y) ∪ (Y \ X)

def result {ι : Type} [DecidableEq ι] (j : Fin 3) (X G G' : Cube ι) : Cube ι :=
  if j.val = 0 then X ∪ G else if j.val = 1 then X \ G else xorSet X G ∪ G'

def LeadsTo {ι : Type} [DecidableEq ι] (X G G' U : Cube ι) : Prop :=
  U = X ∪ G ∨ U = X \ G ∨ U = xorSet X G ∪ G'

noncomputable def Balanced {m : ℕ} (X : HalfSet m) : Prop :=
  ∀ i : Fin m, (m : ℝ)/4 + 1 ≤ (block X i).card ∧
    ((block X i).card : ℝ) ≤ 3 * (m : ℝ)/4 - 1

noncomputable def balancedCenters {m : ℕ} (φA φB : LabelMap m) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : HalfSet m × HalfSet m =>
    Center φA φB p.1 p.2 ∧ Balanced p.1 ∧ Balanced p.2)).card

noncomputable def balancedPairs (m : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : HalfSet m × HalfSet m => Balanced p.1 ∧ Balanced p.2)).card

/-- Each ordered triple is counted once, even if two or three alternatives agree. -/
noncomputable def loadY {m : ℕ} (φA φB : LabelMap m) (Y U : HalfSet m) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : HalfSet m × Selector m × Selector m =>
    Center φA φB p.1 Y ∧ LeadsTo p.1 (selected p.2.1) (selected p.2.2) U)).card

noncomputable def loadX {m : ℕ} (φA φB : LabelMap m) (X V : HalfSet m) : ℕ :=
  loadY φB φA X V

noncomputable def sliceLoad {m : ℕ} (φA φB : LabelMap m)
    (X Y : HalfSet m) (a : Bool) : ℕ := if a then loadX φA φB X Y else loadY φA φB Y X

noncomputable def totalSquaredLoad {m : ℕ} (φA φB : LabelMap m) : ℝ :=
  2 * ∑ X : HalfSet m, ∑ Y : HalfSet m,
    ((loadY φA φB Y X : ℝ)^2 + (loadX φA φB X Y : ℝ)^2)

/-- Both slice families in a single definition; side=true fixes Y and varies X. -/
noncomputable def residual {m : ℕ} (r : Sample m) (G : Oracle (Coord m))
    (side : Bool) (fixed : HalfSet m) (τ : Bool) (Z : HalfSet m) : ℝ :=
  let X := if side then Z else fixed
  let Y := if side then fixed else Z
  let a := if side then false else true
  let b := τ
  let S := (X.image (fun x => Sum.inr (Sum.inl x) : Half m → Coord m)) ∪
    (Y.image (fun y => Sum.inr (Sum.inr y) : Half m → Coord m)) ∪
    (if a then {actionA} else ∅) ∪ (if b then {actionB} else ∅)
  G S - slice r false X Y a b

noncomputable def propagatedPairs {m : ℕ} (g : HalfSet m → ℝ) (X : HalfSet m) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : Selector m × Selector m =>
    g (X ∪ selected p.1) ≠ 0 ∨ g (X \ selected p.1) ≠ 0 ∨
      g (xorSet X (selected p.1) ∪ selected p.2) ≠ 0)).card

/-- Single-block counts use ordered coordinate pairs, including the unused second coordinate. -/
noncomputable def blockGamma {m : ℕ} (j : Fin 3) (X U : Cube (Fin m)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : Fin m × Fin m => result j X {p.1} {p.2} = U)).card

noncomputable def blockS {m : ℕ} (j : Fin 3) (π : Bool) (U : Cube (Fin m)) : ℕ :=
  ∑ X : Cube (Fin m), if decide (X.card % 2 = 1) = π then blockGamma j X U else 0

noncomputable def blockT {m : ℕ} (j : Fin 3) (π : Bool) (U : Cube (Fin m)) : ℕ :=
  ∑ X : Cube (Fin m), if decide (X.card % 2 = 1) = π then (blockGamma j X U)^2 else 0

end BarelyTestable.LowerBound


