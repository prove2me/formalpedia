-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P58
-- name    : QAlgorithms_Papers_Independent_Intake100_P58
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T14:02:20.771879+00:00
-- url     : https://prove2.me/theorems/18012c17-f8a8-48bc-8062-c489987700e4
-- title:
--   Definitions for The cyclotomic BMW algebra associated with the two string type B braid group
-- statement:
--   The objects the formalized statements of *The cyclotomic BMW algebra associated with the two string type B braid group* (arXiv:math/0611518) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `TwoStrandBMW`: The actual two-strand presentation of (1)--(6), PDF p.3.
--   - `x`: X, X inverse, Y, Y inverse and e in the presented algebra, PDF p.3.
--   - `xInv`: The actual inverse of X, Definition 2.1, PDF p.3.
--   - `y`: The actual Y generator, Definition 2.1, PDF p.3.
--   - `yInv`: The actual inverse of Y, Definition 2.1, PDF p.3.
--   - `e`: The actual e generator, Definition 2.1, PDF p.3.
--   - `RegularDelta`: Assumption 2.2, PDF p.3: multiplication by skeinDelta is injective.
--   - `qAt`: q_k=-1, PDF p.4. Values beyond k are unused and are set to zero.
--   - `aAt`: The specified loop coefficients; zero outside their defining range, PDF p.2.
--   - `admissibilityBeta`: The parity term in admissibilityBeta, PDF pp.7--8: 1-epsilon is 1 for even k.
--   - `hCoeff`: The explicit h_l of Definition 3.1, PDF p.8, used only for 1<=l<k. All finite intervals are inclusive, and empty intervals contribute zero.
--   - `TwoStrandAdmissible`: Definition 3.1, PDF p.8. Its ground relation is already a field of P; regularity is carried separately, to make assumption changes explicit.
--   - `CompanionModule`: The fixed coordinate free module of Section 3, PDF p.5.
--   - `vBasis`: The standard coordinate basis of CompanionModule, PDF p.5.
--   - `vNat`: Standard v_i in range; the out-of-range value is unused, PDF p.5.
--   - `Yv`: Companion map (8)--(9), PDF p.5.
--   - `YvInv`: The explicit inverse (10)--(11), PDF p.5; it is constructed before its inverse identities are asserted.
--   - `orbitVector`: Signed orbit indices v_s=Y^s v_0 using the explicit inverse, PDF p.5.
--   - `xColumn`: The recursive columns (14)--(16), PDF p.5. Only columns 0<=i<k are used to define X. In particular the i=1 clause is not used at k=1.
--   - `Xv`: The constructed X of (14)--(16), PDF p.5.
--   - `Ev`: The constructed E of (17), PDF p.5.
--   - `Wv`: W=X-skeinDelta+skeinDelta E, PDF p.5. Multiplication of endomorphisms is composition with the rightmost factor acting first.
--   - `Nv`: N is the computed defect of Section 3, PDF p.9.
--   - `XiIndex`: Coordinates of the three tagged tensor bases, PDF pp.11--12.
--   - `Xi`: Xi=(CompanionModule tensor CompanionModule) direct sum (CompanionModule tensor CompanionModule) direct sum (CompanionModule tensor CompanionModule), in canonical tensor coordinates, PDF p.11.
--   - `xiBasis`: The specified three-copy tensor basis, PDF p.11.
--   - `tensorIn`: Pure tensor a tensor b in tag t: t=0,1,2 means orbitVector,u,w, PDF p.11.
--   - `tensorLabel`: Signed integer tensor labels v_ij,u_ij,w_ij, PDF p.11.
--   - `euColumn`: E u_ij = v_00 Y^i X Y^j. Reversal makes its second tensor factor Y^j X Y^i v_0, in that order, PDF pp.11--12, equation (33).
--   - `Exi`: E on all three tensor summands, equations (17),(33),(34), PDF p.12.
--   - `Xxi`: X on the three summands, equations (14)--(16),(35),(36), PDF p.12.
--   - `Wxi`: W=X-skeinDelta+skeinDelta E on Xi, PDF p.12.
--   - `Yxi`: Y on the three summands, equations (32),(37),(38), PDF p.12. The w-column is computed using the already constructed W, so there is no circular definition or arbitrary operator witness.
--   - `OperatorRelations`: The six identity groups (25)--(30) / (40)--(45), PDF pp.10,13.
--   - `CompatibleV`: A genuine compatible unital R-algebra representation on the fixed CompanionModule; existence of such a map is a conclusion, PDF p.11.
--   - `CompatibleXi`: The specified unital algebra representation on Xi, PDF p.13.
--   - `basisWord`: The ordered basisWord family of Theorem 4.3, PDF p.17. Tag 0,1,2 means Y^i e Y^j, Y^i X Y^j, X Y^i X Y^j respectively.
--   - `wordMap`: The particular R-linear wordMap of Theorem 4.3, PDF p.17.
--   - `wordSpan`: The unconditional spanning submodule, PDF p.19.
--   - `principalEIdeal`: The principal LEFT ideal, PDF p.4, encoded as an R-submodule.
--   - `twoSidedIdeal`: The actual two-sided e-generated ideal, PDF pp.4,18.
--   - `column`: The j-th named column submodule of Corollary 4.4, PDF p.18.
--   - `HeckeLetter`: Free words for the paper's normalized two-generator NormalizedHecke algebra, PDF p.4.
--   - `ht`: A free NormalizedHecke generator, PDF p.4.
--   - `NormalizedHeckeRel`: The INDEPENDENT normalized Hecke presentation of PDF p.4. There are no TwoStrandBMW relations or e-generator here; T1^2=skeinDelta T1+1.
--   - `NormalizedHecke`: h_2^k(R) with the source's normalization, PDF p.4.
--   - `heckeGen`: The actual normalized Hecke generators, PDF p.4.
--   - `EQuotient`: The actual quotient of TwoStrandBMW by its two-sided e-ideal, PDF p.4.
--   - `eQuotientMap`: The canonical map to that quotient, PDF p.4.
-- source:
--   The cyclotomic BMW algebra associated with the two string type B braid group, arXiv:math/0611518v3, https://arxiv.org/abs/math/0611518v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01

/-!
Wilcox--Yu, arXiv:math/0611518v3. Statement targets only.
The accepted nonsplit presentation at n=2 has exactly the six relations of
Definition 2.1 here (its separate square-e relation is the m=0 loop relation).
The ground data, skein scalar, BMW presentation, generators and e-quotient
are reused from the accepted library. All remaining constructions are local
to this paper and carry distinct concept names; unrelated accepted short names
are not mathematical reuse candidates. Tensor products of finite
coordinate free modules are represented in their canonical tensor coordinates.
No nonzero-ring, split-polynomial, unit-A0, or unit-delta assumption is made.
Compilation is pending the batch handoff.
-/

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intake100.P58

namespace Accepted

export QAlgorithms.Papers.Independent.Gap48.P01
  (NonsplitParameters NonsplitBMW skeinDelta X Y E eIdeal HeckeQuotient)

end Accepted

open Accepted

variable {R : Type*} [CommRing R] {k : ℕ}

/-- The actual two-strand presentation of (1)--(6), PDF p.3. -/
abbrev TwoStrandBMW (P : NonsplitParameters R k) := Accepted.NonsplitBMW P 2

/-- X, X inverse, Y, Y inverse and e in the presented algebra, PDF p.3. -/
def x (P : NonsplitParameters R k) : TwoStrandBMW P := Accepted.X P 2 1 false

/-- The actual inverse of X, Definition 2.1, PDF p.3. -/
def xInv (P : NonsplitParameters R k) : TwoStrandBMW P := Accepted.X P 2 1 true

/-- The actual Y generator, Definition 2.1, PDF p.3. -/
def y (P : NonsplitParameters R k) : TwoStrandBMW P := Accepted.Y P 2 false

/-- The actual inverse of Y, Definition 2.1, PDF p.3. -/
def yInv (P : NonsplitParameters R k) : TwoStrandBMW P := Accepted.Y P 2 true

/-- The actual e generator, Definition 2.1, PDF p.3. -/
def e (P : NonsplitParameters R k) : TwoStrandBMW P := Accepted.E P 2 1

/-- Assumption 2.2, PDF p.3: multiplication by skeinDelta is injective. -/
def RegularDelta (P : NonsplitParameters R k) : Prop :=
  Function.Injective (fun r : R => skeinDelta P * r)

/-- q_k=-1, PDF p.4. Values beyond k are unused and are set to zero. -/
def qAt (P : NonsplitParameters R k) (i : ℕ) : R :=
  if h : i < k then P.coeff ⟨i, h⟩ else if i = k then -1 else 0

/-- The specified loop coefficients; zero outside their defining range, PDF p.2. -/
def aAt (P : NonsplitParameters R k) (i : ℕ) : R :=
  if h : i < k then P.loop ⟨i, h⟩ else 0

/-- The parity term in admissibilityBeta, PDF pp.7--8: 1-epsilon is 1 for even k. -/
def admissibilityBeta (P : NonsplitParameters R k) : R :=
  (P.constant : R) * (P.lam : R) - (↑P.constant⁻¹ : R) * (↑P.lam⁻¹ : R) +
    (if Even k then skeinDelta P else 0)

/-- The explicit h_l of Definition 3.1, PDF p.8, used only for 1<=l<k.
All finite intervals are inclusive, and empty intervals contribute zero. -/
def hCoeff (P : NonsplitParameters R k) (l : ℕ) : R :=
  (↑P.lam⁻¹ : R) * (qAt P l + (↑P.constant⁻¹ : R) * qAt P (k-l)) +
    skeinDelta P * ((∑ r ∈ Finset.Icc 1 (k-l), qAt P (r+l) * aAt P r) -
      (∑ i ∈ Finset.Icc (max (l+1) ((k+1)/2)) ((l+k)/2), qAt P (2*i-l)) +
      (∑ i ∈ Finset.Icc ((l+1)/2) (min l ((k+1)/2-1)), qAt P (2*i-l)))

/-- Definition 3.1, PDF p.8. Its ground relation is already a field of P;
regularity is carried separately, to make assumption changes explicit. -/
def TwoStrandAdmissible (P : NonsplitParameters R k) : Prop :=
  admissibilityBeta P = 0 ∧ ∀ l : ℕ, 1 ≤ l → l < k → hCoeff P l = 0

/-- The fixed coordinate free module of Section 3, PDF p.5. -/
abbrev CompanionModule (P : NonsplitParameters R k) := Fin k → R

/-- The standard coordinate basis of CompanionModule, PDF p.5. -/
def vBasis (P : NonsplitParameters R k) : Module.Basis (Fin k) R (CompanionModule P) := Pi.basisFun R (Fin k)

/-- Standard v_i in range; the out-of-range value is unused, PDF p.5. -/
def vNat (P : NonsplitParameters R k) (i : ℕ) : CompanionModule P :=
  if h : i < k then vBasis P ⟨i, h⟩ else 0

/-- Companion map (8)--(9), PDF p.5. -/
def Yv (P : NonsplitParameters R k) : Module.End R (CompanionModule P) :=
  (vBasis P).constr R fun i =>
    if h : i.val + 1 < k then vBasis P ⟨i.val+1, h⟩
    else ∑ j : Fin k, P.coeff j • vBasis P j

/-- The explicit inverse (10)--(11), PDF p.5; it is constructed before
its inverse identities are asserted. -/
def YvInv (P : NonsplitParameters R k) : Module.End R (CompanionModule P) :=
  (vBasis P).constr R fun i =>
    if i.val = 0 then
      -(↑P.constant⁻¹ : R) • (∑ j : Fin k, qAt P (j.val+1) • vBasis P j)
    else vNat P (i.val-1)

/-- Signed orbit indices v_s=Y^s v_0 using the explicit inverse, PDF p.5. -/
def orbitVector (P : NonsplitParameters R k) (s : ℤ) : CompanionModule P :=
  if 0 ≤ s then (Yv P ^ s.toNat) (vNat P 0)
  else (YvInv P ^ (-s).toNat) (vNat P 0)

/-- The recursive columns (14)--(16), PDF p.5. Only columns 0<=i<k
are used to define X. In particular the i=1 clause is not used at k=1. -/
def xColumn (P : NonsplitParameters R k) : ℕ → CompanionModule P
  | 0 => (P.lam : R) • vNat P 0
  | 1 => (↑P.lam⁻¹ : R) • YvInv P (vNat P 0)
  | i+2 => YvInv P (xColumn P (i+1)) - skeinDelta P • vNat P i +
      (skeinDelta P * aAt P (i+1)) • YvInv P (vNat P 0)

/-- The constructed X of (14)--(16), PDF p.5. -/
def Xv (P : NonsplitParameters R k) : Module.End R (CompanionModule P) :=
  (vBasis P).constr R fun i => xColumn P i.val

/-- The constructed E of (17), PDF p.5. -/
def Ev (P : NonsplitParameters R k) : Module.End R (CompanionModule P) :=
  (vBasis P).constr R fun i => P.loop i • vNat P 0

/-- W=X-skeinDelta+skeinDelta E, PDF p.5. Multiplication of endomorphisms
is composition with the rightmost factor acting first. -/
def Wv (P : NonsplitParameters R k) : Module.End R (CompanionModule P) :=
  Xv P - skeinDelta P • (1 : Module.End R (CompanionModule P)) + skeinDelta P • Ev P

/-- N is the computed defect of Section 3, PDF p.9. -/
def Nv (P : NonsplitParameters R k) : Module.End R (CompanionModule P) :=
  Yv P * Xv P * Yv P * Xv P - 1

/-- Coordinates of the three tagged tensor bases, PDF pp.11--12. -/
abbrev XiIndex (k : ℕ) := Fin 3 × (Fin k × Fin k)

/-- Xi=(CompanionModule tensor CompanionModule) direct sum (CompanionModule tensor CompanionModule) direct sum (CompanionModule tensor CompanionModule),
in canonical tensor coordinates, PDF p.11. -/
abbrev Xi (P : NonsplitParameters R k) := XiIndex k → R

/-- The specified three-copy tensor basis, PDF p.11. -/
def xiBasis (P : NonsplitParameters R k) : Module.Basis (XiIndex k) R (Xi P) :=
  Pi.basisFun R (XiIndex k)

/-- Pure tensor a tensor b in tag t: t=0,1,2 means orbitVector,u,w, PDF p.11. -/
def tensorIn (P : NonsplitParameters R k) (t : Fin 3) (a b : CompanionModule P) : Xi P :=
  fun idx => if idx.1 = t then a idx.2.1 * b idx.2.2 else 0

/-- Signed integer tensor labels v_ij,u_ij,w_ij, PDF p.11. -/
def tensorLabel (P : NonsplitParameters R k) (t : Fin 3) (i j : ℤ) : Xi P :=
  tensorIn P t (orbitVector P i) (orbitVector P j)

/-- E u_ij = v_00 Y^i X Y^j. Reversal makes its second tensor factor
Y^j X Y^i v_0, in that order, PDF pp.11--12, equation (33). -/
def euColumn (P : NonsplitParameters R k) (i j : Fin k) : Xi P :=
  tensorIn P 0 (vNat P 0) ((Yv P ^ j.val) (Xv P (vNat P i.val)))

/-- E on all three tensor summands, equations (17),(33),(34), PDF p.12. -/
def Exi (P : NonsplitParameters R k) : Module.End R (Xi P) :=
  (xiBasis P).constr R fun idx =>
    if idx.1.val = 0 then
      tensorIn P 0 (Ev P (vNat P idx.2.1.val)) (vNat P idx.2.2.val)
    else if idx.1.val = 1 then euColumn P idx.2.1 idx.2.2
    else (P.lam : R) • euColumn P idx.2.1 idx.2.2

/-- X on the three summands, equations (14)--(16),(35),(36), PDF p.12. -/
def Xxi (P : NonsplitParameters R k) : Module.End R (Xi P) :=
  (xiBasis P).constr R fun idx =>
    if idx.1.val = 0 then
      tensorIn P 0 (Xv P (vNat P idx.2.1.val)) (vNat P idx.2.2.val)
    else if idx.1.val = 1 then
      tensorIn P 2 (vNat P idx.2.1.val) (vNat P idx.2.2.val)
    else tensorIn P 1 (vNat P idx.2.1.val) (vNat P idx.2.2.val) +
      skeinDelta P • tensorIn P 2 (vNat P idx.2.1.val) (vNat P idx.2.2.val) -
      (skeinDelta P * (P.lam : R)) • euColumn P idx.2.1 idx.2.2

/-- W=X-skeinDelta+skeinDelta E on Xi, PDF p.12. -/
def Wxi (P : NonsplitParameters R k) : Module.End R (Xi P) :=
  Xxi P - skeinDelta P • (1 : Module.End R (Xi P)) + skeinDelta P • Exi P

/-- Y on the three summands, equations (32),(37),(38), PDF p.12.
The w-column is computed using the already constructed W, so there is no
circular definition or arbitrary operator witness. -/
def Yxi (P : NonsplitParameters R k) : Module.End R (Xi P) :=
  (xiBasis P).constr R fun idx =>
    if idx.1.val = 0 then
      tensorIn P 0 (Yv P (vNat P idx.2.1.val)) (vNat P idx.2.2.val)
    else if idx.1.val = 1 then
      tensorIn P 1 (Yv P (vNat P idx.2.1.val)) (vNat P idx.2.2.val)
    else Wxi P (tensorIn P 1 (vNat P idx.2.1.val) (Yv P (vNat P idx.2.2.val))) +
      skeinDelta P • tensorLabel P 1 1 ((idx.2.1.val : ℤ) + (idx.2.2.val : ℤ)) -
      skeinDelta P • tensorIn P 0 (Yv P (Xv P (vNat P idx.2.1.val)))
        (vNat P idx.2.2.val)

/-- The six identity groups (25)--(30) / (40)--(45), PDF pp.10,13. -/
def OperatorRelations (P : NonsplitParameters R k) {M : Type*} [AddCommGroup M] [Module R M]
    (Y X W E : Module.End R M) : Prop :=
  (∑ l ∈ Finset.range (k+1), qAt P l • Y ^ l) = 0 ∧
  X * W = 1 ∧ W * X = 1 ∧
  X * E = (P.lam : R) • E ∧ E * X = (P.lam : R) • E ∧
  Y * X * Y * X = X * Y * X * Y ∧
  (∀ m : Fin k, E * Y ^ m.val * E = P.loop m • E) ∧
  E * Y * X * Y = (↑P.lam⁻¹ : R) • E ∧
  Y * X * Y * E = (↑P.lam⁻¹ : R) • E

/-- A genuine compatible unital R-algebra representation on the fixed CompanionModule;
existence of such a map is a conclusion, PDF p.11. -/
def CompatibleV (P : NonsplitParameters R k) (rho : TwoStrandBMW P →ₐ[R] Module.End R (CompanionModule P)) : Prop :=
  rho (y P) = Yv P ∧ rho (x P) = Xv P ∧
  rho (xInv P) = Wv P ∧ rho (e P) = Ev P

/-- The specified unital algebra representation on Xi, PDF p.13. -/
def CompatibleXi (P : NonsplitParameters R k) (rho : TwoStrandBMW P →ₐ[R] Module.End R (Xi P)) : Prop :=
  rho (y P) = Yxi P ∧ rho (x P) = Xxi P ∧
  rho (xInv P) = Wxi P ∧ rho (e P) = Exi P

/-- The ordered basisWord family of Theorem 4.3, PDF p.17. Tag 0,1,2 means
Y^i e Y^j, Y^i X Y^j, X Y^i X Y^j respectively. -/
def basisWord (P : NonsplitParameters R k) (idx : XiIndex k) : TwoStrandBMW P :=
  if idx.1.val = 0 then y P ^ idx.2.1.val * e P * y P ^ idx.2.2.val
  else if idx.1.val = 1 then y P ^ idx.2.1.val * x P * y P ^ idx.2.2.val
  else x P * y P ^ idx.2.1.val * x P * y P ^ idx.2.2.val

/-- The particular R-linear wordMap of Theorem 4.3, PDF p.17. -/
def wordMap (P : NonsplitParameters R k) : Xi P →ₗ[R] TwoStrandBMW P :=
  (xiBasis P).constr R (basisWord P)

/-- The unconditional spanning submodule, PDF p.19. -/
def wordSpan (P : NonsplitParameters R k) : Submodule R (TwoStrandBMW P) :=
  Submodule.span R (Set.range (basisWord P))

/-- The principal LEFT ideal, PDF p.4, encoded as an R-submodule. -/
def principalEIdeal (P : NonsplitParameters R k) : Submodule R (TwoStrandBMW P) :=
  Submodule.span R {z | ∃ a : TwoStrandBMW P, z = a * e P}

/-- The actual two-sided e-generated ideal, PDF pp.4,18. -/
abbrev twoSidedIdeal (P : NonsplitParameters R k) : Submodule R (TwoStrandBMW P) :=
  Accepted.eIdeal P 2

/-- The j-th named column submodule of Corollary 4.4, PDF p.18. -/
def column (P : NonsplitParameters R k) (j : Fin k) : Submodule R (TwoStrandBMW P) :=
  Submodule.span R (Set.range fun i : Fin k => y P ^ i.val * e P * y P ^ j.val)

/-- Free words for the paper's normalized two-generator NormalizedHecke algebra, PDF p.4. -/
inductive HeckeLetter
  | t0 | t0Inv | t1 | t1Inv
  deriving DecidableEq

/-- A free NormalizedHecke generator, PDF p.4. -/
def ht (l : HeckeLetter) : FreeAlgebra R HeckeLetter := FreeAlgebra.ι R l

/-- The INDEPENDENT normalized Hecke presentation of PDF p.4. There are
no TwoStrandBMW relations or e-generator here; T1^2=skeinDelta T1+1. -/
inductive NormalizedHeckeRel (P : NonsplitParameters R k) :
    FreeAlgebra R HeckeLetter → FreeAlgebra R HeckeLetter → Prop
  | t0Left : NormalizedHeckeRel P (ht .t0 * ht .t0Inv) 1
  | t0Right : NormalizedHeckeRel P (ht .t0Inv * ht .t0) 1
  | t1Left : NormalizedHeckeRel P (ht .t1 * ht .t1Inv) 1
  | t1Right : NormalizedHeckeRel P (ht .t1Inv * ht .t1) 1
  | braid : NormalizedHeckeRel P (ht .t0 * ht .t1 * ht .t0 * ht .t1)
      (ht .t1 * ht .t0 * ht .t1 * ht .t0)
  | cyclotomic : NormalizedHeckeRel P (ht .t0 ^ k)
      (∑ i : Fin k, algebraMap R _ (P.coeff i) * ht .t0 ^ i.val)
  | quadratic : NormalizedHeckeRel P (ht .t1 ^ 2) (algebraMap R _ (skeinDelta P) * ht .t1 + 1)

/-- h_2^k(R) with the source's normalization, PDF p.4. -/
abbrev NormalizedHecke (P : NonsplitParameters R k) := RingQuot (NormalizedHeckeRel P)

/-- The actual normalized Hecke generators, PDF p.4. -/
def heckeGen (P : NonsplitParameters R k) (l : HeckeLetter) : NormalizedHecke P :=
  (RingQuot.mkAlgHom R (NormalizedHeckeRel P)) (ht l)

/-- The actual quotient of TwoStrandBMW by its two-sided e-ideal, PDF p.4. -/
abbrev EQuotient (P : NonsplitParameters R k) := Accepted.HeckeQuotient P 2

/-- The canonical map to that quotient, PDF p.4. -/
def eQuotientMap (P : NonsplitParameters R k) : TwoStrandBMW P →ₐ[R] EQuotient P :=
  RingQuot.mkAlgHom R (fun a b : TwoStrandBMW P => a-b ∈ twoSidedIdeal P)

/-- Sanity: the normalized Hecke quadratic is imposed in its own presentation. -/
example (P : NonsplitParameters R k) :
    (RingQuot.mkAlgHom R (NormalizedHeckeRel P)) (ht .t1 ^ 2) =
      (RingQuot.mkAlgHom R (NormalizedHeckeRel P)) (algebraMap R _ (skeinDelta P) * ht .t1 + 1) := by
  exact RingQuot.mkAlgHom_rel R (NormalizedHeckeRel.quadratic (P := P))

/-- Sanity: the last companion coefficient is exactly -1. -/
example (P : NonsplitParameters R k) : qAt P k = -1 := by simp [qAt]

/-- Sanity: the first two recursive X columns have precisely (14)--(15). -/
example (P : NonsplitParameters R k) :
    xColumn P 0 = (P.lam : R) • vNat P 0 ∧
    xColumn P 1 = (↑P.lam⁻¹ : R) • YvInv P (vNat P 0) := by
  exact ⟨rfl, rfl⟩

/-- Sanity: signed orbit index zero is the specified standard vector. -/
example (P : NonsplitParameters R k) : orbitVector P 0 = vNat P 0 := by simp [orbitVector]

/-- Sanity: tensor coordinates preserve the tag and the order of the factors. -/
example (P : NonsplitParameters R k) (t : Fin 3) (a b : CompanionModule P) (i j : Fin k) :
    tensorIn P t a b (t, (i,j)) = a i * b j := by simp [tensorIn]

/-- Sanity: the actual constructed X has the prescribed recursive columns. -/
example (P : NonsplitParameters R k) (i : Fin k) :
    Xv P (vBasis P i) = xColumn P i.val := by simp [Xv]

/-- Sanity: wordMap maps each tagged standard tensor basis vector to its basisWord. -/
example (P : NonsplitParameters R k) (idx : XiIndex k) :
    wordMap P (xiBasis P idx) = basisWord P idx := by simp [wordMap]

/-- Sanity: the odd-degree admissibilityBeta has no extra skeinDelta term. -/
example (P : NonsplitParameters R k) (h : ¬ Even k) :
    admissibilityBeta P = (P.constant : R) * (P.lam : R) -
      (↑P.constant⁻¹ : R) * (↑P.lam⁻¹ : R) := by simp [admissibilityBeta, h]

end QAlgorithms.Papers.Independent.Intake100.P58


