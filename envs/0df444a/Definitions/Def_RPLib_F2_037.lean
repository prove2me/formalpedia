-- Prove2me | Definitions.Def_RPLib_F2_037
-- name    : RPLib_F2_037
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T15:47:21.75066+00:00
-- url     : https://prove2.me/theorems/e88dcdc7-6fbc-4bb2-829d-74384fc9d553
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 037 of 70
-- statement:
--   File 037 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacComplete_CommLaw`: The Jacobian (unit S4-JacComplete), part `CommLaw` (L22: Weil's law is commutative at points)
--   * `S4.Def_RP_JacComplete_AJPiece`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0`
--   * `S4.Def_RP_JacComplete_AJGen`: The Jacobian (unit S4-JacComplete), part `AJGen`: the pieces cover the chart `{c0}`
--   * `S4.Def_RP_JacFrob_BrO`: S4-JacFrob, part BrO (bridge 3): `F-bar / F_{lev j}` is unramified
--   * `S4.Def_RP_JacFrob_BrD`: S4-JacFrob, part BrD (bridge 4): degree-1 places, separation, fibre count
--   * `S4.Def_RP_JacFrob_BrPsi`: S4-JacFrob, part BrPsi (bridge 5): `Pic(X-bar) ≃ Pic(F-bar / k-bar)`
--   * `S4.Def_RP_CoreB_Triv`: Core B, O2: the genus 0 case
--   * `S4.Def_RP_JacFrob_BrSig`: S4-JacFrob, part BrSig (bridge 6): the bridge intertwines the two Frobenius actions
--   * `S4.Def_RP_JacFrob_Poly`: S4-JacFrob, part Poly: `ℤ[π] → End(J)` for `J = J_{F-bar}` and the kernel/degree bridge to `Pic⁰(X-bar)` (L23)
--   * `S4.Def_RP_Cone_ResGlob`: S4-PD (4), E4B part 5c: the global residue theorem
--   * `S4.Def_RP_Cone_Exist`: S4-PD (4), E4X part 2: existence of global characters with prescribed residues
--   * `S4.Def_RP_Cone_CdSub`: S4-PD (4)/(5), E1: `cd_l ≤ 1` for every CLOSED subgroup of `π₁^geo` (e.g. boundary inertia groups)
--   * `S4.Def_RP_Cone_H3`: S4-PD (4), E4H3: the cone's `H³` vanishes
--   * `S4.Def_RP_Cone_ResTr`: S4-PD E4S arithmetic ResA, part 2: transport of normalised generators under geometric conjugation
--   * `S4.Def_RP_Cone_TwNorm`: S4-PD (4), arithmetic twist part B1: normalised generators under twisted conjugation
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_030
import Definitions.Def_RPLib_F2_034

/-!
# Ramanujan-Petersson curve library (flat edition), file 037 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacComplete_CommLaw`: The Jacobian (unit S4-JacComplete), part `CommLaw` (L22: Weil's law is commutative at points)
* `S4.Def_RP_JacComplete_AJPiece`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0`
* `S4.Def_RP_JacComplete_AJGen`: The Jacobian (unit S4-JacComplete), part `AJGen`: the pieces cover the chart `{c0}`
* `S4.Def_RP_JacFrob_BrO`: S4-JacFrob, part BrO (bridge 3): `F-bar / F_{lev j}` is unramified
* `S4.Def_RP_JacFrob_BrD`: S4-JacFrob, part BrD (bridge 4): degree-1 places, separation, fibre count
* `S4.Def_RP_JacFrob_BrPsi`: S4-JacFrob, part BrPsi (bridge 5): `Pic(X-bar) ≃ Pic(F-bar / k-bar)`
* `S4.Def_RP_CoreB_Triv`: Core B, O2: the genus 0 case
* `S4.Def_RP_JacFrob_BrSig`: S4-JacFrob, part BrSig (bridge 6): the bridge intertwines the two Frobenius actions
* `S4.Def_RP_JacFrob_Poly`: S4-JacFrob, part Poly: `ℤ[π] → End(J)` for `J = J_{F-bar}` and the kernel/degree bridge to `Pic⁰(X-bar)` (L23)
* `S4.Def_RP_Cone_ResGlob`: S4-PD (4), E4B part 5c: the global residue theorem
* `S4.Def_RP_Cone_Exist`: S4-PD (4), E4X part 2: existence of global characters with prescribed residues
* `S4.Def_RP_Cone_CdSub`: S4-PD (4)/(5), E1: `cd_l ≤ 1` for every CLOSED subgroup of `π₁^geo` (e.g. boundary inertia groups)
* `S4.Def_RP_Cone_H3`: S4-PD (4), E4H3: the cone's `H³` vanishes
* `S4.Def_RP_Cone_ResTr`: S4-PD E4S arithmetic ResA, part 2: transport of normalised generators under geometric conjugation
* `S4.Def_RP_Cone_TwNorm`: S4-PD (4), arithmetic twist part B1: normalised generators under twisted conjugation
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_CommLaw =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `CommLaw` (L22: Weil's law is commutative at points)

* `comm_mOut`: `m(a,b) = m(b,a)` at points: the support of `a + b + c0` is symmetric in `a, b`, so both sides run
  through the same points of `Sym^(2g+r3)` and `Sym^(g+r2)` (`pts_mOut`, `eq_of_ptSet_eq`).
* `lawData_law_comm`, `lawData_rel_comm`: the same for the law `μm` of a `LawData` at points of `D(ωm)`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacLaw
open CategoryTheory AlgebraicGeometry

section Pt

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable {T1 T2 : Type*} [CommRing T1] [Algebra K T1] [IsReduced T1] [Algebra.FiniteType K T1]
  [CommRing T2] [Algebra K T2] [IsReduced T2] [Algebra.FiniteType K T2]
  {r3 r2 : ℕ} {D3 : NuData K F (genusFK K F + genusFK K F + r3)} {D2 : NuData K F (genusFK K F + r2)}
  {c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)} {c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)}

end Pt

universe u

section Law

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (L : LawData K F)

/-- **Weil's law is commutative** at points of `D(ωm)`: `m(a,b) = m(b,a)`. -/
theorem lawData_rel_comm (x x' : Localization.Away L.ωm →ₐ[K] K) (e1 : pL x' = pR x) (e2 : pR x' = pL x) :
    x.comp L.μm = x'.comp L.μm :=
  (L.m_nest x).trans <| (lawData_law_comm L _ _ ((L.mB_L x').trans (e1.trans (L.mB_R x).symm))
    ((L.mB_R x').trans (e2.trans (L.mB_L x).symm))).trans (L.m_nest x').symm

end Law

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJPiece =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0`

In `F' = SynF K F c0` (coordinate `x' = 1/(x - c0)`), the `ν`-piece `pieceMap D c : Sym^g(B') → B'[1/f]` of
`AJLoc` is localized at `N(x')` (`ConvR`), converted to `F`-coordinates by `convSym` (`convS`), and localized at
the image of `u0` (`LocR`). This gives **`lawMapP : LawRing K F → LocR`**, i.e. `Spec LocR → X0`, on the open
`Spec LocR ⊆ Spec B'` (`pieceIn`), with the class formula **`psiJ_lawMapP`**: `ψ(piece(Q)) = κ - [Θ] - [Q]`.
`exists_pieceIn`: a point `Q` of `B'` lies on the piece when `f`, `N(x')` and `u0` do not vanish there.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section AwayPt

variable {K : Type u} [Field K] [IsAlgClosed K]

end AwayPt

section AJPiece

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (c0 : K) {r : ℕ} (D : NuData K (SynF K F c0) (1 + r))
  (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

/-- `B'[1/f][1/N(x')]`. -/
abbrev ConvR : Type u := Localization.Away (pieceN c0 D c)

/-- The piece over `ConvR`. -/
noncomputable def convφ : SymRing K (Rfin K (SynF K F c0)) (genusFK K (SynF K F c0)) →ₐ[K] ConvR c0 D c :=
  (awayι (K := K) (pieceN c0 D c)).comp (pieceMap D c)

theorem isUnit_convφ : IsUnit (convφ c0 D c (normS K (xS K F c0))) :=
  IsLocalization.Away.algebraMap_isUnit (pieceN c0 D c)

/-- **The piece in `F`-coordinates**: `Sym^g(Rfin F) → ConvR`. -/
noncomputable def convS : SymRing K (Rfin K F) (genusFK K F) →ₐ[K] ConvR c0 D c :=
  convSym c0 (convφ c0 D c) (isUnit_convφ c0 D c) (genusFK_eq (synEquiv K F c0)).symm

theorem comp_convS (y : ConvR c0 D c →ₐ[K] K) :
    y.comp (convS c0 D c) =
      symPt (convPt c0 (convφ c0 D c) (isUnit_convφ c0 D c) (genusFK_eq (synEquiv K F c0)).symm y) :=
  comp_convSym c0 _ _ _ y

/-- The constant of the piece: `[Hn] - [c]` moved to `F`. -/
noncomputable def kapP : PicK K F :=
  (picMap (synEquiv K F c0)).symm
    (clsK K (SynF K F c0) D.Hn - clsK K (SynF K F c0) (Zdiv (Finset.univ.image c)))

/-- **Class of the converted piece**: `[conv ν(Q + c)] = κ - [Q]`. -/
theorem clsK_convS (y : ConvR c0 D c →ₐ[K] K) :
    clsK K F (Zdiv (ptSet (y.comp (convS c0 D c)))) = kapP c0 D c -
      clsK K F (Finsupp.single ((synPlace c0).symm
        (Sum.inl (ptP ((y.comp (awayι (K := K) (pieceN c0 D c))).comp (pieceι D c))))) 1) := by
  have h1 : divMap (synEquiv K F c0) (Zdiv (ptSet (y.comp (convS c0 D c)))) =
      Zdiv (ptSet (y.comp (convφ c0 D c))) :=
    divMap_Zdiv_convSym c0 (convφ c0 D c) (isUnit_convφ c0 D c) (genusFK_eq (synEquiv K F c0)).symm y
  have h2 := clsK_pieceMap D c (y.comp (awayι (K := K) (pieceN c0 D c)))
  rw [kapP, ← clsK_single_syn, ← map_sub, AddEquiv.eq_symm_apply, picMap_clsK, h1, convφ,
    ← AlgHom.comp_assoc, h2]
  abel

/-- `N(x')` does not vanish where `ν(Q + c)` avoids `x = ∞`. -/
theorem pieceN_ne_zero (z : PieceR D c →ₐ[K] K)
    (h : ∀ e ∈ ptSet (z.comp (pieceMap D c)), e (xS K F c0) ≠ 0) : z (pieceN c0 D c) ≠ 0 := by
  have e := symPt_normS (liftTuple (z.comp (pieceMap D c))) (xS K F c0)
  rw [symPt_liftTuple, AlgHom.comp_apply] at e
  rw [pieceN, e]
  exact Finset.prod_ne_zero_iff.2 fun l _ => h _ ((mem_ptSet _ _).2 ⟨l, rfl⟩)

end AJPiece

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJGen =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJGen`: the pieces cover the chart `{c0}`

* `exists_pool`: arbitrarily large finite sets of points off the roots of `b(x)`.
* `PtY K F c0` (points of `B' = Rfin F'` off `x = ∞`), `tpY` (their `F`-points, injective).
* `goodY_ext`: nonspecial `b`-generic sets of such points extend off any finite set.
* `symPt_convPt_eq`: the converted point depends only on the support.
* **`exists_piece_through`**: every closed point `Q0` of `B'` lies on some piece `Spec LocR c0 D c`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section AJGen

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (c0 : K)

theorem ptSet_convφ {r : ℕ} (D : NuData K (SynF K F c0) (1 + r)) (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))
    (y : ConvR c0 D c →ₐ[K] K) : ptSet (y.comp (convφ c0 D c)) =
      D.nuF (padPt phi1 c rfl ((y.comp (awayι (K := K) (pieceN c0 D c))).comp (pieceι D c))) := by
  rw [convφ, ← AlgHom.comp_assoc, ptSet_pieceMap]

end AJGen

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacFrob_BrO =====
section

/-!
# S4-JacFrob, part BrO (bridge 3): `F-bar / F_{lev j}` is unramified

* generic: `ord_liesOver_mul` (`ord_w (x) = e(w | v) · ord_v x` for `w` over `v`, from Mathlib `valuation_liesOver`);
* `ord_contFinB_mul`, `ord_contInfB_mul` (the same for the contraction to a level);
* `placeOrd_inl_bar/inr_bar` (`Place.ord` on `F-bar`, which has no `Fintype` constants);
* **`ord_contFinB`, `ord_contInfB`, `ord_contB`**: `ord_{contB j P} f = ord_P f` for `f ∈ F_{lev j}` (a uniformizer of
  `P` lies in some level `M`, forcing `e = 1` there, and the levels are unramified over each other).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places

section GenOrd

variable {A K : Type*} (L : Type*) {B : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]

end GenOrd

section Unram

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

/-- **Unramified** (places): `ord_{contB j P} f = ord_P f` for `f ∈ F_{lev j}`. -/
theorem ord_contB (j : ℕ) (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) (f : Fc Fq F Ω (lev j)) :
    (contB Fq F Ω hk j P).ord f = P.ord (incF Fq F Ω j f) := by
  rcases P with w | w
  · rw [contB_inl, Place.ord_inl, placeOrd_inl_bar, ord_contFinB]
  · rw [contB_inr, Place.ord_inr, placeOrd_inr_bar, ord_contInfB]

end Unram

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_BrD =====
section

/-!
# S4-JacFrob, part BrD (bridge 4): degree-1 places, separation, fibre count

* generic: `deg_eq_one_of_const` (a place all of whose residues are constants has degree `1`),
  `exists_const_of_isAlgClosed` (over an algebraically closed field every residue is a constant);
* generic (constant field extensions): `exists_sum_fin/inf` (`A' = Σ L · A`), `const_of_base_fin/inf`;
* `degOne`: every place of `F-bar` contracts to a degree-1 place at all large levels;
* `sepB`, `contB_ne_mono`: places of `F-bar` are separated by their contractions;
* `uniqB`, `fibreB`, `exists_fibreB_singleton`: over a degree-1 level place there is exactly one place of `F-bar`;
* **`card_fibreB`**: `#{P | contB j P = Q} = deg Q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places

section GenDeg

variable {L : Type*} [Field L] {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra L A]

end GenDeg

section Gen

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
variable (h : RR.IsConstExt Fq F L F' c)

end Gen

section DegOne

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

include hk in
/-- **Fibre count**: there are exactly `deg Q` places of `F-bar` over a level place `Q`. -/
theorem card_fibreB (j : ℕ) (Q : Places.Place (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    (fibreB Fq F Ω hk j Q).card = Q.deg := by
  classical
  choose! M0 hM0 using fun P (_ : P ∈ fibreB Fq F Ω hk j Q) => degOne Fq F Ω hk P
  let M := max j ((fibreB Fq F Ω hk j Q).sup M0)
  haveI : Fact (lev j ∣ lev M) := ⟨lev_dvd_lev (le_max_left _ _)⟩
  have hdeg : ∀ P ∈ fibreB Fq F Ω hk j Q, (contB Fq F Ω hk M P).deg = 1 := fun P hP =>
    hM0 P hP M (le_trans (Finset.le_sup hP) (le_max_right _ _))
  have hdown : ∀ P, contB Fq F Ω hk M P ∈ fibre (isConstExt_pair Fq F Ω hk (n := lev j) (N := lev M)) Q ↔
      P ∈ fibreB Fq F Ω hk j Q := fun P => by
    rw [mem_fibre, mem_fibreB]
    exact Iff.of_eq (congrArg (· = Q) (contractNN_contB Fq F Ω hk (i := j) (j := M) P))
  have hbij : (fibreB Fq F Ω hk j Q).card =
      (fibre (isConstExt_pair Fq F Ω hk (n := lev j) (N := lev M)) Q).card := by
    refine Finset.card_bij (fun P _ => contB Fq F Ω hk M P) (fun P hP => (hdown P).2 hP)
      (fun P1 _ P2 hP2 he => uniqB Fq F Ω hk (hdeg P2 hP2) he) (fun Q' hQ' => ?_)
    obtain ⟨P, hP⟩ := exists_contB_eq Fq F Ω hk M Q'
    exact ⟨P, (hdown P).1 (by rw [hP]; exact hQ'), hP⟩
  have hall : ∀ Q' ∈ fibre (isConstExt_pair Fq F Ω hk (n := lev j) (N := lev M)) Q, Q'.deg = 1 := by
    intro Q' hQ'
    obtain ⟨P, rfl⟩ := exists_contB_eq Fq F Ω hk M Q'
    exact hdeg P ((hdown P).1 hQ')
  have hsum := sum_deg_fibre (isConstExt_pair Fq F Ω hk (n := lev j) (N := lev M)) Q
  rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul, mul_one] at hsum
  rw [hbij, hsum]

end DegOne

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_BrPsi =====
section

/-!
# S4-JacFrob, part BrPsi (bridge 5): `Pic(X-bar) ≃ Pic(F-bar / k-bar)`

* `psiD j`: pull a level divisor back to `F-bar` (`psiD j D P = D (contB j P)`); injective, compatible with conorm,
  `psiD j (div f) = div f`, degree preserving (`card_fibreB`);
* `psiPic j`: the induced map on classes; `Psi0 : PicBar →+ PicK` (direct-limit lift);
* **`Psi : PicBar ≃+ PicK (kbar) (Fbar)`**, `degPicK_Psi`, **`Psi0Equiv : PicBar0 ≃+ Pic0K`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places ZetaSB RamanujanPetersson.JacComplete

section Psi

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

theorem psiD_div (j : ℕ) (f : Fc Fq F Ω (lev j)) :
    psiD Fq F Ω hk j (Places.div f) = PlacesK.div (incF Fq F Ω j f) := by
  ext P
  rw [psiD_apply, Places.div_apply, PlacesK.div_apply, ord_contB]

include hk in
/-- **Degree** is preserved. -/
theorem deg_psiD (j : ℕ) (D : Places.Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    Places.Divisor.deg (psiD Fq F Ω hk j D) = Places.Divisor.deg D := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero]; simp [Places.Divisor.deg]
  | add D E hD hE => rw [map_add, PlacesK.Divisor.deg_add, Places.Divisor.deg_add, hD, hE]
  | single Q n =>
    rw [psiD_single, Places.Divisor.deg_single]
    have hs := map_sum (degHomK (kbar Fq Ω) (Fbar Fq F Ω)) (fun P => Finsupp.single P n) (fibreB Fq F Ω hk j Q)
    simp only [degHomK_apply, deg_single'] at hs
    rw [hs, Finset.sum_const, card_fibreB Fq F Ω hk j Q, nsmul_eq_mul, mul_comm]

/-- The induced map on divisor classes at level `lev j`. -/
noncomputable def psiPic (j : ℕ) : PicL Fq F Ω j →+ PicK (kbar Fq Ω) (Fbar Fq F Ω) :=
  QuotientAddGroup.map _ _ (psiD Fq F Ω hk j) (by
    rintro _ ⟨f, hf, rfl⟩
    rw [AddSubgroup.mem_comap, psiD_div]
    exact div_mem_PrincK _ _ ((map_ne_zero (incF Fq F Ω j)).2 hf))

theorem psiPic_mk (j : ℕ) (D : Places.Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    psiPic Fq F Ω hk j (QuotientAddGroup.mk D) = clsK _ _ (psiD Fq F Ω hk j D) := rfl

theorem psiPic_tr {i j : ℕ} (h : i ≤ j) (x : PicL Fq F Ω i) :
    psiPic Fq F Ω hk j (tr Ω hk i j h x) = psiPic Fq F Ω hk i x := by
  have : Fact (lev i ∣ lev j) := ⟨lev_dvd_lev h⟩
  induction x using QuotientAddGroup.induction_on with
  | H D => rw [tr_apply hk h, conNN_mk, psiPic_mk, psiPic_mk, psiD_conormNN]

/-- The direct-limit lift `Pic(X-bar) → Pic(F-bar / k-bar)`. -/
noncomputable def Psi0 : PicBar Ω hk →+ PicK (kbar Fq Ω) (Fbar Fq F Ω) :=
  AddCommGroup.DirectLimit.lift (PicL Fq F Ω) (tr Ω hk) _ (psiPic Fq F Ω hk) fun _ _ h x => psiPic_tr Fq F Ω hk h x

theorem Psi0_of (j : ℕ) (y : PicL Fq F Ω j) : Psi0 Fq F Ω hk (ofBar Ω hk j y) = psiPic Fq F Ω hk j y :=
  AddCommGroup.DirectLimit.lift_of _ _ _ j y

theorem degPicK_Psi0 (z : PicBar Ω hk) : degPicK _ _ (Psi0 Fq F Ω hk z) = degBar Ω hk z := by
  refine AddCommGroup.DirectLimit.induction_on z fun j y => ?_
  change degPicK _ _ (Psi0 Fq F Ω hk (ofBar Ω hk j y)) = degBar Ω hk (ofBar Ω hk j y)
  rw [Psi0_of, degBar_of]
  induction y using QuotientAddGroup.induction_on with
  | H D => rw [psiPic_mk, degPicK_clsK, deg_psiD, degPic_mk]

theorem Psi0_injective : Function.Injective (Psi0 Fq F Ω hk) := by
  refine (injective_iff_map_eq_zero _).2 fun z => ?_
  refine AddCommGroup.DirectLimit.induction_on z fun j y => ?_
  intro hz
  change Psi0 Fq F Ω hk (ofBar Ω hk j y) = 0 at hz
  change ofBar Ω hk j y = 0
  rw [Psi0_of] at hz
  induction y using QuotientAddGroup.induction_on with
  | H D =>
    rw [psiPic_mk, clsK, QuotientAddGroup.eq_zero_iff, mem_PrincK] at hz
    obtain ⟨g, hg0, hg⟩ := hz
    obtain ⟨M, hM⟩ := exists_lev_of_mem_Fbar g.2
    have hjM : j ≤ max j M := le_max_left j M
    haveI : Fact (lev j ∣ lev (max j M)) := ⟨lev_dvd_lev hjM⟩
    have hmem : (g : Ω) ∈ Fc Fq F Ω (lev (max j M)) := Fc_le (lev_dvd_lev (le_max_right j M)) hM
    let g' : Fc Fq F Ω (lev (max j M)) := ⟨g, hmem⟩
    have hgg : incF Fq F Ω (max j M) g' = g := Subtype.ext ((coe_incF Fq F Ω (max j M) g').trans rfl)
    have hg'0 : g' ≠ 0 := fun h0 => hg0 (by rw [← hgg, h0, map_zero])
    have hc : conormNN Ω hk (lev j) (lev (max j M)) D = Places.div g' := by
      apply psiD_injective Fq F Ω hk (max j M)
      rw [psiD_conormNN, psiD_div, hgg, hg]
    have h0 : tr Ω hk j (max j M) hjM (QuotientAddGroup.mk D) = tr Ω hk j (max j M) hjM 0 := by
      rw [map_zero, tr_apply hk hjM, conNN_mk, hc, QuotientAddGroup.eq_zero_iff]
      exact ⟨g', hg'0, rfl⟩
    rw [tr_injective hk hjM h0, map_zero]

theorem Psi0_surjective : Function.Surjective (Psi0 Fq F Ω hk) := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H D =>
    induction D using Finsupp.induction_linear with
    | zero => exact ⟨0, by rw [map_zero]; exact (QuotientAddGroup.mk_zero _).symm⟩
    | add D E hD hE =>
      obtain ⟨z1, h1⟩ := hD
      obtain ⟨z2, h2⟩ := hE
      exact ⟨z1 + z2, by rw [map_add, h1, h2]; exact (QuotientAddGroup.mk_add _ _ _).symm⟩
    | single P n =>
      obtain ⟨M0, hM0⟩ := exists_fibreB_singleton Fq F Ω hk P
      refine ⟨ofBar Ω hk M0 (QuotientAddGroup.mk (Finsupp.single (contB Fq F Ω hk M0 P) n)), ?_⟩
      rw [Psi0_of, psiPic_mk, psiD_single, hM0 M0 le_rfl, Finset.sum_singleton]

/-- **The bridge** `Pic(X-bar) ≃ Pic(F-bar / k-bar)`. -/
noncomputable def Psi : PicBar Ω hk ≃+ PicK (kbar Fq Ω) (Fbar Fq F Ω) :=
  AddEquiv.ofBijective (Psi0 Fq F Ω hk) ⟨Psi0_injective Fq F Ω hk, Psi0_surjective Fq F Ω hk⟩

theorem Psi_apply (z : PicBar Ω hk) : Psi Fq F Ω hk z = Psi0 Fq F Ω hk z := rfl

theorem Psi_of (j : ℕ) (y : PicL Fq F Ω j) : Psi Fq F Ω hk (ofBar Ω hk j y) = psiPic Fq F Ω hk j y :=
  Psi0_of Fq F Ω hk j y

theorem degPicK_Psi (z : PicBar Ω hk) : degPicK _ _ (Psi Fq F Ω hk z) = degBar Ω hk z :=
  degPicK_Psi0 Fq F Ω hk z

theorem degBar_Psi_symm (w : PicK (kbar Fq Ω) (Fbar Fq F Ω)) :
    degBar Ω hk ((Psi Fq F Ω hk).symm w) = degPicK _ _ w := by
  rw [← degPicK_Psi, AddEquiv.apply_symm_apply]

/-- **`Pic⁰(X-bar) ≃ Pic⁰(F-bar / k-bar)`**. -/
noncomputable def Psi0Equiv : PicBar0 Ω hk ≃+ Pic0K (kbar Fq Ω) (Fbar Fq F Ω) where
  toFun z := ⟨Psi Fq F Ω hk (z : PicBar Ω hk), (mem_Pic0K _ _).2 (by rw [degPicK_Psi]; exact (mem_PicBar0 hk _).1 z.2)⟩
  invFun w := ⟨(Psi Fq F Ω hk).symm (w : PicK (kbar Fq Ω) (Fbar Fq F Ω)), (mem_PicBar0 hk _).2 (by rw [degBar_Psi_symm]; exact (mem_Pic0K _ _).1 w.2)⟩
  left_inv z := Subtype.ext ((Psi Fq F Ω hk).symm_apply_apply (z : PicBar Ω hk))
  right_inv w := Subtype.ext ((Psi Fq F Ω hk).apply_symm_apply (w : PicK (kbar Fq Ω) (Fbar Fq F Ω)))
  map_add' a b := Subtype.ext (map_add (Psi Fq F Ω hk) (a : PicBar Ω hk) (b : PicBar Ω hk))

theorem coe_Psi0Equiv (z : PicBar0 Ω hk) : (Psi0Equiv Fq F Ω hk z : PicK (kbar Fq Ω) (Fbar Fq F Ω)) = Psi Fq F Ω hk (z : PicBar Ω hk) :=
  rfl

end Psi

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_CoreB_Triv =====
section

/-!
# Core B, O2: the genus 0 case

* `degreeDataOfSubsingleton`: on a trivial group the constant degree `1` is degree data of genus `0`.
* `subsingleton_Pic0K_of_genus_zero`: for `g = 0` the group `Pic⁰(F / K)` is trivial.
* `subsingleton_PicBar0_of_genus_zero`: if `genusFK (kbar) (Fbar) = 0` then `PicBar0 Ω hk` is trivial.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CoreB

open RamanujanPetersson.JacAlg

section Pic0K

open RamanujanPetersson.JacComplete RamanujanPetersson.RR

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

end Pic0K

section PicBar0

open RamanujanPetersson.JacComplete RamanujanPetersson.JacFrob RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

theorem subsingleton_PicBar0_of_genus_zero (hg : genusFK (kbar Fq Ω) (Fbar Fq F Ω) = 0) :
    Subsingleton (PicBar0 Ω hk) := by
  have := subsingleton_Pic0K_of_genus_zero hg
  exact (Psi0Equiv Fq F Ω hk).injective.subsingleton

end PicBar0

end RamanujanPetersson.CoreB


end

-- ===== S4.Def_RP_JacFrob_BrSig =====
section

/-!
# S4-JacFrob, part BrSig (bridge 6): the bridge intertwines the two Frobenius actions

* `sig_incF`: on a level, `σ` is the level Frobenius `frobF`;
* `plE_contB`: `frob⁻¹ (contB j P) = contB j (σ⁻¹ P)`;
* `psiD_actD`, **`Psi_piBar`**: `Ψ ∘ π = σ_* ∘ Ψ` on `Pic(X-bar)`; `Psi_symm_sigPic`, `Psi0Equiv_piBar`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places ZetaSB RamanujanPetersson.JacComplete

section BrSig

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

/-- `frob⁻¹ (contB j P) = contB j (σ⁻¹ P)`. -/
theorem plE_contB (j : ℕ) (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) :
    plE (isConstExt_Fc Fq F Ω hk (lev j)) (frobL Fq (Lc Fq Ω (lev j))) (contB Fq F Ω hk j P) =
      contB Fq F Ω hk j ((sigPl Fq F Ω hk).symm P) := by
  apply placeN_ext Ω (lev j)
  · rw [isLeft_plE, isLeft_contB, isLeft_contB, isLeft_sigPl_symm]
  · intro f
    rw [ord_plE, ← frobF_apply, ord_contB, ord_contB, ord_sigPl_symm, sig_incF]

theorem psiD_actD (j : ℕ) (D : Places.Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    psiD Fq F Ω hk j (actD (isConstExt_Fc Fq F Ω hk (lev j)) (frobL Fq (Lc Fq Ω (lev j))) D) =
      sigD Fq F Ω hk (psiD Fq F Ω hk j D) := by
  ext P
  rw [psiD_apply, actD_apply, plE_contB, sigD_apply, psiD_apply]

/-- **`Ψ ∘ π = σ_* ∘ Ψ`**: the bridge intertwines the arithmetic Frobenius of `Pic(X-bar)` with `σ_*`. -/
theorem Psi_piBar (z : PicBar Ω hk) : Psi Fq F Ω hk (piBar Ω hk z) = sigPic Fq F Ω hk (Psi Fq F Ω hk z) := by
  refine AddCommGroup.DirectLimit.induction_on z fun j y => ?_
  change Psi Fq F Ω hk (piBar Ω hk (ofBar Ω hk j y)) = sigPic Fq F Ω hk (Psi Fq F Ω hk (ofBar Ω hk j y))
  rw [piBar_of, Psi_of, Psi_of]
  induction y using QuotientAddGroup.induction_on with
  | H D =>
    rw [frobN, actPic_mk, psiPic_mk, psiPic_mk, psiD_actD, sigPic_mk]

theorem Psi_symm_sigPic (w : PicK (kbar Fq Ω) (Fbar Fq F Ω)) :
    (Psi Fq F Ω hk).symm (sigPic Fq F Ω hk w) = piBar Ω hk ((Psi Fq F Ω hk).symm w) := by
  rw [AddEquiv.symm_apply_eq, Psi_piBar, AddEquiv.apply_symm_apply]

end BrSig

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_Poly =====
section

/-!
# S4-JacFrob, part Poly: `ℤ[π] → End(J)` for `J = J_{F-bar}` and the kernel/degree bridge to `Pic⁰(X-bar)` (L23)

* `piBar_mem_PicBar0`, **`piBar0 : Module.End ℤ (PicBar0 Ω hk)`** (the arithmetic Frobenius on `Pic⁰(X-bar)`);
* `Psi0Equiv_symm_piJ` (`π_J` acts on `J(k-bar) ≃ PicBar0` as `piBar0`);
* **`cls_polyEnd_piJ`** (`F(π_J)` acts as `aeval piBar0 F`), **`polyEnd_mul_piJ`**, `polyEnd_X_piJ` (the ring map `ℤ[π] → End(J)`);
* **`kerPtsEquiv_piJ`** (`Ker F(π_J)(k-bar) ≃ ker (aeval piBar0 F)`), **`degree_polyEnd_piJ`**
  (`deg F(π_J) = #ker (aeval piBar0 F)` for `p ∤ F(0)`: the `deg_eq_card_ker` field of `JacAlg.DegreeData`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable {M : Type*} [AddCommGroup M]

end Gen

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

set_option synthInstance.maxHeartbeats 100000 in
/-- `π` preserves `Pic⁰(X-bar)`. -/
theorem piBar_mem_PicBar0 (z : RamanujanPetersson.PicDescent.PicBar Ω hk)
    (hz : z ∈ RamanujanPetersson.PicDescent.PicBar0 Ω hk) :
    RamanujanPetersson.PicDescent.piBar Ω hk z ∈ RamanujanPetersson.PicDescent.PicBar0 Ω hk := by
  rw [← (Psi Fq F Ω hk).symm_apply_apply z, ← Psi_symm_sigPic, RamanujanPetersson.PicDescent.mem_PicBar0,
    degBar_Psi_symm, degPicK_sigPic, degPicK_Psi]
  exact (RamanujanPetersson.PicDescent.mem_PicBar0 hk z).1 hz

end Spec

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_Cone_ResGlob =====
section

/-!
# S4-PD (4), E4B part 5c: the global residue theorem

S3 setting (`F / 𝔽_q`, chart `(Rfin, F, Rinf)`), a finite level `M ≤ K_U` and representatives `Q t` of the
`Γ_H := π₁^geo ∩ Gal(K_U/M)`-orbits of boundary primes; `J t` is the inertia of `Q t` fixing `M`.

* `exists_tau_sum_eq_zero`: from one normalised generator per constant level (`htau`) there are `k₀ > 0` and
  generators `τ t ∈ J t`, normalised at every level `M ⊔ K(𝔽_{p^(e k)})` with `k₀ ∣ k`, such that
  `Σ_t χ(τ t) = 0` for EVERY locally constant additive `χ : Γ_H → ℤ/N` (global residue theorem).
* `htau_norm` (any chart): the level-wise hypothesis `htau` from `exists_norm_tau`.
* `exists_norm_tau_sum`: the same with the tame generators of `exists_norm_tau` and their characters `θ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

noncomputable section

section Chart

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]
variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

end Chart

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable (hζc : ∀ a, 0 < a → ∃ z : maxUnram (Places.Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1))

include hq he hζc in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **Global residue theorem** (S3 chart): generators `τ t` of the inertia groups `J t`, normalised at all constant
levels `M ⊔ K(𝔽_{p^(e k)})` (`k₀ ∣ k`), with `Σ_t χ(τ t) = 0` for every locally constant hom `χ : Γ_H → ℤ/N`. -/
theorem exists_tau_sum_eq_zero {N : ℕ} [NeZero N] (hN : IsUnit (N : Places.Rinf Fq F))
    {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    (hζNg : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), σ ζN = ζN)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {T : Type} [Fintype T] (Qt : T → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
    (hQt : ∀ t, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (Qt t))
    (hcover : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q → ∃ t,
      ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
        g ∈ (IntermediateField.restrict hMU).fixingSubgroup ∧ Q = g • Qt t)
    (hdisj : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hMU).fixingSubgroup → Qt t' = g • Qt t → t = t')
    (Γ : Subgroup (Pi1 (Places.Rfin Fq F) F))
    (hΓ : ∀ σ, σ ∈ Γ ↔ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ∧
      σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (J : T → Subgroup (Pi1 (Places.Rfin Fq F) F)) (hJΓ : ∀ t, J t ≤ Γ)
    (hJ : ∀ t, ∀ σ ∈ J t, σ ∈ (Qt t).inertia (Pi1 (Places.Rfin Fq F) F) ∧
      ∀ y : maxUnram (Places.Rfin Fq F) F, (y : AlgebraicClosure F) ∈ M → σ y = y)
    (P : ∀ t, J t → Prop)
    (htau : ∀ k, 0 < k → ∀ (hLU : M ⊔ constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F)
      [IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))]
      [IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))
        ↥(M ⊔ constLevel F p (e * k))]
      (t : T) (v : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))),
      v.asIdeal = (Qt t).comap (inclU (Places.Rinf Fq F) hLU) →
      ∃ τ : J t, P t τ ∧ ∀ (α : (maxUnram (Places.Rfin Fq F) F)ˣ) (b : ↥(M ⊔ constLevel F p (e * k))),
        (α : maxUnram (Places.Rfin Fq F) F) ^ N = IntermediateField.inclusion hLU b →
        kchar hζN (Γ := J t) α τ =
          ((WithZero.log (v.valuation ↥(M ⊔ constLevel F p (e * k)) b) : ℤ) : ZMod N)) :
    ∃ k₀, 0 < k₀ ∧ ∃ τ : ∀ t, J t, (∀ t, P t (τ t)) ∧
      (∀ k, 0 < k → k₀ ∣ k → ∀ (hLU : M ⊔ constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F)
        [IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))]
        [IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))
          ↥(M ⊔ constLevel F p (e * k))]
        (t : T) (v : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))),
        v.asIdeal = (Qt t).comap (inclU (Places.Rinf Fq F) hLU) →
        ∀ (α : (maxUnram (Places.Rfin Fq F) F)ˣ) (b : ↥(M ⊔ constLevel F p (e * k))),
          (α : maxUnram (Places.Rfin Fq F) F) ^ N = IntermediateField.inclusion hLU b →
          kchar hζN (Γ := J t) α (τ t) =
            ((WithZero.log (v.valuation ↥(M ⊔ constLevel F p (e * k)) b) : ℤ) : ZMod N)) ∧
      ∀ χ : Γ → ZMod N, IsLocallyConstant χ → (∀ σ σ', χ (σ * σ') = χ σ + χ σ') →
        ∑ t, χ ⟨τ t, hJΓ t (τ t).2⟩ = 0 := by
  have := hasFiniteQuotients_of_finiteQuot (S := Places.Rinf Fq F)
  obtain ⟨k₀, hk₀, τ, hP, hnorm⟩ := exists_stable_tau he hN hζN hM Qt hQt J hJ P htau
  refine ⟨k₀, hk₀, τ, hP, hnorm, fun χ hχc hχ => ?_⟩
  -- the character is Kummer, with radicand in a constant level
  have hζΓ : ∀ σ ∈ Γ, σ ζN = ζN := fun σ hσ => hζNg σ ((hΓ σ).1 hσ).1
  obtain ⟨α, hαr, hαχ⟩ := exists_kchar_eq hζN hζΓ χ hχc hχ
  have hfixx : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (p ^ e),
      σ ∈ (IntermediateField.restrict hMU).fixingSubgroup →
      σ ((α : maxUnram (Places.Rfin Fq F) F) ^ N) = (α : maxUnram (Places.Rfin Fq F) F) ^ N := by
    intro σ hσg hσM
    exact (mem_rad _ _ α).1 hαr σ ((hΓ σ).2 ⟨by rw [hq]; exact hσg, hσM⟩)
  obtain ⟨k1, hk1, hx1⟩ := exists_sup_constLevel_of_fixed he hMU hfixx
  -- one level `L = M ⊔ K(𝔽_{p^(e m)})` with `k₀ ∣ m`, `k1 ∣ m` and exact boundary residue degrees
  have hFDM : FiniteDimensional F M := hM.1
  have : IsGalois F M := hM.2.1
  obtain ⟨m0, hm0, hpow⟩ := exists_bdry_pow Fq M
  obtain ⟨m, hm_def⟩ : ∃ m, m = m0 * (k₀ * k1) := ⟨_, rfl⟩
  have hm : 0 < m := hm_def ▸ Nat.mul_pos hm0 (Nat.mul_pos hk₀ hk1)
  have hdvd0 : k₀ ∣ m := ⟨m0 * k1, by rw [hm_def]; ring⟩
  have hdvd1 : k1 ∣ m := ⟨m0 * k₀, by rw [hm_def]; ring⟩
  have hLM : M ⊔ constLevel F p (e * m) ∈ unramSet (Places.Rfin Fq F) F :=
    sup_mem_unramSet (Places.Rfin Fq F) F hM (constLevel_mem_unramSet (Places.Rfin Fq F) (Nat.mul_pos he hm))
  have hLU : M ⊔ constLevel F p (e * m) ≤ maxUnram (Places.Rfin Fq F) F := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hLM
  have hCU : constLevel F p (e * m) ≤ maxUnram (Places.Rfin Fq F) F := le_sup_right.trans hLU
  have hFDL : FiniteDimensional F ↥(M ⊔ constLevel F p (e * m)) := hLM.1
  have : IsGalois F ↥(M ⊔ constLevel F p (e * m)) := hLM.2.1
  have hDedI : IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) :=
    integralClosure.isDedekindDomain (A := Places.Rinf Fq F) (K := F) (L := ↥(M ⊔ constLevel F p (e * m)))
  have hFracI : IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m)))
      ↥(M ⊔ constLevel F p (e * m)) :=
    integralClosure.isFractionRing_of_finite_extension (A := Places.Rinf Fq F) F _
  have hDedF : IsDedekindDomain (integralClosure (Places.Rfin Fq F) ↥(M ⊔ constLevel F p (e * m))) :=
    integralClosure.isDedekindDomain (A := Places.Rfin Fq F) (K := F) (L := ↥(M ⊔ constLevel F p (e * m)))
  have hFracF : IsFractionRing (integralClosure (Places.Rfin Fq F) ↥(M ⊔ constLevel F p (e * m)))
      ↥(M ⊔ constLevel F p (e * m)) :=
    integralClosure.isFractionRing_of_finite_extension (A := Places.Rfin Fq F) F _
  have hres : ∀ w : Ideal (integralClosure (Places.Rinf Fq F) M), w.IsPrime → w ≠ ⊥ →
      ∀ y : integralClosure (Places.Rinf Fq F) M, y ^ (Fintype.card Fq ^ m) - y ∈ w := by
    intro w hw hw0 y
    rw [hm_def]
    exact hpow w hw hw0 _ y
  have hdi : ∀ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))),
      Nat.card (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m)) ⧸ w.asIdeal) =
        Fintype.card Fq ^ m :=
    fun w => card_bdry_sup hq he hζc hMU hm hres hCU w
  -- the orbit representatives for `Γ_H` are representatives for `π₁^geo ∩ Gal(K_U/L)`
  have hgC : ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hCU).fixingSubgroup := by
    intro g hg
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact fixed_of_mem_constLevel he (Nat.mul_pos he hm) ((IntermediateField.mem_restrict hCU _).1 hy) g
      (by rw [← hq]; exact hg)
  have hcoverL : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q → ∃ t,
      ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
        g ∈ (IntermediateField.restrict hLU).fixingSubgroup ∧ Q = g • Qt t := by
    intro Q hQ
    obtain ⟨t, g, hg, hgM, hQg⟩ := hcover Q hQ
    exact ⟨t, g, hg, mem_fix_sup hMU hCU hgM (hgC g hg), hQg⟩
  have hdisjL : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hLU).fixingSubgroup → Qt t' = g • Qt t → t = t' :=
    fun t t' g hg hgL h => hdisj t t' g hg (mem_fix_of_le hMU (le_sup_left.trans (le_fixF hLU hgL))) h
  -- the radicand as an element of `L`
  have hxL : (((α : maxUnram (Places.Rfin Fq F) F) ^ N : maxUnram (Places.Rfin Fq F) F) :
      AlgebraicClosure F) ∈ M ⊔ constLevel F p (e * m) :=
    sup_le_sup_left (constLevel_le_of_dvd (Nat.mul_pos he hm) (Nat.mul_dvd_mul_left e hdvd1)) M hx1
  let b : ↥(M ⊔ constLevel F p (e * m)) := ⟨_, hxL⟩
  have hαb : ((α : maxUnram (Places.Rfin Fq F) F) : AlgebraicClosure F) ^ N = (b : AlgebraicClosure F) :=
    (map_pow (maxUnram (Places.Rfin Fq F) F).val _ N).symm
  have hb : b ≠ 0 := by
    intro h
    have h2 : ((b : ↥(M ⊔ constLevel F p (e * m))) : AlgebraicClosure F) = 0 := by simp [h]
    rw [← hαb] at h2
    have h3 : ((α : maxUnram (Places.Rfin Fq F) F) : AlgebraicClosure F) = 0 :=
      (pow_eq_zero_iff (NeZero.ne N)).1 h2
    exact Units.ne_zero α (by exact_mod_cast h3)
  -- the places under the representatives, built along the S3 instance path (`bdryPlace` uses the generic one)
  let v : T → HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) := fun t =>
    ⟨(Qt t).comap (inclU (Places.Rinf Fq F) hLU), Ideal.IsPrime.comap _ (hK := (hQt t).1),
      comap_inclU_ne_bot hLU (hQt t)⟩
  refine sum_reps_eq_zero hq he hζc hLU hLM hm le_sup_right hdi Qt hQt hcoverL hdisjL
    v (fun t => rfl) (α : maxUnram (Places.Rfin Fq F) F).2 hb hαb
    (fun t => χ ⟨τ t, hJΓ t (τ t).2⟩) ?_
  intro t
  rw [← hαχ ⟨τ t, hJΓ t (τ t).2⟩]
  exact @hnorm m hm hdvd0 hLU hDedI hFracI t (v t) rfl α b (Subtype.ext rfl)

include hq he hζc in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **Global residue theorem with tame generators**: the generators `τ t` of `exists_norm_tau` (with their
characters `θ t`) can be chosen with `Σ_t χ(τ t) = 0` for every locally constant hom `χ : Γ_H → ℤ/N`. -/
theorem exists_norm_tau_sum {N : ℕ} [NeZero N] (hN : IsUnit (N : Places.Rinf Fq F))
    {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    (hζNg : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), σ ζN = ζN)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {T : Type} [Fintype T] (Qt : T → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
    (hQt : ∀ t, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (Qt t))
    (hcover : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q → ∃ t,
      ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
        g ∈ (IntermediateField.restrict hMU).fixingSubgroup ∧ Q = g • Qt t)
    (hdisj : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hMU).fixingSubgroup → Qt t' = g • Qt t → t = t')
    (Γ : Subgroup (Pi1 (Places.Rfin Fq F) F))
    (hΓ : ∀ σ, σ ∈ Γ ↔ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ∧
      σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (J : T → Subgroup (Pi1 (Places.Rfin Fq F) F)) (hJΓ : ∀ t, J t ≤ Γ)
    (hJ : ∀ t σ, σ ∈ J t ↔ σ ∈ (Qt t).inertia (Pi1 (Places.Rfin Fq F) F) ∧
      ∀ y : maxUnram (Places.Rfin Fq F) F, (y : AlgebraicClosure F) ∈ M → σ y = y)
    (d : T → ℕ) (hd0 : ∀ t, 0 < d t)
    (hNA : ∀ t, IsUnit ((N * d t : ℕ) : Places.Rfin Fq F))
    (hNR : ∀ t, IsUnit ((N * d t : ℕ) : Places.Rinf Fq F))
    (ζ : T → maxUnram (Places.Rfin Fq F) F) (hζ : ∀ t, IsPrimitiveRoot (ζ t) (N * d t))
    (hζI : ∀ t, ∀ σ ∈ (Qt t).inertia (Pi1 (Places.Rfin Fq F) F), σ (ζ t) = ζ t)
    (x : T → HeightOneSpectrum (Places.Rinf Fq F))
    (hx : ∀ t, (x t).asIdeal =
      (Qt t).comap (algebraMap (Places.Rinf Fq F) (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))))
    (a : T → Places.Rfin Fq F)
    (ha : ∀ t, 1 < (x t).valuation F (algebraMap (Places.Rfin Fq F) F (a t)))
    (kk : T → ℕ)
    (hd : ∀ t, ∀ σ ∈ (Qt t).inertia (Pi1 (Places.Rfin Fq F) F), σ ^ (p ^ kk t * d t) ∈ J t) :
    ∃ k₀, 0 < k₀ ∧ ∃ τ : ∀ t, J t,
      (∀ t, TauProp (Qt t) (J t) N (τ t)) ∧
      (∀ k, 0 < k → k₀ ∣ k → ∀ (hLU : M ⊔ constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F)
        [IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))]
        [IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))
          ↥(M ⊔ constLevel F p (e * k))]
        (t : T) (v : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))),
        v.asIdeal = (Qt t).comap (inclU (Places.Rinf Fq F) hLU) →
        ∀ (α : (maxUnram (Places.Rfin Fq F) F)ˣ) (b : ↥(M ⊔ constLevel F p (e * k))),
          (α : maxUnram (Places.Rfin Fq F) F) ^ N = IntermediateField.inclusion hLU b →
          kchar hζN (Γ := J t) α (τ t) =
            ((WithZero.log (v.valuation ↥(M ⊔ constLevel F p (e * k)) b) : ℤ) : ZMod N)) ∧
      ∀ χ : Γ → ZMod N, IsLocallyConstant χ → (∀ σ σ', χ (σ * σ') = χ σ + χ σ') →
        ∑ t, χ ⟨τ t, hJΓ t (τ t).2⟩ = 0 := by
  have := hasFiniteQuotients_of_finiteQuot (S := Places.Rinf Fq F)
  exact exists_tau_sum_eq_zero hq he hζc hN hζN hζNg hM hMU Qt hQt hcover hdisj Γ hΓ J hJΓ
    (fun t σ hσ => (hJ t σ).1 hσ)
    (fun t τ => TauProp (Qt t) (J t) N τ)
    (htau_norm he hζN (fun σ hσ => hζNg σ (by rw [hq]; exact hσ)) hM hMU Qt hQt J hJ d hd0 hNA hNR ζ hζ hζI
      x hx a ha kk hd)

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_Exist =====
section

/-!
# S4-PD (4), E4X part 2: existence of global characters with prescribed residues

S3 setting (`F / 𝔽_q`, chart `(Rfin, F, Rinf)`), a finite level `M ≤ K_U`, representatives `Q t` of the
`Γ_H := π₁^geo ∩ Gal(K_U/M)`-orbits of boundary primes and generators `τ t` of their inertia groups `J t`,
normalised at the constant levels `M ⊔ K(𝔽_{p^(e k)})`, `k₀ ∣ k` (output of `exists_norm_tau_sum`).

* `bij_reps`: at a level with exact boundary residue degrees, the places under the representatives are all the
  boundary places, each once.
* `exists_kchar_of_sum_zero` (**existence**, converse of the global residue theorem): under `PicDivX`, for every
  `c : T → ℤ/N` with `Σ_t c t = 0` there is a locally constant hom `χ : Γ_H → ℤ/N` with `χ(τ t) = c t`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CP4a CdOne TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

noncomputable section

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable (hζc : ∀ a, 0 < a → ∃ z : maxUnram (Places.Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1))

include hq he hζc in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **Existence** (converse of the global residue theorem): under `PicDivX`, every `c : T → ℤ/N` with `Σ_t c t = 0`
is `t ↦ χ(τ t)` for a locally constant hom `χ : Γ_H → ℤ/N`. -/
theorem exists_kchar_of_sum_zero {N : ℕ} [NeZero N] (hNA : IsUnit (N : Places.Rfin Fq F))
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p N)
    {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    (hζNg : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), σ ζN = ζN)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {T : Type} [Fintype T] (Qt : T → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
    (hQt : ∀ t, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (Qt t))
    (hcover : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q → ∃ t,
      ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
        g ∈ (IntermediateField.restrict hMU).fixingSubgroup ∧ Q = g • Qt t)
    (hdisj : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hMU).fixingSubgroup → Qt t' = g • Qt t → t = t')
    (Γ : Subgroup (Pi1 (Places.Rfin Fq F) F))
    (hΓ : ∀ σ, σ ∈ Γ ↔ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ∧
      σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (J : T → Subgroup (Pi1 (Places.Rfin Fq F) F)) (hJΓ : ∀ t, J t ≤ Γ)
    (τ : ∀ t, J t) {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hnorm : ∀ k, 0 < k → k₀ ∣ k → ∀ (hLU : M ⊔ constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F)
      [IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))]
      [IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))
        ↥(M ⊔ constLevel F p (e * k))]
      (t : T) (v : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))),
      v.asIdeal = (Qt t).comap (inclU (Places.Rinf Fq F) hLU) →
      ∀ (α : (maxUnram (Places.Rfin Fq F) F)ˣ) (b : ↥(M ⊔ constLevel F p (e * k))),
        (α : maxUnram (Places.Rfin Fq F) F) ^ N = IntermediateField.inclusion hLU b →
        kchar hζN (Γ := J t) α (τ t) =
          ((WithZero.log (v.valuation ↥(M ⊔ constLevel F p (e * k)) b) : ℤ) : ZMod N))
    (c : T → ZMod N) (hc : ∑ t, c t = 0) :
    ∃ χ : Γ → ZMod N, IsLocallyConstant χ ∧ (∀ σ σ', χ (σ * σ') = χ σ + χ σ') ∧
      ∀ t, χ ⟨τ t, hJΓ t (τ t).2⟩ = c t := by
  classical
  have := hasFiniteQuotients_of_finiteQuot (S := Places.Rinf Fq F)
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · exact ⟨fun _ => 0, IsLocallyConstant.const 0, fun _ _ => (add_zero 0).symm, fun t => isEmptyElim t⟩
  -- the level `L = M ⊔ K(𝔽_{p^(e m)})`, `k₀ ∣ m`, with exact boundary residue degrees
  have hFDM : FiniteDimensional F M := hM.1
  have : IsGalois F M := hM.2.1
  obtain ⟨m0, hm0, hpow⟩ := exists_bdry_pow Fq M
  obtain ⟨m, hm_def⟩ : ∃ m, m = m0 * k₀ := ⟨_, rfl⟩
  have hm : 0 < m := hm_def ▸ Nat.mul_pos hm0 hk₀
  have hdvd0 : k₀ ∣ m := ⟨m0, by rw [hm_def]; ring⟩
  have hLM : M ⊔ constLevel F p (e * m) ∈ unramSet (Places.Rfin Fq F) F :=
    sup_mem_unramSet (Places.Rfin Fq F) F hM (constLevel_mem_unramSet (Places.Rfin Fq F) (Nat.mul_pos he hm))
  have hLU : M ⊔ constLevel F p (e * m) ≤ maxUnram (Places.Rfin Fq F) F := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hLM
  have hCU : constLevel F p (e * m) ≤ maxUnram (Places.Rfin Fq F) F := le_sup_right.trans hLU
  have hFDL : FiniteDimensional F ↥(M ⊔ constLevel F p (e * m)) := hLM.1
  have : IsGalois F ↥(M ⊔ constLevel F p (e * m)) := hLM.2.1
  have hDedI : IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) :=
    integralClosure.isDedekindDomain (A := Places.Rinf Fq F) (K := F) (L := ↥(M ⊔ constLevel F p (e * m)))
  have hFracI : IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m)))
      ↥(M ⊔ constLevel F p (e * m)) :=
    integralClosure.isFractionRing_of_finite_extension (A := Places.Rinf Fq F) F _
  have hres : ∀ w : Ideal (integralClosure (Places.Rinf Fq F) M), w.IsPrime → w ≠ ⊥ →
      ∀ y : integralClosure (Places.Rinf Fq F) M, y ^ (Fintype.card Fq ^ m) - y ∈ w := by
    intro w hw hw0 y
    rw [hm_def]
    exact hpow w hw hw0 _ y
  have hdi : ∀ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))),
      Nat.card (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m)) ⧸ w.asIdeal) =
        Fintype.card Fq ^ m :=
    fun w => card_bdry_sup hq he hζc hMU hm hres hCU w
  -- geometric elements fix the constant levels
  have hgC : ∀ {k : ℕ} (hk : 0 < k) (hkU : constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F),
      ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hkU).fixingSubgroup := by
    intro k hk hkU g hg
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact fixed_of_mem_constLevel he (Nat.mul_pos he hk) ((IntermediateField.mem_restrict hkU _).1 hy) g
      (by rw [← hq]; exact hg)
  have hcoverL : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q → ∃ t,
      ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
        g ∈ (IntermediateField.restrict hLU).fixingSubgroup ∧ Q = g • Qt t := by
    intro Q hQ
    obtain ⟨t, g, hg, hgM, hQg⟩ := hcover Q hQ
    exact ⟨t, g, hg, mem_fix_sup hMU hCU hgM (hgC hm hCU g hg), hQg⟩
  have hdisjL : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hLU).fixingSubgroup → Qt t' = g • Qt t → t = t' :=
    fun t t' g hg hgL h => hdisj t t' g hg (mem_fix_of_le hMU (le_sup_left.trans (le_fixF hLU hgL))) h
  -- the boundary places of `L` are the `v t`, each once
  let v : T → HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) := fun t =>
    ⟨(Qt t).comap (inclU (Places.Rinf Fq F) hLU), Ideal.IsPrime.comap _ (hK := (hQt t).1),
      comap_inclU_ne_bot hLU (hQt t)⟩
  have hbij : Function.Bijective v :=
    bij_reps hq he hζc hLU hm le_sup_right hdi Qt hQt hcoverL hdisjL v (fun t => rfl)
  let eqv := Equiv.ofBijective v hbij
  -- an integer lift `D'` of `c` with total `0`
  let c' : T → ℤ := fun t => ((c t).val : ℤ)
  have hcast : ∀ t, ((c' t : ℤ) : ZMod N) = c t := fun t => by
    simp only [c', Int.cast_natCast, ZMod.natCast_zmod_val]
  let s : ℤ := ∑ t, c' t
  have hs : (s : ZMod N) = 0 := by
    show ((∑ t, c' t : ℤ) : ZMod N) = 0
    rw [Int.cast_sum]
    simp only [hcast]
    exact hc
  let D' : T → ℤ := fun t => c' t - if t = t₀ then s else 0
  have hD'sum : ∑ t, D' t = 0 := by
    simp only [D', Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact sub_self _
  have hD'c : ∀ t, ((D' t : ℤ) : ZMod N) = c t := by
    intro t
    simp only [D']
    rw [Int.cast_sub, hcast]
    split_ifs
    · rw [hs, sub_zero]
    · rw [Int.cast_zero, sub_zero]
  -- the boundary divisor `D = -D'` on `L`
  let D : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) → ℤ :=
    fun w => -D' (eqv.symm w)
  have hDv : ∀ t, D (v t) = -D' t := fun t => by
    show -D' (eqv.symm (eqv t)) = -D' t
    rw [Equiv.symm_apply_apply]
  have : Finite (HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m)))) :=
    Finite.of_equiv T eqv
  have hDfin : (Function.support D).Finite := Set.toFinite _
  have hDsum : ∑ᶠ w, D w = 0 := by
    rw [← finsum_comp_equiv eqv, finsum_eq_sum_of_fintype]
    have h : ∀ t, D (eqv t) = -D' t := hDv
    simp only [h, Finset.sum_neg_distrib, hD'sum, neg_zero]
  -- the Kummer root from `PicDivX`
  obtain ⟨m', hm', α, hα⟩ := exists_root_picDivX (hDL := hDedI) (hFL := hFracI) hPic hNA he hM hMU hLM hLU
    le_sup_left hdi D hDfin hDsum
  -- the level `L₂ = M ⊔ K(𝔽_{p^(e m m')})` contains `L·𝔽_{p^m'}` and `k₀ ∣ m m'`
  have hk : 0 < m * m' := Nat.mul_pos hm hm'
  have hdvd : k₀ ∣ m * m' := hdvd0.mul_right m'
  have hL12 : M ⊔ constLevel F p (e * m) ⊔ constLevel F p m' ≤ M ⊔ constLevel F p (e * (m * m')) := by
    refine sup_le (sup_le le_sup_left ((constLevel_le_of_dvd (Nat.mul_pos he hk) ?_).trans le_sup_right))
      ((constLevel_le_of_dvd (Nat.mul_pos he hk) ?_).trans le_sup_right)
    · exact Nat.mul_dvd_mul_left e (Dvd.intro m' rfl)
    · exact ⟨e * m, by ring⟩
  have hL2M : M ⊔ constLevel F p (e * (m * m')) ∈ unramSet (Places.Rfin Fq F) F :=
    sup_mem_unramSet (Places.Rfin Fq F) F hM (constLevel_mem_unramSet (Places.Rfin Fq F) (Nat.mul_pos he hk))
  have hL2U : M ⊔ constLevel F p (e * (m * m')) ≤ maxUnram (Places.Rfin Fq F) F := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hL2M
  have hC2U : constLevel F p (e * (m * m')) ≤ maxUnram (Places.Rfin Fq F) F := le_sup_right.trans hL2U
  have : FiniteDimensional F ↥(M ⊔ constLevel F p (e * (m * m'))) := hL2M.1
  have : IsGalois F ↥(M ⊔ constLevel F p (e * (m * m'))) := hL2M.2.1
  have hDedI2 : IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * (m * m')))) :=
    integralClosure.isDedekindDomain (A := Places.Rinf Fq F) (K := F)
      (L := ↥(M ⊔ constLevel F p (e * (m * m'))))
  have hFracI2 : IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * (m * m'))))
      ↥(M ⊔ constLevel F p (e * (m * m'))) :=
    integralClosure.isFractionRing_of_finite_extension (A := Places.Rinf Fq F) F _
  obtain ⟨b, hαb, hval⟩ := hα (m * m') hk hL12 hL2U
  -- `α` is a Kummer radical for `Γ_H`
  have hζΓ : ∀ σ ∈ Γ, σ ζN = ζN := fun σ hσ => hζNg σ ((hΓ σ).1 hσ).1
  have hαr : α ∈ rad Γ N := by
    refine (mem_rad Γ N α).2 fun σ hσ => ?_
    obtain ⟨hσg, hσM⟩ := (hΓ σ).1 hσ
    have hσL := mem_fix_sup hMU hC2U hσM (hgC hk hC2U σ hσg)
    rw [hαb]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσL _
      ((IntermediateField.mem_restrict _ _).2 b.2)
  refine ⟨kchar hζN (Γ := Γ) α, isLocallyConstant_kchar hζN α, kchar_mul hζN hζΓ hαr, fun t => ?_⟩
  have h1 : kchar hζN (Γ := Γ) α ⟨τ t, hJΓ t (τ t).2⟩ = kchar hζN (Γ := J t) α (τ t) := rfl
  let v2 : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * (m * m')))) :=
    ⟨(Qt t).comap (inclU (Places.Rinf Fq F) hL2U), Ideal.IsPrime.comap _ (hK := (hQt t).1),
      comap_inclU_ne_bot hL2U (hQt t)⟩
  rw [h1, @hnorm (m * m') hk hdvd hL2U hDedI2 hFracI2 t v2 rfl α b hαb]
  have h2 := @hval hDedI2 hFracI2 (Qt t) (hQt t) v2 rfl (v t) rfl
  rw [hDv t] at h2
  have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 h2
  push_cast at h3
  rw [← hD'c t]
  exact (neg_add_eq_zero.1 h3).symm

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_CdSub =====
section

/-!
# S4-PD (4)/(5), E1: `cd_l ≤ 1` for every CLOSED subgroup of `π₁^geo` (e.g. boundary inertia groups)

`Δ ≤ π₁^geo` closed. `E₀' := K_U^Δ ⊇ constFieldU`, `Gal(K_U/E₀') ≅ Δ` (closed: infinite Galois correspondence;
homeomorphism: compact to Hausdorff), and `hypL_of_field` applies to `K_U / E₀'`:
* C1: `isC1_subfield` (a subfield of an algebraic extension containing a C1 field is C1) with Tsen
  (`isC1_constFieldU`), giving `allC1_of_le`;
* Kummer closure: `kumClosure_of_picDiv_of_le` (from `PicDivU`).
Results: `hypL_of_closed`, **`h2_closed_eq_zero`** (`H²(Δ, M) = 0` for finite `lⁿ`-torsion `M` with open kernel),
`inertia_isClosed` (the inertia group `Q.inertia (Pi1 A K)` of a prime of the pro-chart is closed) and
`inertia_inf_isClosed` (so `I_s ∩ π₁^geo` is a closed subgroup of `π₁^geo`).
No local ramification theory is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace RamanujanPetersson.CdOne

open IntermediateField RamanujanPetersson.Tsen RamanujanPetersson.Kummer RamanujanPetersson.CurveCoh Topology

section Closed

variable {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]
  {p : ℕ} [Fact p.Prime] [CharP K p]
  (Fq : Type) [Field Fq] [Fintype Fq] [Algebra Fq K] {e : ℕ} (he : 0 < e) (hq : Fintype.card Fq = p ^ e)
  [Algebra (RatFunc Fq) K] [IsScalarTower Fq (RatFunc Fq) K] [Algebra.IsAlgebraic (RatFunc Fq) K]

include he hq in
/-- **`H²(Δ, M) = 0`** for a closed subgroup `Δ ≤ π₁^geo` and a finite `lⁿ`-torsion `π₁(U)`-module `M` with open
kernel (locally constant cochains on `Δ`), given `Pic(V̄)/l = 0`. -/
theorem h2_closed_eq_zero (hperf : ∀ (P : Ideal A) [P.IsMaximal], PerfectField P.ResidueField)
    (l : ℕ) [Fact l.Prime] (hN : IsUnit (l : A)) (hPic : PicDivU A K p l)
    (Δ : Subgroup (Pi1 A K)) (hΔ : IsClosed (Δ : Set (Pi1 A K))) (hΔg : Δ ≤ pi1geo A K (p ^ e))
    {k : Type*} [CommRing k] {M : Type u} [AddCommGroup M] [Module k M] (ρ : Representation k (Pi1 A K) M)
    (n : ℕ) [Finite M] (hM : ∀ m : M, (l ^ n) • m = 0) (hρ : IsOpen (ρ.ker : Set (Pi1 A K)))
    {f : Δ × Δ → M} (hf : IsLocallyConstant f)
    (hc : ∀ g h j : Δ, f (g * h, j) + f (g, h) = ρ g (f (h, j)) + f (g, h * j)) :
    ∃ b : Δ → M, IsLocallyConstant b ∧ ∀ g h : Δ, f (g, h) = ρ g (b h) - b (g * h) + b g := by
  haveI : CompactSpace Δ := isCompact_iff_compactSpace.mp hΔ.isCompact
  exact h2_eq_zero ρ Δ l (hypL_of_closed A Fq he hq hperf l hN hPic Δ hΔ hΔg) n hM hρ hf hc

end Closed

section Inertia

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
  (R0 : Type) [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]

end Inertia

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_Cone_H3 =====
section

/-!
# S4-PD (4), E4H3: the cone's `H³` vanishes

The cone's `H³` is `Π_s H²(Γ ⊓ I_s, M)`. For `Γ = π₁^geo` and closed `I_s` every factor vanishes by `cd_l ≤ 1` for
closed subgroups of `π₁^geo` (`CdOne.h2_closed_eq_zero`, with `Pic(V̄)/l = 0` as the explicit hypothesis). Stated in the
`H2All` form consumed by `PerfectCx` (`hall`, `hallI` of `ResHyp.h2Equiv`):
* `h2All_closed`, `h2All_geo` (`hall`), `h2All_geo_inf_inertia` (`hallI`, any ideal `Q` of a pro-chart).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open IntermediateField RamanujanPetersson.Kummer RamanujanPetersson.CurveCoh RamanujanPetersson.PerfectCx

section H3

variable {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]
  {p : ℕ} [Fact p.Prime] [CharP K p]
  (Fq : Type) [Field Fq] [Fintype Fq] [Algebra Fq K] {e : ℕ} (he : 0 < e) (hq : Fintype.card Fq = p ^ e)
  [Algebra (RatFunc Fq) K] [IsScalarTower Fq (RatFunc Fq) K] [Algebra.IsAlgebraic (RatFunc Fq) K]

include he hq in
/-- `H²(Δ, -) = 0` (`H2All`) for a closed `Δ ≤ π₁^geo`, given `Pic(V̄)/l = 0`. -/
theorem h2All_closed (hperf : ∀ (P : Ideal A) [P.IsMaximal], PerfectField P.ResidueField)
    (l : ℕ) [Fact l.Prime] (hN : IsUnit (l : A)) (hPic : PicDivU A K p l)
    (Δ : Subgroup (Pi1 A K)) (hΔ : IsClosed (Δ : Set (Pi1 A K))) (hΔg : Δ ≤ pi1geo A K (Fintype.card Fq))
    (Λ : Type) [CommRing Λ] (n : ℕ) : H2All Λ (Pi1 A K) Δ l n := by
  have hΔg' : Δ ≤ pi1geo A K (p ^ e) := by rw [← hq]; exact hΔg
  exact fun _ _ _ ρ _ hM hρ _ hf hc => h2_closed_eq_zero A Fq he hq hperf l hN hPic Δ hΔ hΔg' ρ n hM hρ hf hc

include he hq in
/-- `hall`: `H²(π₁^geo, -) = 0`. -/
theorem h2All_geo (hperf : ∀ (P : Ideal A) [P.IsMaximal], PerfectField P.ResidueField)
    (l : ℕ) [Fact l.Prime] (hN : IsUnit (l : A)) (hPic : PicDivU A K p l) (Λ : Type) [CommRing Λ] (n : ℕ) :
    H2All Λ (Pi1 A K) (pi1geo A K (Fintype.card Fq)) l n :=
  h2All_closed A Fq he hq hperf l hN hPic _ (pi1geo_isClosed A K _) le_rfl Λ n

variable {R0 : Type} [CommRing R0] [Algebra R0 K]

include he hq in
/-- `hallI` (**cone `H³ = 0`**): `H²(π₁^geo ∩ I(Q), -) = 0` for an ideal `Q` of the pro-chart. -/
theorem h2All_geo_inf_inertia (hperf : ∀ (P : Ideal A) [P.IsMaximal], PerfectField P.ResidueField)
    (l : ℕ) [Fact l.Prime] (hN : IsUnit (l : A)) (hPic : PicDivU A K p l) (Q : Ideal (proChart A K R0))
    (Λ : Type) [CommRing Λ] (n : ℕ) :
    H2All Λ (Pi1 A K) (pi1geo A K (Fintype.card Fq) ⊓ Q.inertia (Pi1 A K)) l n := by
  refine h2All_closed A Fq he hq hperf l hN hPic _ ?_ inf_le_left Λ n
  rw [inf_comm]
  exact inertia_inf_isClosed A K R0 _ Q

end H3

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_Cone_ResTr =====
section

/-!
# S4-PD E4S arithmetic ResA, part 2: transport of normalised generators under geometric conjugation

* `inclU_restrict`, `exists_valuation_transport` (L3): if `τ` is the restriction of `g` to a normal level `L`, the
  place of `L` under `g • Q` is the transport of the place under `Q`, and `v_{gQ}(τ b) = v_Q(b)`.
* `norm_conj` (L4, one level): a generator normalised at `(L, Q)` conjugates by `x` (fixing `ζ_N`) to a generator
  normalised at `(L, x • Q)`.
* `NormAll`, `normAll_conj` (L4, S3 chart): the same at all constant levels `M ⊔ K(𝔽_{p^(e k)})`, `k₀ ∣ k`.
* `chi_eq_of_norm` (L5): two generators normalised at the same prime have the same value under every locally
  constant hom `Γ_H → ℤ/N`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section Transport

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

end Transport

section Conj

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

end Conj

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
/-- `τ ∈ J` is normalised at `Q` at every constant level `M ⊔ K(𝔽_{p^(e k)})` with `k₀ ∣ k` (the `hnorm` shape of
`exists_norm_tau_sum`, for one prime). -/
abbrev NormAll (p e : ℕ) {N : ℕ} [NeZero N] {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    (M : IntermediateField F (AlgebraicClosure F))
    (Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))) (J : Subgroup (Pi1 (Places.Rfin Fq F) F))
    (τ : J) (k₀ : ℕ) : Prop :=
  ∀ k, 0 < k → k₀ ∣ k → ∀ (hLU : M ⊔ constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F)
    [IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))]
    [IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))
      ↥(M ⊔ constLevel F p (e * k))]
    (v : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))),
    v.asIdeal = Q.comap (inclU (Places.Rinf Fq F) hLU) →
    ∀ (α : (maxUnram (Places.Rfin Fq F) F)ˣ) (b : ↥(M ⊔ constLevel F p (e * k))),
      (α : maxUnram (Places.Rfin Fq F) F) ^ N = IntermediateField.inclusion hLU b →
      kchar hζN (Γ := J) α τ = ((WithZero.log (v.valuation ↥(M ⊔ constLevel F p (e * k)) b) : ℤ) : ZMod N)

variable {p e : ℕ} [Fact p.Prime] [CharP F p]
variable (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **(L4)** Conjugating a normalised geometric generator by `x` (fixing `ζ_N`) gives a normalised generator at
`x • Q`. -/
theorem normAll_conj {N : ℕ} [NeZero N] {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {J J' : Subgroup (Pi1 (Places.Rfin Fq F) F)} (τ : J)
    (hτg : (τ : Pi1 (Places.Rfin Fq F) F) ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq))
    (hτM : (τ : Pi1 (Places.Rfin Fq F) F) ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    {x : Pi1 (Places.Rfin Fq F) F} (hx : x ζN = ζN) (hτ' : x * (τ : Pi1 (Places.Rfin Fq F) F) * x⁻¹ ∈ J')
    {Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))} {k₀ : ℕ}
    (hn : NormAll p e hζN M Q J τ k₀) :
    NormAll p e hζN M (x • Q) J' ⟨x * (τ : Pi1 (Places.Rfin Fq F) F) * x⁻¹, hτ'⟩ k₀ := by
  intro k hk hdvd hLU hD hF v' hv' α b hαb
  have hLM : M ⊔ constLevel F p (e * k) ∈ unramSet (Places.Rfin Fq F) F :=
    sup_mem_unramSet (Places.Rfin Fq F) F hM (constLevel_mem_unramSet (Places.Rfin Fq F) (Nat.mul_pos he hk))
  have : IsGalois F ↥(M ⊔ constLevel F p (e * k)) := hLM.2.1
  have hCU : constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F := le_sup_right.trans hLU
  have hτC : (τ : Pi1 (Places.Rfin Fq F) F) ∈ (IntermediateField.restrict hCU).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact fixed_of_mem_constLevel he (Nat.mul_pos he hk) ((IntermediateField.mem_restrict hCU _).1 hy) _
      (by rw [← hq]; exact hτg)
  have hτL' := mem_fix_sup hMU hCU hτM hτC
  have hτL : ∀ y : ↥(M ⊔ constLevel F p (e * k)), (τ : Pi1 (Places.Rfin Fq F) F)
      (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU y := fun y =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτL' _ ((IntermediateField.mem_restrict _ _).2 y.2)
  exact norm_conj (hD := hD) (hF := hF) hLU hζN τ hx hτ' hτL Q (fun v hv => @hn k hk hdvd hLU hD hF v hv)
    v' hv' α b hαb

end S3

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_TwNorm =====
section

/-!
# S4-PD (4), arithmetic twist part B1: normalised generators under twisted conjugation

The twisted forms of `kchar_conj`, `norm_conj`, `normAll_conj` and `chi_eq_of_norm` (`Def_RP_Cone_ResTr`): if `x`
acts on `ζ_N` by `x ζ_N = ζ_N ^ w` (e.g. a Frobenius lift, `w = q`), then conjugating a normalised generator by `x`
gives a generator `w`-normalised at `x • Q` (`NormAllTw`), and a `w`-normalised generator has `w` times the
`χ`-value of a normalised one at the same prime (`chi_eq_of_normTw`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section ConjTw

variable {K E : Type} [Field K] [Field E] [Algebra K E] {N : ℕ} [NeZero N] {ζ : E}

end ConjTw

section Conj

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

end Conj

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable {p e : ℕ} [Fact p.Prime] [CharP F p]
variable (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **Twisted (L4)**: conjugating a normalised geometric generator by `x` with `x ζ_N = ζ_N ^ w` gives a
`w`-normalised generator at `x • Q`. -/
theorem normAll_conj_tw {N : ℕ} [NeZero N] {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {J J' : Subgroup (Pi1 (Places.Rfin Fq F) F)} (τ : J)
    (hτg : (τ : Pi1 (Places.Rfin Fq F) F) ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq))
    (hτM : (τ : Pi1 (Places.Rfin Fq F) F) ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    {x : Pi1 (Places.Rfin Fq F) F} {w : ZMod N} (hx : x ζN = epow ζN w)
    (hτ' : x * (τ : Pi1 (Places.Rfin Fq F) F) * x⁻¹ ∈ J')
    {Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))} {k₀ : ℕ}
    (hn : NormAll p e hζN M Q J τ k₀) :
    NormAllTw p e hζN M (x • Q) J' ⟨x * (τ : Pi1 (Places.Rfin Fq F) F) * x⁻¹, hτ'⟩ k₀ w := by
  intro k hk hdvd hLU hD hF v' hv' α b hαb
  have hLM : M ⊔ constLevel F p (e * k) ∈ unramSet (Places.Rfin Fq F) F :=
    sup_mem_unramSet (Places.Rfin Fq F) F hM (constLevel_mem_unramSet (Places.Rfin Fq F) (Nat.mul_pos he hk))
  have : IsGalois F ↥(M ⊔ constLevel F p (e * k)) := hLM.2.1
  have hCU : constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F := le_sup_right.trans hLU
  have hτC : (τ : Pi1 (Places.Rfin Fq F) F) ∈ (IntermediateField.restrict hCU).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact fixed_of_mem_constLevel he (Nat.mul_pos he hk) ((IntermediateField.mem_restrict hCU _).1 hy) _
      (by rw [← hq]; exact hτg)
  have hτL' := mem_fix_sup hMU hCU hτM hτC
  have hτL : ∀ y : ↥(M ⊔ constLevel F p (e * k)), (τ : Pi1 (Places.Rfin Fq F) F)
      (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU y := fun y =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτL' _ ((IntermediateField.mem_restrict _ _).2 y.2)
  exact norm_conj_tw (hD := hD) (hF := hF) hLU hζN τ hx hτ' hτL Q (fun v hv => @hn k hk hdvd hLU hD hF v hv)
    v' hv' α b hαb

end S3

end

end Residue
end RamanujanPetersson


end


