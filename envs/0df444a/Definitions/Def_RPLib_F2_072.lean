-- Prove2me | Definitions.Def_RPLib_F2_072
-- name    : RPLib_F2_072
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T13:21:32.197672+00:00
-- url     : https://prove2.me/theorems/0a93d977-db1d-4b40-907e-b37d8175e084
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 072 (part 2 of file 028 of 70)
-- statement:
--   File 072 (part 2 of file 028 of 70) of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacLaw_Law`: S4-JacLaw, file O8c: the law maps `m`, `r` and the inverse identities
--   * `S4.Def_RP_JacLaw_Assoc`: S4-JacLaw, file O8e: associativity of the law
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_026
import Definitions.Def_RPLib_F2_071

/-!
# Ramanujan-Petersson curve library (flat edition), file 072 (part 2 of file 028 of 70)

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacLaw_Law`: S4-JacLaw, file O8c: the law maps `m`, `r` and the inverse identities
* `S4.Def_RP_JacLaw_Assoc`: S4-JacLaw, file O8e: associativity of the law
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_Law =====
section

/-!
# S4-JacLaw, file O8c: the law maps `m`, `r` and the inverse identities

* `eq_of_ptSet_eq`: reduced points of `Sym^n` with the same support are equal.
* `back_mr`, `back_rm` (supports, two swap steps each): `r(a, m(a,b)) = b` and `m(a, r(a,c)) = c`.
* Generic source `T` (reduced, f.g.): `mOut D3 D2 c0 c1 φa φb : Sym^g → T[1/u3][1/u2]` with points
  `ν2(ν3(a + b + c0) + c1)`, and `rOut D3 D2 c0 c1 φa φc` with points `ν3(a + ν2(c + c1) + c0)` (the inverse
  `l(c,b)` of the other translation is `rOut` with `φa := φb` and its own data); point lemmas `pts_mOut`, `pts_rOut`.
* Composite identities at points: `r_mOut`, `l_mOut`, `m_rOut`, `m_lOut`.
* `LawData K F`: padding tuples and six choice data (roles m, r, l at levels 3 and 2, same `Hn` per level).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace NuData

end NuData

section Maps

variable {T : Type*} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]

/-- Inner step of `m`: `ν3(a + b + c0)` on `T[1/u3]`. -/
noncomputable def mIn {r3 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3))
    (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)) (φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T) :
    SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] Localization.Away (padMap (sumMap φa φb) c0 rfl D3.good) :=
  D3.nuStep (padMap (sumMap φa φb) c0 rfl)

/-- **The law** `m(a,b) = ν2(ν3(a + b + c0) + c1)` on `T[1/u3][1/u2]`. -/
noncomputable def mOut {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3))
    (D2 : NuData K F (genusFK K F + r2)) (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K))
    (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)) (φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T) :
    SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K]
      Localization.Away (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) :=
  D2.nuStep (padMap (mIn D3 c0 φa φb) c1 rfl)

/-- The point of `T` below a point of the target of `mOut`. -/
noncomputable def mBase {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3))
    (D2 : NuData K F (genusFK K F + r2)) (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K))
    (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)) (φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T)
    (x : Localization.Away (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) →ₐ[K] K) : T →ₐ[K] K :=
  baseAway _ (baseAway _ x)

/-- Inner step of `r`: `ν2(c + c1)` on `T[1/v2]`. -/
noncomputable def rIn {r2 : ℕ} (D2 : NuData K F (genusFK K F + r2)) (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K))
    (φc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T) :
    SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] Localization.Away (padMap φc c1 rfl D2.good) :=
  D2.nuStep (padMap φc c1 rfl)

/-- The point `a + ν2(c + c1)` of `Sym^(g+g)` over `T[1/v2]`. -/
noncomputable def rSum {r2 : ℕ} (D2 : NuData K F (genusFK K F + r2)) (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K))
    (φa φc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T) :
    SymRing K (Places.Rfin K F) (genusFK K F + genusFK K F) →ₐ[K] Localization.Away (padMap φc c1 rfl D2.good) :=
  sumMap ((IsScalarTower.toAlgHom K T _).comp φa) (rIn D2 c1 φc)

/-- **The inverse law** `r(a,c) = ν3(a + ν2(c + c1) + c0)` on `T[1/v2][1/v3]`. -/
noncomputable def rOut {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3))
    (D2 : NuData K F (genusFK K F + r2)) (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K))
    (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)) (φa φc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T) :
    SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K]
      Localization.Away (padMap (rSum D2 c1 φa φc) c0 rfl D3.good) :=
  D3.nuStep (padMap (rSum D2 c1 φa φc) c0 rfl)

/-- The point of `T` below a point of the target of `rOut`. -/
noncomputable def rBase {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3))
    (D2 : NuData K F (genusFK K F + r2)) (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K))
    (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)) (φa φc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T)
    (x : Localization.Away (padMap (rSum D2 c1 φa φc) c0 rfl D3.good) →ₐ[K] K) : T →ₐ[K] K :=
  baseAway _ (baseAway _ x)

variable {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3)) (D2 : NuData K F (genusFK K F + r2))
  (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)) (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K))

open Classical in
theorem pts_mOut (φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T)
    (x : Localization.Away (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) →ₐ[K] K) :
    ∃ (y3 : SymRing K (Places.Rfin K F) (genusFK K F + genusFK K F + r3) →ₐ[K] K)
      (y2 : SymRing K (Places.Rfin K F) (genusFK K F + r2) →ₐ[K] K), y3 D3.good ≠ 0 ∧ y2 D2.good ≠ 0 ∧
      ptSet y3 = ptSet ((mBase D3 D2 c0 c1 φa φb x).comp φa) ∪ ptSet ((mBase D3 D2 c0 c1 φa φb x).comp φb) ∪
        Finset.univ.image c0 ∧
      ptSet y2 = D3.nuF y3 ∪ Finset.univ.image c1 ∧
      ptSet (x.comp (mOut D3 D2 c0 c1 φa φb)) = D2.nuF y2 := by
  refine ⟨(baseAway _ (baseAway _ x)).comp (padMap (sumMap φa φb) c0 rfl),
    (baseAway _ x).comp (padMap (mIn D3 c0 φa φb) c1 rfl),
    D3.good_base (padMap (sumMap φa φb) c0 rfl) (baseAway _ x),
    D2.good_base (padMap (mIn D3 c0 φa φb) c1 rfl) x, ?_, ?_,
    D2.ptSet_nuStep (padMap (mIn D3 c0 φa φb) c1 rfl) x⟩
  · rw [comp_padMap, ptSet_padPt, comp_sumMap, ptSet_sumPt]
    rfl
  · rw [comp_padMap, ptSet_padPt]
    exact congrArg (· ∪ Finset.univ.image c1) (D3.ptSet_nuStep (padMap (sumMap φa φb) c0 rfl) (baseAway _ x))

open Classical in
theorem pts_rOut (φa φc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T)
    (x : Localization.Away (padMap (rSum D2 c1 φa φc) c0 rfl D3.good) →ₐ[K] K) :
    ∃ (y2 : SymRing K (Places.Rfin K F) (genusFK K F + r2) →ₐ[K] K)
      (y3 : SymRing K (Places.Rfin K F) (genusFK K F + genusFK K F + r3) →ₐ[K] K), y2 D2.good ≠ 0 ∧
      y3 D3.good ≠ 0 ∧ ptSet y2 = ptSet ((rBase D3 D2 c0 c1 φa φc x).comp φc) ∪ Finset.univ.image c1 ∧
      ptSet y3 = ptSet ((rBase D3 D2 c0 c1 φa φc x).comp φa) ∪ D2.nuF y2 ∪ Finset.univ.image c0 ∧
      ptSet (x.comp (rOut D3 D2 c0 c1 φa φc)) = D3.nuF y3 := by
  refine ⟨(baseAway _ (baseAway _ x)).comp (padMap φc c1 rfl),
    (baseAway _ x).comp (padMap (rSum D2 c1 φa φc) c0 rfl),
    D2.good_base (padMap φc c1 rfl) (baseAway _ x),
    D3.good_base (padMap (rSum D2 c1 φa φc) c0 rfl) x, ?_, ?_,
    D3.ptSet_nuStep (padMap (rSum D2 c1 φa φc) c0 rfl) x⟩
  · rw [comp_padMap, ptSet_padPt]
    rfl
  · rw [comp_padMap, ptSet_padPt]
    show ptSet ((baseAway _ x).comp (sumMap ((IsScalarTower.toAlgHom K T
      (Localization.Away (padMap φc c1 rfl D2.good))).comp φa) (rIn D2 c1 φc))) ∪ Finset.univ.image c0 = _
    rw [comp_sumMap, ptSet_sumPt]
    exact congrArg (fun s => ptSet ((rBase D3 D2 c0 c1 φa φc x).comp φa) ∪ s ∪ Finset.univ.image c0)
      (D2.ptSet_nuStep (padMap φc c1 rfl) (baseAway _ x))

end Maps

section Comp

variable {T : Type*} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]
  {T' : Type*} [CommRing T'] [Algebra K T'] [IsReduced T'] [Algebra.FiniteType K T']
  {r3 r2 : ℕ} {D3 D3' : NuData K F (genusFK K F + genusFK K F + r3)} {D2 D2' : NuData K F (genusFK K F + r2)}
  {c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)} {c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)}

/-- `r(a, m(a,b)) = b` at points (`D3', D2'` the `r` data). -/
theorem r_mOut (h3 : D3'.Hn = D3.Hn) (h2 : D2'.Hn = D2.Hn) {φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T}
    {ψa ψc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T'}
    (x : Localization.Away (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) →ₐ[K] K)
    (x' : Localization.Away (padMap (rSum D2' c1 ψa ψc) c0 rfl D3'.good) →ₐ[K] K)
    (ha : (rBase D3' D2' c0 c1 ψa ψc x').comp ψa = (mBase D3 D2 c0 c1 φa φb x).comp φa)
    (hc : (rBase D3' D2' c0 c1 ψa ψc x').comp ψc = x.comp (mOut D3 D2 c0 c1 φa φb)) :
    x'.comp (rOut D3' D2' c0 c1 ψa ψc) = (mBase D3 D2 c0 c1 φa φb x).comp φb := by
  classical
  obtain ⟨y3, y2, hy3, hy2, e3, e2, em⟩ := pts_mOut D3 D2 c0 c1 φa φb x
  obtain ⟨y2', y3', hy2', hy3', e2', e3', er⟩ := pts_rOut D3' D2' c0 c1 ψa ψc x'
  rw [ha] at e3'
  rw [hc, em] at e2'
  have key := NuData.back_mr rfl rfl h3 h2 hy3 hy2 hy2' hy3' (card_ptSet_le _) (card_ptSet_le _)
    (card_image_tuple c0) (card_image_tuple c1) e3 e2 e2' e3'
  exact eq_of_ptSet_eq (by rw [er, key]) (by rw [er, NuData.card_nuF hy3'])

/-- `l(m(a,b), b) = a` at points (`l(c,b) = rOut` with first argument `b`; `D3', D2'` the `l` data). -/
theorem l_mOut (h3 : D3'.Hn = D3.Hn) (h2 : D2'.Hn = D2.Hn) {φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T}
    {ψb ψc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T'}
    (x : Localization.Away (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) →ₐ[K] K)
    (x' : Localization.Away (padMap (rSum D2' c1 ψb ψc) c0 rfl D3'.good) →ₐ[K] K)
    (hb : (rBase D3' D2' c0 c1 ψb ψc x').comp ψb = (mBase D3 D2 c0 c1 φa φb x).comp φb)
    (hc : (rBase D3' D2' c0 c1 ψb ψc x').comp ψc = x.comp (mOut D3 D2 c0 c1 φa φb)) :
    x'.comp (rOut D3' D2' c0 c1 ψb ψc) = (mBase D3 D2 c0 c1 φa φb x).comp φa := by
  classical
  obtain ⟨y3, y2, hy3, hy2, e3, e2, em⟩ := pts_mOut D3 D2 c0 c1 φa φb x
  obtain ⟨y2', y3', hy2', hy3', e2', e3', er⟩ := pts_rOut D3' D2' c0 c1 ψb ψc x'
  rw [hb] at e3'
  rw [hc, em] at e2'
  rw [Finset.union_comm (ptSet ((mBase D3 D2 c0 c1 φa φb x).comp φa))] at e3
  have key := NuData.back_mr rfl rfl h3 h2 hy3 hy2 hy2' hy3' (card_ptSet_le _) (card_ptSet_le _)
    (card_image_tuple c0) (card_image_tuple c1) e3 e2 e2' e3'
  exact eq_of_ptSet_eq (by rw [er, key]) (by rw [er, NuData.card_nuF hy3'])

/-- `m(a, r(a,c)) = c` at points (`D3, D2` the `r` data, `D3', D2'` the `m` data). -/
theorem m_rOut (h3 : D3'.Hn = D3.Hn) (h2 : D2'.Hn = D2.Hn) {ψa ψc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T}
    {φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T'}
    (x' : Localization.Away (padMap (rSum D2 c1 ψa ψc) c0 rfl D3.good) →ₐ[K] K)
    (x : Localization.Away (padMap (mIn D3' c0 φa φb) c1 rfl D2'.good) →ₐ[K] K)
    (ha : (mBase D3' D2' c0 c1 φa φb x).comp φa = (rBase D3 D2 c0 c1 ψa ψc x').comp ψa)
    (hb : (mBase D3' D2' c0 c1 φa φb x).comp φb = x'.comp (rOut D3 D2 c0 c1 ψa ψc)) :
    x.comp (mOut D3' D2' c0 c1 φa φb) = (rBase D3 D2 c0 c1 ψa ψc x').comp ψc := by
  classical
  obtain ⟨y2, y3, hy2, hy3, e2, e3, er⟩ := pts_rOut D3 D2 c0 c1 ψa ψc x'
  obtain ⟨y3', y2', hy3', hy2', e3', e2', em⟩ := pts_mOut D3' D2' c0 c1 φa φb x
  rw [ha, hb, er] at e3'
  have key := NuData.back_rm rfl rfl h3 h2 hy2 hy3 hy3' hy2' (card_ptSet_le _) (card_ptSet_le _)
    (card_image_tuple c0) (card_image_tuple c1) e2 e3 e3' e2'
  exact eq_of_ptSet_eq (by rw [em, key]) (by rw [em, NuData.card_nuF hy2'])

/-- `m(l(c,b), b) = c` at points (`D3, D2` the `l` data, `D3', D2'` the `m` data). -/
theorem m_lOut (h3 : D3'.Hn = D3.Hn) (h2 : D2'.Hn = D2.Hn) {ψb ψc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T}
    {φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T'}
    (x' : Localization.Away (padMap (rSum D2 c1 ψb ψc) c0 rfl D3.good) →ₐ[K] K)
    (x : Localization.Away (padMap (mIn D3' c0 φa φb) c1 rfl D2'.good) →ₐ[K] K)
    (ha : (mBase D3' D2' c0 c1 φa φb x).comp φa = x'.comp (rOut D3 D2 c0 c1 ψb ψc))
    (hb : (mBase D3' D2' c0 c1 φa φb x).comp φb = (rBase D3 D2 c0 c1 ψb ψc x').comp ψb) :
    x.comp (mOut D3' D2' c0 c1 φa φb) = (rBase D3 D2 c0 c1 ψb ψc x').comp ψc := by
  classical
  obtain ⟨y2, y3, hy2, hy3, e2, e3, er⟩ := pts_rOut D3 D2 c0 c1 ψb ψc x'
  obtain ⟨y3', y2', hy3', hy2', e3', e2', em⟩ := pts_mOut D3' D2' c0 c1 φa φb x
  rw [ha, hb, er, Finset.union_comm (D3.nuF y3)] at e3'
  have key := NuData.back_rm rfl rfl h3 h2 hy2 hy3 hy3' hy2' (card_ptSet_le _) (card_ptSet_le _)
    (card_image_tuple c0) (card_image_tuple c1) e2 e3 e3' e2'
  exact eq_of_ptSet_eq (by rw [em, key]) (by rw [em, NuData.card_nuF hy2'])

end Comp

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_Assoc =====
section

/-!
# S4-JacLaw, file O8e: associativity of the law

* `const_of_mem` (`ℓ(ν(y)) = 1`): at a good `y`, every `f ∈ L(Zdiv (nuF y))` is constant
  (`f · sec y ∈ L(Hn) ∩ B` vanishes on the points of `y`, so it is a multiple of `sec y`).
* `eq_nuF_of_div`: `div u = Zdiv S - Zdiv (nuF y)` with `u ≠ 0` forces `S = nuF y`.
* `div_sec3`, `div_sec2`: the divisor of a good section split along a decomposition of the support.
* **`assoc_sets`**: four `m`-instances with the same data, `m(m(a,b),c)` and `m(a,m(b,c))` have the same support
  (`u = t3 t1 s4 s2 / (s3 s1 t4 t2)` has `div u = Zdiv f - Zdiv f'`).
* **`assoc_mOut`**: associativity at points of the targets of `mOut`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

section Assoc

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace NuData

variable {d : ℕ} {D : NuData K F d} {y : SymRing K (Places.Rfin K F) d →ₐ[K] K}

end NuData

section Pt

variable {T1 T2 T3 T4 : Type*} [CommRing T1] [Algebra K T1] [IsReduced T1] [Algebra.FiniteType K T1]
  [CommRing T2] [Algebra K T2] [IsReduced T2] [Algebra.FiniteType K T2]
  [CommRing T3] [Algebra K T3] [IsReduced T3] [Algebra.FiniteType K T3]
  [CommRing T4] [Algebra K T4] [IsReduced T4] [Algebra.FiniteType K T4]
  {r3 r2 : ℕ} {D3 : NuData K F (genusFK K F + genusFK K F + r3)} {D2 : NuData K F (genusFK K F + r2)}
  {c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)} {c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)}

/-- **Associativity at points**: `m(m(a,b),c) = m(a,m(b,c))` (`x1 : m(a,b)`, `x2 : m(b,c)`, `x3 : m(m(a,b),c)`,
`x4 : m(a,m(b,c))`, glued by the base relations). -/
theorem assoc_mOut {φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T1}
    {φb' φc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T2}
    {ψab ψc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T3}
    {χa χbc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T4}
    (x1 : Localization.Away (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) →ₐ[K] K)
    (x2 : Localization.Away (padMap (mIn D3 c0 φb' φc) c1 rfl D2.good) →ₐ[K] K)
    (x3 : Localization.Away (padMap (mIn D3 c0 ψab ψc) c1 rfl D2.good) →ₐ[K] K)
    (x4 : Localization.Away (padMap (mIn D3 c0 χa χbc) c1 rfl D2.good) →ₐ[K] K)
    (ha : (mBase D3 D2 c0 c1 χa χbc x4).comp χa = (mBase D3 D2 c0 c1 φa φb x1).comp φa)
    (hb : (mBase D3 D2 c0 c1 φb' φc x2).comp φb' = (mBase D3 D2 c0 c1 φa φb x1).comp φb)
    (hc : (mBase D3 D2 c0 c1 ψab ψc x3).comp ψc = (mBase D3 D2 c0 c1 φb' φc x2).comp φc)
    (hab : (mBase D3 D2 c0 c1 ψab ψc x3).comp ψab = x1.comp (mOut D3 D2 c0 c1 φa φb))
    (hbc : (mBase D3 D2 c0 c1 χa χbc x4).comp χbc = x2.comp (mOut D3 D2 c0 c1 φb' φc)) :
    x3.comp (mOut D3 D2 c0 c1 ψab ψc) = x4.comp (mOut D3 D2 c0 c1 χa χbc) := by
  obtain ⟨y31, y21, h31, h21, e31, e21, em1⟩ := pts_mOut D3 D2 c0 c1 φa φb x1
  obtain ⟨y32, y22, h32, h22, e32, e22, em2⟩ := pts_mOut D3 D2 c0 c1 φb' φc x2
  obtain ⟨y33, y23, h33, h23, e33, e23, em3⟩ := pts_mOut D3 D2 c0 c1 ψab ψc x3
  obtain ⟨y34, y24, h34, h24, e34, e24, em4⟩ := pts_mOut D3 D2 c0 c1 χa χbc x4
  rw [hb] at e32
  rw [hab, em1, hc] at e33
  rw [ha, hbc, em2] at e34
  have key := NuData.assoc_sets h31 h32 h33 h34 h21 h22 h23 h24 (card_ptSet_le _) (card_ptSet_le _)
    (card_ptSet_le _) (card_image_tuple c0) (card_image_tuple c1) e31 e21 e32 e22 e33 e23 e34 e24
  exact eq_of_ptSet_eq (by rw [em3, em4, key]) (by rw [em3, NuData.card_nuF h23])

end Pt

end Assoc

end RamanujanPetersson.JacLaw


end


