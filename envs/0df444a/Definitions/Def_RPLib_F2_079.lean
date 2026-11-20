-- Prove2me | Definitions.Def_RPLib_F2_079
-- name    : RPLib_F2_079
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T14:58:02.83967+00:00
-- url     : https://prove2.me/theorems/c76a35a8-fea8-4fc0-aeee-09aadf0a67c9
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 079 (part 1 of file 034 of 70)
-- statement:
--   File 079 (part 1 of file 034 of 70) of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacLaw_GenWit`: S4-JacLaw, file O9h (G5 GenWit): a witness point for the law data
--   * `S4.Def_RP_JacComplete_PicLw`: The Jacobian (unit S4-JacComplete), part `PicLw` (L20: Weil's law in `Pic`)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_033

/-!
# Ramanujan-Petersson curve library (flat edition), file 079 (part 1 of file 034 of 70)

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacLaw_GenWit`: S4-JacLaw, file O9h (G5 GenWit): a witness point for the law data
* `S4.Def_RP_JacComplete_PicLw`: The Jacobian (unit S4-JacComplete), part `PicLw` (L20: Weil's law in `Pic`)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_GenWit =====
section

/-!
# S4-JacLaw, file O9h (G5 GenWit): a witness point for the law data

* `wit_mu_gen`: the point set of `m(a,b)` at a point of the `mOut` target, from the two `m`-roles (any `T`).
* `pair_iL`, `pair_iR`; `wit_m`, `wit_mu`, `wit_r`, `wit_l`: the four steps at `T0 = S_g ⊗ S_g`.
* **`exists_lawData_wit`**: `∃ L : LawData K F, ∃ x, x (phiS L.μm L.ωr) ≠ 0 ∧ x (psiS L.μm L.ωl) ≠ 0`
  (the hypothesis `hw` of `LawData.toPre` / `LawData.chunk`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk
open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

section GenWit

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

section Gen

variable {T : Type u} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]

end Gen

variable (L : LawData K F) {a b E c : Finset (Places.Rfin K F →ₐ[K] K)}

/-- **`m(a, b)` has point set `c`.** -/
theorem wit_mu {ta tb : Fin (genusFK K F) → (Places.Rfin K F →ₐ[K] K)}
    (ea : ptSet (symPt ta) = a) (eb : ptSet (symPt tb) = b)
    (hm3 : RoleOn L.Dm3 (a ∪ b ∪ Finset.univ.image L.c0) E) (hm2 : RoleOn L.Dm2 (E ∪ Finset.univ.image L.c1) c)
    (x : Localization.Away L.ωm →ₐ[K] K) (hxL : pL x = symPt ta) (hxR : pR x = symPt tb) :
    ptSet (x.comp L.μm) = c := by
  rw [L.m_nest x]
  exact wit_mu_gen L.Dm3 L.Dm2 L.c0 L.c1 (iL K F) (iR K F) (x.comp (nestK (K := K) L.mU))
    ((congrArg ptSet ((L.mB_L x).trans hxL)).trans ea) ((congrArg ptSet ((L.mB_R x).trans hxR)).trans eb) hm3 hm2

/-- **`(a, m(a,b))` lies in `D(ωr)`.** -/
theorem wit_r {ta : Fin (genusFK K F) → (Places.Rfin K F →ₐ[K] K)} (ea : ptSet (symPt ta) = a)
    (hr2 : RoleOn L.Dr2 (c ∪ Finset.univ.image L.c1) E) (hr3 : RoleOn L.Dr3 (a ∪ E ∪ Finset.univ.image L.c0) b)
    (w : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] K) (hw : ptSet w = c) :
    pair (symPt ta) w L.ωr ≠ 0 :=
  ne_numA_r (T := T0 K F) L.Dr3 L.Dr2 L.c0 L.c1 (iL K F) (iR K F) (pair (symPt ta) w)
    (by rw [pair_iR, hw]) hr2 (by rw [pair_iL, ea]) (fun y hy => (hr3 y hy).1)

/-- **`(m(a,b), b)` lies in `D(ωl)`.** -/
theorem wit_l {tb : Fin (genusFK K F) → (Places.Rfin K F →ₐ[K] K)} (eb : ptSet (symPt tb) = b)
    (hl2 : RoleOn L.Dl2 (c ∪ Finset.univ.image L.c1) E) (hl3 : RoleOn L.Dl3 (b ∪ E ∪ Finset.univ.image L.c0) a)
    (w : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] K) (hw : ptSet w = c) :
    pair w (symPt tb) L.ωl ≠ 0 :=
  ne_numA_r (T := T0 K F) L.Dl3 L.Dl2 L.c0 L.c1 (iR K F) (iL K F) (pair w (symPt tb))
    (by rw [pair_iL, hw]) hl2 (by rw [pair_iR, eb]) (fun y hy => (hl3 y hy).1)

theorem LawData.HasWit.out (h : L.HasWit) :
    ∃ x : Localization.Away L.ωm →ₐ[K] K, x (phiS L.μm L.ωr) ≠ 0 ∧ x (psiS L.μm L.ωl) ≠ 0 := h

end GenWit

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacComplete_PicLw =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicLw` (L20: Weil's law in `Pic`)

* `cls_mOut`: `[m(a,b)] = [a] + [b] - [Θ]` (`Θ = ThetaD = Hn3 - Hn2 - c0 + c1`), from `div_sec3`, `div_sec2`;
  `card_mBase_L`: inputs of the law are reduced of degree `g`.
* `psiL L y = [supp y] - [Θ]`: additive for the law (`lawData_add`) and (`lawData_rigid` is in `PicLr`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory Limits AlgebraicGeometry
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section Pt

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable {T : Type*} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]
  {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3)) (D2 : NuData K F (genusFK K F + r2))
  (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)) (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K))

/-- **The law in `Pic`**: `[m(a,b)] = [a + b - Θ]`. -/
theorem cls_mOut (φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T)
    (x : Localization.Away (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) →ₐ[K] K) :
    clsK K F (Zdiv (ptSet (x.comp (mOut D3 D2 c0 c1 φa φb)))) =
      clsK K F (Zdiv (ptSet ((mBase D3 D2 c0 c1 φa φb x).comp φa)) +
        Zdiv (ptSet ((mBase D3 D2 c0 c1 φa φb x).comp φb)) - ThetaD D3 D2 c0 c1) := by
  obtain ⟨y3, y2, h3, h2, e3, e2, em⟩ := pts_mOut D3 D2 c0 c1 φa φb x
  have d3 := NuData.div_sec3 h3 (card_ptSet_le _) (card_ptSet_le _) (card_image_tuple c0) e3
  have d2 := NuData.div_sec2 h2 (NuData.card_nuF h3).le (card_image_tuple c1) e2
  rw [clsK_eq_iff, em]
  have key : -Zdiv (D2.nuF y2) + (Zdiv (ptSet ((mBase D3 D2 c0 c1 φa φb x).comp φa)) +
      Zdiv (ptSet ((mBase D3 D2 c0 c1 φa φb x).comp φb)) - ThetaD D3 D2 c0 c1) =
      PlacesK.div (incB K F (D3.sec y3)) - PlacesK.div (incB K F (D2.sec y2)) := by
    rw [d3, d2, ThetaD]; abel
  rw [key]
  exact sub_mem (div_mem_PrincK K F (incB_sec_ne_zero h3)) (div_mem_PrincK K F (incB_sec_ne_zero h2))

/-- Every input of the law is reduced of degree `g`. -/
theorem card_mBase_L (φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T)
    (x : Localization.Away (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) →ₐ[K] K) :
    (ptSet ((mBase D3 D2 c0 c1 φa φb x).comp φa)).card = genusFK K F := by
  obtain ⟨y3, -, h3, -, e3, -, -⟩ := pts_mOut D3 D2 c0 c1 φa φb x
  have hc := NuData.card_ptSet h3
  rw [e3] at hc
  have h1 := Finset.card_union_le (ptSet ((mBase D3 D2 c0 c1 φa φb x).comp φa) ∪
    ptSet ((mBase D3 D2 c0 c1 φa φb x).comp φb)) (Finset.univ.image c0)
  have h2 := Finset.card_union_le (ptSet ((mBase D3 D2 c0 c1 φa φb x).comp φa))
    (ptSet ((mBase D3 D2 c0 c1 φa φb x).comp φb))
  have h4 := card_ptSet_le ((mBase D3 D2 c0 c1 φa φb x).comp φa)
  have h5 := card_ptSet_le ((mBase D3 D2 c0 c1 φa φb x).comp φb)
  have h6 := card_image_tuple c0
  omega

end Pt

section Law

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (L : LawData K F)

end Law

end RamanujanPetersson.JacComplete


end


