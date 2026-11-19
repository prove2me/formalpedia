-- Prove2me | Definitions.Def_RPLib_S4_CDPack33c
-- name    : RPLib_S4_CDPack33c
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T11:45:27.435388+00:00
-- url     : https://prove2.me/theorems/e2d03d87-976b-48d2-8829-a3b449ab3a8f
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 33c of 71
-- statement:
--   Part 33c of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_PicLw`: The Jacobian (unit S4-JacComplete), part `PicLw` (L20: Weil's law in `Pic`)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack33b
import Definitions.Def_RPLib_S4_CDPack25

/-!
# Curve-duality library package, part 33c of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_PicLw`: The Jacobian (unit S4-JacComplete), part `PicLw` (L20: Weil's law in `Pic`)
-/

set_option autoImplicit false

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

theorem clsK_add (D E : Places.Divisor K F) : clsK K F (D + E) = clsK K F D + clsK K F E :=
  QuotientAddGroup.mk_add _ D E

theorem clsK_sub (D E : Places.Divisor K F) : clsK K F (D - E) = clsK K F D - clsK K F E :=
  QuotientAddGroup.mk_sub _ D E

variable {T : Type*} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]
  {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3)) (D2 : NuData K F (genusFK K F + r2))
  (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)) (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K))

/-- The divisor `Θ = Hn3 - Hn2 - c0 + c1` of the law data. -/
noncomputable def ThetaD : Places.Divisor K F :=
  D3.Hn - D2.Hn - Zdiv (Finset.univ.image c0) + Zdiv (Finset.univ.image c1)

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

/-- `ψ(y) = [supp y] - [Θ]` on `K`-points of `S_g`. -/
noncomputable def psiL (y : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] K) : PicK K F :=
  clsK K F (Zdiv (ptSet y)) - clsK K F (ThetaD L.Dm3 L.Dm2 L.c0 L.c1)

set_option maxHeartbeats 1000000 in
theorem lawData_add (x : Localization.Away L.ωm →ₐ[K] K) :
    psiL L (x.comp L.μm) = psiL L (pL x) + psiL L (pR x) := by
  have h : clsK K F (Zdiv (ptSet ((x.comp (nestK (K := K) L.mU)).comp L.mOutL))) =
      clsK K F (Zdiv (ptSet ((L.mB (x.comp (nestK (K := K) L.mU))).comp (iL K F))) +
        Zdiv (ptSet ((L.mB (x.comp (nestK (K := K) L.mU))).comp (iR K F))) - ThetaD L.Dm3 L.Dm2 L.c0 L.c1) :=
    cls_mOut (T := T0 K F) L.Dm3 L.Dm2 L.c0 L.c1 (iL K F) (iR K F) (x.comp (nestK (K := K) L.mU))
  rw [L.mB_L x, L.mB_R x, ← L.m_nest x] at h
  rw [psiL, psiL, psiL, h, clsK_sub, clsK_add]
  abel

end Law

end RamanujanPetersson.JacComplete

end


