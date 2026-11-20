-- Prove2me | Definitions.Def_RPLib_F2_034
-- name    : RPLib_F2_034
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T15:02:45.352364+00:00
-- url     : https://prove2.me/theorems/1c8e53d6-6bcf-4656-a25e-67ab3f4f857f
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 034 of 70
-- statement:
--   File 034 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacComplete_PicLr`: The Jacobian (unit S4-JacComplete), part `PicLr` (L20: rigidity of `psiL`)
--   * `S4.Def_RP_JacComplete_CommLaw`: The Jacobian (unit S4-JacComplete), part `CommLaw` (L22: Weil's law is commutative at points)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_033
import Definitions.Def_RPLib_F2_079

/-!
# Ramanujan-Petersson curve library (flat edition), file 034 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacComplete_PicLr`: The Jacobian (unit S4-JacComplete), part `PicLr` (L20: rigidity of `psiL`)
* `S4.Def_RP_JacComplete_CommLaw`: The Jacobian (unit S4-JacComplete), part `CommLaw` (L22: Weil's law is commutative at points)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_PicLr =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicLr` (L20: rigidity of `psiL`)

`lawData_rigid`: a `K`-point with the same class as an output of Weil's law is that output (outputs are nonspecial).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory Limits AlgebraicGeometry
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section Law

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (L : LawData K F)

set_option maxHeartbeats 1000000 in
theorem lawData_rigid (x : Localization.Away L.ωm →ₐ[K] K) (y : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] K)
    (e : psiL L y = psiL L (x.comp L.μm)) : y = x.comp L.μm := by
  obtain ⟨y3, y2, h3, h2, -, -, em⟩ :=
    pts_mOut (T := T0 K F) L.Dm3 L.Dm2 L.c0 L.c1 (iL K F) (iR K F) (x.comp (nestK (K := K) L.mU))
  have em' : ptSet (x.comp L.μm) = L.Dm2.nuF y2 := by rw [L.m_nest x]; exact em
  rw [psiL, psiL, sub_left_inj] at e
  obtain ⟨f, hf, hdiv⟩ := (mem_PrincK K F).1 ((clsK_eq_iff K F).1 e)
  have hS : ptSet y = L.Dm2.nuF y2 := by
    refine NuData.eq_nuF_of_div (by omega) h2 (inv_ne_zero hf) ?_
    rw [divK_inv K hf, hdiv, em']; abel
  refine eq_of_ptSet_eq (hS.trans em'.symm) ?_
  rw [hS, NuData.card_nuF h2]

end Law

end RamanujanPetersson.JacComplete


end

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

open Classical in
/-- **Commutativity at points**: `m(a,b) = m(b,a)` (`x1 : m(a,b)`, `x2 : m(b,a)`). -/
theorem comm_mOut {φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T1}
    {φa' φb' : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T2}
    (x1 : Localization.Away (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) →ₐ[K] K)
    (x2 : Localization.Away (padMap (mIn D3 c0 φa' φb') c1 rfl D2.good) →ₐ[K] K)
    (ha : (mBase D3 D2 c0 c1 φa' φb' x2).comp φa' = (mBase D3 D2 c0 c1 φa φb x1).comp φb)
    (hb : (mBase D3 D2 c0 c1 φa' φb' x2).comp φb' = (mBase D3 D2 c0 c1 φa φb x1).comp φa) :
    x1.comp (mOut D3 D2 c0 c1 φa φb) = x2.comp (mOut D3 D2 c0 c1 φa' φb') := by
  obtain ⟨y31, y21, h31, h21, e31, e21, em1⟩ := pts_mOut D3 D2 c0 c1 φa φb x1
  obtain ⟨y32, y22, -, -, e32, e22, em2⟩ := pts_mOut D3 D2 c0 c1 φa' φb' x2
  rw [ha, hb] at e32
  have h3 : y31 = y32 := eq_of_ptSet_eq
    (by rw [e31, e32, Finset.union_comm (ptSet ((mBase D3 D2 c0 c1 φa φb x1).comp φa))])
    (NuData.card_ptSet h31)
  have h2 : y21 = y22 := eq_of_ptSet_eq (by rw [e21, e22, h3]) (NuData.card_ptSet h21)
  exact eq_of_ptSet_eq (by rw [em1, em2, h2]) (by rw [em1, NuData.card_nuF h21])

end Pt

universe u

section Law

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (L : LawData K F)

set_option maxHeartbeats 400000 in
theorem lawData_law_comm (y y' : Localization.Away L.mU →ₐ[K] K)
    (ha : (L.mB y').comp (iL K F) = (L.mB y).comp (iR K F))
    (hb : (L.mB y').comp (iR K F) = (L.mB y).comp (iL K F)) : y.comp L.mOutL = y'.comp L.mOutL :=
  comm_mOut (T1 := T0 K F) (T2 := T0 K F) (D3 := L.Dm3) (D2 := L.Dm2) (c0 := L.c0) (c1 := L.c1)
    (φa := iL K F) (φb := iR K F) (φa' := iL K F) (φb' := iR K F) y y' ha hb

end Law

end RamanujanPetersson.JacComplete


end


