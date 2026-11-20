-- Prove2me | Definitions.Def_RPLib_F2_033
-- name    : RPLib_F2_033
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T14:50:58.386576+00:00
-- url     : https://prove2.me/theorems/35392a70-cc21-46bf-9143-7be49d3c4d49
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 033 of 70
-- statement:
--   File 033 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacLaw_InstA`: S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)`
--   * `S4.Def_RP_JacLaw_GenWit`: S4-JacLaw, file O9h (G5 GenWit): a witness point for the law data
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_029
import Definitions.Def_RPLib_F2_078

/-!
# Ramanujan-Petersson curve library (flat edition), file 033 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacLaw_InstA`: S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)`
* `S4.Def_RP_JacLaw_GenWit`: S4-JacLaw, file O9h (G5 GenWit): a witness point for the law data
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_InstA =====
section

/-!
# S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)`

`b_LL b_LR b_RR b_Lmu b_Rmu` (base identities through the nest) and `rel_assoc`.
-/

set_option autoImplicit false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk
open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

section Inst

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace LawData

variable (L : LawData K F)

section Rel

variable (x : Localization.Away L.ωm →ₐ[K] K) (xr : Localization.Away L.ωr →ₐ[K] K)
  (xl : Localization.Away L.ωl →ₐ[K] K)

variable {x xr xl} in
theorem b_Lmu {x' : Localization.Away L.ωm →ₐ[K] K} (h : pL x = x'.comp L.μm) :
    (L.mB (x.comp (nestK (K := K) L.mU))).comp (iL K F) = (x'.comp (nestK (K := K) L.mU)).comp L.mOutL :=
  (L.mB_L x).trans (h.trans (L.m_nest x'))

variable {x xr xl} in
theorem b_Rmu {x' : Localization.Away L.ωm →ₐ[K] K} (h : pR x = x'.comp L.μm) :
    (L.mB (x.comp (nestK (K := K) L.mU))).comp (iR K F) = (x'.comp (nestK (K := K) L.mU)).comp L.mOutL :=
  (L.mB_R x).trans (h.trans (L.m_nest x'))

end Rel

end LawData

end Inst

end RamanujanPetersson.JacLaw


end

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

/-- **The point set of `m(a,b)`** at a point `y` of the target of `mOut`, from the two `m`-roles. -/
theorem wit_mu_gen {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3))
    (D2 : NuData K F (genusFK K F + r2)) (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K))
    (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)) (φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T)
    (y : Localization.Away (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) →ₐ[K] K)
    {a b E c : Finset (Places.Rfin K F →ₐ[K] K)}
    (ha : ptSet ((mBase D3 D2 c0 c1 φa φb y).comp φa) = a) (hb : ptSet ((mBase D3 D2 c0 c1 φa φb y).comp φb) = b)
    (hm3 : RoleOn D3 (a ∪ b ∪ Finset.univ.image c0) E) (hm2 : RoleOn D2 (E ∪ Finset.univ.image c1) c) :
    ptSet (y.comp (mOut D3 D2 c0 c1 φa φb)) = c := by
  obtain ⟨y3, y2, -, -, h3, h2, hout⟩ := pts_mOut D3 D2 c0 c1 φa φb y
  rw [ha, hb] at h3
  rw [(hm3 y3 h3).2] at h2
  exact hout.trans (hm2 y2 h2).2

end Gen

variable (L : LawData K F) {a b E c : Finset (Places.Rfin K F →ₐ[K] K)}

/-- **`(a, b)` lies in `D(ωm)`.** -/
theorem wit_m {ta tb : Fin (genusFK K F) → (Places.Rfin K F →ₐ[K] K)}
    (ea : ptSet (symPt ta) = a) (eb : ptSet (symPt tb) = b)
    (hm3 : RoleOn L.Dm3 (a ∪ b ∪ Finset.univ.image L.c0) E) (hm2 : RoleOn L.Dm2 (E ∪ Finset.univ.image L.c1) c) :
    pair (symPt ta) (symPt tb) L.ωm ≠ 0 :=
  ne_numA_m (T := T0 K F) L.Dm3 L.Dm2 L.c0 L.c1 (iL K F) (iR K F) (pair (symPt ta) (symPt tb))
    (by rw [pair_iL, pair_iR, ea, eb]) hm3 (fun y hy => (hm2 y hy).1)

end GenWit

end RamanujanPetersson.JacLaw


end


