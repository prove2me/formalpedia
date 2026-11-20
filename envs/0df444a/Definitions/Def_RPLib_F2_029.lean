-- Prove2me | Definitions.Def_RPLib_F2_029
-- name    : RPLib_F2_029
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T14:08:30.866584+00:00
-- url     : https://prove2.me/theorems/b93106be-3a6c-4cd7-b2f4-4935c2ee767c
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 029 of 70
-- statement:
--   File 029 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacLaw_InstBase`: S4-JacLaw, file O10e (part Base): points below points of `D(numA _)`
--   * `S4.Def_RP_JacLaw_GenRole`: S4-JacLaw, file O9f (G5 GenRole): one role of the configuration, and the witness steps
--   * `S4.Def_RP_JacLaw_GenCfg`: S4-JacLaw, file O9g (G5 GenCfg): the configuration
--   * `S4.Def_RP_JacLaw_GenWit`: S4-JacLaw, file O9h (G5 GenWit): a witness point for the law data
--   * `S4.Def_RP_JacFrob_BrD`: S4-JacFrob, part BrD (bridge 4): degree-1 places, separation, fibre count
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_028
import Definitions.Def_RPLib_F2_074

/-!
# Ramanujan-Petersson curve library (flat edition), file 029 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacLaw_InstBase`: S4-JacLaw, file O10e (part Base): points below points of `D(numA _)`
* `S4.Def_RP_JacLaw_GenRole`: S4-JacLaw, file O9f (G5 GenRole): one role of the configuration, and the witness steps
* `S4.Def_RP_JacLaw_GenCfg`: S4-JacLaw, file O9g (G5 GenCfg): the configuration
* `S4.Def_RP_JacLaw_GenWit`: S4-JacLaw, file O9h (G5 GenWit): a witness point for the law data
* `S4.Def_RP_JacFrob_BrD`: S4-JacFrob, part BrD (bridge 4): degree-1 places, separation, fibre count
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_InstBase =====
section

/-!
# S4-JacLaw, file O10e (part Base): points below points of `D(numA _)`

`mB_L mB_R rB_L rB_R lB_L lB_R` (`nestK_base` at `T0`, `iL`, `iR`: the base of `x ∘ nestK` is `pL x`, `pR x`)
and `m_nest r_nest l_nest` (`x ∘ μm = (x ∘ nestK) ∘ mOutL`, etc.).
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

section Base

variable (x : Localization.Away L.ωm →ₐ[K] K) (xr : Localization.Away L.ωr →ₐ[K] K)
  (xl : Localization.Away L.ωl →ₐ[K] K)

theorem l_nest : xl.comp L.lal = (xl.comp (nestK (K := K) L.lU)).comp L.lOutL :=
  (AlgHom.comp_assoc _ _ _).symm

end Base

end LawData

end Inst

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_GenRole =====
section

/-!
# S4-JacLaw, file O9f (G5 GenRole): one role of the configuration, and the witness steps

* `exists_enum`: an injective tuple enumerating a finset.
* **`exists_role`**: from a section `s` with exact pole divisor `Hn` and full reduced zero set `Z`, and `A ⊆ Z`
  with `#A = d` and `Z \ A` nonspecial: a `NuData` with `Hn` that is good on `A` with `ν(A) = Z \ A`.
* `ne_u3`, **`ne_numA_m`**, **`ne_numA_r`**: a point `z` of `T` where the inner and outer units of `mOut` /
  `rOut` do not vanish (so `z` lifts to `D(numA _)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section GenRole

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

section Wit

variable {T : Type u} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]
  {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3)) (D2 : NuData K F (genusFK K F + r2))
  (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)) (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K))

/-- **The units of `m` at a point**: `z(u3) ≠ 0` and `z(num u2) ≠ 0`. -/
theorem ne_numA_m (φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T) (z : T →ₐ[K] K)
    {A3 E : Finset (Places.Rfin K F →ₐ[K] K)}
    (hA : ptSet (z.comp φa) ∪ ptSet (z.comp φb) ∪ Finset.univ.image c0 = A3)
    (h3 : ∀ y : SymRing K (Places.Rfin K F) (genusFK K F + genusFK K F + r3) →ₐ[K] K, ptSet y = A3 →
      y D3.good ≠ 0 ∧ D3.nuF y = E)
    (h2 : ∀ y : SymRing K (Places.Rfin K F) (genusFK K F + r2) →ₐ[K] K, ptSet y = E ∪ Finset.univ.image c1 →
      y D2.good ≠ 0) :
    z (numA (padMap (mIn D3 c0 φa φb) c1 rfl D2.good)) ≠ 0 := by
  have hu := ne_u3 D3 c0 φa φb z hA fun y hy => (h3 y hy).1
  obtain ⟨x, hx⟩ := exists_baseAway _ z hu
  have key : x (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) ≠ 0 := by
    have e : x (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) =
        (x.comp (padMap (mIn D3 c0 φa φb) c1 rfl)) D2.good := rfl
    rw [e, comp_padMap]
    refine h2 _ ?_
    rw [ptSet_padPt]
    have e2 : ptSet (x.comp (mIn D3 c0 φa φb)) = E := by
      rw [mIn, NuData.ptSet_nuStep, hx]
      exact (h3 _ (by rw [comp_padMap, ptSet_padPt, comp_sumMap, ptSet_sumPt, hA])).2
    rw [e2]
  have h := (numA_pt (K := K) _ x).2 key
  have hx' : x.comp (awayι (K := K) (padMap (sumMap φa φb) c0 rfl D3.good)) = z := hx
  rwa [hx'] at h

/-- **The units of `r` at a point**: `z(v2) ≠ 0` and `z(num v3) ≠ 0`. -/
theorem ne_numA_r (φa φc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T) (z : T →ₐ[K] K)
    {C2 A3 E : Finset (Places.Rfin K F →ₐ[K] K)}
    (hC : ptSet (z.comp φc) ∪ Finset.univ.image c1 = C2)
    (h2 : ∀ y : SymRing K (Places.Rfin K F) (genusFK K F + r2) →ₐ[K] K, ptSet y = C2 →
      y D2.good ≠ 0 ∧ D2.nuF y = E)
    (hA : ptSet (z.comp φa) ∪ E ∪ Finset.univ.image c0 = A3)
    (h3 : ∀ y : SymRing K (Places.Rfin K F) (genusFK K F + genusFK K F + r3) →ₐ[K] K, ptSet y = A3 →
      y D3.good ≠ 0) :
    z (numA (padMap (rSum D2 c1 φa φc) c0 rfl D3.good)) ≠ 0 := by
  have hv : z (padMap φc c1 rfl D2.good) ≠ 0 := by
    have e : z (padMap φc c1 rfl D2.good) = (z.comp (padMap φc c1 rfl)) D2.good := rfl
    rw [e, comp_padMap]
    exact (h2 _ (by rw [ptSet_padPt, hC])).1
  obtain ⟨x, hx⟩ := exists_baseAway _ z hv
  have key : x (padMap (rSum D2 c1 φa φc) c0 rfl D3.good) ≠ 0 := by
    have e : x (padMap (rSum D2 c1 φa φc) c0 rfl D3.good) =
        (x.comp (padMap (rSum D2 c1 φa φc) c0 rfl)) D3.good := rfl
    rw [e, comp_padMap]
    refine h3 _ ?_
    rw [ptSet_padPt]
    have e1 : x.comp ((IsScalarTower.toAlgHom K T (Localization.Away (padMap φc c1 rfl D2.good))).comp φa) =
        z.comp φa := by
      rw [← AlgHom.comp_assoc]
      exact congrArg (fun w => w.comp φa) hx
    have e2 : ptSet (x.comp (rIn D2 c1 φc)) = E := by
      rw [rIn, NuData.ptSet_nuStep, hx]
      exact (h2 _ (by rw [comp_padMap, ptSet_padPt, hC])).2
    show ptSet (x.comp (sumMap ((IsScalarTower.toAlgHom K T _).comp φa) (rIn D2 c1 φc))) ∪
      Finset.univ.image c0 = A3
    rw [comp_sumMap, ptSet_sumPt, e1, e2, hA]
  have h := (numA_pt (K := K) _ x).2 key
  have hx' : x.comp (awayι (K := K) (padMap φc c1 rfl D2.good)) = z := hx
  rwa [hx'] at h

end Wit

end GenRole

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_GenCfg =====
section

/-!
# S4-JacLaw, file O9g (G5 GenCfg): the configuration

* `role_sub`, `role_card`, `role_sdiff`: finset bookkeeping for one role `X ∪ (Z \ U)` with `X ∪ W = U`.
* `RoleOn D A W`: `D` is good on every point with point set `A`, and `ν = W` there.
* `exists_role_of`: `exists_role` in the configuration shape.
* `exists_pool`: fibre sections over any finset of good points, and a pool of `≥ 5g - 1` good points.
* **`exists_cfg`**: a `LawData` with point tuples `ta`, `tb` and the six roles of the law at `(ta, tb)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Sets

variable {α : Type*} [DecidableEq α]

end Sets

section GenCfg

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **The configuration**: a `LawData` and point tuples `ta`, `tb` with point sets `a`, `b`, such that
`m(a,b) = c` (via `ν3(a+b+c0) = E`, `ν2(E+c1) = c`), `ν2(c+c1) = E`, `ν3(a+E+c0) = b`, `ν3(b+E+c0) = a`,
each data good there. -/
theorem exists_cfg : ∃ L : LawData K F, ∃ ta tb : Fin (genusFK K F) → (Places.Rfin K F →ₐ[K] K),
    ∃ a b E c : Finset (Places.Rfin K F →ₐ[K] K),
      ptSet (symPt ta) = a ∧ ptSet (symPt tb) = b ∧
      RoleOn L.Dm3 (a ∪ b ∪ Finset.univ.image L.c0) E ∧
      RoleOn L.Dm2 (E ∪ Finset.univ.image L.c1) c ∧
      RoleOn L.Dr2 (c ∪ Finset.univ.image L.c1) E ∧
      RoleOn L.Dl2 (c ∪ Finset.univ.image L.c1) E ∧
      RoleOn L.Dr3 (a ∪ E ∪ Finset.univ.image L.c0) b ∧
      RoleOn L.Dl3 (b ∪ E ∪ Finset.univ.image L.c0) a := by
  obtain ⟨a0, hfib, T, hT, hTa⟩ := exists_pool (K := K) (F := F)
  obtain ⟨a, b, E, c, haT, hbT, hET, hcT, ha, hb, hE, hc, hab, haE, -, hbE, -, hEc, hNa, hNb, hNE, hNc⟩ :=
    exists_four_nonspecial T hT
  obtain ⟨s3, Z3, hs30, hs3, hdeg3, hZ3, hU3⟩ := hfib (a ∪ b ∪ E) (fun φ hφ => hTa φ (by
    simp only [Finset.mem_union] at hφ
    rcases hφ with (h | h) | h
    exacts [haT h, hbT h, hET h]))
  obtain ⟨s2, Z2, hs20, hs2, hdeg2, hZ2, hU2⟩ := hfib (E ∪ c) (fun φ hφ => hTa φ (by
    rcases Finset.mem_union.1 hφ with h | h
    exacts [hET h, hcT h]))
  obtain ⟨r3, hr3⟩ : ∃ r, (Z3 \ (a ∪ b ∪ E)).card = r := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ r, (Z2 \ (E ∪ c)).card = r := ⟨_, rfl⟩
  obtain ⟨c0, -, hc0⟩ := exists_enum _ hr3
  obtain ⟨c1, -, hc1⟩ := exists_enum _ hr2
  obtain ⟨ta, -, hta⟩ := exists_enum a ha
  obtain ⟨tb, -, htb⟩ := exists_enum b hb
  have hab' : (a ∪ b).card = genusFK K F + genusFK K F := by
    rw [Finset.card_union_of_disjoint hab, ha, hb]
  have haE' : (a ∪ E).card = genusFK K F + genusFK K F := by
    rw [Finset.card_union_of_disjoint haE, ha, hE]
  have hbE' : (b ∪ E).card = genusFK K F + genusFK K F := by
    rw [Finset.card_union_of_disjoint hbE, hb, hE]
  have hU3c : (a ∪ b ∪ E).card = genusFK K F + genusFK K F + genusFK K F := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨haE, hbE⟩), hab', hE]
  have hU2c : (E ∪ c).card = genusFK K F + genusFK K F := by
    rw [Finset.card_union_of_disjoint hEc, hE, hc]
  have hZ3c : Z3.card = genusFK K F + genusFK K F + r3 + genusFK K F := by
    rw [← Finset.card_sdiff_add_card_eq_card hU3, hr3, hU3c]
    omega
  have hZ2c : Z2.card = genusFK K F + r2 + genusFK K F := by
    rw [← Finset.card_sdiff_add_card_eq_card hU2, hr2, hU2c]
    omega
  have hd3 : (poleDiv (K := K) (incB K F s3)).deg =
      ((genusFK K F + genusFK K F + r3 + genusFK K F : ℕ) : ℤ) := by rw [hdeg3, hZ3c]
  have hd2 : (poleDiv (K := K) (incB K F s2)).deg = ((genusFK K F + r2 + genusFK K F : ℕ) : ℤ) := by
    rw [hdeg2, hZ2c]
  have hI3 := isInf_poleDiv (K := K) (F := F) s3
  have hI2 := isInf_poleDiv (K := K) (F := F) s2
  have h03 : (0 : Places.Divisor K F) ≤ poleDiv (K := K) (incB K F s3) := le_sup_right
  have h02 : (0 : Places.Divisor K F) ≤ poleDiv (K := K) (incB K F s2) := le_sup_right
  obtain ⟨Dm3, hHm3, hm3⟩ := exists_role_of (by omega) hI3 h03 hd3 hs30 hs3 hZ3 hZ3c hU3
    (X := a ∪ b) (W := E) rfl (Finset.disjoint_union_left.2 ⟨haE, hbE⟩) (by rw [hab', hr3]) hNE
  obtain ⟨Dr3, hHr3, hr3'⟩ := exists_role_of (by omega) hI3 h03 hd3 hs30 hs3 hZ3 hZ3c hU3
    (X := a ∪ E) (W := b) (Finset.union_right_comm a E b) (Finset.disjoint_union_left.2 ⟨hab, hbE.symm⟩)
    (by rw [haE', hr3]) hNb
  obtain ⟨Dl3, hHl3, hl3'⟩ := exists_role_of (by omega) hI3 h03 hd3 hs30 hs3 hZ3 hZ3c hU3
    (X := b ∪ E) (W := a) (by rw [Finset.union_comm (b ∪ E) a, ← Finset.union_assoc])
    (Finset.disjoint_union_left.2 ⟨hab.symm, haE.symm⟩) (by rw [hbE', hr3]) hNa
  obtain ⟨Dm2, hHm2, hm2⟩ := exists_role_of (by omega) hI2 h02 hd2 hs20 hs2 hZ2 hZ2c hU2
    (X := E) (W := c) rfl hEc (by rw [hE, hr2]) hNc
  obtain ⟨Dr2, hHr2, hr2'⟩ := exists_role_of (by omega) hI2 h02 hd2 hs20 hs2 hZ2 hZ2c hU2
    (X := c) (W := E) (Finset.union_comm c E) hEc.symm (by rw [hc, hr2]) hNE
  have e0 := image_enum c0 _ hc0
  have e1 := image_enum c1 _ hc1
  have ea : ptSet (symPt ta) = a := by rw [ptSet_symPt]; exact image_enum ta a hta
  have eb : ptSet (symPt tb) = b := by rw [ptSet_symPt]; exact image_enum tb b htb
  rw [← e0] at hm3 hr3' hl3'
  rw [← e1] at hm2 hr2'
  exact ⟨⟨r3, r2, c0, c1, Dm3, Dr3, Dl3, Dm2, Dr2, Dr2, hHr3.trans hHm3.symm, hHl3.trans hHm3.symm,
    hHr2.trans hHm2.symm, hHr2.trans hHm2.symm⟩, ta, tb, a, b, E, c, ea, eb, hm3, hm2, hr2', hr2', hr3', hl3'⟩

end GenCfg

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

end Gen

variable (L : LawData K F) {a b E c : Finset (Places.Rfin K F →ₐ[K] K)}

/-- The witness property of law data (the hypothesis `hw` of `LawData.toPre` / `LawData.chunk`), as a plain def so
that `cases` motives stay small. -/
def LawData.HasWit : Prop :=
  ∃ x : Localization.Away L.ωm →ₐ[K] K, x (phiS L.μm L.ωr) ≠ 0 ∧ x (psiS L.μm L.ωl) ≠ 0

end GenWit

end RamanujanPetersson.JacLaw


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
/-- At all large levels, `P` is the only place of `F-bar` over its contraction. -/
theorem exists_fibreB_singleton (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) :
    ∃ M0, ∀ M, M0 ≤ M → fibreB Fq F Ω hk M (contB Fq F Ω hk M P) = {P} := by
  obtain ⟨M0, h⟩ := degOne Fq F Ω hk P
  exact ⟨M0, fun M hM => Finset.eq_singleton_iff_unique_mem.2
    ⟨(mem_fibreB Fq F Ω hk _ _ _).2 rfl, fun P' hP' => uniqB Fq F Ω hk (h M hM) ((mem_fibreB Fq F Ω hk _ _ _).1 hP')⟩⟩

end DegOne

end RamanujanPetersson.JacFrob


end


