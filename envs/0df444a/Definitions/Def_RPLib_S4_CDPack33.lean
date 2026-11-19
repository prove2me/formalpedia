-- Prove2me | Definitions.Def_RPLib_S4_CDPack33
-- name    : RPLib_S4_CDPack33
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T10:39:28.711493+00:00
-- url     : https://prove2.me/theorems/eed7f93c-7075-437e-96a3-e02ed03626ff
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 33 of 71
-- statement:
--   Part 33 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_GenWit`: S4-JacLaw, file O9h (G5 GenWit): a witness point for the law data
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack32
import Definitions.Def_RPLib_S4_CDPack30b
import Definitions.Def_RPLib_S4_CDPack30x

/-!
# Curve-duality library package, part 33 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_GenWit`: S4-JacLaw, file O9h (G5 GenWit): a witness point for the law data
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

theorem pair_iL (y y' : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] K) : (pair y y').comp (iL K F) = y :=
  pair_incL y y'

theorem pair_iR (y y' : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] K) : (pair y y').comp (iR K F) = y' :=
  pair_incR y y'

variable (L : LawData K F) {a b E c : Finset (Places.Rfin K F →ₐ[K] K)}

/-- **`(a, b)` lies in `D(ωm)`.** -/
theorem wit_m {ta tb : Fin (genusFK K F) → (Places.Rfin K F →ₐ[K] K)}
    (ea : ptSet (symPt ta) = a) (eb : ptSet (symPt tb) = b)
    (hm3 : RoleOn L.Dm3 (a ∪ b ∪ Finset.univ.image L.c0) E) (hm2 : RoleOn L.Dm2 (E ∪ Finset.univ.image L.c1) c) :
    pair (symPt ta) (symPt tb) L.ωm ≠ 0 :=
  ne_numA_m (T := T0 K F) L.Dm3 L.Dm2 L.c0 L.c1 (iL K F) (iR K F) (pair (symPt ta) (symPt tb))
    (by rw [pair_iL, pair_iR, ea, eb]) hm3 (fun y hy => (hm2 y hy).1)

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

/-- The witness property of law data (the hypothesis `hw` of `LawData.toPre` / `LawData.chunk`), as a plain def so
that `cases` motives stay small. -/
def LawData.HasWit : Prop :=
  ∃ x : Localization.Away L.ωm →ₐ[K] K, x (phiS L.μm L.ωr) ≠ 0 ∧ x (psiS L.μm L.ωl) ≠ 0

theorem LawData.HasWit.out (h : L.HasWit) :
    ∃ x : Localization.Away L.ωm →ₐ[K] K, x (phiS L.μm L.ωr) ≠ 0 ∧ x (psiS L.μm L.ωl) ≠ 0 := h

/-- **The witness at a configuration.** -/
theorem wit_all {ta tb : Fin (genusFK K F) → (Places.Rfin K F →ₐ[K] K)}
    (ea : ptSet (symPt ta) = a) (eb : ptSet (symPt tb) = b)
    (hm3 : RoleOn L.Dm3 (a ∪ b ∪ Finset.univ.image L.c0) E) (hm2 : RoleOn L.Dm2 (E ∪ Finset.univ.image L.c1) c)
    (hr2 : RoleOn L.Dr2 (c ∪ Finset.univ.image L.c1) E) (hl2 : RoleOn L.Dl2 (c ∪ Finset.univ.image L.c1) E)
    (hr3 : RoleOn L.Dr3 (a ∪ E ∪ Finset.univ.image L.c0) b) (hl3 : RoleOn L.Dl3 (b ∪ E ∪ Finset.univ.image L.c0) a) :
    L.HasWit := by
  obtain ⟨x, hx0, hxL, hxR⟩ := exists_over_pair (wit_m L ea eb hm3 hm2)
  have hw := wit_mu L ea eb hm3 hm2 x hxL hxR
  have p1 : x (phiS L.μm L.ωr) ≠ 0 := by
    have e : x (phiS L.μm L.ωr) = (x.comp (phiS L.μm)) L.ωr := rfl
    rw [e, phiS_pt, hxL]
    exact wit_r L ea hr2 hr3 _ hw
  have p2 : x (psiS L.μm L.ωl) ≠ 0 := by
    have e : x (psiS L.μm L.ωl) = (x.comp (psiS L.μm)) L.ωl := rfl
    rw [e, psiS_pt, hxR]
    exact wit_l L eb hl2 hl3 _ hw
  exact Exists.intro x ⟨p1, p2⟩

/-- **The witness**: law data and a point of `D(ωm)` where `Φ` and `Ψ` land in `D(ωr)`, `D(ωl)`
(`(exists_lawData_wit).choose_spec.out` is the `hw` of `LawData.chunk`). -/
theorem exists_lawData_wit : ∃ L : LawData K F, L.HasWit := by
  obtain ⟨L, ta, tb, a, b, E, c, ea, eb, hm3, hm2, hr2, hl2, hr3, hl3⟩ := exists_cfg (K := K) (F := F)
  exact ⟨L, wit_all L ea eb hm3 hm2 hr2 hl2 hr3 hl3⟩

end GenWit

end RamanujanPetersson.JacLaw

end


