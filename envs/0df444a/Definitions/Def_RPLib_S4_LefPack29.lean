-- Prove2me | Definitions.Def_RPLib_S4_LefPack29
-- name    : RPLib_S4_LefPack29
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T18:54:18.923875+00:00
-- url     : https://prove2.me/theorems/746e8380-5318-47a5-bb95-726aa424c36d
-- title:
--   Lefschetz trace formula library (Grothendieck–Lefschetz trace formula mod ℓⁿ on curves over finite fields), part 29 of 32
-- statement:
--   Part 29 of 32 of the Lefschetz trace formula library: the following library modules, in dependency order.
--
--   * `Def_RP_Lefschetz_PDiv2`: S4-Lefschetz, L6e (2): transport of Dedekind models and valuations along field isomorphisms
--
--   **Formalization note.** Library package of a formalization of the Grothendieck–Lefschetz trace formula modulo $\ell^n$ for a lisse sheaf of free $\mathbb Z/\ell^n$-modules on an affine curve over a finite field, on the compactly supported cochain complex of the geometric fundamental group. The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. Grothendieck, Formule de Lefschetz et rationalité des fonctions L, Séminaire Bourbaki, exposé 279 (1964/65); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Rapport sur la formule des traces »; J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §13

import Mathlib
import Definitions.Def_RPLib_S4_KummerLev

/-!
# Lefschetz trace formula library package, part 29 of 32

Library modules of the formalization of the Grothendieck-Lefschetz trace formula mod `l^n` for lisse sheaves on an
affine curve over a finite field (`RamanujanPetersson.Lefschetz.lefschetz_main`). Each module below is copied
verbatim (import lines removed) inside its own `section` ... `end`:

* `Def_RP_Lefschetz_PDiv2`: S4-Lefschetz, L6e (2): transport of Dedekind models and valuations along field isomorphisms
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_PDiv2 =====
section

/-!
# S4-Lefschetz, L6e (2): transport of Dedekind models and valuations along field isomorphisms

* `subalgEquiv`: a field isomorphism `φ : L1 ≃+* L2` restricts to subalgebras `S1 ⊆ L1`, `S2 ⊆ L2` with
  `x ∈ S1 ↔ φ x ∈ S2`.
* `valuation_comap_equiv`: valuations of Dedekind domains are transported along a ring isomorphism compatible with a
  field isomorphism of the fraction fields.
* `isIntegral_iff_mem_Rinf`: in a constant field extension `F'/F`, `x ∈ F'` is integral over `Rinf(F)` iff it is
  integral over `O_∞(L)` (the analogue of `Kummer.isIntegral_iff_mem_Rfin`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain
open scoped Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

section SubalgEquiv

variable {R1 R2 L1 L2 : Type*} [CommRing R1] [CommRing R2] [Field L1] [Field L2] [Algebra R1 L1] [Algebra R2 L2]

/-- A field isomorphism restricted to subalgebras with corresponding members. -/
def subalgEquiv (S1 : Subalgebra R1 L1) (S2 : Subalgebra R2 L2) (φ : L1 ≃+* L2) (h : ∀ x, x ∈ S1 ↔ φ x ∈ S2) :
    S1 ≃+* S2 where
  toFun x := ⟨φ x.1, (h x.1).1 x.2⟩
  invFun y := ⟨φ.symm y.1, (h _).2 (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply x.1)
  right_inv y := Subtype.ext (φ.apply_symm_apply y.1)
  map_mul' a b := Subtype.ext (map_mul φ a.1 b.1)
  map_add' a b := Subtype.ext (map_add φ a.1 b.1)

theorem coe_subalgEquiv (S1 : Subalgebra R1 L1) (S2 : Subalgebra R2 L2) (φ : L1 ≃+* L2)
    (h : ∀ x, x ∈ S1 ↔ φ x ∈ S2) (x : S1) : ((subalgEquiv S1 S2 φ h x : S2) : L2) = φ x := rfl

end SubalgEquiv

section ValTransport

variable {B1 B2 L1 L2 : Type*} [CommRing B1] [IsDedekindDomain B1] [CommRing B2] [IsDedekindDomain B2]
  [Field L1] [Field L2] [Algebra B1 L1] [Algebra B2 L2] [IsFractionRing B1 L1] [IsFractionRing B2 L2]

/-- **Transport of valuations** along `e : B1 ≃+* B2` compatible with `φ : L1 ≃+* L2`. -/
theorem valuation_comap_equiv (e : B1 ≃+* B2) (φ : L1 ≃+* L2)
    (he : ∀ b, algebraMap B2 L2 (e b) = φ (algebraMap B1 L1 b)) (w : HeightOneSpectrum B2) (x : L1) :
    (HeightOneSpectrum.comap (e : B1 →+* B2) e.surjective w).valuation L1 x = w.valuation L2 (φ x) := by
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := B1) x
  simp only [map_div₀]
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    Kummer.intValuation_comap, Kummer.intValuation_comap, ← he a, ← he s,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]

end ValTransport

section RinfConst

open PicDescent Places

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

/-- In a constant field extension `F'/F`, the integral closure of `Rinf(F)` in `F'` is `Rinf(F')`. -/
theorem isIntegral_iff_mem_Rinf (h : RR.IsConstExt Fq F L F' c) (x : F') :
    IsIntegral (Rinf Fq F) x ↔ IsIntegral (Oinf L) x := by
  constructor
  · intro hx
    letI := algInf h
    haveI := towerInf h
    refine isIntegral_of_forall_algebraMap (A := Rinf Fq F) (fun a => ?_) hx
    rw [IsScalarTower.algebraMap_apply (Rinf Fq F) (Rinf L F') F']
    exact (algebraMap (Rinf Fq F) (Rinf L F') a).2
  · intro hx
    letI := algInf h
    haveI := towerInf h
    haveI := isIntegral_AA' h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf
    exact (Algebra.IsIntegral.isIntegral (R := Rinf Fq F) (⟨x, hx⟩ : Rinf L F')).algebraMap

end RinfConst

end

end Lefschetz
end RamanujanPetersson

end


