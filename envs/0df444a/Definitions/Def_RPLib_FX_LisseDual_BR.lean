-- Prove2me | Definitions.Def_RPLib_FX_LisseDual_BR
-- name    : RPLib_FX_LisseDual_BR
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T05:39:42.444128+00:00
-- url     : https://prove2.me/theorems/7845d2c4-f1e1-402e-90b9-b75c65ab93b8
-- title:
--   Lisse Poincaré duality on an affine curve over a finite field, top file
-- statement:
--   Top file of the lisse duality library for affine curves over a finite field: the library-form step `SW38Sol.core`. From the divisibility hypotheses, boundary data, a finite unramified quotient and the finiteness of the mod-l cohomology of the cover, it builds the constant-coefficient trace data, the vanishing of the second cohomology of the twist and the residue data of the quotient, and applies the library theorem `CupDuality.lisse_bijective_S3`: the cochain duality map `alphaM` is bijective.
--
--   **Formalization note.** One file of a library formalizing Poincaré duality for $H^1$ with lisse (finite, twisted) coefficients on an affine curve over a finite field: for a finite $\Lambda$-module $M$ with a continuous action of the geometric fundamental group factoring through a finite unramified quotient, the cochain duality map $\alpha_M : H^1_c(M) \to H^1(M^\vee(1))^\vee$ is bijective. It extends the published flat library for constant coefficients (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); J. S. Milne, Arithmetic Duality Theorems, 2nd ed., BookSurge (2006), Chapter II, §3; P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »

import Mathlib
import Definitions.Def_RPLib_FX_LisseDual_07

/-!
# Lisse Poincaré duality on an affine curve over a finite field: top file

`SW38Sol.core`, the library-form step of the lisse duality theorem of the series `RPLib_FX_LisseDual_*`: from the
divisibility hypotheses, boundary data, a finite unramified quotient `π` and the finiteness of `H¹(V̄, ℤ/l)`, it
builds the constant-coefficient trace data (`Residue.exists_resDat_tw`, `CupDuality.constData_of_resHyp`), the
vanishing `H²(Γ, Λ(1)) = 0` (`CdOne.h2All_geo`), the residue data of `π` (`Residue.exists_resDat`), and applies
`CupDuality.lisse_bijective_S3`: the duality map `alphaM` is bijective.
-/

set_option autoImplicit false

open RamanujanPetersson in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem RamanujanPetersson.SW38Sol.core
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (F : Type) [Field F] [Algebra Fq F] [Algebra (Polynomial Fq) F] [Algebra (RatFunc Fq) F]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) F] [IsScalarTower Fq (Polynomial Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]
    (p e : ℕ) [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
    (hk : algebraicClosure Fq F = ⊥)
    (l : ℕ) [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ) (hn : n ≠ 0)
    (hPicU' : CdOne.PicDivU (Places.Rfin Fq F) F p l)
    (hPic' : Residue.PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p (l ^ n))
    (S : Type) [Fintype S] [DecidableEq S] [Nonempty S]
    (D : CurveCoh.BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ CurveCoh.IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    (E : IntermediateField F (AlgebraicClosure F)) (hM : E ∈ unramSet (Places.Rfin Fq F) F)
    (hE1 : FiniteDimensional F E) (hEU : E ≤ maxUnram (Places.Rfin Fq F) F)
    (Gf : Type) [Group Gf] [Finite Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf)
    (hπM : ∀ g, π g = 1 ↔ g ∈ (IntermediateField.restrict hEU).fixingSubgroup)
    (hfin : {y : ↥((CurveCoh.pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)).subgroupOf π.ker) → ZMod l |
      IsLocallyConstant y ∧ ∀ a b, y (a * b) = y a + y b}.Finite)
    (Λ : Type) [CommRing Λ] [Finite Λ] [Module.Injective Λ Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    (hsep : CupDuality.SepDual Λ)
    (σ : Representation Λ (Pi1 (Places.Rfin Fq F) F) Λ) (hσ : IsOpen (σ.ker : Set (Pi1 (Places.Rfin Fq F) F)))
    (htr : ∀ (g : CurveCoh.pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) (x : Λ), σ g x = x)
    (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] (τ : Representation Λ Gf M) :
    ∃ (hπo : IsOpen (π.ker : Set (Pi1 (Places.Rfin Fq F) F)))
      (t : (s : S) → ↥(CurveCoh.pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s))
      (DD : CupDuality.ConstData σ (CurveCoh.pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia t)
      (hv : PerfectCx.H2Van σ (CurveCoh.pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) ⊤),
      Function.Bijective (CupDuality.alphaM hv (CupDuality.h2kEquiv DD hσ).toLinearMap (τ.comp π)
        (CupDuality.isOpen_comp π hπo τ)) := by
  classical
  have hP' : ∀ s, CurveCoh.IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (D.P s) :=
    fun s => (hDB _).1 (D.mem s)
  have hcov' := fun Q (hQ : CurveCoh.IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q) =>
    D.cover Q ((hDB Q).2 hQ)
  have hNF0 : ((l ^ n : ℕ) : F) ≠ 0 := by
    push_cast
    exact pow_ne_zero n hl
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  letI : Fintype ((CurveCoh.pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)).map
      (1 : Pi1 (Places.Rfin Fq F) F →* PUnit)) := Fintype.ofFinite _
  letI : ∀ s, Fintype ((CurveCoh.pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s).map
      (1 : Pi1 (Places.Rfin Fq F) F →* PUnit)) := fun _ => Fintype.ofFinite _
  letI : Fintype (Residue.CosT (1 : Pi1 (Places.Rfin Fq F) F →* PUnit)
      (CurveCoh.pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia) := Fintype.ofFinite _
  letI : DecidableEq (Residue.CosT (1 : Pi1 (Places.Rfin Fq F) F →* PUnit)
      (CurveCoh.pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia) := Classical.decEq _
  have hπ1 : IsOpen (((1 : Pi1 (Places.Rfin Fq F) F →* PUnit).ker : Subgroup _) :
      Set (Pi1 (Places.Rfin Fq F) F)) := by
    rw [MonoidHom.ker_one, Subgroup.coe_top]
    exact isOpen_univ
  obtain ⟨D', -⟩ := Residue.exists_resDat_tw hq he hNF0 hPic' (bot_mem_unramSet (Places.Rfin Fq F) F) bot_le
    (1 : Pi1 (Places.Rfin Fq F) F →* PUnit) CupDuality.one_iff_fix_bot D.P hP' hcov' D.disj D.inertia
    (fun _ => rfl)
  have hall := CdOne.h2All_geo (Places.Rfin Fq F) Fq he hq (Kummer.perfect_Rfin Fq F) l
    (CP4a.isUnit_cast_Rfin hl) hPicU' Λ n
  have hL : ∀ m : Λ, (l ^ n) • m = 0 := fun m => by
    rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]
  have hv := CupDuality.h2Van_top_of_all hall hL hσ
  obtain ⟨t, DD⟩ : ∃ t, CupDuality.ConstData σ (CurveCoh.pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia t :=
    ⟨_, CupDuality.constData_of_resHyp (D'.toResHyp hΛ hπ1) htr⟩
  -- the cover `V` attached to `E`
  have : FiniteDimensional F (IntermediateField.restrict hEU) :=
    LinearEquiv.finiteDimensional (IntermediateField.restrictAlgEquiv hEU).toLinearEquiv
  have hπo : IsOpen (π.ker : Set (Pi1 (Places.Rfin Fq F) F)) := by
    have hk2 : (π.ker : Set (Pi1 (Places.Rfin Fq F) F)) =
        ((IntermediateField.restrict hEU).fixingSubgroup : Set (Pi1 (Places.Rfin Fq F) F)) := by
      ext g
      exact hπM g
    rw [hk2]
    exact (IntermediateField.restrict hEU).fixingSubgroup_isOpen
  have hNF : ((l ^ n : ℕ) : F) ≠ 0 := by
    push_cast
    exact pow_ne_zero n hl
  haveI : Fintype (Residue.CosT π (CurveCoh.pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia) :=
    Fintype.ofFinite _
  obtain ⟨RD⟩ := Residue.exists_resDat hq he hNF hPic' hM hEU π hπM D.P hP' hcov' D.disj D.inertia
    (fun s => rfl)
  haveI : Fintype ((CurveCoh.pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)).map π) := Fintype.ofFinite _
  haveI : ∀ s, Fintype ((CurveCoh.pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s).map π) :=
    fun s => Fintype.ofFinite _
  have : Finite ↥(CupDuality.parMod (CurveCoh.geoU (CurveCoh.pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) π.ker)
      (CupDuality.rdJ RD π.ker) l) :=
    (hfin.subset fun y hy => ⟨hy.1, hy.2.1⟩).to_subtype
  haveI : Fintype Gf := Fintype.ofFinite _
  haveI : Nonempty (Residue.CosT π (CurveCoh.pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia) :=
    ⟨⟨Classical.arbitrary S, QuotientGroup.mk 1⟩⟩
  have hbij := CupDuality.lisse_bijective_S3 hq he hk hl hn hPicU' hPic' D hDB π hπo RD
    hsep hΛ σ hσ DD hv τ
  exact ⟨hπo, t, DD, hv, hbij⟩


