-- Prove2me | Definitions.Def_RPLib_F2_065
-- name    : RPLib_F2_065
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T22:32:09.593183+00:00
-- url     : https://prove2.me/theorems/b398136e-556f-482d-a11d-44bd1c90621d
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 065 of 70
-- statement:
--   File 065 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_CupDuality_ParS3a`: S4-CurveDuality O9-2: a dual basis of the parabolic homomorphisms `π₁^geo → ℤ/lⁿ` (S3 chart)
--   * `S4.Def_RP_CupDuality_ParS3b`: S4-CurveDuality O9-3: constant-coefficient duality on `Ū` is perfect (S3 chart, any `Λ`)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_050
import Definitions.Def_RPLib_F2_064

/-!
# Ramanujan-Petersson curve library (flat edition), file 065 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_CupDuality_ParS3a`: S4-CurveDuality O9-2: a dual basis of the parabolic homomorphisms `π₁^geo → ℤ/lⁿ` (S3 chart)
* `S4.Def_RP_CupDuality_ParS3b`: S4-CurveDuality O9-3: constant-coefficient duality on `Ū` is perfect (S3 chart, any `Λ`)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CupDuality_ParS3a =====
section

/-!
# S4-CurveDuality O9-2: a dual basis of the parabolic homomorphisms `π₁^geo → ℤ/lⁿ` (S3 chart)

`parSub I`: the parabolic homomorphisms `Γ → ℤ/N` (locally constant, additive, zero on every `I_s`);
`parEquiv`: `parSub I ≃+ H¹_par(Γ, ℤ/N)` for coefficients trivial on `Γ` (no coboundaries). In the S3 chart,
`H¹_par(π₁^geo, ℤ/lⁿ) ≃ Pic⁰(X̄)[lⁿ]` (Kummer, `exists_kummerPicEquiv`) and `Pic⁰(X̄)[lⁿ] ≃ (ℤ/lⁿ)^(2g)` (Tate
coordinates `tatePicN_bijective` with CB1 divisibility), so `exists_dualBasis` gives `χ_i`, `e_j`
(`exists_parBasis`): the input `hχ hδ hspan` of `LamCoord` / `LamPerf`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace CupDuality

noncomputable section

open CurveCoh Kummer CP4a
open scoped Polynomial

section Gen

variable {N : ℕ} [NeZero N] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Γ : Subgroup G} {S : Type} [Fintype S] {I : S → Subgroup G}

variable {σ : Representation (ZMod N) G (ZMod N)}

end Gen

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option maxHeartbeats 1600000 in
/-- **Dual basis of `H¹_par(π₁^geo, ℤ/lⁿ)`** (`l ≠ p`, `X` geometrically connected): parabolic homomorphisms
`χ_i` with `e_j ∈ π₁^geo`, `χ_i(e_j) = δ_ij`, spanning all parabolic homomorphisms. -/
theorem exists_parBasis (hk : Places.constField Fq F = ⊥) {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ)
    {S : Type} [Fintype S] (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q) :
    ∃ (r : ℕ) (χ : Fin r → pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) → ZMod (l ^ n))
      (e : Fin r → pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)),
      (∀ i, IsParHom (InBdry D.inertia) (χ i)) ∧ (∀ i j, χ i (e j) = if i = j then 1 else 0) ∧
      ∀ y : pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) → ZMod (l ^ n), IsParHom (InBdry D.inertia) y →
        ∀ g, y g = ∑ i, y (e i) * χ i g := by
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hNF : ((l ^ n : ℕ) : F) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hl
  have hlq := not_dvd_card hq hl
  obtain ⟨ζ, hζ, hζΓ⟩ := exists_zeta_geo hq he hNF
  obtain ⟨Φ, -⟩ := exists_kummerPicEquiv hk hq he (isUnit_cast_Rfin hNF) (isUnit_cast_Rinf hNF) hζ hζΓ D hDB
    bdryLift hNF
  obtain ⟨k0, hdiv, b1, hb1, M, h1, -, -, -, htopiff, -, -⟩ :=
    CoreA.tate_module_Pic (Ω := AlgebraicClosure F) hk l hlq
  have htop := htopiff.mpr (CoreB.divisible_Aℓ Fq F (AlgebraicClosure F) hk l hlq)
  let E := AddEquiv.ofBijective _
    (tatePicN_bijective hk hdiv b1 hb1 (fun N => (h1 N).1) (fun N => (h1 N).2) htop n)
  let Ψ := (E.trans Φ.symm).trans (parEquiv (I := D.inertia)
    (σ := triv F (maxUnram (Places.Rfin Fq F) F) (l ^ n)) (fun _ _ => rfl)).symm
  obtain ⟨e, hδ, hspan⟩ := exists_dualBasis (parSub (l ^ n) _ D.inertia) Ψ (fun y hy => hy.2.1)
  exact ⟨_, chiOf _ Ψ, e, fun i => chiOf_mem _ Ψ i, hδ, fun y hy g => hspan y hy g⟩

end S3

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_ParS3b =====
section

/-!
# S4-CurveDuality O9-3: constant-coefficient duality on `Ū` is perfect (S3 chart, any `Λ`)

Same residue data `D'` (hence the same tame generators `t`) for `Λ` and for `ℤ/lⁿ`. Over `ℤ/lⁿ` (trivial
character) the right kernel of `constPair` is zero (`inR_eq_zero`, Route G), so with the dual basis of
`exists_parBasis` the parabolic block is perfect (`parabolic_of_rightKer`); `parabolic_of_zmod` moves it to `Λ`
along `ℤ/lⁿ → Λ`, and `constPair_isPerfPair_of_parabolic` gives the full duality
`H¹_c(Ū, Λ) × H¹(Ū, σ) → Λ`, with its Frobenius formula (`constDuality_S3_perfect`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace CupDuality

noncomputable section

open CurveCoh Kummer CP4a Residue PerfectCx
open scoped Pointwise Polynomial

attribute [local instance] GalCover.grp GalCover.fG

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option maxHeartbeats 1600000 in
/-- **Constant-coefficient Poincaré duality on `Ū`** (S3 chart, `X` geometrically connected, `l ≠ p`, `Λ` finite
with `lⁿ = 0`, `σ` a character trivial on `π₁^geo`): the parabolic block and the full pairing
`H¹_c(Ū, Λ) × H¹(Ū, σ) → Λ` are perfect, and `⟨F x, F y⟩ = q · σ(φ⁻¹)(1) · ⟨x, y⟩` for every Frobenius lift. -/
theorem constDuality_S3_perfect (hk : Places.constField Fq F = ⊥) {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ)
    (hPicU : CdOne.PicDivU (Places.Rfin Fq F) F p l)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p (l ^ n))
    {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    {Λ : Type} [CommRing Λ] [Finite Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    (σ : Representation Λ (Pi1 (Places.Rfin Fq F) F) Λ) (hσ : IsOpen (σ.ker : Set (Pi1 (Places.Rfin Fq F) F)))
    (htriv : ∀ (g : pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) (x : Λ), σ g x = x) :
    ∃ (t : (s : S) → ↥(pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s))
      (DD : ConstData σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia t)
      (H : CupHyp (Representation.trivial Λ (Pi1 (Places.Rfin Fq F) F) Λ) σ σ (LinearMap.mul Λ Λ)
        (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq))),
      ParabolicPerfect H DD ∧ (constPair H DD).IsPerfPair ∧
      ∀ φ : Pi1 (Places.Rfin Fq F) F, IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) φ →
        ∀ (x : H1c (Representation.trivial Λ (Pi1 (Places.Rfin Fq F) F) Λ)
            (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia)
          (y : H1 σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq))),
        constPair H DD (frobH1c (Representation.trivial Λ (Pi1 (Places.Rfin Fq F) F) Λ)
            (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia φ⁻¹ (trueTau D φ⁻¹) (trueH D φ⁻¹)
            (trueCompat D φ⁻¹) x) (frobH1 σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) φ⁻¹ y) =
          ((Fintype.card Fq : Λ) * σ φ⁻¹ 1) * constPair H DD x y := by
  letI : Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)).map
      (1 : Pi1 (Places.Rfin Fq F) F →* PUnit)) := Fintype.ofFinite _
  letI : ∀ s, Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s).map
      (1 : Pi1 (Places.Rfin Fq F) F →* PUnit)) := fun _ => Fintype.ofFinite _
  letI : Fintype (CosT (1 : Pi1 (Places.Rfin Fq F) F →* PUnit)
      (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia) := Fintype.ofFinite _
  letI : DecidableEq (CosT (1 : Pi1 (Places.Rfin Fq F) F →* PUnit)
      (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia) := Classical.decEq _
  have hP : ∀ s, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (D.P s) := fun s => (hDB _).1 (D.mem s)
  have hcov : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q →
      ∃ s, ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), Q = g • D.P s :=
    fun Q hQ => D.cover Q ((hDB Q).2 hQ)
  have hNF : ((l ^ n : ℕ) : F) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hl
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hπ : IsOpen (((1 : Pi1 (Places.Rfin Fq F) F →* PUnit).ker : Subgroup _) : Set (Pi1 (Places.Rfin Fq F) F)) := by
    rw [MonoidHom.ker_one, Subgroup.coe_top]
    exact isOpen_univ
  obtain ⟨D', -⟩ := exists_resDat_tw hq he hNF hPic (bot_mem_unramSet (Places.Rfin Fq F) F) bot_le
    (1 : Pi1 (Places.Rfin Fq F) F →* PUnit) one_iff_fix_bot D.P hP hcov D.disj D.inertia (fun _ => rfl)
  -- coefficients `Λ`
  have hall := CdOne.h2All_geo (Places.Rfin Fq F) Fq he hq (Kummer.perfect_Rfin Fq F) l
    (CP4a.isUnit_cast_Rfin hl) hPicU Λ n
  have hL : ∀ m : Λ, (l ^ n) • m = 0 := fun m => by
    rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]
  let H := constCupHyp σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) hσ (h2Van_top_of_all hall hL hσ)
  let DD := constData_of_resHyp (D'.toResHyp hΛ hπ) htriv
  obtain ⟨E, hE⟩ := h2Equiv_lisse hq he hl n hPicU hPic D hDB hΛ σ hσ
  -- coefficients `ℤ/lⁿ`, trivial character
  let σ0 := Representation.trivial (ZMod (l ^ n)) (Pi1 (Places.Rfin Fq F) F) (ZMod (l ^ n))
  have hσ0 : IsOpen (σ0.ker : Set (Pi1 (Places.Rfin Fq F) F)) := by
    rw [show σ0.ker = ⊤ from eq_top_iff.2 fun g _ => MonoidHom.mem_ker.2 (LinearMap.ext fun _ => rfl),
      Subgroup.coe_top]
    exact isOpen_univ
  have hΛ0 : ((l ^ n : ℕ) : ZMod (l ^ n)) = 0 := ZMod.natCast_self _
  have hall0 := CdOne.h2All_geo (Places.Rfin Fq F) Fq he hq (Kummer.perfect_Rfin Fq F) l
    (CP4a.isUnit_cast_Rfin hl) hPicU (ZMod (l ^ n)) n
  have hL0 : ∀ m : ZMod (l ^ n), (l ^ n) • m = 0 := fun m => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ n)), hΛ0, zero_smul]
  let H0 := constCupHyp σ0 (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) hσ0 (h2Van_top_of_all hall0 hL0 hσ0)
  let DD0 : ConstData σ0 (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia (D'.toResHyp hΛ hπ).sg :=
    constData_of_resHyp (D'.toResHyp hΛ0 hπ) (fun _ _ => rfl)
  obtain ⟨E0, hE0⟩ := h2Equiv_lisse hq he hl n hPicU hPic D hDB hΛ0 σ0 hσ0
  obtain ⟨φ, hφ⟩ := exists_frobLift hk hq he
  obtain ⟨r, χ, e, hχ, hδ, hspan⟩ := exists_parBasis hq he hk hl n D hDB
  have hR0 : ∀ d, InR H0 DD0 d → d = 0 := fun d hd =>
    inR_eq_zero hq he hl n hPicU hPic D hDB hΛ0 (fun _ _ => rfl) H0 DD0 hφ
      (fun x y => constPair_frob_of_equiv H0 DD0 φ⁻¹ (trueTau D φ⁻¹) (trueH D φ⁻¹) (trueCompat D φ⁻¹) _ E0
        (hE0 φ hφ) x y) hd
  have h0 := parabolic_of_rightKer H0 DD0 hχ hδ hspan hR0
  have hpar : ParabolicPerfect H DD :=
    parabolic_of_zmod (ZMod.castHom (ringChar.dvd hΛ) Λ) H0 DD0 H DD hχ hδ hspan h0
  exact ⟨_, DD, H, hpar, constPair_isPerfPair_of_parabolic H DD hpar, fun φ hφ x y =>
    constPair_frob_of_equiv H DD φ⁻¹ (trueTau D φ⁻¹) (trueH D φ⁻¹) (trueCompat D φ⁻¹) _ E (hE φ hφ) x y⟩

end S3

end

end CupDuality
end RamanujanPetersson


end


