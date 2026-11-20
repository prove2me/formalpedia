-- Prove2me | Definitions.Def_RPLib_F2_063
-- name    : RPLib_F2_063
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T19:39:25.924012+00:00
-- url     : https://prove2.me/theorems/85404aca-30e5-4cf0-81f6-31de5764bd2e
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 063 of 70
-- statement:
--   File 063 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_CP4a_Main`: S4-CP4a, part h: the assembled Lefschetz point count (Core B as a hypothesis)
--   * `S4.Def_RP_Lefschetz_ZFin2`: S4-Lefschetz, L6z (2): `Z¹(π₁^geo, ℤ/N)` is finite (full constant field)
--   * `S4.Def_RP_Lefschetz_ZFin3`: S4-Lefschetz, L6z (3): `Z¹(π₁^geo, Λ[Gf])` and `Z¹(π₁^geo ∩ I_s, Λ[Gf])` are finite
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_048
import Definitions.Def_RPLib_F2_052
import Definitions.Def_RPLib_F2_085

/-!
# Ramanujan-Petersson curve library (flat edition), file 063 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_CP4a_Main`: S4-CP4a, part h: the assembled Lefschetz point count (Core B as a hypothesis)
* `S4.Def_RP_Lefschetz_ZFin2`: S4-Lefschetz, L6z (2): `Z¹(π₁^geo, ℤ/N)` is finite (full constant field)
* `S4.Def_RP_Lefschetz_ZFin3`: S4-Lefschetz, L6z (3): `Z¹(π₁^geo, Λ[Gf])` and `Z¹(π₁^geo ∩ I_s, Λ[Gf])` are finite
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CP4a_Main =====
section

/-!
# S4-CP4a, part h: the assembled Lefschetz point count (Core B as a hypothesis)

For a function field `F/𝔽_q` with full constant field (`hk`), its affine chart `U = Spec Rfin` (the complement of
the places over `∞` of `𝔽_q(x)`) and every prime `l ∤ q`, `n > 0`, ASSUMING the Core B statement `CoreBHyp hk l`:
* `lefschetz_point_count`: for EVERY lift `φ` of the arithmetic Frobenius to `π₁(U)` and every `m ≥ 1`,
  `Tr(F^m | H²_c(Ū, ℤ/l^n)) - Tr(F^m | H¹_c(Ū, ℤ/l^n)) = #U(𝔽_{q^m})` in `ℤ/l^n`, where
  `#U(𝔽_{q^m}) := #Hom_{𝔽_q}(Rfin, L)` for any finite `L/𝔽_q` of degree `m`, the cohomology is the S4-CurveCoh
  cohomology with the canonical boundary data over `∞` and `F` is geometric Frobenius (`φ⁻¹`).
* `cp4a_lefschetz`: the same with a Frobenius lift that exists (`exists_frobLift`), so the statement is not vacuous;
  `finite_bdryS` / `nonempty_bdryS`: the canonical boundary is a nonempty finite set.
No hypothesis other than Core B is left: the Frobenius lift, the roots of unity, the units `N` in the charts,
the boundary data and the inertia lifting are all constructed (parts f1-f4).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer GalCover

noncomputable section

section Main

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hk hq he in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **Lefschetz point count for `U`** (Core B as a hypothesis), for every Frobenius lift `φ`. -/
theorem lefschetz_point_count [Fintype (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F))]
    [DecidableEq (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F))]
    (l n : ℕ) [Fact l.Prime] (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq)
    (hB : CoreBHyp hk l) (φ : Pi1 (Rfin Fq F) F) (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ)
    (m : ℕ) (hm : 1 ≤ m) (L : Type) [Field L] [Algebra Fq L] [Finite L] (hL : Module.finrank Fq L = m) :
    LinearMap.trace (ZMod N) (curveH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N))
        (geomFrobH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ ^ m) -
      LinearMap.trace (ZMod N) (curveH1c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) (bdryInf Fq F))
        (frobH1c (triv F (maxUnram (Rfin Fq F) F) N) (pi1geo (Rfin Fq F) F (Fintype.card Fq))
          (bdryInf Fq F).inertia φ⁻¹ (trueTau (bdryInf Fq F) φ⁻¹) (trueH (bdryInf Fq F) φ⁻¹)
          (trueCompat (bdryInf Fq F) φ⁻¹) ^ m) =
      (Nat.card (Rfin Fq F →ₐ[Fq] L) : ZMod N) := by
  have hNF : (N : F) ≠ 0 := by
    rw [hN]
    exact cast_ne_zero_of_not_dvd hq he hlq n
  obtain ⟨ζ, hζ, hζΓ⟩ := exists_zeta_geo hq he hNF
  have := nonempty_bdryS (Fq := Fq) (F := F)
  exact lefschetz_count hk hq he (isUnit_cast_Rfin hNF) (isUnit_cast_Rinf hNF) hζ hζΓ (bdryInf Fq F)
    (bdryData_B _ _ _ _) (bdryLift) hNF (exists_zeta_level he) l n hn hN hlq hB φ hφ m hm L hL

end Main

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_Lefschetz_ZFin2 =====
section

/-!
# S4-Lefschetz, L6z (2): `Z¹(π₁^geo, ℤ/N)` is finite (full constant field)

* `finite_homLC_of_gen`: locally constant homomorphisms `J → ℤ/N` determined by their value at `τ` form a finite set.
* `finite_Z1_triv_of_eq`, `finite_homLC_of_Z1`: `Z¹(Δ, Λ)` (trivial action) and `Hom_lc(Δ, Λ)` are the same set.
* `finite_Z1_geo`: for a curve `U/𝔽_q` with full constant field, `Z¹(π₁^geo, ℤ/l^n)` is finite: `H¹_c` is finite
  (`free_curveH1c`) and each inertia group has a tame generator (`exists_norm_tau_fin` with `π = 1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places CurveCoh Kummer GalCover CP4a Residue PerfectCx

section Gen

variable {G : Type} [Group G] [TopologicalSpace G]

variable {Λ : Type} [CommRing Λ]

end Gen

section Base

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Every boundary inertia group `π₁^geo ∩ I_s` has finitely many locally constant characters to `ℤ/N`. -/
theorem finite_Z1_triv_inertia [Fintype (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F))]
    {N : ℕ} [NeZero N] (hNF : (N : F) ≠ 0) (s : BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F)) :
    Finite (Z1 (Representation.trivial (ZMod N) (Pi1 (Rfin Fq F) F) (ZMod N))
      (pi1geo (Rfin Fq F) F (Fintype.card Fq) ⊓ (bdryInf Fq F).inertia s)) := by
  obtain ⟨ζ, hζ, hζΓ⟩ := exists_zeta_geo hq he hNF
  have hQt : ∀ t, IsBdryPrime (Rfin Fq F) F (Rinf Fq F) ((bdryInf Fq F).P t) := fun t =>
    (bdryData_B _ _ _ _ _).1 ((bdryInf Fq F).mem t)
  have hfix : ∀ g : Pi1 (Rfin Fq F) F, g ∈ (IntermediateField.restrict
      (bot_le : (⊥ : IntermediateField F (AlgebraicClosure F)) ≤ maxUnram (Rfin Fq F) F)).fixingSubgroup :=
    fun g => (one_iff_fix_bot' g).1 rfl
  have hJΓ : ∀ t, Jt (1 : Pi1 (Rfin Fq F) F →* PUnit.{1}) ((bdryInf Fq F).P t) ≤
      pi1geo (Rfin Fq F) F (Fintype.card Fq) := fun t σ hσ =>
    Kummer.inertia_le_pi1geo he hq (hP := (hQt t).1) (Subgroup.mem_inf.1 hσ).1
  obtain ⟨-, -, τ, hT, -, -⟩ := exists_norm_tau_fin hq he hNF hζ hζΓ (bot_mem_unramSet _ _) bot_le
    (1 : Pi1 (Rfin Fq F) F →* PUnit.{1}) one_iff_fix_bot' (bdryInf Fq F).P hQt
    (fun Q hQ => by
      obtain ⟨t, g, hg, hQg⟩ := (bdryInf Fq F).cover Q ((bdryData_B _ _ _ _ Q).2 hQ)
      exact ⟨t, g, hg, hfix g, hQg⟩)
    (fun t t' g hg _ h => (bdryInf Fq F).disj t t' g hg h)
    (pi1geo (Rfin Fq F) F (Fintype.card Fq)) (fun σ => ⟨fun h => ⟨h, hfix σ⟩, fun h => h.1⟩) hJΓ
  obtain ⟨θ, -, -, -, -, hθ⟩ := hT s
  refine finite_Z1_triv_of_eq _ (Jt (1 : Pi1 (Rfin Fq F) F →* PUnit.{1}) ((bdryInf Fq F).P s)) ?_
    (finite_homLC_of_gen _ N (τ s) θ hθ)
  ext σ
  refine ⟨fun h => Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 h).2, MonoidHom.mem_ker.2 rfl⟩,
    fun h => Subgroup.mem_inf.2 ⟨hJΓ s h, (Subgroup.mem_inf.1 h).1⟩⟩

end Base

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ZFin3 =====
section

/-!
# S4-Lefschetz, L6z (3): `Z¹(π₁^geo, Λ[Gf])` and `Z¹(π₁^geo ∩ I_s, Λ[Gf])` are finite

For `π : π₁(U) → Gf` cut out by a finite unramified `M` (`ker π = Gal(K_U/M)`), `Λ = ℤ/l^n`:
* `finite_homLC_cover`: `Hom_lc(π₁^geo ∩ range thetaE, Λ)` is finite: pull back along `thetaE` to `π₁^geo` of the
  cover `E` over its constant field (`finite_homLC_geo` there).
* `finite_Z1_regRep_geo`: `Z¹(π₁^geo, Λ[Gf])` is finite (`finite_Z1_regRep` with `K = π₁^geo ∩ ker π`).
* `finite_Z1_regRep_inertia`: `Z¹(π₁^geo ∩ I_s, Λ[Gf])` is finite (`finite_Z1_regRep` with the normalised tame
  generators of `exists_norm_tau_fin` at the cover points `cosQA`; no `PicDiv` needed).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a Residue PerfectCx

section Cover

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **`Z¹(π₁^geo ∩ I_s, ℤ/l^n[Gf])` is finite** for `π` cut out by a finite unramified `M`. -/
theorem finite_Z1_regRep_inertia [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    (l n : ℕ) [Fact l.Prime] {N : ℕ} [NeZero N] (hN : N = l ^ n)
    (hlq : ¬ l ∣ Fintype.card Fq)
    {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
    (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (s : BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K)) :
    Module.Finite (ZMod N)
      (Z1 (regRep (ZMod N) π) (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s)) := by
  classical
  have hNF : (N : K) ≠ 0 := by
    rw [hN]
    exact cast_ne_zero_of_not_dvd hq he hlq n
  obtain ⟨ζN, hζN, hζNg⟩ := exists_zeta_geo hq he hNF
  let _ : Fintype (CosT π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia) := Fintype.ofFinite _
  have hP : ∀ s, IsBdryPrime (Rfin Fq K) K (Rinf Fq K) ((bdryInf Fq K).P s) := fun s =>
    (bdryData_B _ _ _ _ _).1 ((bdryInf Fq K).mem s)
  have hcov : ∀ Q, IsBdryPrime (Rfin Fq K) K (Rinf Fq K) Q →
      ∃ s, ∃ g ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq), Q = g • (bdryInf Fq K).P s := fun Q hQ =>
    (bdryInf Fq K).cover Q ((bdryData_B _ _ _ _ Q).2 hQ)
  have hI : ∀ s, (bdryInf Fq K).inertia s = Inert ((bdryInf Fq K).P s) := fun _ => rfl
  obtain ⟨-, -, τ, hT, -, -⟩ := exists_norm_tau_fin hq he hNF hζN hζNg hM hMU π hπM
    (cosQA π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia (bdryInf Fq K).P)
    (cosQA_bdry π _ _ _ hP) (cosQA_cover π _ _ _ hπM hcov hI)
    (cosQA_disj_S3 hq he hMU π hπM _ hP (bdryInf Fq K).disj _ hI)
    (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ π.ker) (memΓH_S3 hMU hπM)
    (jt_le π _ _ _ (fun _ hQ => inertia_le_geo_S3 hq he hQ) hP)
  obtain ⟨θ, -, -, -, -, hθ⟩ := hT (cosB π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia s)
  have hfin := finite_homLC_of_gen _ N _ θ hθ
  have := finite_Z1_regRep π (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s) _
    (jt_base_iff π _ _ _ hI (ile_S3 hq he _ hP _ hI) s) hfin
  exact Module.Finite.of_finite

end Cover

end

end Lefschetz
end RamanujanPetersson


end


