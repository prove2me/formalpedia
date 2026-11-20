-- Prove2me | Definitions.Def_RPLib_F2_068
-- name    : RPLib_F2_068
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T23:20:01.315499+00:00
-- url     : https://prove2.me/theorems/e2ac3eab-1045-4f3c-84e7-5724ffe1162a
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 068 of 70
-- statement:
--   File 068 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_CoverLef`: S4-Lefschetz, L4 assembly: the Lefschetz formula of a cover `E ⊆ K_U`, read inside `π₁(U)`
--   * `S4.Def_RP_Lefschetz_ZFin3`: S4-Lefschetz, L6z (3): `Z¹(π₁^geo, Λ[Gf])` and `Z¹(π₁^geo ∩ I_s, Λ[Gf])` are finite
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_067

/-!
# Ramanujan-Petersson curve library (flat edition), file 068 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_CoverLef`: S4-Lefschetz, L4 assembly: the Lefschetz formula of a cover `E ⊆ K_U`, read inside `π₁(U)`
* `S4.Def_RP_Lefschetz_ZFin3`: S4-Lefschetz, L6z (3): `Z¹(π₁^geo, Λ[Gf])` and `Z¹(π₁^geo ∩ I_s, Λ[Gf])` are finite
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_CoverLef =====
section

/-!
# S4-Lefschetz, L4 assembly: the Lefschetz formula of a cover `E ⊆ K_U`, read inside `π₁(U)`

For a finite separable `E/K` inside `K_U` with full constant field `k' = Kc Fq E`, an ambient `G' = H·Γ`
(`H = range thetaE`) and a Frobenius lift `φ` of `E` over `k'`:
`Tr(F^m | H²_c(Γ ∩ G'; Ind_H^{G'} Λ)) - Tr(F^m | H¹_c(Γ ∩ G'; Ind_H^{G'} Λ)) = #(Spec R_E)(𝔽_{q'^m})`,
with `F` the Frobenius at `thetaE φ⁻¹` (true boundary data of `U`) and `χ = #k'` on `H²_c`.

* `hlq_Kc`: `l ∤ q ⇒ l ∤ #k'`; `exists_cosetReps_E`; `trH2Sub` (the `H²_c` trace on the `G'` side);
* **`lefschetz_cover`** (CP4 on `E` + `trace_cover_sub` + `trace_frobH2c_ind`), stated with `trH2Sub` /
  `trH1Sub` (the olean export step folds over every public theorem type: keep them small).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a CupDuality Representation

section CoverLef

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
/-- **L4 (cover Lefschetz inside `π₁(U)`)**: for `G' = H·Γ`, a Frobenius lift `φ` of `E` over `k'` and `m ≥ 1`,
`Tr(F^m | H²_c(Γ ∩ G'; Ind Λ)) - Tr(F^m | H¹_c(Γ ∩ G'; Ind Λ)) = #(R_E →ₐ[k'] L)` with `[L : k'] = m`. -/
theorem lefschetz_cover (l n : ℕ) [Fact l.Prime] (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = l ^ n)
    (hlq : ¬ l ∣ Fintype.card Fq) {G' : Subgroup (Pi1 (Rfin Fq K) K)}
    (hΓ : pi1geo (Rfin Fq K) K (Fintype.card Fq) ≤ G') (hH : (thetaE Fq K E hE).range ≤ G')
    (hcov' : ∀ x ∈ G', ∃ a ∈ (thetaE Fq K E hE).range, ∃ b ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq), x = a * b)
    (φ : Pi1 (Rfin (Kc Fq E) E) E) (hφ : IsFrobLift (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) φ)
    (m : ℕ) (hm : 1 ≤ m) (L : Type) [Field L] [Algebra (Kc Fq E) L] [Finite L]
    (hL : Module.finrank (Kc Fq E) L = m) :
    trH2Sub Fq K E hE N hH φ⁻¹ (Fintype.card (Kc Fq E) : ZMod N) m - trH1Sub Fq K E hE N hΓ hH φ⁻¹ m =
      (Nat.card (Rfin (Kc Fq E) E →ₐ[Kc Fq E] L) : ZMod N) := by
  -- every `obtain` destructs a local hypothesis: `obtain .. := <term>` generalizes the term in this large goal,
  -- and `kabstract` (no sharing cache) ran > 25 min in v1; no `rw` on the goal for the same reason.
  have hR := exists_cosetReps_E Fq K E hE
  obtain ⟨R⟩ := hR
  have : CharP E p := charP_of_injective_algebraMap (algebraMap K E).injective p
  have hc := card_Kc Fq E p
  obtain ⟨e', he', hqE⟩ := hc
  have := finite_bdryS (Fq := Kc Fq E) (F := E) hqE he'
  let := Fintype.ofFinite (BdryS (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) (Rinf (Kc Fq E) E))
  let : DecidableEq (BdryS (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) (Rinf (Kc Fq E) E)) :=
    Classical.decEq _
  have hcp := CP4.lefschetz_point_count (Fq := Kc Fq E) (F := E) (constField_eq_bot Fq E) hqE he' l n hn hN
    (hlq_Kc Fq K E l hlq) φ hφ m hm L hL
  have h2 : LinearMap.trace (ZMod N) (curveH2c (Fintype.card (Kc Fq E))
        (Representation.trivial (ZMod N) (Pi1 (Rfin (Kc Fq E) E) E) (ZMod N)))
        (geomFrobH2c (Fintype.card (Kc Fq E))
          (Representation.trivial (ZMod N) (Pi1 (Rfin (Kc Fq E) E) E) (ZMod N)) φ ^ m) =
        (Fintype.card (Kc Fq E) : ZMod N) ^ m :=
    CP4a.trace_frobH2c_triv _ _ _ m
  have h1 : trH2Sub Fq K E hE N hH φ⁻¹ (Fintype.card (Kc Fq E) : ZMod N) m =
      (Fintype.card (Kc Fq E) : ZMod N) ^ m :=
    trace_frobH2c_ind ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
      (downH (thetaE Fq K E hE).range G')) (fun _ => rfl) (cosetReps_sub hΓ R) (hcov_sub hΓ hH hcov')
      ((upH hH (rangeElt (thetaE Fq K E hE) φ⁻¹) : (thetaE Fq K E hE).range.subgroupOf G') : G')
      (Fintype.card (Kc Fq E) : ZMod N) m
  have h3 := trace_cover_sub Fq K E hE hq he N hΓ hH hcov' R φ⁻¹ m
  exact (congrArg₂ HSub.hSub (h1.trans h2.symm) h3).trans hcp

end CoverLef

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
set_option maxHeartbeats 1000000 in
/-- **`Z¹(π₁^geo, ℤ/l^n[Gf])` is finite** for `π` cut out by a finite unramified `M`. -/
theorem finite_Z1_regRep_geo (l n : ℕ) [Fact l.Prime] {N : ℕ} [NeZero N] (hN : N = l ^ n)
    (hlq : ¬ l ∣ Fintype.card Fq)
    {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
    (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup) :
    Module.Finite (ZMod N) (Z1 (regRep (ZMod N) π) (pi1geo (Rfin Fq K) K (Fintype.card Fq))) := by
  haveI : FiniteDimensional K Mf := hM.1
  haveI : IsGalois K Mf := hM.2.1
  have hE : Mf ≤ maxUnram Fq[X] K := fun x hx => by
    rw [← maxUnram_rfin Fq K]
    exact hMU hx
  have hKk : ∀ g, g ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ π.ker ↔
      g ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq) ∧ g ∈ (thetaE Fq K Mf hE).range := fun g => by
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, hπM g, mem_range_thetaE_iff_fix Fq K Mf hE g]
    refine and_congr Iff.rfl ?_
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h y hy => h y ((IntermediateField.mem_restrict _ _).2 hy),
      fun h y hy => h y ((IntermediateField.mem_restrict _ _).1 hy)⟩
  have hfin := finite_homLC_cover Fq K hq he Mf hE l n hN hlq _ hKk
  have := finite_Z1_regRep π (pi1geo (Rfin Fq K) K (Fintype.card Fq))
    (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ π.ker)
    (fun g => Subgroup.mem_inf.trans (and_congr Iff.rfl MonoidHom.mem_ker)) hfin
  exact Module.Finite.of_finite

end Cover

end

end Lefschetz
end RamanujanPetersson


end


