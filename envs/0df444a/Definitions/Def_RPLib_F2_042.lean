-- Prove2me | Definitions.Def_RPLib_F2_042
-- name    : RPLib_F2_042
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T13:18:06.668644+00:00
-- url     : https://prove2.me/theorems/73aa4ffb-6c47-43ee-bdb8-e49b4ddc4718
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 042 of 70
-- statement:
--   File 042 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_BlockPt`: S4-Lefschetz, L3f2b: one fixed block counts the points of its cover
--   * `S4.Def_RP_Lefschetz_PDiv1b`: S4-Lefschetz, L6e (1b): any divisor is `l^n`-divisible modulo principal divisors at the finite places
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_039

/-!
# Ramanujan-Petersson curve library (flat edition), file 042 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_BlockPt`: S4-Lefschetz, L3f2b: one fixed block counts the points of its cover
* `S4.Def_RP_Lefschetz_PDiv1b`: S4-Lefschetz, L6e (1b): any divisor is `l^n`-divisible modulo principal divisors at the finite places
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_BlockPt =====
section

/-!
# S4-Lefschetz, L3f2b: one fixed block counts the points of its cover

For a block `[a]` of `Gf` fixed by `π(φ⁻¹^m) · γ`, with block data `c0 ∈ π₁^geo`, `g = c0⁻¹ φ⁻¹^m`, a cover `E` with
`#k'_E = q^m`, a Frobenius lift `σ` of `E` with `thetaE σ = g⁻¹` and `range thetaE ∩ π₁^geo = ker π ∩ π₁^geo`:
`Σ_i (-1)^i Tr(P_[a] ∘ ρPC γ⁻¹ ∘ frobPC^m | PC^i) = #(R_E →ₐ[k'_E] k'_E)` (`block_count`).
Route: `block_euler` in the ambient `G' = range thetaE ⊔ π₁^geo`, `frobH1c_sub_true` (the block Frobenius is the
canonical one of `thetaE σ⁻¹`), and `lefschetz_cover` at `m = 1`, `L = k'_E`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation
open scoped Pointwise

section BlockPt

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
/-- The block `H¹_c` Frobenius (datum `t^[m]`, `hpow` of `φ⁻¹`) is the canonical Frobenius of `thetaE σ⁻¹`. -/
def trace_block_H1 (N : ℕ) (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ maxUnram Fq[X] K)
    [FiniteDimensional K E] [Algebra.IsSeparable K E] {G' : Subgroup (Pi1 (Rfin Fq K) K)}
    (hΓ : pi1geo (Rfin Fq K) K (Fintype.card Fq) ≤ G') (hH : (thetaE Fq K E hE).range ≤ G')
    {φ : Pi1 (Rfin Fq K) K} {m : ℕ} (hmem : φ⁻¹ ^ m ∈ G') (σ : Pi1 (Rfin (Kc Fq E) E) E)
    {c0 : Pi1 (Rfin Fq K) K} (hc0 : c0 ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq)) (hσ : thetaE Fq K E hE σ = (c0⁻¹ * φ⁻¹ ^ m)⁻¹)
    (hI' : BdryCompat ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).subgroupOf G') (fun s => ((bdryInf Fq K).inertia s).subgroupOf G')
      (⟨φ⁻¹ ^ m, hmem⟩ : G') (trueTau (bdryInf Fq K) φ⁻¹)^[m]
      (fun s => liftΓh hΓ (hpow (pi1geo (Rfin Fq K) K (Fintype.card Fq)) φ⁻¹ (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) m s))) :
    LinearMap.trace (ZMod N) _ (frobH1c
      (σB ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
        (downH (thetaE Fq K E hE).range G')))
      ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).subgroupOf G') (fun s => ((bdryInf Fq K).inertia s).subgroupOf G')
      ⟨φ⁻¹ ^ m, hmem⟩ (trueTau (bdryInf Fq K) φ⁻¹)^[m]
      (fun s => liftΓh hΓ (hpow (pi1geo (Rfin Fq K) K (Fintype.card Fq)) φ⁻¹ (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) m s)) hI') =
      trH1Sub Fq K E hE N hΓ hH σ⁻¹ 1 := by
  have hS := frobSpec_pow (bdryInf Fq K) (frobSpec_true (bdryInf Fq K) φ⁻¹) m
  have hstabD := hstabD_of (bdryInf Fq K) (fun _ => Iff.rfl) (stab_mem_inertia_K Fq K hq he)
  have hψ' : ((⟨φ⁻¹ ^ m, hmem⟩ : G') : Pi1 (Rfin Fq K) K) = ((⟨c0, hc0⟩ : pi1geo (Rfin Fq K) K (Fintype.card Fq)) : Pi1 (Rfin Fq K) K) *
      (((upH hH (rangeElt (thetaE Fq K E hE) σ⁻¹) : ((thetaE Fq K E hE).range).subgroupOf G') : G') :
        Pi1 (Rfin Fq K) K) := by
    rw [coe_upH_rangeElt, map_inv, hσ, inv_inv]
    show φ⁻¹ ^ m = c0 * (c0⁻¹ * φ⁻¹ ^ m)
    group
  have h1 := frobH1c_sub_true (bdryInf Fq K)
    (σB ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
      (downH (thetaE Fq K E hE).range G'))) hΓ hstabD (ψ' := ⟨φ⁻¹ ^ m, hmem⟩) ⟨c0, hc0⟩ hψ' hS hI'
    (bdryCompat_sub hΓ _ _ _ (trueCompat (bdryInf Fq K) _))
  -- operator-level equality first; NO rw/rewrite on the goal (kabstract has no sharing cache: > 10 min here) and no
  -- `congrArg (LinearMap.trace R _)` with an unknown module (80-200 s)
  have e : frobH1c
      (σB ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
        (downH (thetaE Fq K E hE).range G')))
      ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).subgroupOf G') (fun s => ((bdryInf Fq K).inertia s).subgroupOf G')
      ⟨φ⁻¹ ^ m, hmem⟩ (trueTau (bdryInf Fq K) φ⁻¹)^[m]
      (fun s => liftΓh hΓ (hpow (pi1geo (Rfin Fq K) K (Fintype.card Fq)) φ⁻¹ (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) m s)) hI' =
      frobH1c (pushRep ((thetaE Fq K E hE).range.subgroupOf G')
        ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
          (downH (thetaE Fq K E hE).range G')))
        (geoU (pi1geo (Rfin Fq K) K (Fintype.card Fq)) G') (fun s => ((bdryInf Fq K).inertia s).subgroupOf G')
        ((upH hH (rangeElt (thetaE Fq K E hE) σ⁻¹) : (thetaE Fq K E hE).range.subgroupOf G') : G')
        (trueTau (bdryInf Fq K) (thetaE Fq K E hE σ⁻¹))
        (fun s => liftΓ hΓ (trueH (bdryInf Fq K) (thetaE Fq K E hE σ⁻¹) s))
        (bdryCompat_sub hΓ (upH hH (rangeElt (thetaE Fq K E hE) σ⁻¹) : G') _ _
          (trueCompat (bdryInf Fq K) (thetaE Fq K E hE σ⁻¹))) ^ 1 :=
    (h1.trans (frobH1c_congr _ _ _ rfl (congrArg (trueTau (bdryInf Fq K)) (coe_upH_rangeElt _ hH σ⁻¹))
      (by rw [coe_upH_rangeElt]) _ _)).trans (pow_one _).symm
  exact (congrArg (fun f => LinearMap.trace (ZMod N)
    (H1c (σB ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
        (downH (thetaE Fq K E hE).range G')))
      ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).subgroupOf G') (fun s => ((bdryInf Fq K).inertia s).subgroupOf G')) f)
    e).trans rfl

end BlockPt

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PDiv1b =====
section

/-!
# S4-Lefschetz, L6e (1b): any divisor is `l^n`-divisible modulo principal divisors at the finite places

* `exists_fin_div_level`: for any divisor `D` on `F_m` and `l ∤ q`, at some level `(j+1)!` (`m ≤ j`) the conorm of
  `D` agrees with `l^n • z + div f` at every finite place. A degree-one place at infinity (at a large level,
  `JacFrob.degOne`) absorbs the degree of `D`, and `exists_div_level` handles the degree-zero remainder.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open PicDescent Places ZetaSB

section PicFin

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

include hk in
/-- **A place at infinity of degree one** at a finite level `lev M0`. -/
theorem exists_inf_degOne :
    ∃ M0 : ℕ, ∃ Q : Place (Lc Fq Ω (lev M0)) (Fc Fq F Ω (lev M0)), Q.isLeft = false ∧ Q.deg = 1 := by
  obtain ⟨w0⟩ := Places.nonempty_infPlace (Lc Fq Ω (lev 0)) (Fc Fq F Ω (lev 0))
  obtain ⟨P, hP⟩ := JacFrob.exists_contB_eq Fq F Ω hk 0 (Sum.inr w0)
  obtain ⟨M0, hM0⟩ := JacFrob.degOne Fq F Ω hk P
  refine ⟨M0, JacFrob.contB Fq F Ω hk M0 P, ?_, hM0 M0 le_rfl⟩
  rw [JacFrob.isLeft_contB, ← JacFrob.isLeft_contB Fq F Ω hk 0 P, hP]
  rfl

end PicFin

end

end Lefschetz
end RamanujanPetersson


end


