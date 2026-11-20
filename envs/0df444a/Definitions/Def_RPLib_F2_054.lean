-- Prove2me | Definitions.Def_RPLib_F2_054
-- name    : RPLib_F2_054
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T15:49:08.106201+00:00
-- url     : https://prove2.me/theorems/6f9b3eb9-7c39-4997-b484-9db054736aca
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 054 of 70
-- statement:
--   File 054 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_H1Sub`: S4-Lefschetz, L3e2d2: `H¹_c` of the ambient `G'`-cone is finite free
--   * `S4.Def_RP_Lefschetz_PtE`: S4-Lefschetz, L5c4b: a block cover `E` inside a finite level `L`, and the per-point block count
--   * `S4.Def_RP_Lefschetz_PtAsm`: S4-Lefschetz, L5c4c: the `k_E`-points of a block cover `E`, summed over the points of `U`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_051
import Definitions.Def_RPLib_F2_082

/-!
# Ramanujan-Petersson curve library (flat edition), file 054 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_H1Sub`: S4-Lefschetz, L3e2d2: `H¹_c` of the ambient `G'`-cone is finite free
* `S4.Def_RP_Lefschetz_PtE`: S4-Lefschetz, L5c4b: a block cover `E` inside a finite level `L`, and the per-point block count
* `S4.Def_RP_Lefschetz_PtAsm`: S4-Lefschetz, L5c4c: the `k_E`-points of a block cover `E`, summed over the points of `U`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_H1Sub =====
section

/-!
# S4-Lefschetz, L3e2d2: `H¹_c` of the ambient `G'`-cone is finite free

For `H = range thetaE ≤ G'` and `G' = H·Γ`: Shapiro inside `G'` (`shapiroH1cEquiv` with the `_sub` data), the ambient
transport (`h1cTr (intw_sub ..)`) and the chart (`h1cTr (intwE ..)`) give
`h1cSubEquiv : H¹_c(Γ ∩ G'; Ind_{H}^{G'} Λ) ≃ H¹_c(E, Λ)` (the linear equivalence behind `trace_cover_sub`), so
`free_h1cSub`: the left side is finite free over `ℤ/l^n` (`free_curveH1c` for `E` over its constant field).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a CupDuality Representation

section H1Sub

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
/-- Shapiro + ambient transport + chart: `H¹_c(Γ ∩ G'; Ind_H^{G'} Λ) ≃ H¹_c(E, Λ)` (`H = range thetaE`). -/
def h1cSubEquiv (N : ℕ) {G' : Subgroup (Pi1 (Rfin Fq K) K)}
    (hΓ : pi1geo (Rfin Fq K) K (Fintype.card Fq) ≤ G') (hH : (thetaE Fq K E hE).range ≤ G')
    (hcov' : ∀ x ∈ G', ∃ a ∈ (thetaE Fq K E hE).range, ∃ b ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq), x = a * b)
    (R : CosetReps (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (thetaE Fq K E hE).range) :
    H1c (pushRep ((thetaE Fq K E hE).range.subgroupOf G')
        ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
          (downH (thetaE Fq K E hE).range G')))
      (geoU (pi1geo (Rfin Fq K) K (Fintype.card Fq)) G') (fun s => ((bdryInf Fq K).inertia s).subgroupOf G')
      ≃ₗ[ZMod N]
    H1c (Representation.trivial (ZMod N) (Pi1 (Rfin (Kc Fq E) E) E) (ZMod N))
      (pi1geo (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E))) (bdryInf (Kc Fq E) E).inertia :=
  ((shapiroH1cEquiv (geoU (pi1geo (Rfin Fq K) K (Fintype.card Fq)) G') ((thetaE Fq K E hE).range.subgroupOf G')
      ((Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)).comp
        (downH (thetaE Fq K E hE).range G'))
      (fun s => ((bdryInf Fq K).inertia s).subgroupOf G') _ _ _
      (inertiaLift_sub hΓ (shap_inertiaLift Fq K E hE))
      (dCover_sub hΓ hH (shap_dCover Fq K E hE hq he)) (dDisj_sub hΓ (shap_dDisj Fq K E hE)) (cosetReps_sub hΓ R)
      (hcov_sub hΓ hH hcov') (isOpen_sub (isOpen_range_thetaE Fq K E hE))).trans
    (h1cTr (intw_sub (pi1geo (Rfin Fq K) K (Fintype.card Fq))
        (Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)) hH)
      (intwI_sub (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdJE Fq K E hE) hH))).trans
    (h1cTr (intwE Fq K E hE N) (intwIE Fq K E hE)).symm

end H1Sub

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtE =====
section

/-!
# S4-Lefschetz, L5c4b: a block cover `E` inside a finite level `L`, and the per-point block count

* `mem_range_thetaE_iff_fix`: `range thetaE` = the automorphisms of `K_U` fixing `E` pointwise;
* `resPt_mem_fix_iff`: `resPt x ∈ Gal(L/E) ↔ x` fixes `E`;
* `rfixE`: the `Gal(L/E)`-invariants of the integral closure of `R_fin` in `L`; `rfixEquiv : R_E ≃+* rfixE`;
* `kcInc`, `toStar`, `kappaE`: the constants of `E` in `K_U`, in `kStar`, in `rfixE`;
* `frob_apply_kStar`: a normalized Frobenius acts on `kStar` as `x ↦ x^Q`;
* `hGH_ptE`, `hcond_ptE`, `hRpG_ptE`, `hRpD_ptE`: the hypotheses of `card_fixed_blk_lift`;
* `card_pt_blk`: the `k_E`-points of `R_E` over a point `u` of `U` = `#{p ∈ π(Γ) | (p a)⁻¹ π(F_u) (p a) = γ}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a

section PtE

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

variable {K}

section RFix

variable {E L : IntermediateField K (AlgebraicClosure K)} (hEL : E ≤ L)

end RFix

section Hyp

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e)
variable {E L : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K E] [Algebra.IsSeparable K E]

variable (hEL : E ≤ L) [FiniteDimensional K L] [IsGalois K L]

variable (hE : E ≤ maxUnram Fq[X] K) (hLU : L ≤ maxUnram (Rfin Fq K) K)
variable {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
variable {φ c0 : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)
  (hc0 : c0 ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq)) {m : ℕ} (hm : 0 < m)
  [NeZero ((Fintype.card Fq ^ m) ^ Fintype.card Gf - 1)] {ζ : maxUnram (Rfin Fq K) K}
  (hζ : IsPrimitiveRoot ζ ((Fintype.card Fq ^ m) ^ Fintype.card Gf - 1))
  (hblk : ∀ τ, τ ∈ (thetaE Fq K E hE).range ↔ τ ∈ blkH π (c0⁻¹ * φ⁻¹ ^ m) ζ hζ)

set_option maxHeartbeats 2000000 in
include hφ hc0 hm hblk in
/-- **The block count at one point `u`** (for `E ⊆ L`): the `Fr`-fixed points of `rfixE` over `u` with the
normalization on `k_E` are counted by `#{p ∈ π(Γ) | (p a)⁻¹ π(F) (p a) = γ}`. -/
theorem card_pt_blk (hLun : IsUnramifiedSub (Rfin Fq K) K L)
    (hLπ : ∀ σ : Pi1 (Rfin Fq K) K, (∀ y : maxUnram (Rfin Fq K) K, (y : AlgebraicClosure K) ∈ L → σ y = y) →
      σ ∈ π.ker)
    {n : ℕ} (hcard : Fintype.card (Kc Fq E) = Fintype.card Fq ^ m) (hmn : m ∣ n) (hQ : 1 < p ^ (e * n))
    (hζn : ζ ∈ kStar (Rfin Fq K) K hq n) {a γ : Gf} (hπg : π (c0⁻¹ * φ⁻¹ ^ m) = a * γ⁻¹ * a⁻¹)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (Fr : Ω →+* Ω) (hFr : ∀ z, Fr z = z ^ (Fintype.card Fq ^ m))
    (ιS : kStar (Rfin Fq K) K hq n →+* Ω) (u : Rfin Fq K →+* Ω) (hu : Fr.comp u = u)
    (w : proChart (Rfin Fq K) K (Rfin Fq K) →+* Ω) (F : Pi1 (Rfin Fq K) K)
    (hwu : w.comp (algebraMap (Rfin Fq K) _) = u) (hwF : ∀ b, w (F • b) = Fr (w b))
    (hwι : ∀ x, w (incStar (Rfin Fq K) K hq n hQ x) = ιS x) :
    Finite {v : rfixE Fq hEL →+* Ω // (v.comp (algebraMap (Rfin Fq K) _) = u ∧ Fr.comp v = v) ∧
        ∀ c, v (kappaE Fq hEL c) = ιS (toStar Fq hq (hEL.trans hLU) hcard hmn c)} ∧
    Nat.card {v : rfixE Fq hEL →+* Ω // (v.comp (algebraMap (Rfin Fq K) _) = u ∧ Fr.comp v = v) ∧
        ∀ c, v (kappaE Fq hEL c) = ιS (toStar Fq hq (hEL.trans hLU) hcard hmn c)} =
      Nat.card {p : Gf // p ∈ (pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π ∧ (p * a)⁻¹ * π F * (p * a) = γ} := by
  haveI hG := isGaloisGroup_ptE Fq (L := L)
  haveI : SMulCommClass (L ≃ₐ[K] L) (Rfin Fq K) (integralClosure (Rfin Fq K) L) := hG.commutes
  haveI : Algebra.IsInvariant (Rfin Fq K) (integralClosure (Rfin Fq K) L) (L ≃ₐ[K] L) := hG.isInvariant
  haveI hGC := isGaloisGroup_rfixE Fq hEL
  haveI : SMulCommClass (galLE hEL) (rfixE Fq hEL) (integralClosure (Rfin Fq K) L) := hGC.commutes
  haveI : Algebra.IsInvariant (rfixE Fq hEL) (integralClosure (Rfin Fq K) L) (galLE hEL) := hGC.isInvariant
  haveI := faithfulSMul_rfixE Fq hEL
  haveI : Module.Finite (Rfin Fq K) (integralClosure (Rfin Fq K) L) :=
    IsIntegralClosure.finite (Rfin Fq K) K L (integralClosure (Rfin Fq K) L)
  have hq2 : 2 ≤ Fintype.card Fq := Fintype.one_lt_card
  have hQm : 1 < Fintype.card Fq ^ m := Nat.one_lt_pow hm.ne' hq2
  have hfinu : (Set.range u).Finite := (finite_setOf_pow_eq (F := Ω) hQm).subset (by
    rintro _ ⟨a', rfl⟩
    have h1 := RingHom.congr_fun hu a'
    rw [RingHom.comp_apply, hFr] at h1
    exact h1)
  have hfin := hfin_gen (A := Rfin Fq K) (B := integralClosure (Rfin Fq K) L) u hfinu
  have hw0 : (w.comp (jPt (Rfin Fq K) K hLU)).comp (algebraMap (Rfin Fq K) _) = u := by
    ext a'
    show w (jPt (Rfin Fq K) K hLU (algebraMap (Rfin Fq K) _ a')) = u a'
    rw [jPt_algebraMap]
    exact RingHom.congr_fun hwu a'
  have hF : ∀ b, Fr ((w.comp (jPt (Rfin Fq K) K hLU)) b) =
      (w.comp (jPt (Rfin Fq K) K hLU)) (resPt (Rfin Fq K) K hLU F • b) := by
    intro b
    show Fr (w (jPt (Rfin Fq K) K hLU b)) = w (jPt (Rfin Fq K) K hLU (resPt (Rfin Fq K) K hLU F • b))
    rw [jPt_smul]
    exact (hwF _).symm
  have hker : ∀ σ, resPt (Rfin Fq K) K hLU σ = 1 → π σ = 1 := fun σ hσ =>
    (MonoidHom.mem_ker).1 (hLπ σ (fix_of_resPt_eq_one hLU hσ))
  have hFζ : F ζ = ζ ^ (Fintype.card Fq ^ m) := frob_apply_kStar Fq hq hQ Fr hFr ιS w F hwF hwι ζ hζn
  have keyF := finite_fixed_ptRes_pred (A := Rfin Fq K) (B := integralClosure (Rfin Fq K) L) (C := rfixE Fq hEL)
    (G := L ≃ₐ[K] L) (Ω := Ω) (galLE hEL)
  have key := card_fixed_blk_lift (A := Rfin Fq K) (B := integralClosure (Rfin Fq K) L) (C := rfixE Fq hEL)
    (G := L ≃ₐ[K] L) (Ω := Ω) (galLE hEL)
  exact ⟨keyF hLun Fr u hfin _ hw0 (resPt (Rfin Fq K) K hLU F) hF
      (fun v => ∀ c, v (kappaE Fq hEL c) = ιS (toStar Fq hq (hEL.trans hLU) hcard hmn c)),
    key hLun Fr u hfin _ hw0 (resPt (Rfin Fq K) K hLU) (resPt_surjective _ _ hLU) π hker F hF
      (fun v => ∀ c, v (kappaE Fq hEL c) = ιS (toStar Fq hq (hEL.trans hLU) hcard hmn c))
      (pi1geo (Rfin Fq K) K (Fintype.card Fq))
      (fun y hy c => hRpG_ptE Fq hq hEL hLU hm hcard hmn hQ ιS w hwι y hy c)
      (hRpD_ptE Fq hq hEL hE hLU π hφ hc0 hm hζ hblk hcard hmn hQ ιS w hwι)
      (fun y hy => hGH_ptE Fq hEL hE hLU π hφ hc0 hm hζ hblk y hy) a γ
      (fun y hy => hcond_ptE Fq hEL hE hLU π hφ hc0 hm hζ hblk hπg F hFζ y hy)⟩

end Hyp

end PtE

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtAsm =====
section

/-!
# S4-Lefschetz, L5c4c: the `k_E`-points of a block cover `E`, summed over the points of `U`

* `pow_pow_fix`, `coe_algebraMap_kc`, `toStar_algebraMap_ptA`, `algebraMap_rfixE_fq`: compatibilities;
* `rfixHomEquiv`, `card_fixed_rfin_eq`: `k_E`-points of `R_E` = normalized `Fr`-fixed points of `rfixE`;
* `card_rfin_eq_sum`: `#R_E(k_E) = Σ_{u ∈ S} #{p ∈ π(Γ) | (p a)⁻¹ π(F_u) (p a) = γ}` for the `F_{q^m}`-points `S` of `U`
  (normalized by `ιS` on `𝔽_q`) and normalized Frobenius elements `F_u`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a

section PtAsm

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {K : Type} [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e)
variable {E L : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K E] [Algebra.IsSeparable K E]

variable (hEL : E ≤ L) [FiniteDimensional K L] [IsGalois K L]

variable (Ω : Type) [Field Ω]

end PtAsm

section Main

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {K : Type} [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e)

set_option maxHeartbeats 2000000 in
/-- **L5c4c: the `k_E`-points of a block cover, summed over the points of `U`.** For `E ⊆ K_U` finite separable
over `K` with constant field `k_E` of degree `m` (`hcard`) and `Gal(K_U/E)` the block group `blkH` (`hblk`), the
`k_E`-points of `R_E` number `Σ_{u ∈ S} #{p ∈ π(Γ) | (p a)⁻¹ π(F_u) (p a) = γ}`, where `S` is the set of
`Fr`-fixed points `u : R_fin → Ω` restricting to `ιS` on `𝔽_q`, and `F_u` are normalized Frobenius elements. -/
theorem card_rfin_eq_sum (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    [Algebra.IsSeparable K E] (hE : E ≤ maxUnram Fq[X] K) {Gf : Type} [Group Gf] [Fintype Gf]
    (π : Pi1 (Rfin Fq K) K →* Gf) (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
    {φ c0 : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)
    (hc0 : c0 ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq)) {m : ℕ} (hm : 0 < m)
    [NeZero ((Fintype.card Fq ^ m) ^ Fintype.card Gf - 1)] {ζ : maxUnram (Rfin Fq K) K}
    (hζ : IsPrimitiveRoot ζ ((Fintype.card Fq ^ m) ^ Fintype.card Gf - 1))
    (hblk : ∀ τ, τ ∈ (thetaE Fq K E hE).range ↔ τ ∈ blkH π (c0⁻¹ * φ⁻¹ ^ m) ζ hζ)
    (hcard : Fintype.card (Kc Fq E) = Fintype.card Fq ^ m) {n : ℕ} (hmn : m * Fintype.card Gf ∣ n)
    (hQ : 1 < p ^ (e * n)) {a γ : Gf} (hπg : π (c0⁻¹ * φ⁻¹ ^ m) = a * γ⁻¹ * a⁻¹)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (Fr : Ω →+* Ω) (hFr : ∀ z, Fr z = z ^ (Fintype.card Fq ^ m))
    (ιS : kStar (Rfin Fq K) K hq n →+* Ω) (S : Finset (Rfin Fq K →+* Ω))
    (hS : ∀ u, u ∈ S ↔ (u.comp (algebraMap Fq (Rfin Fq K)) = ιS.comp (algebraMap Fq (kStar (Rfin Fq K) K hq n)) ∧
      Fr.comp u = u))
    (Fu : (Rfin Fq K →+* Ω) → Pi1 (Rfin Fq K) K)
    (hFu : ∀ u ∈ S, ∃ w : proChart (Rfin Fq K) K (Rfin Fq K) →+* Ω,
      w.comp (algebraMap (Rfin Fq K) _) = u ∧ (∀ b, w (Fu u • b) = Fr (w b)) ∧
        ∀ x, w (incStar (Rfin Fq K) K hq n hQ x) = ιS x) :
    Nat.card (Rfin (Kc Fq E) E →ₐ[Kc Fq E] Kc Fq E) =
      ∑ u ∈ S, Nat.card {p : Gf // p ∈ (pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π ∧
        (p * a)⁻¹ * π (Fu u) * (p * a) = γ} := by
  classical
  have hq2 : 2 ≤ Fintype.card Fq := Fintype.one_lt_card
  have hmn' : m ∣ n := dvd_trans (dvd_mul_right m _) hmn
  have hζn : ζ ∈ kStar (Rfin Fq K) K hq n := by
    rw [mem_kStar]
    obtain ⟨t, rfl⟩ := hmn
    have hQ1 : 1 ≤ (Fintype.card Fq ^ m) ^ Fintype.card Gf :=
      Nat.one_le_pow _ _ (pow_pos (lt_of_lt_of_le two_pos hq2) m)
    rw [pow_mul, pow_mul]
    exact pow_pow_fix (prim_pow_fix hQ1 hζ) t
  have hfg : E.FG := by
    apply IntermediateField.fg_of_fg_toSubalgebra
    apply Subalgebra.fg_of_fg_toSubmodule
    exact (Submodule.fg_iff_finiteDimensional _).mpr ‹FiniteDimensional K E›
  obtain ⟨t, htfin, hadj⟩ := IntermediateField.fg_def.mp hfg
  obtain ⟨L, hL, hadjL, hLπ⟩ := exists_unramSet_fix (Rfin Fq K) K π.ker hπ htfin.toFinset (fun x hx => by
    have hxt : x ∈ t := by simpa using hx
    have hxE : x ∈ E := by
      rw [← hadj]
      exact IntermediateField.subset_adjoin K t hxt
    exact le_maxUnram_rfin_ptE Fq K hE hxE)
  rw [Set.Finite.coe_toFinset, hadj] at hadjL
  haveI : FiniteDimensional K L := hL.1
  haveI : IsGalois K L := hL.2.1
  have hLU : L ≤ maxUnram (Rfin Fq K) K := le_maxUnram_of_mem hL
  have hEU : E ≤ maxUnram (Rfin Fq K) K := hadjL.trans hLU
  have h1 := card_algHom_eq_fixed (k := Kc Fq E) (R := Rfin (Kc Fq E) E) (Ω := Ω)
    (ιS.comp (toStar Fq hq hEU hcard hmn'))
  have h2 := card_fixed_rfin_eq Fq hadjL Ω hcard Fr hFr (ιS.comp (toStar Fq hq hEU hcard hmn'))
  refine h1.trans (h2.trans ?_)
  have hs : ∀ v : rfixE Fq hadjL →+* Ω,
      (Fr.comp v = v ∧ ∀ c, v (kappaE Fq hadjL c) = (ιS.comp (toStar Fq hq hEU hcard hmn')) c) →
        v.comp (algebraMap (Rfin Fq K) (rfixE Fq hadjL)) ∈ S := by
    rintro v ⟨hv1, hv2⟩
    rw [hS]
    refine ⟨RingHom.ext fun c => ?_, ?_⟩
    · show v (algebraMap (Rfin Fq K) (rfixE Fq hadjL) (algebraMap Fq (Rfin Fq K) c)) =
        ιS (algebraMap Fq (kStar (Rfin Fq K) K hq n) c)
      rw [algebraMap_rfixE_fq Fq hadjL c, hv2, RingHom.comp_apply, toStar_algebraMap_ptA Fq hq hEU hcard hmn' c]
    · rw [← RingHom.comp_assoc, hv1]
  have hfib : ∀ u, Finite {v : rfixE Fq hadjL →+* Ω // v.comp (algebraMap (Rfin Fq K) (rfixE Fq hadjL)) = u ∧
      (Fr.comp v = v ∧ ∀ c, v (kappaE Fq hadjL c) = (ιS.comp (toStar Fq hq hEU hcard hmn')) c)} := by
    intro u
    by_cases hu : u ∈ S
    · obtain ⟨w, hwu, hwF, hwι⟩ := hFu u hu
      have hb := card_pt_blk Fq hq hadjL hE hLU π hφ hc0 hm hζ hblk hL.2.2 hLπ hcard hmn' hQ hζn hπg Fr hFr ιS u
        ((hS u).1 hu).2 w (Fu u) hwu hwF hwι
      exact @Finite.of_equiv _ _ hb.1 (Equiv.subtypeEquivRight fun v => and_assoc)
    · haveI : IsEmpty {v : rfixE Fq hadjL →+* Ω // v.comp (algebraMap (Rfin Fq K) (rfixE Fq hadjL)) = u ∧
          (Fr.comp v = v ∧ ∀ c, v (kappaE Fq hadjL c) = (ιS.comp (toStar Fq hq hEU hcard hmn')) c)} :=
        ⟨fun v => hu (v.2.1 ▸ hs v.1 v.2.2)⟩
      infer_instance
  haveI := hfib
  refine (card_eq_sum_fiber (fun v : rfixE Fq hadjL →+* Ω => v.comp (algebraMap (Rfin Fq K) (rfixE Fq hadjL)))
    (fun v => Fr.comp v = v ∧ ∀ c, v (kappaE Fq hadjL c) = (ιS.comp (toStar Fq hq hEU hcard hmn')) c) S hs).trans
    (Finset.sum_congr rfl fun u hu => ?_)
  obtain ⟨w, hwu, hwF, hwι⟩ := hFu u hu
  have hb := card_pt_blk Fq hq hadjL hE hLU π hφ hc0 hm hζ hblk hL.2.2 hLπ hcard hmn' hQ hζn hπg Fr hFr ιS u
    ((hS u).1 hu).2 w (Fu u) hwu hwF hwι
  exact (Nat.card_congr (Equiv.subtypeEquivRight fun v => and_assoc.symm)).trans hb.2

end Main

end

end Lefschetz
end RamanujanPetersson


end


