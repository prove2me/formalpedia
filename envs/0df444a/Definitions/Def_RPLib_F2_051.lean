-- Prove2me | Definitions.Def_RPLib_F2_051
-- name    : RPLib_F2_051
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T15:10:23.716226+00:00
-- url     : https://prove2.me/theorems/ddf6044a-7301-4078-ab97-c578d44f78f9
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 051 of 70
-- statement:
--   File 051 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_CurveTr2`: S4-Lefschetz, L4i part 2b: Frobenius traces on `H¹_c` of a cover `E ⊆ K_U` inside `π₁(U)`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_048

/-!
# Ramanujan-Petersson curve library (flat edition), file 051 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_CurveTr2`: S4-Lefschetz, L4i part 2b: Frobenius traces on `H¹_c` of a cover `E ⊆ K_U` inside `π₁(U)`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_CurveTr2 =====
section

/-!
# S4-Lefschetz, L4i part 2b: Frobenius traces on `H¹_c` of a cover `E ⊆ K_U` inside `π₁(U)`

* `trace_cover_eq`: `Tr(F^m | H¹_c(E))` (true Frobenius data of `E`) equals the trace on `H¹_c(Γ ∩ H; Λ)`
  (`H = range thetaE`) with the Frobenius data `rangeElt`/`geoLift` of the Shapiro setting;
* **`trace_cover_sub`**: inside any ambient `G' = H·Γ`, `Tr(F^m | H¹_c(Γ ∩ G'; Ind_H^{G'} Λ))` with the true
  Frobenius data of `U` at `thetaE ψ` equals `Tr(F^m | H¹_c(E))` with the true data of `E` at `ψ`
  (stated with the trace definitions `trH1Sub` / `trH1E`).

Big intermediate statements are `private` and the headline is stated through `def`s: the olean export step
(`LibrarySuggestions` symbol frequencies) folds over the type of every public theorem, and on the unwrapped
statements of this file it ran for hours (session 16).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a CupDuality Representation

section BdryTr

variable {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂] [IsTopologicalGroup G₁]
  {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂} [Δ₁.Normal] {e : Δ₁ ≃ₜ* Δ₂} {S : Type}
  {I₁ : S → Subgroup G₁} {I₂ : S → Subgroup G₂}

end BdryTr

section CurveTr2

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

set_option synthInstance.maxHeartbeats 400000 in
private theorem bdryCompat_eE (ψ : Pi1 (Rfin (Kc Fq E) E) E) :
    BdryCompat (geoU (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (thetaE Fq K E hE).range)
      (bdJE Fq K E hE) (thEq Fq K E hE ψ) (trueTau (bdryInf (Kc Fq E) E) ψ)
      (fun t => eE Fq K E hE (trueH (bdryInf (Kc Fq E) E) ψ t)) :=
  bdryCompat_tr (intwIE Fq K E hE) (thEq Fq K E hE) (fun _ => rfl) (trueCompat (bdryInf (Kc Fq E) E) ψ)

set_option synthInstance.maxHeartbeats 400000 in
/-- The Shapiro-side Frobenius datum of the cover is boundary-compatible (stated with `bdJE`). -/
def bdryCompat_geoLift (ψ : Pi1 (Rfin (Kc Fq E) E) E) :
    BdryCompat (geoU (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (thetaE Fq K E hE).range)
      (bdJE Fq K E hE) (rangeElt (thetaE Fq K E hE) ψ) (trueTau (bdryInf (Kc Fq E) E) ψ)
      (geoLift (thetaE Fq K E hE) (thetaE_mem_pi1geo_iff Fq K E hE) (trueH (bdryInf (Kc Fq E) E) ψ)) := by
  rw [← thEq_eq_rangeElt, ← eE_eq_geoLift]
  exact bdryCompat_eE Fq K E hE ψ

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
/-- The transport `h1cTr` along `eE` turns the Frobenius of `E` into the Shapiro-side Frobenius. -/
private theorem h1cTr_frob_cover (N : ℕ) (ψ : Pi1 (Rfin (Kc Fq E) E) E)
    (x : H1c (Representation.trivial (ZMod N) (Pi1 (Rfin (Kc Fq E) E) E) (ZMod N))
      (pi1geo (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E))) (bdryInf (Kc Fq E) E).inertia) :
    h1cTr (intwE Fq K E hE N) (intwIE Fq K E hE)
      (frobH1c (Representation.trivial (ZMod N) (Pi1 (Rfin (Kc Fq E) E) E) (ZMod N))
        (pi1geo (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E))) (bdryInf (Kc Fq E) E).inertia ψ
        (trueTau (bdryInf (Kc Fq E) E) ψ) (trueH (bdryInf (Kc Fq E) E) ψ)
        (trueCompat (bdryInf (Kc Fq E) E) ψ) x) =
    frobH1c (Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N))
      (geoU (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (thetaE Fq K E hE).range) (bdJE Fq K E hE)
      (rangeElt (thetaE Fq K E hE) ψ) (trueTau (bdryInf (Kc Fq E) E) ψ)
      (geoLift (thetaE Fq K E hE) (thetaE_mem_pi1geo_iff Fq K E hE) (trueH (bdryInf (Kc Fq E) E) ψ))
      (bdryCompat_geoLift Fq K E hE ψ)
      (h1cTr (intwE Fq K E hE N) (intwIE Fq K E hE) x) :=
  (h1cTr_frob (intwE Fq K E hE N) (intwIE Fq K E hE) (thEq Fq K E hE) (fun _ => rfl) ψ rfl
    (trueTau (bdryInf (Kc Fq E) E) ψ) (trueH (bdryInf (Kc Fq E) E) ψ) (trueCompat (bdryInf (Kc Fq E) E) ψ)
    (bdryCompat_eE Fq K E hE ψ) x).trans
  (congrFun (congrArg DFunLike.coe (frobH1c_congr
    (Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N))
    (geoU (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (thetaE Fq K E hE).range) (bdJE Fq K E hE)
    (thEq_eq_rangeElt Fq K E hE ψ) rfl (eE_eq_geoLift Fq K E hE (trueH (bdryInf (Kc Fq E) E) ψ))
    (bdryCompat_eE Fq K E hE ψ)
    (bdryCompat_geoLift Fq K E hE ψ))) _)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
/-- `Tr(F^m | H¹_c(E))` (true Frobenius data of `E` at `ψ`) is the trace on `H¹_c(Γ ∩ H; Λ)` with the
Shapiro-side data `rangeElt`/`geoLift`. -/
def trace_cover_eq (N : ℕ) (ψ : Pi1 (Rfin (Kc Fq E) E) E) (m : ℕ) :
    LinearMap.trace (ZMod N) _ (frobH1c (Representation.trivial (ZMod N) (Pi1 (Rfin (Kc Fq E) E) E) (ZMod N))
      (pi1geo (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E))) (bdryInf (Kc Fq E) E).inertia ψ
      (trueTau (bdryInf (Kc Fq E) E) ψ) (trueH (bdryInf (Kc Fq E) E) ψ)
      (trueCompat (bdryInf (Kc Fq E) E) ψ) ^ m) =
    LinearMap.trace (ZMod N) _ (frobH1c (Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N))
      (geoU (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (thetaE Fq K E hE).range) (bdJE Fq K E hE)
      (rangeElt (thetaE Fq K E hE) ψ) (trueTau (bdryInf (Kc Fq E) E) ψ)
      (geoLift (thetaE Fq K E hE) (thetaE_mem_pi1geo_iff Fq K E hE) (trueH (bdryInf (Kc Fq E) E) ψ))
      (bdryCompat_geoLift Fq K E hE ψ) ^ m) :=
  trace_pow_eq_of_comm (h1cTr (intwE Fq K E hE N) (intwIE Fq K E hE)) _ _ (h1cTr_frob_cover Fq K E hE N ψ) m

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end CurveTr2

end

end Lefschetz
end RamanujanPetersson


end


