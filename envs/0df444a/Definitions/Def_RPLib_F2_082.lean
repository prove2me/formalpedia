-- Prove2me | Definitions.Def_RPLib_F2_082
-- name    : RPLib_F2_082
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T15:16:46.431676+00:00
-- url     : https://prove2.me/theorems/486b7284-30f0-4bf9-ae78-ad8120168069
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 082 (part 1 of file 054 of 70)
-- statement:
--   File 082 (part 1 of file 054 of 70) of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_CurveTr2`: S4-Lefschetz, L4i part 2b: Frobenius traces on `H¹_c` of a cover `E ⊆ K_U` inside `π₁(U)`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_051

/-!
# Ramanujan-Petersson curve library (flat edition), file 082 (part 1 of file 054 of 70)

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

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **L4i2**: inside an ambient `G' = H·Γ` (`H = range thetaE`), the Frobenius trace on
`H¹_c(Γ ∩ G'; Ind_H^{G'} Λ)` with the true data of `U` at `thetaE ψ` is the trace on `H¹_c(E)` with the
true data of `E` at `ψ`. -/
theorem trace_cover_sub (N : ℕ) {G' : Subgroup (Pi1 (Rfin Fq K) K)}
    (hΓ : pi1geo (Rfin Fq K) K (Fintype.card Fq) ≤ G') (hH : (thetaE Fq K E hE).range ≤ G')
    (hcov' : ∀ x ∈ G', ∃ a ∈ (thetaE Fq K E hE).range, ∃ b ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq), x = a * b)
    (R : CosetReps (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (thetaE Fq K E hE).range)
    (ψ : Pi1 (Rfin (Kc Fq E) E) E) (m : ℕ) :
    trH1Sub Fq K E hE N hΓ hH ψ m = trH1E Fq K E N ψ m := by
  have h1 := trace_shapiro_sub (Representation.trivial (ZMod N) (thetaE Fq K E hE).range (ZMod N)) hΓ hH
    (shap_inertiaLift Fq K E hE) (shap_dCover Fq K E hE hq he) (shap_dDisj Fq K E hE) R hcov'
    (isOpen_range_thetaE Fq K E hE) (rangeElt (thetaE Fq K E hE) ψ) _ _
    (trueCompat (bdryInf Fq K) (thetaE Fq K E hE ψ)) _ _
    (bdryCompat_geoLift Fq K E hE ψ)
    (gen_frobMatch (bdryInf Fq K) (bdryInf (Kc Fq E) E) (chartE Fq K E hE).symm (fun _ => Iff.rfl)
      (fun _ => Iff.rfl) (thetaE Fq K E hE) (fun σ x => chartE_symm_smul Fq K E hE σ x)
      (thetaE_mem_pi1geo_iff Fq K E hE)
      (hstabD_of (bdryInf Fq K) (fun _ => Iff.rfl) (stab_mem_inertia_K Fq K hq he)) ψ
      (frobSpec_true (bdryInf Fq K) (thetaE Fq K E hE ψ)) (frobSpec_true (bdryInf (Kc Fq E) E) ψ)) m
  have h2 := trace_cover_eq Fq K E hE N ψ m
  unfold trH1Sub trH1E
  with_reducible_and_instances exact h1.trans h2.symm

end CurveTr2

end

end Lefschetz
end RamanujanPetersson


end


