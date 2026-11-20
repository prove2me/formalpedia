-- Prove2me | Definitions.Def_RPLib_F2_048
-- name    : RPLib_F2_048
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T14:33:41.27007+00:00
-- url     : https://prove2.me/theorems/b6c13891-5ae1-4609-b786-6fb0e1f8b22e
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 048 of 70
-- statement:
--   File 048 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Kummer_Frob`: S4-Kummer K5e: Frobenius equivariance of `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`
--   * `S4.Def_RP_Lefschetz_ShapData`: S4-Lefschetz L4g part 3: Shapiro boundary data for a finite subcover
--   * `S4.Def_RP_Lefschetz_CurveTr1`: S4-Lefschetz, L4i part 2a: `π₁(E)` and `π₁^geo(E)` inside `π₁(U)` as topological groups
--   * `S4.Def_RP_Lefschetz_PDiv5`: S4-Lefschetz, L6e (5): places over `∞` of `M` and of its constant levels
--   * `S4.Def_RP_Lefschetz_PDiv6`: S4-Lefschetz, L6e (6): the divisibility hypothesis `PicDivX` holds
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_046

/-!
# Ramanujan-Petersson curve library (flat edition), file 048 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Kummer_Frob`: S4-Kummer K5e: Frobenius equivariance of `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`
* `S4.Def_RP_Lefschetz_ShapData`: S4-Lefschetz L4g part 3: Shapiro boundary data for a finite subcover
* `S4.Def_RP_Lefschetz_CurveTr1`: S4-Lefschetz, L4i part 2a: `π₁(E)` and `π₁^geo(E)` inside `π₁(U)` as topological groups
* `S4.Def_RP_Lefschetz_PDiv5`: S4-Lefschetz, L6e (5): places over `∞` of `M` and of its constant levels
* `S4.Def_RP_Lefschetz_PDiv6`: S4-Lefschetz, L6e (6): the divisibility hypothesis `PicDivX` holds
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Kummer_Frob =====
section

/-!
# S4-Kummer K5e: Frobenius equivariance of `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`

* `geomFrobH1_mem_curveH1par`: the geometric Frobenius preserves `H¹_par`.
* `piBar_toBar`, `divN_frobF`, `psiAt_frobF`: the arithmetic Frobenius `π` on `Pic(X̄)` and `[div(a)/N]`.
* `frobLift_Fc`: an arithmetic Frobenius lift `φ ∈ π₁(U)` restricts to `frobF` on every constant level `F_m`.
* `Psi_frob`: `Ψ(φ α) = π Ψ(α)`.
* `exists_kummerPicEquiv_frob` (**K5e**): `Φ : H¹_par ≃+ Pic⁰(X̄)[N]` with `Φ[kchar α] = Ψ α` and
  `π (Φ (F x)) = q • Φ x` for the geometric Frobenius `F` (the `μ_N⁻¹` twist, review R4).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh IsDedekindDomain Polynomial PicDescent Places

noncomputable section

section Generic

end Generic

section ParFrob

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {q : ℕ} {R0 : Type} [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)] {S : Type}
  {Λ : Type} [CommRing Λ] {M : Type} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ (Pi1 A K) M)
  (D : BdryData A K q R0 S)

end ParFrob

section DivFrob

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
variable (h : RR.IsConstExt Fq F L F' c)

end DivFrob

section FrobPic

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)

end FrobPic

section Curve

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

section PsiFrob

variable {N : ℕ} [NeZero N]

include hq he in
/-- **`Ψ(φ α) = π Ψ(α)`** for an arithmetic Frobenius lift `φ`. -/
theorem Psi_frob {φ : Pi1 (Rfin Fq F) F} (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ)
    {α : (maxUnram (Rfin Fq F) F)ˣ} (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N) :
    Psi hk N (Units.map (φ : maxUnram (Rfin Fq F) F →* maxUnram (Rfin Fq F) F) α) =
      piBar (AlgebraicClosure F) hk (Psi hk N α) := by
  obtain ⟨m, hm, h1⟩ := exists_Fc_of_rad hq he hα
  have : NeZero m := ⟨hm.ne'⟩
  have hfa := frobLift_Fc hk hq he hφ m ⟨_, h1⟩
  rw [Psi_eq hk α ⟨_, h1⟩ rfl, ← psiAt_frobF hk N m]
  refine Psi_eq hk _ _ ?_
  have hx : (⟨((⟨_, h1⟩ : Fc Fq F (AlgebraicClosure F) m) : AlgebraicClosure F), Fc_le_maxUnram hq he m h1⟩ :
      maxUnram (Rfin Fq F) F) = (α : maxUnram (Rfin Fq F) F) ^ N :=
    Subtype.ext (SubmonoidClass.coe_pow _ _).symm
  rw [← hfa, hx, map_pow, SubmonoidClass.coe_pow]
  rfl

variable (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)

include hk hq he in
theorem Psi_rad_map_inv {φ : Pi1 (Rfin Fq F) F} (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ) {α : (maxUnram (Rfin Fq F) F)ˣ}
    (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N) :
    Psi hk N α = piBar (AlgebraicClosure F) hk
      (Psi hk N (Units.map ((φ⁻¹ : Pi1 (Rfin Fq F) F) : maxUnram (Rfin Fq F) F →* maxUnram (Rfin Fq F) F) α)) := by
  have hPsi := Psi_frob hk hq he hφ (rad_map φ⁻¹ hα)
  rw [units_map_aut_inv] at hPsi
  exact hPsi

include hk hq he hNF in
set_option maxHeartbeats 1000000 in
/-- The Frobenius identity for any `Φ` with `Φ [kchar α] = Ψ α`. -/
theorem frob_of_kummerPicEquiv (Φ : curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D ≃+ PicBar0N (AlgebraicClosure F) hk N)
    (hΦ : ∀ (α : (maxUnram (Rfin Fq F) F)ˣ) (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
        (hpar : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D),
        (Φ ⟨kclass hζ hζΓ hα, hpar⟩ : PicBar (AlgebraicClosure F) hk) = Psi hk N α)
    {φ : Pi1 (Rfin Fq F) F} (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ)
    {x : curveH1 (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N)} (hx : x ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) :
    piBar (AlgebraicClosure F) hk
        (Φ ⟨geomFrobH1 (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ x,
          geomFrobH1_mem_curveH1par _ D φ hx⟩ : PicBar (AlgebraicClosure F) hk) =
      Fintype.card Fq • (Φ ⟨x, hx⟩ : PicBar (AlgebraicClosure F) hk) := by
  have hφζ := frobLift_zeta_card hq hNF hζ hφ
  have hcop : Nat.Coprime (Fintype.card Fq) N := by rw [hq]; exact coprime_q F p N hNF
  obtain ⟨q', hq'⟩ := exists_inv_of_coprime hcop
  obtain ⟨α, hα, rfl⟩ := kclass_surjective hζ hζΓ x
  have hsub := geomFrob_kclass_par hζ hζΓ D hφζ hq' hα hx
  have hPsi := Psi_rad_map_inv hk hq he hφ hα
  have hβ := hΦ _ (rad_map φ⁻¹ hα) (kclass_rad_map_mem_par hζ hζΓ D hφζ hq' hα hx)
  rw [hsub, map_nsmul]
  rw [AddSubmonoidClass.coe_nsmul, map_nsmul]
  rw [hβ, ← hPsi, hΦ α hα hx]

include hk hq he hNf hNi hDB hlift hNF in
/-- **K5e**: `Φ : H¹_par(π₁^geo, Z/N) ≃+ Pic⁰(X̄)[N]` (`[kchar α] ↦ [div(α ^ N) / N]`) intertwines the geometric
Frobenius with `q⁻¹ • π`: `π (Φ (F x)) = q • Φ x` (`H¹(X̄, Z/N) ≅ Pic⁰(X̄)[N] ⊗ μ_N⁻¹` equivariantly, review R4). -/
theorem exists_kummerPicEquiv_frob :
    ∃ Φ : curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D ≃+ PicBar0N (AlgebraicClosure F) hk N,
      (∀ (α : (maxUnram (Rfin Fq F) F)ˣ) (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
        (hpar : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D),
        (Φ ⟨kclass hζ hζΓ hα, hpar⟩ : PicBar (AlgebraicClosure F) hk) = Psi hk N α) ∧
      ∀ φ : Pi1 (Rfin Fq F) F, IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ →
        ∀ (x : curveH1 (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N)) (hx : x ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D),
          piBar (AlgebraicClosure F) hk
              (Φ ⟨geomFrobH1 (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ x,
                geomFrobH1_mem_curveH1par _ D φ hx⟩ : PicBar (AlgebraicClosure F) hk) =
            Fintype.card Fq • (Φ ⟨x, hx⟩ : PicBar (AlgebraicClosure F) hk) := by
  have key := exists_kummerPicEquiv hk hq he hNf hNi hζ hζΓ D hDB hlift hNF
  obtain ⟨Φ, hΦ⟩ := key
  exact ⟨Φ, hΦ, fun φ hφ x hx => frob_of_kummerPicEquiv hk hq he hζ hζΓ D hNF Φ hΦ hφ hx⟩

end PsiFrob

end Curve

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ShapData =====
section

/-!
# S4-Lefschetz L4g part 3: Shapiro boundary data for a finite subcover

Generic part (`ShapGen`): two pro-charts with boundary data `D` (of `V`) and `D'` (of `U`), an isomorphism
`f : proChart(V) ≃+* proChart(U)` equivariant along an injective `r : π₁(U) →* π₁(V)` with `r⁻¹(Γ) = Γ_U`, and
"stabiliser in `Γ` ⇒ inertia" on `V`. Then `gπ`, `gxT` (from `D.cover`), `gJ` satisfy the three Shapiro
hypotheses `InertiaLift`, `DCover`, `DDisj` of `CurveCoh_ShapiroCone` for `H = range r`.

Concrete part (`ShapE`): `V = K`, `U = E ⊆ K_U` over `k' = Kc 𝔽_q E`, `f = chartE.symm`, `r = thetaE`:
`thetaE_mem_pi1geo_iff`, `thetaE_injective`, `stab_mem_inertia_K`, the objects `bdPiE`, `bdxE`, `bdJE` and
`shap_inertiaLift`, `shap_dCover`, `shap_dDisj`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

open Places GalCover CurveCoh CP4a

noncomputable section

section ShapGen

variable {A K R0 : Type} [CommRing A] [Field K] [Algebra A K] [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
variable {A' K' R0' : Type} [CommRing A'] [Field K'] [Algebra A' K'] [CommRing R0'] [Algebra R0' K']
  [Algebra R0' (maxUnram A' K')] [IsScalarTower R0' K' (maxUnram A' K')]

variable {q q' : ℕ} {S T : Type} (D : BdryData A K q R0 S) (D' : BdryData A' K' q' R0' T)
  (f : proChart A K R0 ≃+* proChart A' K' R0')
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime A K R0 Q) (hD'B : ∀ Q, D'.B Q ↔ IsBdryPrime A' K' R0' Q)

variable (r : Pi1 A' K' →* Pi1 A K) (hf : ∀ σ x, f (r σ • x) = σ • f x) (hr : Function.Injective r)
  (hgeo : ∀ σ, r σ ∈ pi1geo A K q ↔ σ ∈ pi1geo A' K' q')
  (hstab : ∀ Q, IsBdryPrime A K R0 Q → ∀ σ ∈ pi1geo A K q, σ • Q = Q → σ ∈ Q.inertia (Pi1 A K))

end ShapGen

section ShapE

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

set_option synthInstance.maxHeartbeats 400000 in
/-- **InertiaLift** for `E ⊆ K_U`. -/
theorem shap_inertiaLift :
    InertiaLift (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (thetaE Fq K E hE).range (bdryInf Fq K).inertia
      (bdJE Fq K E hE) (bdPiE Fq K E hE) (bdxE Fq K E hE) :=
  gen_inertiaLift (bdryInf Fq K) (bdryInf (Kc Fq E) E) (chartE Fq K E hE).symm (fun _ => Iff.rfl)
    (fun _ => Iff.rfl) (thetaE Fq K E hE) (fun σ x => chartE_symm_smul Fq K E hE σ x)
    (thetaE_injective Fq K E hE)

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
/-- **DCover** for `E ⊆ K_U`. -/
theorem shap_dCover :
    DCover (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (thetaE Fq K E hE).range (bdryInf Fq K).inertia
      (bdPiE Fq K E hE) (bdxE Fq K E hE) :=
  gen_dCover (bdryInf Fq K) (bdryInf (Kc Fq E) E) (chartE Fq K E hE).symm (fun _ => Iff.rfl)
    (fun _ => Iff.rfl) (thetaE Fq K E hE) (fun σ x => chartE_symm_smul Fq K E hE σ x)
    (thetaE_mem_pi1geo_iff Fq K E hE) (stab_mem_inertia_K Fq K hq he)

set_option synthInstance.maxHeartbeats 400000 in
/-- **DDisj** for `E ⊆ K_U`. -/
theorem shap_dDisj :
    DDisj (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (thetaE Fq K E hE).range (bdryInf Fq K).inertia
      (bdPiE Fq K E hE) (bdxE Fq K E hE) :=
  gen_dDisj (bdryInf Fq K) (bdryInf (Kc Fq E) E) (chartE Fq K E hE).symm (fun _ => Iff.rfl)
    (fun _ => Iff.rfl) (thetaE Fq K E hE) (fun σ x => chartE_symm_smul Fq K E hE σ x)
    (thetaE_injective Fq K E hE) (thetaE_mem_pi1geo_iff Fq K E hE)

end ShapE

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_CurveTr1 =====
section

/-!
# S4-Lefschetz, L4i part 2a: `π₁(E)` and `π₁^geo(E)` inside `π₁(U)` as topological groups

For a finite `E ⊆ K_U` (constant field `k' = Kc Fq E`), with `H = range thetaE ≤ π₁(U)`:

* `isOpen_range_theta`, `isOpen_range_thetaE`: `H` is open;
* `thE : π₁(E) ≃ₜ* H` (compact to Hausdorff), `eE : π₁^geo(E) ≃ₜ* Γ ∩ H` (its restriction);
* `intwE`, `intwIE`: `eE` intertwines the trivial coefficients and the boundary inertia (`bdJE`);
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a CupDuality Representation

section RangeOpen

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
  (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ maxUnram A K)

end RangeOpen

section CurveTr

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

set_option synthInstance.maxHeartbeats 400000 in
theorem intwIE : IntwI (bdryInf (Kc Fq E) E).inertia (bdJE Fq K E hE) (eE Fq K E hE) := by
  intro t g
  constructor
  · intro hg
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨(g : Pi1 (Rfin (Kc Fq E) E) E), hg, rfl⟩)
  · intro hg
    obtain ⟨σ, hσ, hσe⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)
    have hσe' : thetaE Fq K E hE σ = thetaE Fq K E hE (g : Pi1 (Rfin (Kc Fq E) E) E) := hσe
    have h2 : σ = (g : Pi1 (Rfin (Kc Fq E) E) E) := thetaE_injective Fq K E hE hσe'
    rw [← h2]
    exact hσ

end CurveTr

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PDiv5 =====
section

/-!
# S4-Lefschetz, L6e (5): places over `∞` of `M` and of its constant levels

The `Rinf` side of `PDiv4` (generic-instance `IC`): `eBaseInfG : IC (Rinf Fq K) M ≃+* Rinf k' M`,
`eLevInfG : Rinf (L_n) (F_n(M)) ≃+* IC (Rinf Fq K) (M ⊔ constLevel)`, `underI_eq_contInf`; and the two transport
steps of `picDivX`: `dvd_fin_of` (finite places) and `dvd_inf_of` (places over `∞`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open PicDescent Places Kummer CdOne

section PicX

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (M : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K M] [Algebra.IsSeparable K M]

theorem mem_baseInf_Ω (x : M) :
    x ∈ integralClosure (Oinf (Kc Fq M)) M ↔ IsIntegral (Rinf Fq K) ((RingEquiv.refl M x : M) : AlgebraicClosure K) := by
  show IsIntegral (Oinf (Kc Fq M)) x ↔ _
  refine (isIntegral_Oinf_iff Fq M x).trans (Iff.trans ?_ (isIntegral_tower_Ω (Rinf Fq K) (Oinf Fq) _).symm)
  haveI : IsScalarTower (Oinf Fq) M (AlgebraicClosure K) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (isIntegral_algebraMap_iff (R := Oinf Fq) (B := AlgebraicClosure K) Subtype.val_injective).symm

/-- `B∞_M ≃ Rinf(k', M)` with the generic instance on `B∞_M`. -/
def eBaseInfG : IC (Rinf Fq K) M ≃+* Rinf (Kc Fq M) M :=
  (eIC (Rinf Fq K) M (integralClosure (Oinf (Kc Fq M)) M) (RingEquiv.refl M) (mem_baseInf_Ω Fq K M)).symm

theorem coe_eBaseInfG (x : IC (Rinf Fq K) M) : ((eBaseInfG Fq K M x : Rinf (Kc Fq M) M) : M) = (x : M) :=
  coe_eIC_symm (Rinf Fq K) M _ (RingEquiv.refl M) (mem_baseInf_Ω Fq K M) x

variable {p : ℕ} [Fact p.Prime] [CharP K p]

theorem mem_levInf_Ω {e' : ℕ} (hqM : Fintype.card (Kc Fq M) = p ^ e') (n : ℕ) [NeZero n] (hn : 0 < e' * n)
    (x : Fc (Kc Fq M) M (AlgebraicClosure K) n) :
    x ∈ integralClosure (Oinf (Lc (Kc Fq M) (AlgebraicClosure K) n)) (Fc (Kc Fq M) M (AlgebraicClosure K) n) ↔
      IsIntegral (Rinf Fq K) ((levEquiv Fq K M hqM n hn x : ↥(M ⊔ constLevel K p (e' * n))) : AlgebraicClosure K) := by
  show IsIntegral _ x ↔ _
  refine (isIntegral_iff_mem_Rinf (isConstExt_Fc (Kc Fq M) M (AlgebraicClosure K) (constField_eq_bot Fq M) n)
    x).symm.trans (Iff.trans ?_ (isIntegral_tower_Ω (Rinf Fq K) (Oinf Fq) _).symm)
  haveI : IsScalarTower (Rinf (Kc Fq M) M) (Fc (Kc Fq M) M (AlgebraicClosure K) n) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [← isIntegral_algebraMap_iff (R := Rinf (Kc Fq M) M) (B := AlgebraicClosure K) Subtype.val_injective,
    IntermediateField.algebraMap_apply, coe_levEquiv]
  exact isIntegral_rinfKc_Ω_iff Fq K M _

/-- `Rinf(L_n, F_n(M)) ≃ B∞_{M ⊔ constLevel}` with the generic instance. -/
def eLevInfG {e' : ℕ} (hqM : Fintype.card (Kc Fq M) = p ^ e') (n : ℕ) [NeZero n] (hn : 0 < e' * n) :
    Rinf (Lc (Kc Fq M) (AlgebraicClosure K) n) (Fc (Kc Fq M) M (AlgebraicClosure K) n) ≃+*
      IC (Rinf Fq K) (M ⊔ constLevel K p (e' * n)) :=
  eIC (Rinf Fq K) _ _ (levEquiv Fq K M hqM n hn) (mem_levInf_Ω Fq K M hqM n hn)

theorem coe_eLevInfG {e' : ℕ} (hqM : Fintype.card (Kc Fq M) = p ^ e') (n : ℕ) [NeZero n] (hn : 0 < e' * n)
    (r : Rinf (Lc (Kc Fq M) (AlgebraicClosure K) n) (Fc (Kc Fq M) M (AlgebraicClosure K) n)) :
    (((eLevInfG Fq K M hqM n hn r : IC (Rinf Fq K) (M ⊔ constLevel K p (e' * n))) :
      ↥(M ⊔ constLevel K p (e' * n))) : AlgebraicClosure K) =
      ((r : Fc (Kc Fq M) M (AlgebraicClosure K) n) : AlgebraicClosure K) :=
  (congrArg Subtype.val (coe_eIC (Rinf Fq K) _ _ (levEquiv Fq K M hqM n hn) (mem_levInf_Ω Fq K M hqM n hn) r)).trans
    (coe_levEquiv Fq K M hqM n hn _)

theorem algebraMap_eLevInfG {e' : ℕ} (hqM : Fintype.card (Kc Fq M) = p ^ e') (n : ℕ) [NeZero n] (hn : 0 < e' * n)
    (r : Rinf (Lc (Kc Fq M) (AlgebraicClosure K) n) (Fc (Kc Fq M) M (AlgebraicClosure K) n)) :
    algebraMap (IC (Rinf Fq K) (M ⊔ constLevel K p (e' * n))) ↥(M ⊔ constLevel K p (e' * n))
      (eLevInfG Fq K M hqM n hn r) = levEquiv Fq K M hqM n hn
        (algebraMap (Rinf (Lc (Kc Fq M) (AlgebraicClosure K) n) (Fc (Kc Fq M) M (AlgebraicClosure K) n))
          (Fc (Kc Fq M) M (AlgebraicClosure K) n) r) :=
  coe_eIC (Rinf Fq K) _ _ (levEquiv Fq K M hqM n hn) (mem_levInf_Ω Fq K M hqM n hn) r

set_option maxHeartbeats 800000 in
/-- **The base place at infinity under a level place**: `underI` matches the contraction `F_n(M) / M`. -/
theorem underI_eq_contInf {e' : ℕ} (hqM : Fintype.card (Kc Fq M) = p ^ e') (n : ℕ) [NeZero n]
    (hn : 0 < e' * n) [IsDedekindDomain (IC (Rinf Fq K) M)]
    [IsDedekindDomain (IC (Rinf Fq K) (M ⊔ constLevel K p (e' * n)))]
    (w : HeightOneSpectrum (IC (Rinf Fq K) (M ⊔ constLevel K p (e' * n)))) :
    underI (Rinf Fq K) (le_sup_left : M ≤ M ⊔ constLevel K p (e' * n)) w =
      HeightOneSpectrum.comap (eBaseInfG Fq K M : IC (Rinf Fq K) M →+* Rinf (Kc Fq M) M) (eBaseInfG Fq K M).surjective
        (contInf (isConstExt_Fc (Kc Fq M) M (AlgebraicClosure K) (constField_eq_bot Fq M) n)
          (HeightOneSpectrum.comap (eLevInfG Fq K M hqM n hn : Rinf (Lc (Kc Fq M) (AlgebraicClosure K) n)
            (Fc (Kc Fq M) M (AlgebraicClosure K) n) →+* IC (Rinf Fq K) (M ⊔ constLevel K p (e' * n)))
            (eLevInfG Fq K M hqM n hn).surjective w)) := by
  letI := algInf (isConstExt_Fc (Kc Fq M) M (AlgebraicClosure K) (constField_eq_bot Fq M) n)
  apply HeightOneSpectrum.ext
  ext x
  have hx : RamanujanPetersson.incl (Rinf Fq K) K (le_sup_left : M ≤ M ⊔ constLevel K p (e' * n)) x =
      eLevInfG Fq K M hqM n hn (algebraMap (Rinf (Kc Fq M) M) (Rinf (Lc (Kc Fq M) (AlgebraicClosure K) n)
        (Fc (Kc Fq M) M (AlgebraicClosure K) n)) (eBaseInfG Fq K M x)) := by
    apply Subtype.ext
    apply Subtype.ext
    rw [RamanujanPetersson.incl_val, coe_eLevInfG, JacFrob.coe_algInf, coe_eBaseInfG]
    rfl
  show RamanujanPetersson.incl (Rinf Fq K) K _ x ∈ w.asIdeal ↔ eLevInfG Fq K M hqM n hn (algebraMap
    (Rinf (Kc Fq M) M) (Rinf (Lc (Kc Fq M) (AlgebraicClosure K) n) (Fc (Kc Fq M) M (AlgebraicClosure K) n))
    (eBaseInfG Fq K M x)) ∈ w.asIdeal
  rw [hx]

/-- Finite places: `N ∣ ord_v f` on `F_n(M)` gives `N ∣ v_y(f)` at the finite places of `M ⊔ constLevel`. -/
theorem dvd_fin_of {e' : ℕ} (hqM : Fintype.card (Kc Fq M) = p ^ e') (n : ℕ) [NeZero n] (hn : 0 < e' * n) (N : ℕ)
    (f : Fc (Kc Fq M) M (AlgebraicClosure K) n)
    (h : ∀ v : HeightOneSpectrum (Rfin (Lc (Kc Fq M) (AlgebraicClosure K) n) (Fc (Kc Fq M) M (AlgebraicClosure K) n)),
      (N : ℤ) ∣ Places.ord v f)
    [IsDedekindDomain (IC (Rfin Fq K) (M ⊔ constLevel K p (e' * n)))]
    [IsFractionRing (IC (Rfin Fq K) (M ⊔ constLevel K p (e' * n))) ↥(M ⊔ constLevel K p (e' * n))]
    (y : HeightOneSpectrum (IC (Rfin Fq K) (M ⊔ constLevel K p (e' * n)))) :
    (N : ℤ) ∣ WithZero.log (y.valuation ↥(M ⊔ constLevel K p (e' * n)) (levEquiv Fq K M hqM n hn f)) := by
  have h1 := h (HeightOneSpectrum.comap (eLevG Fq K M hqM n hn : Rfin (Lc (Kc Fq M) (AlgebraicClosure K) n)
    (Fc (Kc Fq M) M (AlgebraicClosure K) n) →+* IC (Rfin Fq K) (M ⊔ constLevel K p (e' * n)))
    (eLevG Fq K M hqM n hn).surjective y)
  rw [Places.ord, valuation_comap_equiv (eLevG Fq K M hqM n hn) (levEquiv Fq K M hqM n hn)
    (algebraMap_eLevG Fq K M hqM n hn) y f, dvd_neg] at h1
  exact h1

set_option maxHeartbeats 1600000 in
/-- Places over `∞`: `N ∣ D(v ∩ M) - ord_v f` on `F_n(M)` gives the boundary congruence of `PicDivX`. -/
theorem dvd_inf_of {e' : ℕ} (hqM : Fintype.card (Kc Fq M) = p ^ e') (n : ℕ) [NeZero n] (hn : 0 < e' * n) (N : ℕ)
    (f : Fc (Kc Fq M) M (AlgebraicClosure K) n) [IsDedekindDomain (IC (Rinf Fq K) M)]
    (D : HeightOneSpectrum (IC (Rinf Fq K) M) → ℤ)
    (h : ∀ v : HeightOneSpectrum (Rinf (Lc (Kc Fq M) (AlgebraicClosure K) n) (Fc (Kc Fq M) M (AlgebraicClosure K) n)),
      (N : ℤ) ∣ D (HeightOneSpectrum.comap (eBaseInfG Fq K M : IC (Rinf Fq K) M →+* Rinf (Kc Fq M) M)
        (eBaseInfG Fq K M).surjective (contInf (isConstExt_Fc (Kc Fq M) M (AlgebraicClosure K)
          (constField_eq_bot Fq M) n) v)) - Places.ord v f)
    [IsDedekindDomain (IC (Rinf Fq K) (M ⊔ constLevel K p (e' * n)))]
    [IsFractionRing (IC (Rinf Fq K) (M ⊔ constLevel K p (e' * n))) ↥(M ⊔ constLevel K p (e' * n))]
    (w : HeightOneSpectrum (IC (Rinf Fq K) (M ⊔ constLevel K p (e' * n)))) :
    (N : ℤ) ∣ D (underI (Rinf Fq K) (le_sup_left : M ≤ M ⊔ constLevel K p (e' * n)) w) +
      WithZero.log (w.valuation ↥(M ⊔ constLevel K p (e' * n)) (levEquiv Fq K M hqM n hn f)) := by
  have h1 := h (HeightOneSpectrum.comap (eLevInfG Fq K M hqM n hn : Rinf (Lc (Kc Fq M) (AlgebraicClosure K) n)
    (Fc (Kc Fq M) M (AlgebraicClosure K) n) →+* IC (Rinf Fq K) (M ⊔ constLevel K p (e' * n)))
    (eLevInfG Fq K M hqM n hn).surjective w)
  rw [Places.ord, valuation_comap_equiv (eLevInfG Fq K M hqM n hn) (levEquiv Fq K M hqM n hn)
    (algebraMap_eLevInfG Fq K M hqM n hn) w f, sub_neg_eq_add] at h1
  rw [underI_eq_contInf Fq K M hqM n hn w]
  exact h1

end PicX

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PDiv6 =====
section

/-!
# S4-Lefschetz, L6e (6): the divisibility hypothesis `PicDivX` holds

`picDivX`: for `K` a function field over `𝔽_q` with full constant field and `l ∤ q`,
`Residue.PicDivX (Rfin Fq K) K (Rinf Fq K) p (l ^ m)` for every `m`: a degree-`0` divisor `D` on the places over `∞`
of a finite `M ⊆ K_U` (all of one residue size) becomes `l^m`-divisible up to `div a` at some constant level, with
`l^m ∣ v(a)` at every finite place. Proof (`exists_D0`): the places over `∞` of `M` all have the same degree `d`, so
`D` extended by `0` is a degree-`0` divisor on `M / k'`; apply `exists_base_div0` (`Pic⁰(X̄_M)` is `l^m`-divisible)
and transport with `dvd_fin_of`, `dvd_inf_of` (PDiv5).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open PicDescent Places Kummer CdOne

section PicX1

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (M : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K M] [Algebra.IsSeparable K M]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **Places over `∞` of `M`** of one residue size: a degree-`0` divisor on them, pulled back along `eBaseInfG` and
extended by `0` at the finite places, is a degree-`0` divisor of `M / k'`. -/
theorem exists_D0 [IsDedekindDomain (IC (Rinf Fq K) M)] {r : ℕ}
    (hr : ∀ w : HeightOneSpectrum (IC (Rinf Fq K) M), Nat.card (IC (Rinf Fq K) M ⧸ w.asIdeal) = r)
    (D : HeightOneSpectrum (IC (Rinf Fq K) M) → ℤ) (hD : (Function.support D).Finite) (hD0 : ∑ᶠ w, D w = 0) :
    ∃ D0 : HeightOneSpectrum (Rinf (Kc Fq M) M) →₀ ℤ, (∀ u, D0 u = D (HeightOneSpectrum.comap
      (eBaseInfG Fq K M : IC (Rinf Fq K) M →+* Rinf (Kc Fq M) M) (eBaseInfG Fq K M).surjective u)) ∧
      Divisor.deg (Finsupp.sumElim 0 D0 : Divisor (Kc Fq M) M) = 0 := by
  letI iA : Algebra (Kc Fq M) (Rinf (Kc Fq M) M) := inferInstance
  have hτ : Function.Injective (fun u : HeightOneSpectrum (Rinf (Kc Fq M) M) =>
      HeightOneSpectrum.comap (eBaseInfG Fq K M : IC (Rinf Fq K) M →+* Rinf (Kc Fq M) M)
        (eBaseInfG Fq K M).surjective u) := by
    intro u1 u2 h12
    apply HeightOneSpectrum.ext
    exact Ideal.comap_injective_of_surjective _ (eBaseInfG Fq K M).surjective (congrArg HeightOneSpectrum.asIdeal h12)
  have hτs : Function.Surjective (fun u : HeightOneSpectrum (Rinf (Kc Fq M) M) =>
      HeightOneSpectrum.comap (eBaseInfG Fq K M : IC (Rinf Fq K) M →+* Rinf (Kc Fq M) M)
        (eBaseInfG Fq K M).surjective u) := by
    intro w
    refine ⟨HeightOneSpectrum.comap ((eBaseInfG Fq K M).symm : Rinf (Kc Fq M) M →+* IC (Rinf Fq K) M)
      (eBaseInfG Fq K M).symm.surjective w, ?_⟩
    apply HeightOneSpectrum.ext
    ext x
    show (eBaseInfG Fq K M).symm (eBaseInfG Fq K M x) ∈ w.asIdeal ↔ x ∈ w.asIdeal
    rw [RingEquiv.symm_apply_apply]
  let D0 : HeightOneSpectrum (Rinf (Kc Fq M) M) →₀ ℤ := Finsupp.ofSupportFinite
    (fun u => D (HeightOneSpectrum.comap (eBaseInfG Fq K M : IC (Rinf Fq K) M →+* Rinf (Kc Fq M) M)
      (eBaseInfG Fq K M).surjective u)) (hD.preimage hτ.injOn)
  have hsum : ∑ᶠ u, D0 u = 0 := (finsum_comp_equiv (Equiv.ofBijective _ ⟨hτ, hτs⟩) (f := D)).trans hD0
  have hcard : ∀ u : HeightOneSpectrum (Rinf (Kc Fq M) M),
      Fintype.card (Kc Fq M) ^ Places.deg (Kc Fq M) u = r := by
    intro u
    rw [← Places.card_residue_eq (Kc Fq M) u, ← hr (HeightOneSpectrum.comap (eBaseInfG Fq K M :
      IC (Rinf Fq K) M →+* Rinf (Kc Fq M) M) (eBaseInfG Fq K M).surjective u)]
    exact Nat.card_congr (Ideal.quotientEquiv _ _ (eBaseInfG Fq K M)
      (Ideal.map_comap_of_surjective _ (eBaseInfG Fq K M).surjective _).symm).toEquiv.symm
  have hq2 : 1 < Fintype.card (Kc Fq M) := Fintype.one_lt_card
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ∀ u : HeightOneSpectrum (Rinf (Kc Fq M) M), Places.deg (Kc Fq M) u = d := by
    by_cases hne : Nonempty (HeightOneSpectrum (Rinf (Kc Fq M) M))
    · obtain ⟨u0⟩ := hne
      exact ⟨_, fun u => Nat.pow_right_injective hq2 ((hcard u).trans (hcard u0).symm)⟩
    · exact ⟨0, fun u => (hne ⟨u⟩).elim⟩
  have h1 : degS (Kc Fq M) D0 = (∑ᶠ u, D0 u) * d := by
    unfold degS Finsupp.sum
    rw [finsum_eq_sum_of_support_subset (s := D0.support) _ (by rw [Finsupp.fun_support_eq]), Finset.sum_mul]
    exact Finset.sum_congr rfl fun u _ => by simp only [hd u]
  refine ⟨D0, fun u => rfl, ?_⟩
  rw [Divisor.deg_sumElim, h1, hsum, zero_mul, add_zero]
  exact Finsupp.sum_zero_index

end PicX1

section PicX2

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

end PicX2

end

end Lefschetz
end RamanujanPetersson


end


