-- Prove2me | Definitions.Def_RPLib_FX_LisseDual_07
-- name    : RPLib_FX_LisseDual_07
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T04:56:55.330471+00:00
-- url     : https://prove2.me/theorems/a3e15111-6d9f-460f-a80e-fdf4078fb25c
-- title:
--   Lisse Poincaré duality on an affine curve over a finite field, library file 07 of 7
-- statement:
--   File 07 of 7 of the lisse duality library for affine curves over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_CupDuality_LisseS3`: S4-CurveDuality, O9b capstone: lisse duality on `Ū` in the S3 chart
--
--   **Formalization note.** One file of a library formalizing Poincaré duality for $H^1$ with lisse (finite, twisted) coefficients on an affine curve over a finite field: for a finite $\Lambda$-module $M$ with a continuous action of the geometric fundamental group factoring through a finite unramified quotient, the cochain duality map $\alpha_M : H^1_c(M) \to H^1(M^\vee(1))^\vee$ is bijective. It extends the published flat library for constant coefficients (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); J. S. Milne, Arithmetic Duality Theorems, 2nd ed., BookSurge (2006), Chapter II, §3; P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »

import Mathlib
import Definitions.Def_RPLib_FX_LisseDual_06

/-!
# Poincaré duality with lisse coefficients on an affine curve over a finite field, library file 07 of 7

Declarations of the formalization of Poincaré duality for H¹ with lisse (finite, twisted) coefficients on an
affine curve over a finite field (the cochain duality map `alphaM` is bijective), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_CupDuality_LisseS3`: S4-CurveDuality, O9b capstone: lisse duality on `Ū` in the S3 chart
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CupDuality_LisseS3 =====
section

/-!
# S4-CurveDuality, O9b capstone: lisse duality on `Ū` in the S3 chart

For a finite quotient `π : π₁(U) → Gf` with open kernel and residue data `RD` of level `lⁿ`, the duality map
`alphaM` of every finite representation `τ ∘ π` is bijective (**`lisse_bijective_S3`**): `lisse_bijective` with the
`H²` vanishing of the S3 chart (`h2All_geo`, `h2All_geo_inf_inertia`, `h2All_closed`) and `V`'s parabolic
perfectness `parabolicPerfect_V_S3`. It carries `hPicU`, `hPic` and the finiteness of `V`'s `ℤ/l`-valued parabolic
homomorphisms (`[Finite (parMod ..)]`).
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
/-- **Lisse Poincaré duality on `Ū`** (S3 chart): for every finite `Λ`-representation `τ` of a finite quotient
`π` of `π₁(U)` with residue data of level `lⁿ`, the duality map `H¹_c(Ū, τ ∘ π) → H¹(Ū, (τ ∘ π)^∨(σ))^∨` is bijective. -/
theorem lisse_bijective_S3 (hk : Places.constField Fq F = ⊥) {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) [NeZero (l ^ n)]
    (hPicU : CdOne.PicDivU (Places.Rfin Fq F) F p l)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p (l ^ n))
    {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    {Gf : Type} [Group Gf] [Fintype Gf] [DecidableEq Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf)
    (hπ : IsOpen (π.ker : Set (Pi1 (Places.Rfin Fq F) F)))
    {T : Type} [Fintype T] [DecidableEq T] [Nonempty T]
    [Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)).map π)]
    [∀ s, Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s).map π)]
    (RD : ResDat π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia (l ^ n) T)
    [Finite ↥(parMod (geoU (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) π.ker) (rdJ RD π.ker) l)]
    {Λ : Type} [CommRing Λ] [Finite Λ] [Module.Injective Λ Λ] (hsep : SepDual Λ) (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    (σ : Representation Λ (Pi1 (Places.Rfin Fq F) F) Λ) (hσ : IsOpen (σ.ker : Set (Pi1 (Places.Rfin Fq F) F)))
    {t : (s : S) → ↥(pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s)}
    (DD : ConstData σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia t)
    (hv : H2Van σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) ⊤)
    {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] (τ : Representation Λ Gf M) :
    Function.Bijective (alphaM hv (h2kEquiv DD hσ).toLinearMap (τ.comp π) (isOpen_comp π hπ τ)) := by
  have hL : ∀ a : Λ, (l ^ n) • a = 0 := fun a => by
    rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]
  have hall := CdOne.h2All_geo (Places.Rfin Fq F) Fq he hq (Kummer.perfect_Rfin Fq F) l
    (CP4a.isUnit_cast_Rfin hl) hPicU Λ n
  have hallI : ∀ s, H2All Λ (Pi1 (Places.Rfin Fq F) F)
      (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s) l n := fun s =>
    CdOne.h2All_geo_inf_inertia (Places.Rfin Fq F) Fq he hq (Kummer.perfect_Rfin Fq F) l
      (CP4a.isUnit_cast_Rfin hl) hPicU (D.P s) Λ n
  have hcl : IsClosed ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ π.ker : Subgroup _) :
      Set (Pi1 (Places.Rfin Fq F) F)) := by
    rw [Subgroup.coe_inf]
    exact (pi1geo_isClosed _ _ _).inter (π.ker.isClosed_of_isOpen hπ)
  have hallK := CdOne.h2All_closed (Places.Rfin Fq F) Fq he hq (Kummer.perfect_Rfin Fq F) l
    (CP4a.isUnit_cast_Rfin hl) hPicU _ hcl inf_le_left Λ n
  exact lisse_bijective σ π hsep hall hallI hallK hL hπ hσ hv DD RD hΛ
    (parabolicPerfect_V_S3 hq he hk hl hn hPicU hPic D hDB hπ RD hΛ σ hσ DD.triv
      (h2Van_top_of_all hallK hL hσ)) τ

end S3

end

end CupDuality
end RamanujanPetersson


end


