-- Prove2me | Definitions.Def_RPLib_FX_GOSC_14
-- name    : RPLib_FX_GOSC_14
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T03:02:12.340784+00:00
-- url     : https://prove2.me/theorems/5eda6112-9c3d-542a-bd03-c5bc106b0846
-- title:
--   Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 14 of 14
-- statement:
--   File 14 of 14 of the Grothendieck–Ogg–Shafarevich library for the affine line over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_GOS_C_GOSF2`: S4-GOS-C, part GOSF2: Grothendieck-Ogg-Shafarevich on `𝔸¹`
--
--   **Formalization note.** One file of a library formalizing the Grothendieck–Ogg–Shafarevich formula on the affine line over a finite field: for a lisse sheaf $M$ of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1_{\mathbb F_q}$ trivialized on a finite étale Galois cover ($\ell \nmid q$), $\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) - \dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) = \dim M - \mathrm{Sw}_\infty(M)$, with the cohomology written in continuous cochains of the geometric fundamental group and the Swan conductor in the lower numbering at a place over infinity. It extends the published flat library (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13; M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib
import Definitions.Def_RPLib_FX_GOSC_13

/-!
# Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 14 of 14

Declarations of the formalization of the Grothendieck–Ogg–Shafarevich formula for lisse sheaves on the affine
line over a finite field (h²_c - h¹_c = rank - Swan conductor at infinity), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_GOS_C_GOSF2`: S4-GOS-C, part GOSF2: Grothendieck-Ogg-Shafarevich on `𝔸¹`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_GOS_C_GOSF2 =====
section

/-!
# S4-GOS-C, part GOSF2: Grothendieck-Ogg-Shafarevich on `𝔸¹`

`K = 𝔽_q(x)`, `M_f/K` the trivialising cover with group `G ≅ Gf`, `τ` a representation of `Gf` on a finite
`ℤ/l`-module `M` (`l ∤ q`). From `gos_int`, `χ = h²_c - h¹_c` (`chi_eq_h2c_sub_h1c`), `|I_Q| Sw_Q = Σ_j ...`
(`card_mul_swanQ`), the places over `∞` being conjugate (one place of `K` over `∞`) and
`Σ_Q deg Q |I_Q| = |G|` (`χ_c(𝔸¹) = 1`, `chiC_rat`):
**`gos_A1`**: `h²_c(M) - h¹_c(M) = dim M - Sw_{Q₀}(M)` for any place `Q₀ | ∞` of `M_f`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial IsDedekindDomain
open scoped Pointwise

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue Lefschetz

section GOSF2

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {p e : ℕ} [Fact p.Prime] [CharP (RatFunc Fq) p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable [Fintype (BdryS (Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq) (Rinf Fq (RatFunc Fq)))]
  [DecidableEq (BdryS (Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq) (Rinf Fq (RatFunc Fq)))]
  {Mf : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq))} [FiniteDimensional (RatFunc Fq) Mf]
  [IsGalois (RatFunc Fq) Mf] (hM : Mf ∈ unramSet (Rfin Fq (RatFunc Fq)) (RatFunc Fq))
  (hMU : Mf ≤ maxUnram (Rfin Fq (RatFunc Fq)) (RatFunc Fq))
  {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq) →* Gf)
  (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
  (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq)))) (hπs : Function.Surjective π)
  {φ : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq)}
  (hφ : IsFrobLift (Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq) φ)

open Classical in
include hq he hM hπ hπs hφ in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **Grothendieck-Ogg-Shafarevich on `𝔸¹`**: `h²_c - h¹_c = dim M - Sw_∞(M)`. -/
theorem gos_A1 (l : ℕ) [Fact l.Prime] [Fact (l ^ 1).Prime] (hlq : ¬ l ∣ Fintype.card Fq)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Module.Finite (ZMod (l ^ 1)) M]
    (τ : Representation (ZMod (l ^ 1)) Gf M) (Q0 : HeightOneSpectrum (Rinf Fq Mf)) :
    ((Module.finrank (ZMod (l ^ 1)) (H2c (τ.comp π) (pi1geo (Rfin Fq (RatFunc Fq)) (RatFunc Fq)
        (Fintype.card Fq))) : ℚ) -
      Module.finrank (ZMod (l ^ 1)) (H1c (τ.comp π) (pi1geo (Rfin Fq (RatFunc Fq)) (RatFunc Fq)
        (Fintype.card Fq)) (bdryInf Fq (RatFunc Fq)).inertia)) =
      Module.finrank (ZMod (l ^ 1)) M -
        swanQ Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) (iotaG Fq hMU π hπM) τ Q0 := by
  letI := actRinf Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf)
  have hl : l.Prime := Fact.out
  have hlp : l ≠ p := by
    rintro rfl
    exact hlq (hq ▸ dvd_pow_self l he.ne')
  haveI : CharP Mf p := charP_of_injective_algebraMap (algebraMap (RatFunc Fq) Mf).injective p
  have hinj : Function.Injective (iotaG Fq hMU π hπM) := iotaG_injective Fq hMU π hπM
  have hbij : Function.Bijective (iotaG Fq hMU π hπM) := ⟨hinj, iotaG_surjective Fq hMU π hπM hπs⟩
  have hE := chi_eq_h2c_sub_h1c Fq (RatFunc Fq) hq he l hlq hM hMU π hπM hπ τ
  have hG := gos_int Fq hq he hM hMU π hπM hπ hπs hφ l hlq τ
  have hlQ : ∀ Q : HeightOneSpectrum (Rinf Fq Mf), ∀ j, (Nat.card ((lowerQ Fq (RatFunc Fq) Mf
      (Mf ≃ₐ[RatFunc Fq] Mf) Q (j + 1)).map (iotaG Fq hMU π hπM)) : ZMod (l ^ 1)) ≠ 0 := by
    intro Q j
    rw [Subgroup.card_map_of_injective hinj, Ne, ZMod.natCast_eq_zero_iff, pow_one]
    exact not_dvd_card_lowerQ Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) Q (by omega) hl hlp
  have hS : ((∑ Q : HeightOneSpectrum (Rinf Fq Mf), ∑ j ∈ Finset.range (Jbd Fq Mf (Mf ≃ₐ[RatFunc Fq] Mf)),
      (Places.deg Fq Q : ℤ) * ((WQ Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) Q j).card : ℤ) *
        ((Module.finrank (ZMod (l ^ 1)) M : ℤ) - (Module.finrank (ZMod (l ^ 1))
          (Coinvariants (τ.comp ((lowerQ Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) Q (j + 1)).map
            (iotaG Fq hMU π hπM)).subtype)) : ℤ)) : ℤ) : ℚ) =
      swanQ Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) (iotaG Fq hMU π hπM) τ Q0 *
        (Fintype.card (Mf ≃ₐ[RatFunc Fq] Mf) : ℚ) := by
    rw [← Nat.card_eq_fintype_card, ← sum_deg_card_inertia_rat Fq,
      ← sum_swanQ_of_conj Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) (iotaG Fq hMU π hπM) τ Q0
        (fun Q => conj_rat Fq Q0 Q)]
    push_cast
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [mul_assoc, card_mul_swanQ Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) (iotaG Fq hMU π hπM) τ Q
      (fun j => by rw [Fintype.card_eq_nat_card]; exact hlQ Q j),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  exact gos_alg hE hG (chiC_rat Fq) hS (Fintype.card_of_bijective hbij).symm
    (Fintype.card_pos_iff.mpr ⟨1⟩)

end GOSF2

end

end RamanujanPetersson.GOS


end


