-- Prove2me | Definitions.Def_RPLib_FX_GOSC_12
-- name    : RPLib_FX_GOSC_12
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T02:37:50.422618+00:00
-- url     : https://prove2.me/theorems/6ab493c1-9fc0-4686-8622-9f04eff4a166
-- title:
--   Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 12 of 14
-- statement:
--   File 12 of 14 of the Grothendieck–Ogg–Shafarevich library for the affine line over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_GOS_C_GOSI`: S4-GOS-C, part GOSI: the integer Grothendieck-Ogg-Shafarevich identity on the concrete cover
--
--   **Formalization note.** One file of a library formalizing the Grothendieck–Ogg–Shafarevich formula on the affine line over a finite field: for a lisse sheaf $M$ of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1_{\mathbb F_q}$ trivialized on a finite étale Galois cover ($\ell \nmid q$), $\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) - \dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) = \dim M - \mathrm{Sw}_\infty(M)$, with the cohomology written in continuous cochains of the geometric fundamental group and the Swan conductor in the lower numbering at a place over infinity. It extends the published flat library (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13; M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib
import Definitions.Def_RPLib_FX_GOSC_11

/-!
# Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 12 of 14

Declarations of the formalization of the Grothendieck–Ogg–Shafarevich formula for lisse sheaves on the affine
line over a finite field (h²_c - h¹_c = rank - Swan conductor at infinity), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_GOS_C_GOSI`: S4-GOS-C, part GOSI: the integer Grothendieck-Ogg-Shafarevich identity on the concrete cover
-/

set_option autoImplicit false

-- ===== S4.Def_RP_GOS_C_GOSI =====
section

/-!
# S4-GOS-C, part GOSI: the integer Grothendieck-Ogg-Shafarevich identity on the concrete cover

`K = RatFunc 𝔽_q`, `G = Gal(M_f/K) ≅ Gf` (via `iotaG`), `τ` a representation of `Gf` on a finite `ℤ/l`-module `M`
(`l ∤ q`). With `χ(τ) = Σ_i (-1)^i dim (PC i ⊗ M)_{Gf}`, `W_Q(j) = G_{Q,j+1}` and `d_{Q,j} = dim M_{ι W_Q(j)}`:
**`gos_int`**: `|Gf| χ(τ) = |G| χ_c(K) dim M - Σ_{Q | ∞} Σ_{j < J} deg Q |W_Q(j)| (dim M - d_{Q,j})` in `ℤ`,
from Brauer's formula at every level `ℤ/l^n` (`brauer_lev`), `chiPC_eq_Phi`, `Φ = Σ_Q Σ_j [· ∈ W_Q(j)] deg Q`,
`Σ Φ = |G| χ_c(K)` and the wild groups being `p`-groups.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue Lefschetz

section Transfer

variable {G Gf : Type*} [Group G] [Group Gf] [Fintype G] {Λ : Type*} [AddCommMonoid Λ]

end Transfer

section GOSI

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
/-- **The integer GOS identity** on the concrete cover. -/
theorem gos_int (l : ℕ) [Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Module.Finite (ZMod (l ^ 1)) M]
    (τ : Representation (ZMod (l ^ 1)) Gf M) :
    (Fintype.card Gf : ℤ) * ∑ i ∈ Finset.range 3, (-1 : ℤ) ^ i *
        (Module.finrank (ZMod (l ^ 1)) (Coinvariants ((ρPC (ZMod (l ^ 1)) π (pi1geo (Rfin Fq (RatFunc Fq))
          (RatFunc Fq) (Fintype.card Fq)) (bdryInf Fq (RatFunc Fq)).inertia i).tprod τ)) : ℤ) =
      (Fintype.card (Mf ≃ₐ[RatFunc Fq] Mf) : ℤ) * chiC Fq (RatFunc Fq) * (Module.finrank (ZMod (l ^ 1)) M : ℤ) -
        ∑ Q : HeightOneSpectrum (Rinf Fq Mf), ∑ j ∈ Finset.range (Jbd Fq Mf (Mf ≃ₐ[RatFunc Fq] Mf)),
          (Places.deg Fq Q : ℤ) * ((WQ Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) Q j).card : ℤ) *
            ((Module.finrank (ZMod (l ^ 1)) M : ℤ) - (Module.finrank (ZMod (l ^ 1))
              (Coinvariants (τ.comp ((lowerQ Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) Q (j + 1)).map
                (iotaG Fq hMU π hπM)).subtype)) : ℤ)) := by
  have hl : l.Prime := Fact.out
  apply int_eq_of_forall_zmod hl.two_le
  intro n hn
  obtain ⟨β, hβH, hβχ⟩ := brauer_lev Fq (RatFunc Fq) hq he l n hn hlq hM hMU π hπM hπ τ
  have hinj : Function.Injective (iotaG Fq hMU π hπM) := iotaG_injective Fq hMU π hπM
  have hbij : Function.Bijective (iotaG Fq hMU π hπM) := ⟨hinj, iotaG_surjective Fq hMU π hπM hπs⟩
  have hlp : l ≠ p := by
    rintro rfl
    exact hlq (hq ▸ dvd_pow_self l he.ne')
  haveI : CharP Mf p := charP_of_injective_algebraMap (algebraMap (RatFunc Fq) Mf).injective p
  have h1 : ∑ g : Gf, chiPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq))
      (bdryInf Fq (RatFunc Fq)).inertia g * β g = ∑ σ : Mf ≃ₐ[RatFunc Fq] Mf,
        (Phi Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) σ : ZMod (l ^ n)) * β (iotaG Fq hMU π hπM σ) := by
    rw [← hbij.sum_comp]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [chiPC_eq_Phi Fq hq he hM hMU π hπM hπ hπs hφ l n hn hlq σ]
  have hβ1 : β (iotaG Fq hMU π hπM 1) = (((Module.finrank (ZMod (l ^ 1)) M : ℤ)) : ZMod (l ^ n)) := by
    have hb := hβH ⊥ (by rw [Fintype.card_eq_nat_card, Subgroup.card_bot]; exact hl.not_dvd_one)
    rw [Finset.sum_eq_single (1 : (⊥ : Subgroup Gf)) (fun b _ hb1 => absurd (Subtype.ext
      (Subgroup.mem_bot.mp b.2)) hb1) (fun h => absurd (Finset.mem_univ _) h), Fintype.card_eq_nat_card,
      Subgroup.card_bot, Nat.cast_one, one_mul, finrank_coinvariants_bot] at hb
    rw [map_one, Int.cast_natCast]
    exact hb
  have hβW : ∀ Q : HeightOneSpectrum (Rinf Fq Mf), ∀ j ∈ Finset.range (Jbd Fq Mf (Mf ≃ₐ[RatFunc Fq] Mf)),
      ∑ g ∈ WQ Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) Q j, β (iotaG Fq hMU π hπM g) =
        ((WQ Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) Q j).card : ZMod (l ^ n)) *
          (((Module.finrank (ZMod (l ^ 1)) (Coinvariants (τ.comp ((lowerQ Fq (RatFunc Fq) Mf
            (Mf ≃ₐ[RatFunc Fq] Mf) Q (j + 1)).map (iotaG Fq hMU π hπM)).subtype)) : ℤ)) : ZMod (l ^ n)) := by
    intro Q j _
    have hs := mem_WQ_iff Fq Q j (G := Mf ≃ₐ[RatFunc Fq] Mf) (K := RatFunc Fq)
    have hnd : ¬ l ∣ Fintype.card ((lowerQ Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) Q (j + 1)).map
        (iotaG Fq hMU π hπM)) := by
      rw [Fintype.card_eq_nat_card, Subgroup.card_map_of_injective hinj]
      exact not_dvd_card_lowerQ Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) Q (by omega) hl hlp
    rw [sum_finset_comp_map _ hinj _ _ hs, hβH _ hnd, card_finset_eq_card_map _ hinj _ _ hs, Int.cast_natCast]
  have hmain := sum_Phi_mul_beta (Λ := ZMod (l ^ n)) (Phi Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf))
    (fun Q => (Places.deg Fq Q : ℤ)) (Jbd Fq Mf (Mf ≃ₐ[RatFunc Fq] Mf)) (WQ Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf))
    (fun g hg => by convert Phi_eq_sum_WQ Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) hg)
    (chiC Fq (RatFunc Fq))
    (by rw [sum_Phi_eq Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) (hfin_of_unram Fq Mf hM.2.2),
      Nat.card_eq_fintype_card])
    (fun σ => β (iotaG Fq hMU π hπM σ)) (Module.finrank (ZMod (l ^ 1)) M : ℤ) hβ1
    (fun Q j => (Module.finrank (ZMod (l ^ 1)) (Coinvariants (τ.comp ((lowerQ Fq (RatFunc Fq) Mf
      (Mf ≃ₐ[RatFunc Fq] Mf) Q (j + 1)).map (iotaG Fq hMU π hπM)).subtype)) : ℤ)) hβW
  convert cast_natCast_mul_eq (hβχ.trans (h1.trans hmain)) using 2

end GOSI

end

end RamanujanPetersson.GOS


end


