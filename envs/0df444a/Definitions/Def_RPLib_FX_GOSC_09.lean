-- Prove2me | Definitions.Def_RPLib_FX_GOSC_09
-- name    : RPLib_FX_GOSC_09
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T01:31:48.044467+00:00
-- url     : https://prove2.me/theorems/49f09939-aa24-425d-8aee-7d4db9d90c35
-- title:
--   Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 09 of 14
-- statement:
--   File 09 of 14 of the Grothendieck–Ogg–Shafarevich library for the affine line over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_GOS_B_Lev`: S4-GOS-B, part Lev: the perfect complex over `ℤ/l^n` for the true boundary data
--   * `S4.Def_RP_GOS_B_GCnt`: S4-GOS-B, part GCnt: subgroup sums of the point counts on the concrete cover (O6c)
--
--   **Formalization note.** One file of a library formalizing the Grothendieck–Ogg–Shafarevich formula on the affine line over a finite field: for a lisse sheaf $M$ of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1_{\mathbb F_q}$ trivialized on a finite étale Galois cover ($\ell \nmid q$), $\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) - \dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) = \dim M - \mathrm{Sw}_\infty(M)$, with the cohomology written in continuous cochains of the geometric fundamental group and the Swan conductor in the lower numbering at a place over infinity. It extends the published flat library (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13; M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib
import Definitions.Def_RPLib_F2_068
import Definitions.Def_RPLib_FX_GOSC_08

/-!
# Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 09 of 14

Declarations of the formalization of the Grothendieck–Ogg–Shafarevich formula for lisse sheaves on the affine
line over a finite field (h²_c - h¹_c = rank - Swan conductor at infinity), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_GOS_B_Lev`: S4-GOS-B, part Lev: the perfect complex over `ℤ/l^n` for the true boundary data
* `S4.Def_RP_GOS_B_GCnt`: S4-GOS-B, part GCnt: subgroup sums of the point counts on the concrete cover (O6c)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_GOS_B_Lev =====
section

/-!
# S4-GOS-B, part Lev: the perfect complex over `ℤ/l^n` for the true boundary data

* **`pc_lev`**: for `l ∤ q` and `n > 0`, every term of `PC (ℤ/l^n)` is free and finite and every `ρPC i` is
  projective (`pc_free_finite`, `isProj_ρPC_of_sylow` with the `H²`-vanishing inputs of `LCnt`).
* **`finrank_lev`**: the rank of `PC₀ × (PC₁ × PC₂)` over `ℤ/l^n` equals the one over `ℤ/l` (`finrank_pc3_red`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue Lefschetz

section Lev

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
/-- Free, finite and projective terms of `PC (ℤ/l^n)` for the true boundary data. -/
theorem pc_lev (l n : ℕ) [Fact l.Prime] (hn : 0 < n) (hlq : ¬ l ∣ Fintype.card Fq)
    [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
    (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K))) :
    ((∀ i, Module.Free (ZMod (l ^ n))
      (PC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)) ∧
     ∀ i, Module.Finite (ZMod (l ^ n))
      (PC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)) ∧
    ∀ i, IsProj (ρPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i) := by
  classical
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : IsLocalRing (ZMod (l ^ n)) := isLocalRing_zmod_pow l n hl hn
  haveI : CharP (IsLocalRing.ResidueField (ZMod (l ^ n))) l := charP_residue_zmod l n hn
  have hl0 : (l : K) ≠ 0 := by
    have h1 := cast_ne_zero_of_not_dvd (F := K) hq he hlq 1
    rwa [pow_one] at h1
  have hPicU := picDivU Fq K l hlq
  haveI := finite_Z1_regRep_geo Fq K hq he l n rfl hlq hM hMU π hπM
  haveI := fun s => finite_Z1_regRep_inertia Fq K hq he l n rfl hlq hM hMU π hπM s
  have hΛ : ((l ^ n : ℕ) : ZMod (l ^ n)) = 0 := ZMod.natCast_self _
  have hall := CdOne.h2All_geo (Rfin Fq K) Fq he hq (Kummer.perfect_Rfin Fq K) l (isUnit_cast_Rfin hl0) hPicU
    (ZMod (l ^ n)) n
  have hallI : ∀ s, H2All (ZMod (l ^ n)) (Pi1 (Rfin Fq K) K)
      (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s) l n :=
    fun s => cone_h3_eq_zero hq he hl0 hPicU (bdryInf Fq K) s (ZMod (l ^ n)) n
  obtain ⟨P⟩ : Nonempty (Sylow l Gf) := inferInstance
  letI : Fintype (P : Subgroup Gf) := Fintype.ofFinite _
  exact ⟨pc_free_finite π _ _ (zmod_maximalIdeal_eq l n hn) (zmod_l_pow_eq_zero l n)
      (fun _ h => zmod_l_pow_ne_zero l n h) hΛ hall hallI hπ,
    isProj_ρPC_of_sylow π _ _ (zmod_maximalIdeal_eq l n hn) (zmod_l_pow_eq_zero l n)
      (fun _ h => zmod_l_pow_ne_zero l n h) hΛ hall hallI hπ (P : Subgroup Gf) P.isPGroup' P.not_dvd_index⟩

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
/-- The rank of `PC₀ × (PC₁ × PC₂)` over `ℤ/l^n` is the one over `ℤ/l`. -/
theorem finrank_lev (l n : ℕ) [Fact l.Prime] (hn : 0 < n) (hlq : ¬ l ∣ Fintype.card Fq)
    [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
    (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K))) :
    Module.finrank (ZMod (l ^ n))
      (PC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia 0 ×
        (PC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia 1 ×
          PC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia 2)) =
    Module.finrank (ZMod (l ^ 1))
      (PC (ZMod (l ^ 1)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia 0 ×
        (PC (ZMod (l ^ 1)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia 1 ×
          PC (ZMod (l ^ 1)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia 2)) := by
  classical
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow hn.ne' hl.one_lt⟩
  haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl.one_lt⟩
  have hl0 : (l : K) ≠ 0 := by
    have h1 := cast_ne_zero_of_not_dvd (F := K) hq he hlq 1
    rwa [pow_one] at h1
  have hPicU := picDivU Fq K l hlq
  have hΛ : ((l ^ n : ℕ) : ZMod (l ^ n)) = 0 := ZMod.natCast_self _
  have hall := CdOne.h2All_geo (Rfin Fq K) Fq he hq (Kummer.perfect_Rfin Fq K) l (isUnit_cast_Rfin hl0) hPicU
    (ZMod (l ^ n)) n
  have hallI : ∀ s, H2All (ZMod (l ^ n)) (Pi1 (Rfin Fq K) K)
      (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s) l n :=
    fun s => cone_h3_eq_zero hq he hl0 hPicU (bdryInf Fq K) s (ZMod (l ^ n)) n
  obtain ⟨⟨f1, f2⟩, -⟩ := pc_lev Fq K hq he l n hn hlq hM hMU π hπM hπ
  obtain ⟨⟨f3, f4⟩, -⟩ := pc_lev Fq K hq he l 1 one_pos hlq hM hMU π hπM hπ
  letI : Algebra (ZMod (l ^ n)) (ZMod (l ^ 1)) := ZMod.algebra' (ZMod (l ^ 1)) (l ^ 1) (pow_dvd_pow l hn)
  have hsurj : Function.Surjective (algebraMap (ZMod (l ^ n)) (ZMod (l ^ 1))) := ZMod.ringHom_surjective _
  have ht : algebraMap (ZMod (l ^ n)) (ZMod (l ^ 1)) (l : ZMod (l ^ n)) = 0 := by
    rw [map_natCast, ZMod.natCast_eq_zero_iff, pow_one]
  have hk : ∀ r, algebraMap (ZMod (l ^ n)) (ZMod (l ^ 1)) r = 0 → ∃ s, r = (l : ZMod (l ^ n)) * s := by
    intro r hr
    rw [← ZMod.natCast_zmod_val r, map_natCast, ZMod.natCast_eq_zero_iff, pow_one] at hr
    obtain ⟨t, ht⟩ := hr
    exact ⟨t, by rw [← ZMod.natCast_zmod_val r, ht, Nat.cast_mul]⟩
  exact (finrank_pc3_red π _ _ hsurj ht hk hΛ hall hallI hπ).symm

end Lev

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_GCnt =====
section

/-!
# S4-GOS-B, part GCnt: subgroup sums of the point counts on the concrete cover (O6c)

`K = RatFunc 𝔽_q`, `M ⊆ K_U` finite Galois and unramified over `R_fin(K)`, `π : π_1 → Gf` with kernel `π_1(M)` and
`π` surjective, `ι = iotaG : Gal(M/K) ≅ Gf`. For `H ≤ Gal(M/K)`, `E' = M^H`, `m > 0`:
**`sum_ptSeq_map`**: `Σ_{h ∈ ι H} ptSeq h m = |ι H| · weilSeq E' m` (`= |H| · #Hom_{𝔽_q}(R_fin(E'), 𝔽_{q^m})`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh Lefschetz CupDuality CP4a

section GCnt

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {p e : ℕ} [Fact p.Prime] [CharP (RatFunc Fq) p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

variable {M : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq))} [FiniteDimensional (RatFunc Fq) M]
  [IsGalois (RatFunc Fq) M] (hun : IsUnramifiedSub (Rfin Fq (RatFunc Fq)) (RatFunc Fq) M)
  (hMU : M ≤ maxUnram (Rfin Fq (RatFunc Fq)) (RatFunc Fq))
  {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq) →* Gf)
  (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup) (hπs : Function.Surjective π)

variable {φ : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq)}
  (hφ : IsFrobLift (Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq) φ)

include hun hπs in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in
/-- **O6c: subgroup sums of the point counts** = `|H| ·` the affine point counts of `M^H`. -/
theorem sum_ptSeq_map (H : Subgroup (M ≃ₐ[RatFunc Fq] M)) [Fintype (H.map (iotaG Fq hMU π hπM))] {m : ℕ}
    (hm : 0 < m) :
    ∑ h : H.map (iotaG Fq hMU π hπM), ptSeq Fq (RatFunc Fq) hq he hφ π (h : Gf) m =
      (Nat.card (H.map (iotaG Fq hMU π hπM)) : ℤ) * weilSeq Fq (fixF Fq M (M ≃ₐ[RatFunc Fq] M) H) m := by
  have hspec := (exists_ptData_alg Fq (RatFunc Fq) hq he hφ hm
    (Nat.mul_pos hm (Fintype.card_pos (α := Gf)))).choose_spec.choose_spec
  have hQm : 1 < Fintype.card Fq ^ m := Nat.one_lt_pow hm.ne' Fintype.one_lt_card
  have hfr := frob_alg Fq (RatFunc Fq) hq m
  let P : (Rfin Fq (fixF Fq M (M ≃ₐ[RatFunc Fq] M) H) →+* AlgebraicClosure (RatFunc Fq)) → Prop := fun v =>
    v.comp (algebraMap Fq _) = algebraMap Fq (AlgebraicClosure (RatFunc Fq)) ∧
      ∀ r, v r ^ (Fintype.card Fq ^ m) = v r
  let res : (Rfin Fq (fixF Fq M (M ≃ₐ[RatFunc Fq] M) H) →+* AlgebraicClosure (RatFunc Fq)) →
      (Rfin Fq (RatFunc Fq) →+* AlgebraicClosure (RatFunc Fq)) := fun v => v.comp (algebraMap _ _)
  have hcomp : ∀ v : Rfin Fq (fixF Fq M (M ≃ₐ[RatFunc Fq] M) H) →+* AlgebraicClosure (RatFunc Fq),
      (res v).comp (algebraMap Fq (Rfin Fq (RatFunc Fq))) = v.comp (algebraMap Fq _) := fun v => by
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have hs : ∀ v, P v → res v ∈ ptSet Fq (RatFunc Fq) hq he hφ Gf hm := fun v hv =>
    (hspec.1 _).2 ⟨by rw [hcomp, hv.1, ιK_comp_algebraMap],
      RingHom.ext fun a => (hfr _).trans (hv.2 _)⟩
  haveI : ∀ u, Finite {v // res v = u ∧ P v} := fun u =>
    ((finite_ptSet Fq (fixF Fq M (M ≃ₐ[RatFunc Fq] M) H) hm _ hfr
      (algebraMap Fq (AlgebraicClosure (RatFunc Fq)))).subset
      (t := {v | res v = u ∧ P v}) fun v hv => ⟨hv.2.1, RingHom.ext fun r => (hfr _).trans (hv.2.2 r)⟩).to_subtype
  have hu_card : ∀ u ∈ ptSet Fq (RatFunc Fq) hq he hφ Gf hm,
      Nat.card {b : Gf // b⁻¹ * π (ptFu Fq (RatFunc Fq) hq he hφ Gf hm u) * b ∈ H.map (iotaG Fq hMU π hπM)} =
        Nat.card H * Nat.card {v // res v = u ∧ P v} := by
    intro u hu
    obtain ⟨w, hwu, hwF, -⟩ := hspec.2 u hu
    have hmem := (hspec.1 u).1 hu
    have hfinu : (Set.range u).Finite := (finite_setOf_pow_eq hQm).subset (by
      rintro _ ⟨a, rfl⟩
      show u a ^ (Fintype.card Fq ^ m) = u a
      rw [← hfr]
      exact RingHom.congr_fun hmem.2 a)
    rw [card_conj_map_iotaG Fq hMU π hπM hπs, card_conj_mem_eq Fq hun hMU H _ u hfinu w hwu
      (ptFu Fq (RatFunc Fq) hq he hφ Gf hm u) hwF, mul_comm]
    congr 1
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ⟨fun h => ⟨h.1, ?_, ?_⟩, fun h => ⟨h.1, ?_⟩⟩)
    · rw [← hcomp, show res v = u from h.1, hmem.1, ιK_comp_algebraMap]
    · exact fun r => (hfr _).symm.trans (RingHom.congr_fun h.2 r)
    · exact RingHom.ext fun r => (hfr _).trans (h.2.2 r)
  have hmain : (∑ u ∈ ptSet Fq (RatFunc Fq) hq he hφ Gf hm,
      Nat.card {b : Gf // b⁻¹ * π (ptFu Fq (RatFunc Fq) hq he hφ Gf hm u) * b ∈ H.map (iotaG Fq hMU π hπM)}) =
        Nat.card H * Nat.card {v // P v} := by
    rw [card_eq_sum_fiber res P _ hs, Finset.mul_sum]
    exact Finset.sum_congr rfl hu_card
  haveI := finite_levelField_alg (Fq := Fq) (Ω := AlgebraicClosure (RatFunc Fq)) hm
  rw [sum_ptSeq_subgroup Fq (RatFunc Fq) hq he hφ π hm, hmain,
    weilSeq_pos Fq (fixF Fq M (M ≃ₐ[RatFunc Fq] M) H) hm (levelField Fq (AlgebraicClosure (RatFunc Fq)) m)
      (finrank_levelField_alg hm),
    ← card_fixed_eq_card_algHom,
    Nat.card_congr (H.equivMapOfInjective _ (iotaG_injective Fq hMU π hπM)).toEquiv.symm]
  push_cast
  rfl

end GCnt

end

end RamanujanPetersson.GOS


end


