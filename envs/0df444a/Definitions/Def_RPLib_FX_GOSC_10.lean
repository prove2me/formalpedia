-- Prove2me | Definitions.Def_RPLib_FX_GOSC_10
-- name    : RPLib_FX_GOSC_10
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T02:18:14.039701+00:00
-- url     : https://prove2.me/theorems/0fb3661d-4dce-4de3-8847-74b6e69331f2
-- title:
--   Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 10 of 14
-- statement:
--   File 10 of 14 of the Grothendieck–Ogg–Shafarevich library for the affine line over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_LCnt`: S4-Lefschetz, L7f3: the Lefschetz numbers of the Frobenius on the perfect complex are point counts
--   * `S4.Def_RP_GOS_B_Cnt`: S4-GOS-B, part Cnt: the twisted Frobenius traces of the perfect complex are `l`-independent point counts
--   * `S4.Def_RP_GOS_C_LEV`: S4-GOS-C, part LEV: Brauer's formula for the true boundary data at level `ℤ/l^n`
--
--   **Formalization note.** One file of a library formalizing the Grothendieck–Ogg–Shafarevich formula on the affine line over a finite field: for a lisse sheaf $M$ of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1_{\mathbb F_q}$ trivialized on a finite étale Galois cover ($\ell \nmid q$), $\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) - \dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) = \dim M - \mathrm{Sw}_\infty(M)$, with the cohomology written in continuous cochains of the geometric fundamental group and the Swan conductor in the lower numbering at a place over infinity. It extends the published flat library (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13; M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib
import Definitions.Def_RPLib_F2_070
import Definitions.Def_RPLib_FX_GOSC_09

/-!
# Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 10 of 14

Declarations of the formalization of the Grothendieck–Ogg–Shafarevich formula for lisse sheaves on the affine
line over a finite field (h²_c - h¹_c = rank - Swan conductor at infinity), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_LCnt`: S4-Lefschetz, L7f3: the Lefschetz numbers of the Frobenius on the perfect complex are point counts
* `S4.Def_RP_GOS_B_Cnt`: S4-GOS-B, part Cnt: the twisted Frobenius traces of the perfect complex are `l`-independent point counts
* `S4.Def_RP_GOS_C_LEV`: S4-GOS-C, part LEV: Brauer's formula for the true boundary data at level `ℤ/l^n`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_LCnt =====
section

/-!
# S4-Lefschetz, L7f3: the Lefschetz numbers of the Frobenius on the perfect complex are point counts

* **`lefschetz_count_main`**: for a function field `K/𝔽_q` with full constant field, `l ∤ q` and a finite quotient
  `π : π₁ → Gf` cut out by a finite unramified `M`, the Lefschetz number of `F^m` on the perfect complex over `ℤ/l^n`
  at the class of `γ` is the number of `𝔽_{q^m}`-points `u` of `U` with `π(F_u) ~ γ` (`ptCount`). This is the
  coefficient-free content of `lefschetz_main` (same hypotheses, no `τ`), used to transfer the trace formula to
  coefficient rings free over `ℤ/l^n` (`O/l^n`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue

section Count

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
/-- **Lefschetz numbers of `F^m` are twisted point counts** (over `ℤ/l^n`, unconditional). -/
theorem lefschetz_count_main (l n k : ℕ) [Fact l.Prime] (hn : 0 < n) (hlq : ¬ l ∣ Fintype.card Fq)
    [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
    (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
    {Gf : Type} [Group Gf] [Fintype Gf] [Fintype (ConjClasses Gf)] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
    [Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π)]
    [∀ s, Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s).map π)]
    [∀ i, Module.Free (ZMod (l ^ n))
      (PC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)]
    [∀ i, Module.Finite (ZMod (l ^ n))
      (PC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)]
    {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)
    (hkv : (Fintype.card Gf).factorization l ≤ k)
    {m : ℕ} (hm : 0 < m) {r : ℕ} (hmr : m * Fintype.card Gf ∣ r) (hQ : 1 < p ^ (e * r))
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (Fr : Ω →+* Ω) (hFr : ∀ z, Fr z = z ^ (Fintype.card Fq ^ m))
    (ιS : kStar (Rfin Fq K) K hq r →+* Ω) (S : Finset (Rfin Fq K →+* Ω))
    (hS : ∀ u, u ∈ S ↔ (u.comp (algebraMap Fq (Rfin Fq K)) = ιS.comp (algebraMap Fq (kStar (Rfin Fq K) K hq r)) ∧
      Fr.comp u = u))
    (Fu : (Rfin Fq K →+* Ω) → Pi1 (Rfin Fq K) K)
    (hFu : ∀ u ∈ S, ∃ w : proChart (Rfin Fq K) K (Rfin Fq K) →+* Ω,
      w.comp (algebraMap (Rfin Fq K) _) = u ∧ (∀ b, w (Fu u • b) = Fr (w b)) ∧
        ∀ x, w (incStar (Rfin Fq K) K hq r hQ x) = ιS x) (γ : Gf) :
    lefschetz (ρPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia) 2
      (fun i => frobPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
        (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) i ^ m)
      (ConjClasses.mk γ) = (ptCount S (fun u => π (Fu u)) γ : ZMod (l ^ n)) := by
  classical
  have hl : l.Prime := Fact.out
  have hnk : 0 < n + k := by omega
  haveI : NeZero (l ^ (n + k)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : IsLocalRing (ZMod (l ^ (n + k))) := isLocalRing_zmod_pow l (n + k) hl hnk
  haveI : CharP (IsLocalRing.ResidueField (ZMod (l ^ (n + k)))) l := charP_residue_zmod l (n + k) hnk
  haveI := nonempty_bdryS (Fq := Fq) (F := K)
  have hl0 : (l : K) ≠ 0 := by
    have h1 := cast_ne_zero_of_not_dvd (F := K) hq he hlq 1
    rwa [pow_one] at h1
  have hPicU := picDivU Fq K l hlq
  have hPic := picDivX Fq K l hlq (n + k)
  haveI := finite_Z1_regRep_geo Fq K hq he l (n + k) rfl hlq hM hMU π hπM
  haveI := fun s => finite_Z1_regRep_inertia Fq K hq he l (n + k) rfl hlq hM hMU π hπM s
  have hΛk : ((l ^ (n + k) : ℕ) : ZMod (l ^ (n + k))) = 0 := ZMod.natCast_self _
  obtain ⟨Hr, hTW⟩ := exists_resHyp_tw hq he hl0 (n + k) hPic hM hMU π hπM hπ (bdryInf Fq K)
    (bdryData_B _ _ _ _) hΛk
  have hall := CdOne.h2All_geo (Rfin Fq K) Fq he hq (Kummer.perfect_Rfin Fq K) l (isUnit_cast_Rfin hl0) hPicU
    (ZMod (l ^ (n + k))) (n + k)
  have hallI : ∀ s, H2All (ZMod (l ^ (n + k))) (Pi1 (Rfin Fq K) K)
      (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s) l (n + k) :=
    fun s => cone_h3_eq_zero hq he hl0 hPicU (bdryInf Fq K) s (ZMod (l ^ (n + k))) (n + k)
  obtain ⟨P⟩ : Nonempty (Sylow l Gf) := inferInstance
  letI : Fintype (P : Subgroup Gf) := Fintype.ofFinite _
  have hρ := isProj_ρPC_of_sylow π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia
    (zmod_maximalIdeal_eq l (n + k) hnk) (zmod_l_pow_eq_zero l (n + k)) (fun _ h => zmod_l_pow_ne_zero l (n + k) h)
    hΛk hall hallI hπ (P : Subgroup Gf) P.isPGroup' P.not_dvd_index
  have hPCk := pc_free_finite π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia
    (zmod_maximalIdeal_eq l (n + k) hnk) (zmod_l_pow_eq_zero l (n + k)) (fun _ h => zmod_l_pow_ne_zero l (n + k) h)
    hΛk hall hallI hπ
  haveI := hPCk.1
  haveI := hPCk.2
  exact lefschetz_pow_eq_count π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
    (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) hl n k hall hallI hπ
    hkv hρ m (fun γ => ptCount S (fun u => π (Fu u)) γ) γ
    (euler_eq_count Fq K hq he l (n + k) hnk rfl hlq π hπ Hr hφ (hTW φ hφ) γ hm hmr hQ Fr hFr ιS S hS Fu hFu)

end Count

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_GOS_B_Cnt =====
section

/-!
# S4-GOS-B, part Cnt: the twisted Frobenius traces of the perfect complex are `l`-independent point counts

* `exists_ptData_alg`: the point data of `exists_ptData` for `Ω = K̄`, `Fr = z ↦ z ^ (q ^ m)`, `ιS` the inclusion.
* **`ptSeq`**: `ptSeq g m = |C(g)| · #{u ∈ U(𝔽_{q^m}) : π(F_u) ~ g}` (an integer, `0` at `m = 0`), independent of `l`.
* **`pcSeq_eq_ptSeq`**: for `l ∤ q`, `n > 0`, `m > 0`: `pcSeq (ℤ/l^n) … g m = ptSeq g m`
  (`lefschetz_trace_inv_comp` + `lefschetz_count_main`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue Lefschetz

section Cnt

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
/-- **Twisted Frobenius traces are point counts**: `pcSeq (ℤ/l^n) … g m = ptSeq g m` for `m > 0`. -/
theorem pcSeq_eq_ptSeq (l n : ℕ) [Fact l.Prime] (hn : 0 < n) (hlq : ¬ l ∣ Fintype.card Fq)
    [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
    (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
    {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ) {m : ℕ} (hm : 0 < m) (g : Gf) :
    pcSeq (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
      (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) g m =
      (ptSeq Fq K hq he hφ π g m : ZMod (l ^ n)) := by
  classical
  obtain ⟨⟨f1, f2⟩, hρ⟩ := pc_lev Fq K hq he l n hn hlq hM hMU π hπM hπ
  haveI := f1
  haveI := f2
  have hr : 0 < m * Fintype.card Gf := Nat.mul_pos hm (Fintype.card_pos (α := Gf))
  obtain ⟨hS, hFu⟩ := (exists_ptData_alg Fq K hq he hφ hm hr).choose_spec.choose_spec
  have h1 := lefschetz_trace_inv_comp hρ
    (φ := fun i => frobPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
      (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) i ^ m)
    (fun i => isEquivariant_pow (frobPC_equiv _ _ _ _ _ _ _ i) m) 2 g
  have h2 := lefschetz_count_main Fq K hq he l n ((Fintype.card Gf).factorization l) hn hlq hM hMU π hπM hπ hφ
    le_rfl hm (dvd_refl _) (hQ_of hr he) _ (frob_alg Fq K hq m) (ιK Fq K hq _) _ hS _ hFu g
  refine Eq.trans h1 ?_
  rw [h2, ptSeq, dif_pos hm, Int.cast_mul, Int.cast_natCast, Int.cast_natCast]

end Cnt

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_C_LEV =====
section

/-!
# S4-GOS-C, part LEV: Brauer's formula for the true boundary data at level `ℤ/l^n`

**`brauer_lev`**: for `l ∤ q`, `n > 0` and a representation `τ` of the cover group `Gf` on a finite `ℤ/l`-module `M`,
there is `β : Gf → ℤ/l^n` with `Σ_{h ∈ H} β h = |H| dim (M|_H)_H` for every `l'`-subgroup `H`, and
`|Gf| · χ(τ) = Σ_g chiPC_{ℤ/l^n}(g) β(g)`, where `χ(τ) = Σ_i (-1)^i dim (PC_{ℤ/l} i ⊗ M)_{Gf}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue Lefschetz

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
/-- **Brauer's formula at level `ℤ/l^n`** for the true boundary data. -/
theorem brauer_lev (l n : ℕ) [Fact l.Prime] (hn : 0 < n) (hlq : ¬ l ∣ Fintype.card Fq)
    [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
    (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Module.Finite (ZMod (l ^ 1)) M]
    (τ : Representation (ZMod (l ^ 1)) Gf M) :
    ∃ β : Gf → ZMod (l ^ n),
      (∀ (H : Subgroup Gf) [Fintype H], ¬ l ∣ Fintype.card H → ∑ h : H, β h =
        (Fintype.card H : ZMod (l ^ n)) *
          (Module.finrank (ZMod (l ^ 1)) (Coinvariants (τ.comp H.subtype)) : ZMod (l ^ n))) ∧
      (Fintype.card Gf : ZMod (l ^ n)) * ((∑ i ∈ Finset.range 3, (-1 : ℤ) ^ i *
        (Module.finrank (ZMod (l ^ 1)) (Coinvariants ((ρPC (ZMod (l ^ 1)) π (pi1geo (Rfin Fq K) K
          (Fintype.card Fq)) (bdryInf Fq K).inertia i).tprod τ)) : ℤ) : ℤ) : ZMod (l ^ n)) =
      ∑ g, chiPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia g * β g := by
  classical
  have hl : l.Prime := Fact.out
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact hl⟩
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : IsLocalRing (ZMod (l ^ n)) := isLocalRing_zmod_pow l n hl hn
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
  obtain ⟨⟨f3, f4⟩, hp1⟩ := pc_lev Fq K hq he l 1 one_pos hlq hM hMU π hπM hπ
  letI : Algebra (ZMod (l ^ n)) (ZMod (l ^ 1)) := ZMod.algebra' (ZMod (l ^ 1)) (l ^ 1) (pow_dvd_pow l hn)
  have hsurj : Function.Surjective (algebraMap (ZMod (l ^ n)) (ZMod (l ^ 1))) := ZMod.ringHom_surjective _
  have ht : algebraMap (ZMod (l ^ n)) (ZMod (l ^ 1)) (l : ZMod (l ^ n)) = 0 := by
    rw [map_natCast, ZMod.natCast_eq_zero_iff, pow_one]
  have hk : ∀ r, algebraMap (ZMod (l ^ n)) (ZMod (l ^ 1)) r = 0 → ∃ s, r = (l : ZMod (l ^ n)) * s := by
    intro r hr
    rw [← ZMod.natCast_zmod_val r, map_natCast, ZMod.natCast_eq_zero_iff, pow_one] at hr
    obtain ⟨t, ht⟩ := hr
    exact ⟨t, by rw [← ZMod.natCast_zmod_val r, ht, Nat.cast_mul]⟩
  letI : Module (ZMod (l ^ n)) M := Module.compHom M (algebraMap (ZMod (l ^ n)) (ZMod (l ^ 1)))
  haveI : IsScalarTower (ZMod (l ^ n)) (ZMod (l ^ 1)) M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have hl' : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : ZMod (l ^ 1)) := fun m hm => by
    rw [isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff, pow_one]
    exact hm
  have hϖN : (l : ZMod (l ^ n)) ^ n = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  obtain ⟨β, hβ⟩ := exists_beta (l : ZMod (l ^ n)) hsurj hk hϖN hl' τ
  exact ⟨β, fun H _ hH => sum_beta_subgroup _ hsurj ht hk hϖN hl' τ hβ H hH,
    brauer_PC π _ _ hsurj ht hk hϖN hl hΛ hl' hall hallI hπ hp1 τ hβ⟩

end

end RamanujanPetersson.GOS


end


