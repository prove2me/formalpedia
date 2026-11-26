-- Prove2me | Definitions.Def_RPLib_FX_GOSC_11
-- name    : RPLib_FX_GOSC_11
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T02:20:42.854502+00:00
-- url     : https://prove2.me/theorems/0f4f8523-dfe0-51ef-9ab2-b15a7596289c
-- title:
--   Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 11 of 14
-- statement:
--   File 11 of 14 of the Grothendieck–Ogg–Shafarevich library for the affine line over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_GOS_B_Lift`: S4-GOS-B, part Lift: an `l`-independent integer lift of the character of the perfect complex
--   * `S4.Def_RP_GOS_B_Ass`: S4-GOS-B, part Ass: the character of the perfect complex is `Φ`, given the subgroup sums (O6) and `hfin`
--   * `S4.Def_RP_GOS_B_Pos`: S4-GOS-B, part Pos: subgroup sums of the character from an integer recurrence of the counts (O6a)
--   * `S4.Def_RP_GOS_B_HH2`: S4-GOS-B, part HH2: the character of the perfect complex on the concrete cover (O6 + O8, umbrella)
--
--   **Formalization note.** One file of a library formalizing the Grothendieck–Ogg–Shafarevich formula on the affine line over a finite field: for a lisse sheaf $M$ of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1_{\mathbb F_q}$ trivialized on a finite étale Galois cover ($\ell \nmid q$), $\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) - \dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) = \dim M - \mathrm{Sw}_\infty(M)$, with the cohomology written in continuous cochains of the geometric fundamental group and the Swan conductor in the lower numbering at a place over infinity. It extends the published flat library (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13; M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib
import Definitions.Def_RPLib_FX_GOSC_10

/-!
# Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 11 of 14

Declarations of the formalization of the Grothendieck–Ogg–Shafarevich formula for lisse sheaves on the affine
line over a finite field (h²_c - h¹_c = rank - Swan conductor at infinity), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_GOS_B_Lift`: S4-GOS-B, part Lift: an `l`-independent integer lift of the character of the perfect complex
* `S4.Def_RP_GOS_B_Ass`: S4-GOS-B, part Ass: the character of the perfect complex is `Φ`, given the subgroup sums (O6) and `hfin`
* `S4.Def_RP_GOS_B_Pos`: S4-GOS-B, part Pos: subgroup sums of the character from an integer recurrence of the counts (O6a)
* `S4.Def_RP_GOS_B_HH2`: S4-GOS-B, part HH2: the character of the perfect complex on the concrete cover (O6 + O8, umbrella)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_GOS_B_Lift =====
section

/-!
# S4-GOS-B, part Lift: an `l`-independent integer lift of the character of the perfect complex

`chiPC Λ … g = Σ_{i<3} (-1)^i Tr(ρPC_i g)`.
* `pcSeq_zero`: `pcSeq … g 0 = chiPC … g⁻¹`.
* `exists_rec_ptSeq`: the counts `ptSeq g` satisfy a nonzero integer recurrence from position `1` (Hankel argument
  `exists_rec_of_mod_pow` at one prime `l₀ ∤ q`, orders fixed by `finrank_lev`, recurrences by `pcSeq_rec`).
* `exists_mul_chi_eq`: `a · chi^{l,n}(g⁻¹) = u` with `a ≠ 0`, `u` integers independent of `l ∤ q`, `n > 0`
  (periodicity `pcSeq_periodic` + `mul_zero_eq_of_periodic`).
* **`exists_int_lift`**: `∃ b₀ ≠ 0, ∃ r : Gf → ℤ, ∀ l ∤ q prime, n > 0, g: r g = b₀ · chi^{l,n}(g)` in `ℤ/l^n`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue Lefschetz

section Chi

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

end Chi

section Lift

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
  [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
  {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
  (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
  {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
  (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
  (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
  {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)

include hM hπM hπ in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
/-- The counts satisfy a nonzero integer linear recurrence from position `1`. -/
theorem exists_rec_ptSeq (l0 : ℕ) [Fact l0.Prime] (hlq0 : ¬ l0 ∣ Fintype.card Fq) (g : Gf) :
    ∃ D : ℕ, ∃ μ : Fin (D + 1) → ℤ, μ ≠ 0 ∧
      ∀ k, 1 ≤ k → ∑ j : Fin (D + 1), μ j * ptSeq Fq K hq he hφ π g (k + j) = 0 := by
  classical
  have hl : l0.Prime := Fact.out
  obtain ⟨D, hD⟩ : ∃ D, Module.finrank (ZMod (l0 ^ 1))
      (PC (ZMod (l0 ^ 1)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia 0 ×
        (PC (ZMod (l0 ^ 1)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia 1 ×
          PC (ZMod (l0 ^ 1)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia 2)) = D :=
    ⟨_, rfl⟩
  have hrec : ∀ n, 0 < n → ∃ c : Fin D → ZMod (l0 ^ n), ∀ k,
      pcSeq (ZMod (l0 ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
        (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) g (k + D) =
      ∑ j, c j * pcSeq (ZMod (l0 ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
        (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) g (k + j) := by
    intro n hn
    obtain ⟨⟨f1, f2⟩, -⟩ := pc_lev Fq K hq he l0 n hn hlq0 hM hMU π hπM hπ
    haveI := f1
    haveI := f2
    haveI : Fact (1 < l0 ^ n) := ⟨Nat.one_lt_pow hn.ne' hl.one_lt⟩
    have hDn := finrank_lev Fq K hq he l0 n hn hlq0 hM hMU π hπM hπ
    obtain ⟨c, hc⟩ := pcSeq_rec (Λ := ZMod (l0 ^ n)) π _ _ φ⁻¹ (trueTau (bdryInf Fq K) φ⁻¹)
      (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) g
    revert c hc
    rw [hDn, hD]
    exact fun c hc => ⟨c, hc⟩
  have hrec' : ∀ n : ℕ, ∃ c : Fin D → ZMod (l0 ^ n), ∀ k,
      ((ptSeq Fq K hq he hφ π g (k + D + 1) : ℤ) : ZMod (l0 ^ n)) =
        ∑ j, c j * ((ptSeq Fq K hq he hφ π g (k + j + 1) : ℤ) : ZMod (l0 ^ n)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · haveI : Subsingleton (ZMod (l0 ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero l0)
      exact ⟨0, fun k => Subsingleton.elim _ _⟩
    · obtain ⟨c, hc⟩ := hrec n hn
      refine ⟨c, fun k => ?_⟩
      have e1 : ∀ m, 0 < m → pcSeq (ZMod (l0 ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq))
          (bdryInf Fq K).inertia φ⁻¹ (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹)
          (trueCompat (bdryInf Fq K) φ⁻¹) g m = (ptSeq Fq K hq he hφ π g m : ZMod (l0 ^ n)) :=
        fun m hm => pcSeq_eq_ptSeq Fq K hq he l0 n hn hlq0 hM hMU π hπM hπ hφ hm g
      have h1 := hc (k + 1)
      rw [e1 _ (by omega)] at h1
      rw [Nat.add_right_comm k D 1, h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [e1 _ (by omega), Nat.add_right_comm k 1 (j : ℕ)]
  obtain ⟨μ, hμ0, hμ⟩ := exists_rec_of_mod_pow (s := fun k => ptSeq Fq K hq he hφ π g (k + 1)) (l := l0)
    (D := D) hl.two_le hrec'
  refine ⟨D, μ, hμ0, fun k hk => ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (hμ k')
  rw [Nat.add_right_comm k' 1 (j : ℕ)]

include hq he hM hπM hπ hφ in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
/-- `a · chi^{l,n}(g⁻¹) = u` for integers `a ≠ 0`, `u` independent of `l ∤ q` and `n > 0`. -/
theorem exists_mul_chi_eq (g : Gf) :
    ∃ a u : ℤ, a ≠ 0 ∧ ∀ (l n : ℕ) [Fact l.Prime], 0 < n → ¬ l ∣ Fintype.card Fq →
      (a : ZMod (l ^ n)) * chiPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq))
        (bdryInf Fq K).inertia g⁻¹ = (u : ZMod (l ^ n)) := by
  classical
  obtain ⟨l0, hl0q, hl0⟩ := Nat.exists_infinite_primes (Fintype.card Fq + 1)
  haveI : Fact l0.Prime := ⟨hl0⟩
  have hlq0 : ¬ l0 ∣ Fintype.card Fq := fun hd => by
    have := Nat.le_of_dvd Fintype.card_pos hd
    omega
  obtain ⟨D, μ, hμ0, hμ⟩ := exists_rec_ptSeq Fq K hq he hM hMU π hπM hπ hφ l0 hlq0 g
  have hne : (Finset.univ.filter fun j => μ j ≠ 0).Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hμ0
    exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩
  have he0 : ∀ j, j < (Finset.univ.filter fun j => μ j ≠ 0).min' hne → μ j = 0 := fun j hj => by
    by_contra h
    exact absurd (Finset.min'_le _ j (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)) (not_le.2 hj)
  have hμe : μ ((Finset.univ.filter fun j => μ j ≠ 0).min' hne) ≠ 0 :=
    (Finset.mem_filter.1 (Finset.min'_mem _ hne)).2
  refine ⟨_, -∑ j, if (Finset.univ.filter fun j => μ j ≠ 0).min' hne < j then
    μ j * ptSeq Fq K hq he hφ π g (j - (Finset.univ.filter fun j => μ j ≠ 0).min' hne) else 0, hμe, ?_⟩
  intro l n _ hn hlq
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨⟨f1, f2⟩, -⟩ := pc_lev Fq K hq he l n hn hlq hM hMU π hπM hπ
  haveI := f1
  haveI := f2
  obtain ⟨T, hT, hTp⟩ := pcSeq_periodic (Λ := ZMod (l ^ n)) π _ _ φ⁻¹ (trueTau (bdryInf Fq K) φ⁻¹)
    (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹)
    (fun i => (frobPC_bijective_true (Λ := ZMod (l ^ n)) π (bdryInf Fq K) φ⁻¹ i).1)
  have hres := mul_zero_eq_of_periodic (R := ZMod (l ^ n)) μ _ he0 (s := ptSeq Fq K hq he hφ π g) hμ
    (x := fun m => pcSeq (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
      (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) g m) hT
    (fun m => hTp g m) (fun m hm => pcSeq_eq_ptSeq Fq K hq he l n hn hlq hM hMU π hπM hπ hφ hm g)
  rw [← pcSeq_zero (Λ := ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
    (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) g]
  refine hres.trans ?_
  simp only [Int.cast_neg, Int.cast_sum, Int.cast_ite, Int.cast_zero]

include hq he hM hπM hπ hφ in
/-- **`l`-independent integer lift**: `r g = b₀ · chi^{l,n}(g)` in `ℤ/l^n` for all primes `l ∤ q`, `n > 0`. -/
theorem exists_int_lift :
    ∃ b0 : ℤ, b0 ≠ 0 ∧ ∃ r : Gf → ℤ, ∀ (l n : ℕ) [Fact l.Prime], 0 < n → ¬ l ∣ Fintype.card Fq → ∀ g : Gf,
      (r g : ZMod (l ^ n)) = b0 * chiPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq))
        (bdryInf Fq K).inertia g := by
  classical
  choose a u ha hau using exists_mul_chi_eq Fq K hq he hM hMU π hπM hπ hφ
  refine ⟨∏ g, a g, Finset.prod_ne_zero_iff.2 fun g _ => ha g,
    fun g => (∏ g' ∈ Finset.univ.erase g⁻¹, a g') * u g⁻¹, ?_⟩
  intro l n _ hn hlq g
  have h := hau g⁻¹ l n hn hlq
  rw [inv_inv] at h
  rw [← Finset.prod_erase_mul Finset.univ a (Finset.mem_univ g⁻¹)]
  push_cast
  rw [← h, mul_assoc]

end Lift

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_Ass =====
section

/-!
# S4-GOS-B, part Ass: the character of the perfect complex is `Φ`, given the subgroup sums (O6) and `hfin`

* `exists_int_chi_two`: `chi^{l,n}(g)` and `chi^{l,n'}(g)` are casts of one integer (a common period of `pcSeq`).
* `chiPC_pow_prime_one`: `chi^{l,1}(g^l) = chi^{l,1}(g)` (`chi_pow_prime` over `ℤ/l`).
* `chiPC_eq_of_lift`: `r g = b₀ P` and `r ≡ b₀ chi^{l,n}` for all `n` give `chi^{l,n}(g) = P` (level shift by `v_l(b₀)`).
* **`chiPC_eq_Phi_of`**: for a Galois `G`-cover `L/𝔽_q(t)` with trivial finite inertia, `ι : G →* Gf`, and the cyclic
  subgroup sums `∑_{h ∈ ⟨τ⟩} chi^{l,1}(ι h) = |⟨τ⟩| χ_c(L^⟨τ⟩)` for all large `l`:
  `chi^{l,n}(ι σ) = Φ(σ)` in `ℤ/l^n` for every prime `l ∤ q` and `n > 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue Lefschetz

section Ass

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
  [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
  {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
  (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
  {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
  (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
  (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
  {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)

include hq he hM hπM hπ hφ in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
/-- `chi^{l,n}(g)` and `chi^{l,n'}(g)` are the casts of one integer. -/
theorem exists_int_chi_two (l : ℕ) [Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq) {n n' : ℕ} (hn : 0 < n)
    (hn' : 0 < n') (g : Gf) :
    ∃ z : ℤ, chiPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia g =
        (z : ZMod (l ^ n)) ∧
      chiPC (ZMod (l ^ n')) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia g =
        (z : ZMod (l ^ n')) := by
  classical
  have hl : l.Prime := Fact.out
  have per : ∀ k, 0 < k → ∃ T, 0 < T ∧ ∀ m j,
      pcSeq (ZMod (l ^ k)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
        (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) g⁻¹ (m + j * T) =
      pcSeq (ZMod (l ^ k)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
        (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) g⁻¹ m := by
    intro k hk
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hl.ne_zero⟩
    obtain ⟨⟨f1, f2⟩, -⟩ := pc_lev Fq K hq he l k hk hlq hM hMU π hπM hπ
    haveI := f1
    haveI := f2
    obtain ⟨T, hT, hTp⟩ := pcSeq_periodic (Λ := ZMod (l ^ k)) π _ _ φ⁻¹ (trueTau (bdryInf Fq K) φ⁻¹)
      (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹)
      (fun i => (frobPC_bijective_true (Λ := ZMod (l ^ k)) π (bdryInf Fq K) φ⁻¹ i).1)
    refine ⟨T, hT, fun m j => ?_⟩
    induction j with
    | zero => rw [zero_mul, add_zero]
    | succ j ih => rw [Nat.succ_mul, ← add_assoc, hTp, ih]
  obtain ⟨T, hT, hTp⟩ := per n hn
  obtain ⟨T', hT', hTp'⟩ := per n' hn'
  have e0 := pcSeq_zero (Λ := ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
    (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) g⁻¹
  have e0' := pcSeq_zero (Λ := ZMod (l ^ n')) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
    (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) g⁻¹
  rw [inv_inv] at e0 e0'
  refine ⟨ptSeq Fq K hq he hφ π g⁻¹ (T' * T), ?_, ?_⟩
  · rw [← e0, ← hTp 0 T', zero_add,
      pcSeq_eq_ptSeq Fq K hq he l n hn hlq hM hMU π hπM hπ hφ (Nat.mul_pos hT' hT) g⁻¹]
  · rw [← e0', ← hTp' 0 T, zero_add, mul_comm T T',
      pcSeq_eq_ptSeq Fq K hq he l n' hn' hlq hM hMU π hπM hπ hφ (Nat.mul_pos hT' hT) g⁻¹]

include hq he hM hπM hπ hφ in
/-- Level shift: `r g = b₀ P` and `r ≡ b₀ chi^{l,n}` for all `n > 0` give `chi^{l,n}(g) = P`. -/
theorem chiPC_eq_of_lift (b0 : ℤ) (hb0 : b0 ≠ 0) (r : Gf → ℤ)
    (hr : ∀ (l n : ℕ) [Fact l.Prime], 0 < n → ¬ l ∣ Fintype.card Fq → ∀ g : Gf,
      (r g : ZMod (l ^ n)) = b0 * chiPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq))
        (bdryInf Fq K).inertia g)
    (g : Gf) (P : ℤ) (hrP : r g = b0 * P) (l n : ℕ) [Fact l.Prime] (hn : 0 < n)
    (hlq : ¬ l ∣ Fintype.card Fq) :
    chiPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia g =
      (P : ZMod (l ^ n)) := by
  have hl : l.Prime := Fact.out
  obtain ⟨v, b', hb', hb⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hb0) l hl.ne_one
  obtain ⟨z, hz, hz'⟩ := exists_int_chi_two Fq K hq he hM hMU π hπM hπ hφ l hlq hn (Nat.add_pos_left hn v) g
  have h1 := hr l (n + v) (Nat.add_pos_left hn v) hlq g
  rw [hrP, hz', ← Int.cast_mul, ZMod.intCast_eq_intCast_iff_dvd_sub, ← mul_sub, Int.natCast_dvd,
    Int.natAbs_mul, hb, pow_add, mul_comm (l ^ n) (l ^ v), mul_assoc] at h1
  have h2 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hl.pos v) h1
  have hc : Nat.Coprime (l ^ n) b' := Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hl).2 hb')
  have h3 := hc.dvd_of_dvd_mul_left h2
  rw [hz, ZMod.intCast_eq_intCast_iff_dvd_sub, Int.natCast_dvd, ← Int.natAbs_neg, neg_sub]
  exact h3

open Classical in
include hq he hM hπM hπ hφ in
set_option maxHeartbeats 1000000 in
/-- **The character of the perfect complex is `Φ`** (given the cyclic subgroup sums and `hfin`). -/
theorem chiPC_eq_Phi_of (L : Type) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
    [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
    [Algebra.IsSeparable (RatFunc Fq) L] (G : Type) [Group G] [Fintype G] [MulSemiringAction G L]
    [IsGaloisGroup G (RatFunc Fq) L]
    (hfin : letI := actRfin Fq (RatFunc Fq) L G;
      ∀ Q : IsDedekindDomain.HeightOneSpectrum (Places.Rfin Fq L), Q.asIdeal.inertia G = ⊥)
    (ι : G →* Gf) (N1 : ℕ)
    (hH2 : ∀ τ : G, ∀ (l : ℕ) [Fact l.Prime], N1 < l →
      ∑ h : Subgroup.zpowers τ, chiPC (ZMod (l ^ 1)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq))
        (bdryInf Fq K).inertia (ι h) =
      (((Nat.card (Subgroup.zpowers τ) : ℤ) * chiC Fq (fixF Fq L G (Subgroup.zpowers τ)) : ℤ) : ZMod (l ^ 1)))
    (l n : ℕ) [Fact l.Prime] (hn : 0 < n) (hlq : ¬ l ∣ Fintype.card Fq) (σ : G) :
    chiPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia (ι σ) =
      (Phi Fq (RatFunc Fq) L G σ : ZMod (l ^ n)) := by
  obtain ⟨b0, hb0, r, hr⟩ := exists_int_lift Fq K hq he hM hMU π hπM hπ hφ
  have hnd : ∀ l' : ℕ, l'.Prime → Fintype.card Fq < l' → ¬ l' ∣ Fintype.card Fq := fun l' _ hl' hd => by
    have := Nat.le_of_dvd Fintype.card_pos hd
    omega
  have h1 : ∀ σ : G, ∀ l' : ℕ, l'.Prime → Fintype.card Fq < l' →
      ((r (ι (σ ^ l')) : ZMod l') = (r (ι σ) : ZMod l')) := by
    intro σ l' hl' hql'
    haveI : Fact l'.Prime := ⟨hl'⟩
    have hlq' := hnd l' hl' hql'
    obtain ⟨⟨f1, f2⟩, -⟩ := pc_lev Fq K hq he l' 1 one_pos hlq' hM hMU π hπM hπ
    haveI := f1
    haveI := f2
    have e1 := hr l' 1 one_pos hlq' (ι (σ ^ l'))
    have e2 := hr l' 1 one_pos hlq' (ι σ)
    rw [map_pow, chiPC_pow_prime_one Fq K π l' (ι σ), ← e2, ZMod.intCast_eq_intCast_iff_dvd_sub, pow_one] at e1
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub, map_pow]
    exact e1
  have h2 : ∀ τ : G, ∑ h : Subgroup.zpowers τ, r (ι h) =
      b0 * ((Nat.card (Subgroup.zpowers τ) : ℤ) * chiC Fq (fixF Fq L G (Subgroup.zpowers τ))) := by
    intro τ
    rw [← sub_eq_zero]
    apply eq_zero_of_large_prime_dvd
    intro B
    obtain ⟨p', hp'B, hp'⟩ := Nat.exists_infinite_primes (B + N1 + Fintype.card Fq + 1)
    haveI : Fact p'.Prime := ⟨hp'⟩
    refine ⟨p', by omega, hp', ?_⟩
    have hlq' := hnd p' hp' (by omega)
    have key : ((∑ h : Subgroup.zpowers τ, r (ι h) -
        b0 * ((Nat.card (Subgroup.zpowers τ) : ℤ) * chiC Fq (fixF Fq L G (Subgroup.zpowers τ))) : ℤ) :
          ZMod (p' ^ 1)) = 0 := by
      simp only [Int.cast_sub, Int.cast_sum, hr p' 1 one_pos hlq', ← Finset.mul_sum, hH2 τ p' (by omega),
        Int.cast_mul, sub_self]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, pow_one] at key
    exact key
  have hP := eq_mul_Phi_of_congr Fq L G hfin b0 (fun σ => r (ι σ)) (Fintype.card Fq) h1 (by convert h2)
  exact chiPC_eq_of_lift Fq K hq he hM hMU π hπM hπ hφ b0 hb0 r hr (ι σ) _ (hP σ) l n hn hlq

end Ass

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_Pos =====
section

/-!
# S4-GOS-B, part Pos: subgroup sums of the character from an integer recurrence of the counts (O6a)

* `neg_sum_ite_pos`: `-Σ_{j>0} B_j (c E_j) = B_0 (c E_0)` when `Σ_j B_j E_j = 0`.
* `isUnit_intCast_of_not_dvd`: `l ∤ b ⇒ b` is a unit in `ℤ/l^n`.
* **`sum_chiPC_eq_of_rec`**: for a subgroup `H' ≤ Gf`, if `Σ_{h ∈ H'} ptSeq h m = |H'| ê m` for `m > 0` and an integer
  recurrence `Σ_j b_j ê (k + j) = 0` (all `k`) has `l ∤ b_0`, then `Σ_{h ∈ H'} chi^{l,n}(h) = |H'| ê 0` in `ℤ/l^n`
  (periodicity + `mul_zero_eq_of_periodic` at index `0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue Lefschetz

section Pos

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
  [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
  {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
  (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
  {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
  (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
  (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
  {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)

include hq he hM hπM hπ hφ in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
/-- **Subgroup sums of the character** from an integer recurrence of the point counts with `l ∤ b₀`. -/
theorem sum_chiPC_eq_of_rec (H' : Subgroup Gf) [Fintype H'] (ê : ℕ → ℤ)
    (hN : ∀ m, 0 < m → ∑ h : H', ptSeq Fq K hq he hφ π (h : Gf) m = (Nat.card H' : ℤ) * ê m)
    {D : ℕ} (b : Fin (D + 1) → ℤ) (hb : ∀ k, ∑ j : Fin (D + 1), b j * ê (k + j) = 0)
    (l n : ℕ) [Fact l.Prime] (hn : 0 < n) (hlq : ¬ l ∣ Fintype.card Fq) (hbl : ¬ (l : ℤ) ∣ b 0) :
    ∑ h : H', chiPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia (h : Gf) =
      (((Nat.card H' : ℤ) * ê 0 : ℤ) : ZMod (l ^ n)) := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨⟨f1, f2⟩, -⟩ := pc_lev Fq K hq he l n hn hlq hM hMU π hπM hπ
  haveI := f1
  haveI := f2
  obtain ⟨T, hT, hTp⟩ := pcSeq_periodic (Λ := ZMod (l ^ n)) π _ _ φ⁻¹ (trueTau (bdryInf Fq K) φ⁻¹)
    (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹)
    (fun i => (frobPC_bijective_true (Λ := ZMod (l ^ n)) π (bdryInf Fq K) φ⁻¹ i).1)
  set c : ℤ := (Nat.card H' : ℤ) with hc
  have hμ : ∀ k, 1 ≤ k → ∑ j : Fin (D + 1), b j * (c * ê (k + j)) = 0 := fun k _ => by
    rw [← mul_zero c, ← hb k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have key := mul_zero_eq_of_periodic (R := ZMod (l ^ n)) b 0 (fun j hj => absurd hj (Fin.not_lt_zero j))
    (s := fun m => c * ê m) hμ
    (x := fun m => ∑ h : H', pcSeq (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq))
      (bdryInf Fq K).inertia φ⁻¹ (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹)
      (trueCompat (bdryInf Fq K) φ⁻¹) (h : Gf) m) hT
    (fun m => Finset.sum_congr rfl fun h _ => hTp (h : Gf) m)
    (fun m hm => by
      simp only [pcSeq_eq_ptSeq Fq K hq he l n hn hlq hM hMU π hπM hπ hφ (by omega : 0 < m)]
      rw [← Int.cast_sum, hN m (by omega)])
  have h0 := congrArg (Int.cast : ℤ → ZMod (l ^ n)) (hb 0)
  push_cast at h0
  simp only [zero_add] at h0
  have hR := neg_sum_ite_pos (fun j => (b j : ZMod (l ^ n))) (fun j => (ê j : ZMod (l ^ n))) (c : ZMod (l ^ n)) h0
  have hx0 : (∑ h : H', pcSeq (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq))
      (bdryInf Fq K).inertia φ⁻¹ (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹)
      (trueCompat (bdryInf Fq K) φ⁻¹) (h : Gf) 0) =
      ∑ h : H', chiPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia (h : Gf) := by
    simp only [pcSeq_zero]
    exact Fintype.sum_equiv (Equiv.inv H') _ _ (fun h => by simp)
  have key2 : (b 0 : ZMod (l ^ n)) * ∑ h : H', chiPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq))
      (bdryInf Fq K).inertia (h : Gf) = (b 0 : ZMod (l ^ n)) * (((c * ê 0 : ℤ)) : ZMod (l ^ n)) := by
    rw [← hx0]
    refine key.trans ?_
    push_cast
    simp only [Fin.val_zero, Nat.sub_zero]
    exact hR
  exact (isUnit_intCast_of_not_dvd hl n hbl).mul_left_cancel key2

end Pos

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_HH2 =====
section

/-!
# S4-GOS-B, part HH2: the character of the perfect complex on the concrete cover (O6 + O8, umbrella)

`K = RatFunc 𝔽_q`, `M_f ∈ unramSet` with `π : π_1(U) → Gf` surjective with kernel `π_1(M_f)`, `ι = iotaG`.
* `sum_chiPC_zpowers`: for `τ ∈ Gal(M_f/K)` and primes `l > q`:
  `Σ_{h ∈ ⟨τ⟩} chi^{l,1}(ι h) = |⟨τ⟩| χ_c(M_f^{⟨τ⟩})` (subgroup sums of `ptSeq` = `|H|` weil counts + the Weil
  recurrence with `l ∤ b₀`).
* **`chiPC_eq_Phi`**: `chi^{l,n}(ι σ) = Φ(σ)` in `ℤ/l^n` for every `l ∤ q`, `n > 0`, `σ ∈ Gal(M_f/K)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue Lefschetz

section HH2

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
/-- **Cyclic subgroup sums of the character** on the concrete cover, for primes `l > q`. -/
theorem sum_chiPC_zpowers (τ : Mf ≃ₐ[RatFunc Fq] Mf) (l : ℕ) [Fact l.Prime] (hl : Fintype.card Fq < l) :
    ∑ h : Subgroup.zpowers τ, chiPC (ZMod (l ^ 1)) π (pi1geo (Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq))
        (bdryInf Fq (RatFunc Fq)).inertia (iotaG Fq hMU π hπM h) =
      (((Nat.card (Subgroup.zpowers τ) : ℤ) *
        chiC Fq (fixF Fq Mf (Mf ≃ₐ[RatFunc Fq] Mf) (Subgroup.zpowers τ)) : ℤ) : ZMod (l ^ 1)) := by
  have hlq : ¬ l ∣ Fintype.card Fq := fun hd => absurd (Nat.le_of_dvd Fintype.card_pos hd) (not_le.2 hl)
  obtain ⟨D, b, hb, hb0⟩ := exists_weil_rec Fq (fixF Fq Mf (Mf ≃ₐ[RatFunc Fq] Mf) (Subgroup.zpowers τ))
  have key := sum_chiPC_eq_of_rec Fq (RatFunc Fq) hq he hM hMU π hπM hπ hφ
    ((Subgroup.zpowers τ).map (iotaG Fq hMU π hπM))
    (weilSeq Fq (fixF Fq Mf (Mf ≃ₐ[RatFunc Fq] Mf) (Subgroup.zpowers τ)))
    (fun m hm => sum_ptSeq_map Fq hq he hM.2.2 hMU π hπM hπs hφ (Subgroup.zpowers τ) hm) b hb l 1 one_pos hlq
    (hb0 l Fact.out hlq)
  rw [weilSeq_zero, Nat.card_congr ((Subgroup.zpowers τ).equivMapOfInjective _
    (iotaG_injective Fq hMU π hπM)).toEquiv.symm] at key
  rw [← key]
  exact Fintype.sum_equiv ((Subgroup.zpowers τ).equivMapOfInjective _ (iotaG_injective Fq hMU π hπM)).toEquiv _ _
    fun h => rfl

open Classical in
include hq he hM hπ hπs hφ in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **The character of the perfect complex is `Φ`** on the Galois group of the concrete cover `M_f / 𝔽_q(X)`. -/
theorem chiPC_eq_Phi (l n : ℕ) [Fact l.Prime] (hn : 0 < n) (hlq : ¬ l ∣ Fintype.card Fq)
    (σ : Mf ≃ₐ[RatFunc Fq] Mf) :
    chiPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq))
        (bdryInf Fq (RatFunc Fq)).inertia (iotaG Fq hMU π hπM σ) =
      (Phi Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) σ : ZMod (l ^ n)) :=
  chiPC_eq_Phi_of Fq (RatFunc Fq) hq he hM hMU π hπM hπ hφ Mf (Mf ≃ₐ[RatFunc Fq] Mf)
    (hfin_of_unram Fq Mf hM.2.2) (iotaG Fq hMU π hπM) (Fintype.card Fq)
    (fun τ l _ hl => sum_chiPC_zpowers Fq hq he hM hMU π hπM hπ hπs hφ τ l hl) l n hn hlq σ

end HH2

end

end RamanujanPetersson.GOS


end


