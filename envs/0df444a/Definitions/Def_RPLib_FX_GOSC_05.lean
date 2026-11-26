-- Prove2me | Definitions.Def_RPLib_FX_GOSC_05
-- name    : RPLib_FX_GOSC_05
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:58:31.438299+00:00
-- url     : https://prove2.me/theorems/6b0332ba-6e38-4a3c-a79f-ed9d087c0545
-- title:
--   Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 05 of 14
-- statement:
--   File 05 of 14 of the Grothendieck–Ogg–Shafarevich library for the affine line over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_GOS_B_TowH`: S4-GOS-B, part TowH: the tower identity for a subgroup
--   * `S4.Def_RP_GOS_B_Inv`: S4-GOS-B, part Inv: `Φ` is invariant under powers prime to the order
--   * `S4.Def_RP_GOS_B_Rec`: S4-GOS-B, part Rec: the Cayley–Hamilton recurrence for twisted traces, and the scaled character criterion
--   * `S4.Def_RP_GOS_B_Cov`: S4-GOS-B, part Cov: the concrete cover `M ⊆ K_U` over `K = 𝔽_q(X)` (O4u, O8b)
--   * `S4.Def_RP_GOS_C_PHI`: S4-GOS-C, part PHI: the global character `Φ` as a sum over lower ramification groups
--   * `S4.Def_RP_Swan_GlobPc`: S4-Swan (K2), part 20: Swan conductors and breaks at `∞` do not depend on the place
--   * `S4.Def_RP_GOS_C_SWB`: S4-GOS-C, part SWB: the GOS wild term at a place is `|I_Q|` times the Swan conductor
--   * `S4.Def_RP_GOS_C_SWS`: S4-GOS-C, part SWS: the Swan conductors at conjugate places agree
--
--   **Formalization note.** One file of a library formalizing the Grothendieck–Ogg–Shafarevich formula on the affine line over a finite field: for a lisse sheaf $M$ of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1_{\mathbb F_q}$ trivialized on a finite étale Galois cover ($\ell \nmid q$), $\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) - \dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) = \dim M - \mathrm{Sw}_\infty(M)$, with the cohomology written in continuous cochains of the geometric fundamental group and the Swan conductor in the lower numbering at a place over infinity. It extends the published flat library (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13; M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib
import Definitions.Def_RPLib_F2_023
import Definitions.Def_RPLib_FX_GOSC_04

/-!
# Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 05 of 14

Declarations of the formalization of the Grothendieck–Ogg–Shafarevich formula for lisse sheaves on the affine
line over a finite field (h²_c - h¹_c = rank - Swan conductor at infinity), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_GOS_B_TowH`: S4-GOS-B, part TowH: the tower identity for a subgroup
* `S4.Def_RP_GOS_B_Inv`: S4-GOS-B, part Inv: `Φ` is invariant under powers prime to the order
* `S4.Def_RP_GOS_B_Rec`: S4-GOS-B, part Rec: the Cayley–Hamilton recurrence for twisted traces, and the scaled character criterion
* `S4.Def_RP_GOS_B_Cov`: S4-GOS-B, part Cov: the concrete cover `M ⊆ K_U` over `K = 𝔽_q(X)` (O4u, O8b)
* `S4.Def_RP_GOS_C_PHI`: S4-GOS-C, part PHI: the global character `Φ` as a sum over lower ramification groups
* `S4.Def_RP_Swan_GlobPc`: S4-Swan (K2), part 20: Swan conductors and breaks at `∞` do not depend on the place
* `S4.Def_RP_GOS_C_SWB`: S4-GOS-C, part SWB: the GOS wild term at a place is `|I_Q|` times the Swan conductor
* `S4.Def_RP_GOS_C_SWS`: S4-GOS-C, part SWS: the Swan conductors at conjugate places agree
-/

set_option autoImplicit false

-- ===== S4.Def_RP_GOS_B_TowH =====
section

/-!
# S4-GOS-B, part TowH: the tower identity for a subgroup

For `IsGaloisGroup G Fq(X) L` and `H ≤ G`, with `L^H = fixF Fq L G H`:
**`Σ_{h ∈ H} Φ(h) = |H| χ_c(L^H)`** (`sum_Phi_subgroup`), where `Φ = Phi Fq (RatFunc Fq) L G` is the global
character of `G` (`Phi_subgroup`: the character of `H` on `L / L^H` is its restriction).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial IsDedekindDomain Classical

namespace RamanujanPetersson.GOS

open RamanujanPetersson.Places (Place Divisor Rfin Rinf Oinf)

section TowH

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]

variable (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G (RatFunc Fq) L]
variable (H : Subgroup G)

/-- **The tower identity for a subgroup** `H ≤ G`: `Σ_{h ∈ H} Φ(h) = |H| χ_c(L^H)`. -/
theorem sum_Phi_subgroup (hfin : letI := actRfin Fq (RatFunc Fq) L G;
      ∀ Q : HeightOneSpectrum (Rfin Fq L), Q.asIdeal.inertia G = ⊥) :
    ∑ h : H, Phi Fq (RatFunc Fq) L G h = (Nat.card H : ℤ) * chiC Fq (fixF Fq L G H) := by
  rw [← sum_Phi_eq Fq (fixF Fq L G H) L H (hfin_subgroup Fq L G H hfin)]
  exact Finset.sum_congr rfl fun h _ => (Phi_subgroup Fq L G H h).symm

end TowH

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Inv =====
section

/-!
# S4-GOS-B, part Inv: `Φ` is invariant under powers prime to the order

* `i_pow_of_coprime`: for a ramification function `R`, `R.i (σ ^ c) = R.i σ` when `c` is prime to `ord σ`;
* `iQ_pow_of_coprime`: the same for `i_Q` on the inertia group `I_Q`;
* **`Phi_pow_of_coprime`**: `Φ(τ ^ c) = Φ(τ)` for `c` prime to `ord τ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial IsDedekindDomain Classical

namespace RamanujanPetersson.GOS

open RamanujanPetersson.Places (Place Divisor Rfin Rinf Oinf)
open RamanujanPetersson.RR

section RamPow

variable {H : Type*} [Group H] (R : Swan.RamFn H)

end RamPow

section IQ

variable (L : Type*) [Field L] {G : Type*} [Group G] [Finite G] [MulSemiringAction G L]
variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra S L] [IsFractionRing S L]
  [MulSemiringAction G S] {R : Type*} [CommRing R] [Algebra R S] [IsGaloisGroup G R S]

include R in
theorem iQ_pow_of_coprime (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
    (Q : HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)] {σ : G} (hσ : σ ∈ Q.asIdeal.inertia G) {c : ℕ}
    (hcop : Nat.Coprime c (orderOf σ)) : iQ L (σ ^ c) Q = iQ L σ Q := by
  have h1 : iQ L σ Q = ((Swan.inertiaLocData (R := R) hc Q).ramFn.i ⟨σ, hσ⟩).toNat := rfl
  have h2 : iQ L (σ ^ c) Q = ((Swan.inertiaLocData (R := R) hc Q).ramFn.i (⟨σ, hσ⟩ ^ c)).toNat := rfl
  have ho : orderOf (⟨σ, hσ⟩ : Q.asIdeal.inertia G) = orderOf σ := Subgroup.orderOf_mk σ hσ
  rw [h1, h2, i_pow_of_coprime _ _ (ho ▸ hcop)]

end IQ

section Tow

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type*) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]
variable [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower Fq[X] K L] [IsScalarTower (RatFunc Fq) K L]
variable (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **`Φ(τ ^ c) = Φ(τ)`** for `c` prime to the order of `τ`. -/
theorem Phi_pow_of_coprime (τ : G) {c : ℕ} (hc : Nat.Coprime c (orderOf τ)) :
    Phi Fq K L G (τ ^ c) = Phi Fq K L G τ := by
  letI := actRinf Fq K L G
  haveI := isGaloisGroup_rinf Fq K L G
  by_cases h1 : τ = 1
  · rw [h1, one_pow]
  have h2 : τ ^ c ≠ 1 := fun h => h1 ((pow_eq_one_iff_of_coprime τ hc).1 h)
  rw [Phi_of_ne_one Fq K L G h1, Phi_of_ne_one Fq K L G h2]
  refine Finset.sum_congr rfl fun Q _ => ?_
  by_cases hQ : τ ∈ Q.asIdeal.inertia G
  · rw [if_pos ((pow_mem_iff_of_coprime _ τ hc).2 hQ), if_pos hQ,
      iQ_pow_of_coprime L (S := Rinf Fq L) (R := Rinf Fq K) (fun _ _ => rfl) Q hQ hc]
  · rw [if_neg (fun h => hQ ((pow_mem_iff_of_coprime _ τ hc).1 h)), if_neg hQ]

end Tow

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Rec =====
section

/-!
# S4-GOS-B, part Rec: the Cayley–Hamilton recurrence for twisted traces, and the scaled character criterion

* `comp_pow_of_comm` / `comp_aeval_of_comm`: `d ∘ F^j = F'^j ∘ d` and `d ∘ b(F) = b(F') ∘ d` for a chain map;
* **`sum_coeff_twisted_eq_zero`**: on a three-term complex over a field, if `b(F)` (`b ∈ ℤ[X]`) induces `0` on
  cohomology and `ρ(g)` is a chain map, then `Σ_j b_j χ(ρ(g) ∘ F^j) = 0` (Hopf);
* **`eq_mul_Phi_of_congr`**: the version of `eq_Phi_of_congr` scaled by `b₀ : ℤ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial LinearMap

namespace RamanujanPetersson.GOS

section RecAlg

variable {K : Type*} [Field K]
variable {V0 V1 V2 : Type*} [AddCommGroup V0] [Module K V0] [FiniteDimensional K V0]
  [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1]
  [AddCommGroup V2] [Module K V2] [FiniteDimensional K V2]

end RecAlg

section Ass

open Classical

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]
variable (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G (RatFunc Fq) L]

/-- **Scaled character criterion**: `r = b₀ Φ` from Fermat congruences and the `b₀`-scaled cyclic subgroup sums. -/
theorem eq_mul_Phi_of_congr (hfin : letI := actRfin Fq (RatFunc Fq) L G;
      ∀ Q : IsDedekindDomain.HeightOneSpectrum (Places.Rfin Fq L), Q.asIdeal.inertia G = ⊥)
    (b0 : ℤ) (r : G → ℤ) (N0 : ℕ)
    (h1 : ∀ σ : G, ∀ l : ℕ, l.Prime → N0 < l → ((r (σ ^ l) : ZMod l) = (r σ : ZMod l)))
    (h2 : ∀ τ : G, ∑ h : Subgroup.zpowers τ, r h =
      b0 * ((Nat.card (Subgroup.zpowers τ) : ℤ) * chiC Fq (fixF Fq L G (Subgroup.zpowers τ)))) :
    ∀ σ : G, r σ = b0 * Phi Fq (RatFunc Fq) L G σ := by
  have key := eq_zero_of_sum_pow (G := G) (R := ℤ) Set.univ (fun _ _ _ => Set.mem_univ _)
    (fun τ _ => isOfFinOrder_of_finite τ) (fun σ => r σ - b0 * Phi Fq (RatFunc Fq) L G σ)
    (fun τ _ => by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← sum_zpowers_eq_sum_range r τ,
        ← sum_zpowers_eq_sum_range (Phi Fq (RatFunc Fq) L G) τ, h2 τ,
        sum_Phi_subgroup Fq L G _ hfin, sub_self])
    (fun τ _ c hc => by
      rw [pow_eq_of_prime_congr r N0 h1 τ hc, Phi_pow_of_coprime Fq (RatFunc Fq) L G τ hc])
  intro σ
  have := key σ (Set.mem_univ _)
  omega

end Ass

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Cov =====
section

/-!
# S4-GOS-B, part Cov: the concrete cover `M ⊆ K_U` over `K = 𝔽_q(X)` (O4u, O8b)

`M` finite Galois over `K = RatFunc 𝔽_q`, `G = Gal(M/K)`:
* `rfinEquiv`: `R_fin(M) ≃ O_M` (the integral closure of `R_fin(K)` in `M` used by S4-Lefschetz), `G`-equivariant
  (`rfinEquiv_smul`);
* `hun_rfin`: every prime of `R_fin(M)` has trivial inertia if `M` is unramified over `R_fin(K)`;
  **`hfin_of_unram`** (O4u): the `hfin` hypothesis of `chiPC_eq_Phi_of`;
* `iotaG`: `Gal(M/K) →* Gf` with `iotaG (resPt σ) = π σ` (O8b), injective; surjective if `π` is.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh Lefschetz

section Cov

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (M : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq))) [FiniteDimensional (RatFunc Fq) M]
  [IsGalois (RatFunc Fq) M]

/-- `R_fin(M)` is the integral closure of `R_fin(K)` in `M`. -/
def rfinEquiv : Rfin Fq M ≃ₐ[Rfin Fq (RatFunc Fq)] integralClosure (Rfin Fq (RatFunc Fq)) M :=
  IsIntegralClosure.equiv (Rfin Fq (RatFunc Fq)) (Rfin Fq M) M (integralClosure (Rfin Fq (RatFunc Fq)) M)

variable {M} (hMU : M ≤ maxUnram (Rfin Fq (RatFunc Fq)) (RatFunc Fq))

variable {Gf : Type} [Group Gf] (π : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq) →* Gf)
  (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)

end Cov

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_C_PHI =====
section

/-!
# S4-GOS-C, part PHI: the global character `Φ` as a sum over lower ramification groups

For `IsGaloisGroup G K L` and a place `Q | ∞` of `L`: the lower ramification groups `G_{Q,u} ≤ I_Q ≤ G`
(`lowerQ`, from `Swan.inertiaLocData`), their finsets `W_Q(j) = G_{Q,j+1}` (`WQ`), and for `σ ≠ 1`
**`Φ(σ) = Σ_Q Σ_{j < J} [σ ∈ W_Q(j)] deg Q`** (`Phi_eq_sum_WQ`); in characteristic `p` the groups `W_Q(j)`
have order prime to every `l ≠ p` (`not_dvd_card_lowerQ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial IsDedekindDomain Classical

namespace RamanujanPetersson.GOS

open RamanujanPetersson.Places (Place Divisor Rfin Rinf Oinf)

section PhiW

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type*) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]
variable [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower Fq[X] K L] [IsScalarTower (RatFunc Fq) K L]
variable (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- The local data of the inertia group at a place `Q | ∞` (valuation `v_Q`, uniformizer `unifQ`). -/
def locQ (Q : HeightOneSpectrum (Rinf Fq L)) :
    letI := actRinf Fq K L G
    Swan.LocData (Q.asIdeal.inertia G) L :=
  letI := actRinf Fq K L G
  haveI := isGaloisGroup_rinf Fq K L G
  Swan.inertiaLocData (R := Rinf Fq K) (fun _ _ => rfl) Q

/-- The lower ramification group `G_{Q,u}` as a subgroup of `G`. -/
def lowerQ (Q : HeightOneSpectrum (Rinf Fq L)) (u : ℕ) : Subgroup G :=
  letI := actRinf Fq K L G
  ((locQ Fq K L G Q).ramFn.lower u).map (Q.asIdeal.inertia G).subtype

/-- `W_Q(j) = G_{Q,j+1}` as a finset. -/
def WQ (Q : HeightOneSpectrum (Rinf Fq L)) (j : ℕ) : Finset G :=
  Finset.univ.filter (· ∈ lowerQ Fq K L G Q (j + 1))

/-- A bound for all `i_Q(σ)`. -/
def Jbd : ℕ := ∑ Q : HeightOneSpectrum (Rinf Fq L), ∑ σ : G, iQ L σ Q

theorem iQ_le_Jbd (σ : G) (Q : HeightOneSpectrum (Rinf Fq L)) : iQ L σ Q ≤ Jbd Fq L G :=
  (Finset.single_le_sum (f := fun σ => iQ L σ Q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)).trans
    (Finset.single_le_sum (f := fun Q => ∑ σ : G, iQ L σ Q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ Q))

theorem toNat_ramFn_i (Q : HeightOneSpectrum (Rinf Fq L)) :
    letI := actRinf Fq K L G
    ∀ τ : Q.asIdeal.inertia G, ((locQ Fq K L G Q).ramFn.i τ).toNat = iQ L (τ : G) Q :=
  fun _ => rfl

theorem mem_lowerQ_iff (Q : HeightOneSpectrum (Rinf Fq L)) {σ : G} (hσ1 : σ ≠ 1) (u : ℕ) :
    letI := actRinf Fq K L G
    σ ∈ lowerQ Fq K L G Q u ↔ σ ∈ Q.asIdeal.inertia G ∧ u + 1 ≤ iQ L σ Q := by
  letI := actRinf Fq K L G
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx1 : x ≠ 1 := fun h => hσ1 (by rw [h]; rfl)
    obtain ⟨n, -, hn⟩ := (locQ Fq K L G Q).ramFn.exists_i_eq hx1
    refine ⟨x.2, ?_⟩
    have h1 := (Swan.RamFn.mem_lower _).mp hx
    rw [hn, Nat.cast_le] at h1
    show u + 1 ≤ iQ L (x : G) Q
    rw [← toNat_ramFn_i Fq K L G Q x, hn, ENat.toNat_natCast]
    exact h1
  · rintro ⟨hI, hu⟩
    have hx1 : (⟨σ, hI⟩ : Q.asIdeal.inertia G) ≠ 1 := fun h => hσ1 (congrArg Subtype.val h)
    obtain ⟨n, -, hn⟩ := (locQ Fq K L G Q).ramFn.exists_i_eq hx1
    refine ⟨⟨σ, hI⟩, ?_, rfl⟩
    rw [← toNat_ramFn_i Fq K L G Q ⟨σ, hI⟩, hn, ENat.toNat_natCast] at hu
    exact (Swan.RamFn.mem_lower _).mpr (by rw [hn]; exact_mod_cast hu)

theorem one_le_iQ (Q : HeightOneSpectrum (Rinf Fq L)) {σ : G} (hσ1 : σ ≠ 1) :
    letI := actRinf Fq K L G
    σ ∈ Q.asIdeal.inertia G → 1 ≤ iQ L σ Q := by
  letI := actRinf Fq K L G
  intro hI
  have hx1 : (⟨σ, hI⟩ : Q.asIdeal.inertia G) ≠ 1 := fun h => hσ1 (congrArg Subtype.val h)
  obtain ⟨n, hn1, hn⟩ := (locQ Fq K L G Q).ramFn.exists_i_eq hx1
  rw [← toNat_ramFn_i Fq K L G Q ⟨σ, hI⟩, hn, ENat.toNat_natCast]
  exact hn1

/-- **`Φ(σ) = Σ_Q Σ_{j < J} [σ ∈ W_Q(j)] deg Q`** for `σ ≠ 1`. -/
theorem Phi_eq_sum_WQ {σ : G} (hσ : σ ≠ 1) :
    Phi Fq K L G σ = ∑ Q : HeightOneSpectrum (Rinf Fq L), ∑ j ∈ Finset.range (Jbd Fq L G),
      if σ ∈ WQ Fq K L G Q j then (Places.deg Fq Q : ℤ) else 0 := by
  letI := actRinf Fq K L G
  rw [Phi_of_ne_one Fq K L G hσ]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hJ := iQ_le_Jbd Fq L G σ Q
  by_cases hI : σ ∈ Q.asIdeal.inertia G
  · rw [if_pos hI]
    have h1 := one_le_iQ Fq K L G Q hσ hI
    have hf : (Finset.range (Jbd Fq L G)).filter (fun j => σ ∈ WQ Fq K L G Q j) =
        Finset.range (iQ L σ Q - 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, WQ, Finset.mem_univ, true_and,
        mem_lowerQ_iff Fq K L G Q hσ]
      constructor
      · rintro ⟨-, -, h⟩; omega
      · intro h; exact ⟨by omega, hI, by omega⟩
    rw [hf, Finset.card_range, Nat.cast_sub h1, Nat.cast_one, mul_comm]
  · rw [if_neg hI]
    have hf : (Finset.range (Jbd Fq L G)).filter (fun j => σ ∈ WQ Fq K L G Q j) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, WQ, Finset.mem_univ, true_and,
        mem_lowerQ_iff Fq K L G Q hσ, Finset.notMem_empty, iff_false, not_and]
      exact fun _ h => absurd h hI
    rw [hf, Finset.card_empty, Nat.cast_zero, zero_mul]

theorem card_WQ (Q : HeightOneSpectrum (Rinf Fq L)) (j : ℕ) :
    (WQ Fq K L G Q j).card = Nat.card (lowerQ Fq K L G Q (j + 1)) := by
  rw [WQ, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- In characteristic `p` the groups `G_{Q,u}`, `u ≥ 1`, have order prime to every prime `l ≠ p`. -/
theorem not_dvd_card_lowerQ {p : ℕ} [Fact p.Prime] [CharP L p] (Q : HeightOneSpectrum (Rinf Fq L)) {u : ℕ}
    (hu : 1 ≤ u) {l : ℕ} (hl : l.Prime) (hlp : l ≠ p) : ¬ l ∣ Nat.card (lowerQ Fq K L G Q u) := by
  letI := actRinf Fq K L G
  rw [lowerQ, Subgroup.card_map_of_injective (Q.asIdeal.inertia G).subtype_injective]
  exact not_dvd_card_lower (locQ Fq K L G Q) hu hl hlp

end PhiW

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_Swan_GlobPc =====
section

/-!
# S4-Swan (K2), part 20: Swan conductors and breaks at `∞` do not depend on the place

If `τ • P = P'` for two height-one primes of a Dedekind domain with a Galois action, then
`v_{P'}(τ x) = v_P(x)` (`adicAdd_smul_eq`), conjugation `σ ↦ τ⁻¹ σ τ` maps the inertia group of `P'` onto that
of `P` (`conjInertia`), and the two inertia local data form a `LocData.Tower` along `τ` with trivial kernel
(`conjTower`). Isomorphic representations have equal Swan conductors and breaks (`RamFn.swan_equiv`,
`RamFn.allBrk_equiv`), so the Swan conductor and breaks of `ρ` restricted to inertia agree at `P` and `P'`.
At `∞` the base `O_∞` is local, so the cover group acts transitively on the places over `∞`
(`GalCover.exists_smul_inf`), giving `GalCover.swanInf_eq` and `GalCover.allBrkInf_eq`.
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain
open scoped Pointwise

namespace RamanujanPetersson

namespace Swan

section AdicConj

variable {S : Type*} [CommRing S] [IsDedekindDomain S] {L : Type*} [Field L] [Algebra S L]
  [IsFractionRing S L] {G : Type*} [Group G] [MulSemiringAction G S] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
include hc

/-- The Galois action transports valuations: `v_{τP}(τ x) = v_P(x)`. -/
theorem adicAdd_smul_eq (τ : G) {P P' : HeightOneSpectrum S} (h : τ • P.asIdeal = P'.asIdeal) (x : L) :
    adicAdd P' (τ • x) = adicAdd P x := by
  have hpow : ∀ n : ℕ, τ • (P.asIdeal ^ n) = P'.asIdeal ^ n := fun n => by
    rw [Ideal.pointwise_smul_def, Ideal.map_pow, ← Ideal.pointwise_smul_def, h]
  have hint : ∀ r : S, adicAdd P' (algebraMap S L (τ • r)) = adicAdd P (algebraMap S L r) := by
    intro r
    refine withTop_eq_of_natCast_le_iff (adicAdd_algebraMap_nonneg P' _)
      (adicAdd_algebraMap_nonneg P _) (fun n => ?_)
    rw [natCast_le_adicAdd_algebraMap_iff, natCast_le_adicAdd_algebraMap_iff, ← hpow n]
    exact Ideal.smul_mem_pointwise_smul_iff
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  rw [smul_div₀', hc, hc, AddValuation.map_div, AddValuation.map_div, hint, hint]

end AdicConj

section ConjInertia

variable {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]

end ConjInertia

section ConjTower

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S] {G : Type*}
  [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (τ : G) {P P' : HeightOneSpectrum S} (h : τ • P.asIdeal = P'.asIdeal)
  [Finite (S ⧸ P.asIdeal)] [Finite (S ⧸ P'.asIdeal)]

/-- The inertia local data at `P` and at `τ • P` form a tower along conjugation by `τ`. -/
theorem conjTower [Fintype (conjInertia τ h).ker] :
    LocData.Tower (inertiaLocData (R := R) hc P) (inertiaLocData (R := R) hc P')
      (MulSemiringAction.toRingHom G L τ) (conjInertia τ h) where
  surj := conjInertia_surjective τ h
  compat σ x := by
    show (σ : G) • τ • x = τ • ((τ⁻¹ * σ * τ) • x)
    rw [mul_smul, mul_smul, smul_inv_smul]
  v_iota x m hx := by
    rw [card_ker_conjInertia, Nat.cast_one, one_mul, ← hx]
    exact adicAdd_smul_eq hc τ h x
  val x _ hx0 := by
    rw [card_ker_conjInertia]
    exact ⟨-WithZero.log (P'.valuation L x), by rw [Nat.cast_one, one_mul]; exact negLogV_of_ne P' hx0⟩

end ConjTower

section RepEquiv

variable {G : Type*} [Group G] {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  (ρ₁ ρ₂ : Representation k G V) (e : V ≃ₗ[k] V) (he : ∀ g v, ρ₁ g (e v) = e (ρ₂ g v))
include he

namespace RamFn

variable (R : RamFn G)

end RamFn

end RepEquiv

section ConjRep

variable {G : Type*} [Group G] {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

variable {S : Type*} [CommRing S] [MulSemiringAction G S]

end ConjRep

section ConjSwan

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S] {G : Type*}
  [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (τ : G) {P P' : HeightOneSpectrum S} (h : τ • P.asIdeal = P'.asIdeal)
  [Finite (S ⧸ P.asIdeal)] [Finite (S ⧸ P'.asIdeal)]
  [Fintype (P.asIdeal.inertia G)] [Fintype (P'.asIdeal.inertia G)]
  {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)

include h in
/-- The Swan conductor of `ρ` at `P` equals the one at `τ • P`. -/
theorem swan_inertia_conj [FiniteDimensional k V] :
    (inertiaLocData (R := R) hc P').ramFn.swan (ρ.comp (P'.asIdeal.inertia G).subtype) =
      (inertiaLocData (R := R) hc P).ramFn.swan (ρ.comp (P.asIdeal.inertia G).subtype) := by
  classical
  have : Fintype (conjInertia τ h).ker := Fintype.ofFinite _
  rw [← (conjTower hc τ h).swan_comp]
  exact RamFn.swan_equiv _ _ (repEquiv ρ τ) (conj_rep_intertwine ρ τ h) _

end ConjSwan

end Swan

namespace GalCover

section Place

variable {A : Type} [CommRing A] [IsDomain A]
variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] [Algebra A (RatFunc Fq)]
  [IsFractionRing A (RatFunc Fq)]
variable (L : Type) [Field L] [Algebra (RatFunc Fq) L] [Algebra A L] [IsScalarTower A (RatFunc Fq) L]
variable [FiniteDimensional (RatFunc Fq) L] [Algebra.IsSeparable (RatFunc Fq) L] [Fintype Fq]

end Place

end GalCover

end RamanujanPetersson

end

end

-- ===== S4.Def_RP_GOS_C_SWB =====
section

/-!
# S4-GOS-C, part SWB: the GOS wild term at a place is `|I_Q|` times the Swan conductor

For `ι : G →* Gf` injective and a representation `τ` of `Gf` on a finite-dimensional `M` over a field in which the
orders of the wild groups `ι(G_{Q,j+1})` are invertible: **`card_mul_swanQ`**:
`|I_Q| Sw_Q(τ ∘ ι) = Σ_{j < J} |W_Q(j)| (dim M - dim M_{ι W_Q(j)})`, with `Sw_Q` S4-Swan's `RamFn.swan` of `locQ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial IsDedekindDomain Classical Module

namespace RamanujanPetersson.GOS

open RamanujanPetersson.Places (Place Divisor Rfin Rinf Oinf)

section SWB

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type*) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]
variable [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower Fq[X] K L] [IsScalarTower (RatFunc Fq) K L]
variable (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M] {Gf : Type*} [Group Gf] [Fintype Gf]
  (ι : G →* Gf) (τ : Representation k Gf M)

/-- The Swan conductor of `τ ∘ ι` at a place `Q | ∞`. -/
def swanQ (Q : HeightOneSpectrum (Rinf Fq L)) : ℚ :=
  letI := actRinf Fq K L G
  (locQ Fq K L G Q).ramFn.swan ((τ.comp ι).comp (Q.asIdeal.inertia G).subtype)

theorem top_le_Jbd (Q : HeightOneSpectrum (Rinf Fq L)) :
    letI := actRinf Fq K L G
    (locQ Fq K L G Q).ramFn.top ≤ Jbd Fq L G := by
  letI := actRinf Fq K L G
  refine Finset.sup_le fun σ _ => ?_
  show ((locQ Fq K L G Q).ramFn.i σ).toNat - 1 ≤ _
  rw [toNat_ramFn_i]
  exact (Nat.sub_le _ _).trans (iQ_le_Jbd Fq L G _ Q)

theorem finrank_fixd_lowerQ (Q : HeightOneSpectrum (Rinf Fq L)) (j : ℕ) :
    letI := actRinf Fq K L G
    finrank k (Swan.fixd ((τ.comp ι).comp (Q.asIdeal.inertia G).subtype)
      ((locQ Fq K L G Q).ramFn.lower (j + 1))) =
      finrank k (Representation.invariants (τ.comp ((lowerQ Fq K L G Q (j + 1)).map ι).subtype)) := by
  letI := actRinf Fq K L G
  have h := invariants_comp_map τ (ι.comp (Q.asIdeal.inertia G).subtype)
    ((locQ Fq K L G Q).ramFn.lower (j + 1))
  rw [← Subgroup.map_map] at h
  exact congrArg (fun S : Submodule k M => finrank k S) h

/-- **`|I_Q| Sw_Q = Σ_j |W_Q(j)| (dim M - dim M_{ι W_Q(j)})`**. -/
theorem card_mul_swanQ [FiniteDimensional k M] (Q : HeightOneSpectrum (Rinf Fq L))
    (hl : ∀ j, (Fintype.card ((lowerQ Fq K L G Q (j + 1)).map ι) : k) ≠ 0) :
    letI := actRinf Fq K L G
    (Nat.card (Q.asIdeal.inertia G) : ℚ) * swanQ Fq K L G ι τ Q =
      ∑ j ∈ Finset.range (Jbd Fq L G), ((WQ Fq K L G Q j).card : ℚ) *
        ((finrank k M : ℚ) - finrank k (Representation.Coinvariants
          (τ.comp ((lowerQ Fq K L G Q (j + 1)).map ι).subtype))) := by
  letI := actRinf Fq K L G
  rw [swanQ, Swan.RamFn.swan_eq_range _ _ (top_le_Jbd Fq K L G Q), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hI : (Nat.card (Q.asIdeal.inertia G) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hW : ((WQ Fq K L G Q j).card : ℚ) = Nat.card ((locQ Fq K L G Q).ramFn.lower (j + 1)) := by
    rw [card_WQ, lowerQ, Subgroup.card_map_of_injective (Q.asIdeal.inertia G).subtype_injective]
  have hd := finrank_coinv_subgroup τ _ (hl j)
  rw [← finrank_fixd_lowerQ Fq K L G ι τ Q j] at hd
  have hle := Submodule.finrank_le (Swan.fixd ((τ.comp ι).comp (Q.asIdeal.inertia G).subtype)
    ((locQ Fq K L G Q).ramFn.lower (j + 1)))
  rw [hW, hd, Swan.cod, Nat.cast_sub hle]
  field_simp

end SWB

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_SWS =====
section

/-!
# S4-GOS-C, part SWS: the Swan conductors at conjugate places agree

`swanQ_conj`: `Sw_{σ Q} = Sw_Q` (S4-Swan's `swan_inertia_conj`); `exists_smul_eq_rinf`: places of `L` over the same
place of `K` are conjugate; **`sum_swanQ_of_conj`**: if all places over `∞` are conjugate to `Q₀`, then
`Σ_Q deg Q |I_Q| Sw_Q = Sw_{Q₀} Σ_Q deg Q |I_Q|`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial IsDedekindDomain Classical Module
open scoped Pointwise

namespace RamanujanPetersson.GOS

open RamanujanPetersson.Places (Place Divisor Rfin Rinf Oinf)

section SWS

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type*) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]
variable [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower Fq[X] K L] [IsScalarTower (RatFunc Fq) K L]
variable (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M] {Gf : Type*} [Group Gf] [Fintype Gf]
  (ι : G →* Gf) (τ : Representation k Gf M)

theorem swanQ_conj [FiniteDimensional k M] (σ : G) {Q Q' : HeightOneSpectrum (Rinf Fq L)}
    (h : letI := actRinf Fq K L G; σ • Q.asIdeal = Q'.asIdeal) :
    swanQ Fq K L G ι τ Q' = swanQ Fq K L G ι τ Q := by
  letI := actRinf Fq K L G
  haveI := isGaloisGroup_rinf Fq K L G
  exact Swan.swan_inertia_conj (R := Rinf Fq K) (fun _ _ => rfl) σ h (τ.comp ι)

theorem sum_swanQ_of_conj [FiniteDimensional k M] (Q0 : HeightOneSpectrum (Rinf Fq L))
    (hconj : letI := actRinf Fq K L G; ∀ Q : HeightOneSpectrum (Rinf Fq L), ∃ σ : G, σ • Q0.asIdeal = Q.asIdeal) :
    letI := actRinf Fq K L G
    ∑ Q : HeightOneSpectrum (Rinf Fq L), (Places.deg Fq Q : ℚ) * Nat.card (Q.asIdeal.inertia G) *
        swanQ Fq K L G ι τ Q =
      swanQ Fq K L G ι τ Q0 * ∑ Q : HeightOneSpectrum (Rinf Fq L),
        (Places.deg Fq Q : ℚ) * Nat.card (Q.asIdeal.inertia G) := by
  letI := actRinf Fq K L G
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q _ => ?_
  obtain ⟨σ, hσ⟩ := hconj Q
  rw [swanQ_conj Fq K L G ι τ σ hσ]
  ring

end SWS

end RamanujanPetersson.GOS

end

end


