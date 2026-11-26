-- Prove2me | Definitions.Def_RPLib_FX_GOSC_04
-- name    : RPLib_FX_GOSC_04
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:50:56.839494+00:00
-- url     : https://prove2.me/theorems/4059807e-2790-4ec2-925e-588c8562fb71
-- title:
--   Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 04 of 14
-- statement:
--   File 04 of 14 of the Grothendieck–Ogg–Shafarevich library for the affine line over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Swan_GlobV`: S4-Swan (K2), part 13: the `P`-adic additive valuation and the local data of an inertia group
--   * `S4.Def_RP_PerfectCx_RedPC`: S4-PD (5), E3: the perfect complex mod `t` (`Pₙ ⊗ Λₘ ≅ Pₘ`)
--   * `S4.Def_RP_GOS_A_Unr`: S4-GOS-A, part 5: the inertia ring is unramified
--   * `S4.Def_RP_GOS_B_Cnt`: S4-GOS-B, part Cnt: the twisted Frobenius traces of the perfect complex are `l`-independent point counts
--   * `S4.Def_RP_GOS_A_Hilb`: S4-GOS-A, part 6: Hilbert's different formula
--   * `S4.Def_RP_GOS_B_Hil`: S4-GOS-B, part Hil: Hilbert's formula and `e = |I|` on the charts of a Galois extension
--   * `S4.Def_RP_GOS_B_Tow`: S4-GOS-B, part Tow: the global character `Φ` and the tower identity
--   * `S4.Def_RP_GOS_B_TowH`: S4-GOS-B, part TowH: the tower identity for a subgroup
--   * `S4.Def_RP_GOS_B_Lvl`: S4-GOS-B, part Lvl: `𝔽_{q^m}`-points as Frobenius-fixed points (O6c, generic)
--   * `S4.Def_RP_GOS_B_Bij`: S4-GOS-B, part Bij: the Frobenius of the perfect complex is bijective
--   * `S4.Def_RP_GOS_C_B1a`: S4-GOS-C, part B1a: idempotents of `End(Y)[C]` and traces on projective modules (abelian `C`)
--   * `S4.Def_RP_GOS_C_B1b`: S4-GOS-C, part B1b: the conjugation argument and restriction of Higman elements
--   * `S4.Def_RP_GOS_C_TLIFT`: S4-GOS-C, part TLIFT: reductions, `1 ⊗ q = 0`, and tensor products of lifts
--   * `S4.Def_RP_GOS_C_EUL`: S4-GOS-C, part EUL: the Euler characteristic of the perfect complex is `h²_c - h¹_c`
--   * `S4.Def_RP_GOS_C_RAT`: S4-GOS-C, part RAT: the projective line `𝔽_q(x)`
--
--   **Formalization note.** One file of a library formalizing the Grothendieck–Ogg–Shafarevich formula on the affine line over a finite field: for a lisse sheaf $M$ of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1_{\mathbb F_q}$ trivialized on a finite étale Galois cover ($\ell \nmid q$), $\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) - \dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) = \dim M - \mathrm{Sw}_\infty(M)$, with the cohomology written in continuous cochains of the geometric fundamental group and the Swan conductor in the lower numbering at a place over infinity. It extends the published flat library (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13; M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib
import Definitions.Def_RPLib_F2_005
import Definitions.Def_RPLib_F2_010
import Definitions.Def_RPLib_F2_022
import Definitions.Def_RPLib_FX_GOSC_03

/-!
# Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 04 of 14

Declarations of the formalization of the Grothendieck–Ogg–Shafarevich formula for lisse sheaves on the affine
line over a finite field (h²_c - h¹_c = rank - Swan conductor at infinity), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Swan_GlobV`: S4-Swan (K2), part 13: the `P`-adic additive valuation and the local data of an inertia group
* `S4.Def_RP_PerfectCx_RedPC`: S4-PD (5), E3: the perfect complex mod `t` (`Pₙ ⊗ Λₘ ≅ Pₘ`)
* `S4.Def_RP_GOS_A_Unr`: S4-GOS-A, part 5: the inertia ring is unramified
* `S4.Def_RP_GOS_B_Cnt`: S4-GOS-B, part Cnt: the twisted Frobenius traces of the perfect complex are `l`-independent point counts
* `S4.Def_RP_GOS_A_Hilb`: S4-GOS-A, part 6: Hilbert's different formula
* `S4.Def_RP_GOS_B_Hil`: S4-GOS-B, part Hil: Hilbert's formula and `e = |I|` on the charts of a Galois extension
* `S4.Def_RP_GOS_B_Tow`: S4-GOS-B, part Tow: the global character `Φ` and the tower identity
* `S4.Def_RP_GOS_B_TowH`: S4-GOS-B, part TowH: the tower identity for a subgroup
* `S4.Def_RP_GOS_B_Lvl`: S4-GOS-B, part Lvl: `𝔽_{q^m}`-points as Frobenius-fixed points (O6c, generic)
* `S4.Def_RP_GOS_B_Bij`: S4-GOS-B, part Bij: the Frobenius of the perfect complex is bijective
* `S4.Def_RP_GOS_C_B1a`: S4-GOS-C, part B1a: idempotents of `End(Y)[C]` and traces on projective modules (abelian `C`)
* `S4.Def_RP_GOS_C_B1b`: S4-GOS-C, part B1b: the conjugation argument and restriction of Higman elements
* `S4.Def_RP_GOS_C_TLIFT`: S4-GOS-C, part TLIFT: reductions, `1 ⊗ q = 0`, and tensor products of lifts
* `S4.Def_RP_GOS_C_EUL`: S4-GOS-C, part EUL: the Euler characteristic of the perfect complex is `h²_c - h¹_c`
* `S4.Def_RP_GOS_C_RAT`: S4-GOS-C, part RAT: the projective line `𝔽_q(x)`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Swan_GlobV =====
section

/-!
# S4-Swan (K2), part 13: the `P`-adic additive valuation and the local data of an inertia group

For a Dedekind domain `S` with fraction field `L` and a height-one prime `P`, `adicAdd P` is the `P`-adic
valuation of `L` as an `AddValuation L (WithTop ℤ)` (`-log` of Mathlib's multiplicative `P.valuation L`).
It has a uniformizer, integral elements are approximated by elements of `S` modulo `P`, and it is invariant
under every automorphism of `S` (compatibly extended to `L`) that stabilizes `P`.

If a finite group `G` is a Galois group for `S / R` (`IsGaloisGroup G R S`) and `S ⧸ P` is finite, every element
of `S` is congruent mod `P` to an element fixed by the inertia group `I = P.inertia G` (the residue field
extension of `S` over `S^I` is trivial: `card_stabilizer_eq_card_inertia_mul_finrank` with stabilizer = inertia
= `I`). Hence `(I, L, adicAdd P)` is local data (`inertiaLocData`), so `Swan.LocData.ramFn` applies.
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero
open scoped Pointwise

namespace RamanujanPetersson.Swan

section AdicAdd

variable {S : Type*} [CommRing S] [IsDedekindDomain S] {L : Type*} [Field L] [Algebra S L]
  [IsFractionRing S L] (P : HeightOneSpectrum S)

theorem natCast_le_adicAdd_iff (x : L) (n : ℕ) :
    (n : WithTop ℤ) ≤ adicAdd P x ↔ P.valuation L x ≤ exp (-(n : ℤ)) := by
  rw [adicAdd_apply]
  by_cases hx : x = 0
  · rw [hx, negLogV_zero, map_zero]; exact ⟨fun _ => zero_le, fun _ => le_top⟩
  have h1 : P.valuation L x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [negLogV_of_ne P hx, ← WithTop.coe_natCast, WithTop.coe_le_coe]
  conv_rhs => rw [← exp_log h1]
  rw [exp_le_exp]
  constructor <;> intro h <;> omega

theorem natCast_le_adicAdd_algebraMap_iff (r : S) (n : ℕ) :
    (n : WithTop ℤ) ≤ adicAdd P (algebraMap S L r) ↔ r ∈ P.asIdeal ^ n := by
  rw [natCast_le_adicAdd_iff, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_le_pow_iff_mem]

theorem adicAdd_nonneg_iff (x : L) : 0 ≤ adicAdd P x ↔ P.valuation L x ≤ 1 := by
  have := natCast_le_adicAdd_iff P x 0
  simpa using this

theorem adicAdd_algebraMap_nonneg (r : S) : 0 ≤ adicAdd P (algebraMap S L r) := by
  have := (natCast_le_adicAdd_algebraMap_iff (L := L) P r 0).2 (by simp)
  simpa using this

theorem one_le_adicAdd_algebraMap_iff (r : S) :
    1 ≤ adicAdd P (algebraMap S L r) ↔ r ∈ P.asIdeal := by
  have := natCast_le_adicAdd_algebraMap_iff (L := L) P r 1
  simpa using this

variable (L) in
theorem exists_adicAdd_eq_one : ∃ π : L, adicAdd P π = 1 := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer L
  have h0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact exp_ne_zero hπ.symm
  refine ⟨π, ?_⟩
  rw [adicAdd_apply, negLogV_of_ne P h0, hπ, log_exp, neg_neg, WithTop.coe_one]

theorem exists_one_le_adicAdd_sub {x : L} (hx : 0 ≤ adicAdd P x) :
    ∃ r : S, 1 ≤ adicAdd P (x - algebraMap S L r) := by
  obtain ⟨r, hr⟩ := P.exists_valuation_sub_lt_of_integer ((adicAdd_nonneg_iff P x).1 hx) 1
  refine ⟨r, ?_⟩
  have key : P.valuation L (algebraMap S L r - x) ≤ exp (-((1 : ℕ) : ℤ)) := by
    by_cases h0 : P.valuation L (algebraMap S L r - x) = 0
    · rw [h0]; exact zero_le
    rw [Units.val_one] at hr
    rw [← exp_log h0] at hr ⊢
    rw [← exp_zero, exp_lt_exp] at hr
    rw [exp_le_exp]
    omega
  have := (natCast_le_adicAdd_iff P _ 1).2 key
  rw [← AddValuation.map_neg, neg_sub] at this
  simpa using this

section Smul

variable {G : Type*} [Group G] [MulSemiringAction G S] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
include hc

/-- `adicAdd P` is invariant under every `σ` with `σ • P = P`. -/
theorem adicAdd_smul (σ : G) (hσ : σ • P.asIdeal = P.asIdeal) (x : L) :
    adicAdd P (σ • x) = adicAdd P x := by
  have hpow : ∀ n : ℕ, σ • (P.asIdeal ^ n) = P.asIdeal ^ n := fun n => by
    rw [Ideal.pointwise_smul_def, Ideal.map_pow, ← Ideal.pointwise_smul_def, hσ]
  have hint : ∀ r : S, adicAdd P (algebraMap S L (σ • r)) = adicAdd P (algebraMap S L r) := by
    intro r
    refine withTop_eq_of_natCast_le_iff (adicAdd_algebraMap_nonneg P _)
      (adicAdd_algebraMap_nonneg P _) (fun n => ?_)
    rw [natCast_le_adicAdd_algebraMap_iff, natCast_le_adicAdd_algebraMap_iff]
    conv_lhs => rw [← hpow n]
    exact Ideal.smul_mem_pointwise_smul_iff
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  rw [smul_div₀', hc, hc, AddValuation.map_div, AddValuation.map_div, hint, hint]

end Smul

end AdicAdd

section Residue

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {G : Type*} [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

end Residue

section Inertia

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S] {G : Type*}
  [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (Q : HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)]

include R in
/-- The inertia group of `Q` acting on `L` with the `Q`-adic valuation is local data. -/
def inertiaLocData : LocData (Q.asIdeal.inertia G) L where
  v := adicAdd Q
  v_smul σ x := adicAdd_smul Q hc (σ : G)
    (MulAction.mem_stabilizer_iff.1 (Ideal.inertia_le_stabilizer Q.asIdeal σ.2)) x
  faithful σ hσ := by
    have : FaithfulSMul G S := IsGaloisGroup.faithful R
    apply Subtype.ext
    show (σ : G) = 1
    apply eq_of_smul_eq_smul (α := S)
    intro s
    apply IsFractionRing.injective S L
    rw [one_smul, ← hc]
    exact hσ (algebraMap S L s)
  ϖ := Classical.choose (exists_adicAdd_eq_one L Q)
  v_ϖ := Classical.choose_spec (exists_adicAdd_eq_one L Q)
  res x hx := by
    obtain ⟨r, hr⟩ := exists_one_le_adicAdd_sub Q hx
    obtain ⟨a, ha, hra⟩ := exists_inertia_fixed_sub_mem (R := R) (G := G) Q.asIdeal r
    refine ⟨algebraMap S L a, fun σ => ?_, ?_⟩
    · show (σ : G) • algebraMap S L a = _
      rw [hc, ha σ σ.2]
    · have h2 : (1 : WithTop ℤ) ≤ adicAdd Q (algebraMap S L r - algebraMap S L a) := by
        rw [← map_sub]
        exact (one_le_adicAdd_algebraMap_iff Q (r - a)).2 hra
      have e : x - algebraMap S L a =
          (x - algebraMap S L r) + (algebraMap S L r - algebraMap S L a) := by ring
      rw [e]
      exact le_trans (le_min hr h2) ((adicAdd Q).map_add _ _)

theorem inertiaLocData_v : (inertiaLocData (R := R) hc Q).v = adicAdd Q := rfl

end Inertia

end RamanujanPetersson.Swan

end

end

-- ===== S4.Def_RP_PerfectCx_RedPC =====
section

/-!
# S4-PD (5), E3: the perfect complex mod `t` (`Pₙ ⊗ Λₘ ≅ Pₘ`)

Termwise reductions `redA`, `red1`, `red2` of `PC Λ → PC Λ'` are onto with kernel `t • PC` (`H2All`), commute with
the `Gf`-actions, the Frobenius and the differentials, so `Λ' ⊗ PC Λ i ≃ PC Λ' i` (`pcRed0`, `pcRed1`, `pcRed2`,
compatibilities via `redEquiv_comm`) and the Lefschetz numbers of the Frobenius reduce (`lefschetz_frob_red`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings TensorProduct

noncomputable section

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {Gf : Type} [Group Gf] {G : Type} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

section Frob

variable [Γ.Normal] (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

end Frob

section Red

variable [Finite Λ] [Fintype Gf] {ϖ : Λ} (hsurj : Function.Surjective (algebraMap Λ Λ'))
  (ht : algebraMap Λ Λ' ϖ = 0) (hk : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = ϖ * s) {l N : ℕ}
  (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)
  (hπ : IsOpen (π.ker : Set G))

/-- `Λ' ⊗ P⁰_Λ ≃ P⁰_Λ'`. -/
def pcRed0 : Λ' ⊗[Λ] MonoidAlgebra Λ Gf ≃ₗ[Λ'] MonoidAlgebra Λ' Gf :=
  redEquiv ϖ hsurj ht (redA Λ Λ' Gf) (redA_surjective hsurj) (redA_ker hk)

variable [Γ.Normal] (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

end Red

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_GOS_A_Unr =====
section

/-!
# S4-GOS-A, part 5: the inertia ring is unramified

For `S / R` Dedekind with Galois group `G` and `Q` a height-one prime of `S` with finite residue field, the inertia
ring `S ^ (I_Q)` (`inertiaRing R G Q`) is Dedekind and finite over `R` (global instances `fixed_*`), the prime
`Q ∩ S^(I_Q)` has ramification index one over `R` (`ramificationIdx_inertiaRing`), so `Q` does not divide the
extended different of `S^(I_Q) / R` (`not_dvd_map_differentIdeal`).
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain
open scoped Classical Pointwise nonZeroDivisors

namespace RamanujanPetersson.GOS

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section Instances

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {G : Type*} [Group G]
  [MulSemiringAction G S] [SMulCommClass G R S] (H : Subgroup G) [Module.Finite R S]

instance fixed_finite_top : Module.Finite (FixedPoints.subalgebra R S H) S := Swan.finite_fixed H

instance fixed_isIntegral : Algebra.IsIntegral R (FixedPoints.subalgebra R S H) :=
  Swan.isIntegral_fixedSubalgebra H

variable [IsDedekindDomain R] [IsDedekindDomain S]

instance fixed_isDedekindDomain : IsDedekindDomain (FixedPoints.subalgebra R S H) :=
  Swan.isDedekindDomain_fixed H

end Instances

section Unr

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
  (Q : HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)]

/-- The prime `Q ∩ S^(I_Q)` has ramification index `1` over `R`. -/
theorem ramificationIdx_inertiaRing :
    (Q.asIdeal.under (inertiaRing R G Q)).ramificationIdx R = 1 := by
  have := Q.isMaximal
  have hQ : Q.asIdeal.LiesOver (Q.asIdeal.under (inertiaRing R G Q)) := ⟨rfl⟩
  have hQR : Q.asIdeal.LiesOver (Q.asIdeal.under R) := ⟨rfl⟩
  have : (Q.asIdeal.under R).IsMaximal := Ideal.IsMaximal.under R Q.asIdeal
  have : (Q.asIdeal.under (inertiaRing R G Q)).IsMaximal :=
    Ideal.IsMaximal.under (inertiaRing R G Q) Q.asIdeal
  have := finite_residueField Q (Q.asIdeal.under R)
  have := finite_residueField Q (Q.asIdeal.under (inertiaRing R G Q))
  have h1 : Q.asIdeal.ramificationIdx R = Nat.card (Q.asIdeal.inertia G) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := G) (Q.asIdeal.under R) Q.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.asIdeal.under R) Q.asIdeal G]
  have htop : Q.asIdeal.inertia (Q.asIdeal.inertia G) = ⊤ :=
    eq_top_iff.2 fun σ _ => AddSubgroup.coe_mem_inertia.1 σ.2
  have h2 : Q.asIdeal.ramificationIdx (inertiaRing R G Q) = Nat.card (Q.asIdeal.inertia G) := by
    rw [← Subgroup.card_top (G := Q.asIdeal.inertia G), ← htop,
      Ideal.card_inertia_eq_ramificationIdxIn (G := Q.asIdeal.inertia G)
        (Q.asIdeal.under (inertiaRing R G Q)) Q.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.asIdeal.under (inertiaRing R G Q)) Q.asIdeal
        (Q.asIdeal.inertia G)]
  have h3 := Ideal.ramificationIdx_tower (R := R) (Q.asIdeal.under (inertiaRing R G Q)) Q.asIdeal
  rw [h1, h2] at h3
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [one_mul]; exact h3.symm)

/-- The inertia ring is unramified at `Q ∩ S^(I_Q)`, so `Q` does not divide the extended different of
`S^(I_Q) / R`. -/
theorem not_dvd_map_differentIdeal :
    ¬ Q.asIdeal ∣ (differentIdeal R (inertiaRing R G Q)).map (algebraMap (inertiaRing R G Q) S) := by
  have := Q.isMaximal
  have := isSeparable_frac R S G
  have : Algebra.IsSeparable (FractionRing R) (FractionRing (inertiaRing R G Q)) :=
    Algebra.isSeparable_tower_bot_of_isSeparable _ _ (FractionRing S)
  have : (Q.asIdeal.under (inertiaRing R G Q)).IsMaximal :=
    Ideal.IsMaximal.under (inertiaRing R G Q) Q.asIdeal
  have : ((Q.asIdeal.under (inertiaRing R G Q)).under R).IsMaximal :=
    Ideal.IsMaximal.under R _
  have : Q.asIdeal.LiesOver ((Q.asIdeal.under (inertiaRing R G Q)).under R) := ⟨rfl⟩
  have := finite_residueField Q ((Q.asIdeal.under (inertiaRing R G Q)).under R)
  have hq : Algebra.IsUnramifiedAt R (Q.asIdeal.under (inertiaRing R G Q)) :=
    Ideal.ramificationIdx_eq_one_iff.1 (ramificationIdx_inertiaRing Q)
  have hnd := (not_dvd_differentIdeal_iff (A := R) (B := inertiaRing R G Q)).2 hq
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
  rwa [Ideal.dvd_iff_le] at hnd

end Unr

end RamanujanPetersson.GOS

end

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

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Lefschetz

section Cnt

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq in
theorem frob_alg (m : ℕ) (z : AlgebraicClosure K) :
    iterateFrobenius (AlgebraicClosure K) p (e * m) z = z ^ (Fintype.card Fq ^ m) := by
  rw [iterateFrobenius_def, hq, ← pow_mul]

end Cnt

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_A_Hilb =====
section

/-!
# S4-GOS-A, part 6: Hilbert's different formula

`S / R` finite torsion-free extension of Dedekind domains with Galois group `G`, `Q` a height-one prime of `S` with
finite residue field and inertia group `I_Q`. The different of `S / R` has the same `Q`-exponent as that of
`S / S^(I_Q)` (part 5: `S^(I_Q)` is unramified at `Q`), and `S / S^(I_Q)` is totally ramified (part 4), so
* `ordI_differentIdeal`: `v_Q(𝔇_{S/R}) = ∑_{σ ∈ I_Q, σ ≠ 1} v_Q(ϖ - σ ϖ)` for any uniformizer `ϖ`;
* `ordI_differentIdeal_eq_sum_ramFn`: `v_Q(𝔇_{S/R}) = ∑_{σ ∈ I_Q, σ ≠ 1} i_Q(σ)` with S4-Swan's ramification
  function of `Swan.inertiaLocData`;
* `ordI_differentIdeal_eq_sum_lower`: `v_Q(𝔇_{S/R}) = ∑_{u ≥ 0} (|G_u| - 1)` (lower numbering).
The subgroup version (`S^H ⊆ S`) is the case `R := FixedPoints.subalgebra R S H`, `G := H` (instances of part 5).
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain
open scoped Classical Pointwise nonZeroDivisors

namespace RamanujanPetersson.GOS

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section Hilb

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
  (Q : HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)] [Fintype (Q.asIdeal.inertia G)]

omit [Fintype (Q.asIdeal.inertia G)] in
/-- `𝔇_{S/R}` and `𝔇_{S/S^(I_Q)}` have the same `Q`-exponent. -/
theorem ordI_differentIdeal_eq_inertiaRing :
    ordI Q (differentIdeal R S) = ordI Q (differentIdeal (inertiaRing R G Q) S) := by
  have := isSeparable_frac R S G
  have h := differentIdeal_eq_differentIdeal_mul_differentIdeal R (inertiaRing R G Q) S
  have hne : differentIdeal R S ≠ ⊥ := differentIdeal_ne_bot
  rw [h] at hne ⊢
  have hne' := hne
  rw [Ne, Ideal.mul_eq_bot, not_or] at hne'
  have h0 : ordI Q ((differentIdeal R (inertiaRing R G Q)).map
      (algebraMap (inertiaRing R G Q) S)) = 0 :=
    (ordI_eq_zero_iff Q hne'.2).2 fun hle =>
      not_dvd_map_differentIdeal (R := R) (G := G) Q (Ideal.dvd_iff_le.2 hle)
  rw [ordI_mul Q hne'.1 hne'.2, h0, add_zero]

/-- **Hilbert's different formula**: for a uniformizer `ϖ` of `Q`,
`v_Q(𝔇_{S/R}) = ∑_{σ ∈ I_Q, σ ≠ 1} v_Q(ϖ - σ ϖ)`. -/
theorem ordI_differentIdeal {ϖ : S} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) :
    ordI Q (differentIdeal R S) = ∑ σ ∈ Finset.univ.erase (1 : Q.asIdeal.inertia G),
      ordI Q (Ideal.span {ϖ - (σ : G) • ϖ}) := by
  rw [ordI_differentIdeal_eq_inertiaRing (G := G) Q, ordI_differentIdeal_of_totally
    (A := inertiaRing R G Q) (G := Q.asIdeal.inertia G) Q
    (fun σ => AddSubgroup.coe_mem_inertia.1 σ.2) h1 h2]
  exact Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun _ _ => rfl

end Hilb

section Lower

variable {K : Type*} [Group K] [Fintype K] [DecidableEq K]

end Lower

section Ram

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (Q : HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)] [Fintype (Q.asIdeal.inertia G)]

omit [IsDedekindDomain R] [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [MulSemiringAction G L] [Finite (S ⧸ Q.asIdeal)]
  [Fintype (Q.asIdeal.inertia G)] in
theorem adicAdd_algebraMap_eq {x : S} (hx : x ≠ 0) :
    Swan.adicAdd Q (algebraMap S L x) = ((ordI Q (Ideal.span {x}) : ℤ) : WithTop ℤ) := by
  refine Swan.withTop_eq_of_natCast_le_iff (Swan.adicAdd_algebraMap_nonneg Q x)
    (WithTop.coe_nonneg.2 (Int.natCast_nonneg _)) fun n => ?_
  rw [Swan.natCast_le_adicAdd_algebraMap_iff, ← le_ordI_span_iff Q hx, ← WithTop.coe_natCast,
    WithTop.coe_le_coe, Int.ofNat_le]

omit [IsDedekindDomain R] [Module.Finite R S] [Module.IsTorsionFree R S]
  [Fintype (Q.asIdeal.inertia G)] in
include hc in
/-- `i_Q(σ) = v_Q(σ ϖ - ϖ)` for `σ ≠ 1` in the inertia group. -/
theorem ramFn_i_eq_ordI {ϖ : S} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2)
    (σ : Q.asIdeal.inertia G) (hσ : σ ≠ 1) :
    (Swan.inertiaLocData (R := R) hc Q).ramFn.i σ = ordI Q (Ideal.span {ϖ - (σ : G) • ϖ}) := by
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    exact h2 (Ideal.zero_mem _)
  have hv : (Swan.inertiaLocData (R := R) hc Q).v (algebraMap S L ϖ) = 1 := by
    rw [Swan.inertiaLocData_v, adicAdd_algebraMap_eq Q hϖ, ordI_span_eq_one Q h1 h2]
    rfl
  rw [Swan.LocData.ramFn_i_of_unif _ hv, Subgroup.smul_def, hc, ← map_sub, Swan.inertiaLocData_v]
  by_cases h0 : (σ : G) • ϖ - ϖ = 0
  · exfalso
    apply (Swan.inertiaLocData (R := R) hc Q).ramFn.i_ne_top hσ
    rw [Swan.LocData.ramFn_i_of_unif _ hv, Subgroup.smul_def, hc, ← map_sub, h0, map_zero,
      AddValuation.map_zero, Swan.toENat_top]
  rw [adicAdd_algebraMap_eq Q h0, Swan.toENat_coe, Int.toNat_natCast, ← neg_sub,
    Ideal.span_singleton_neg]

include hc in
/-- Hilbert's formula with the ramification function: `v_Q(𝔇_{S/R}) = ∑_{σ ∈ I_Q, σ ≠ 1} i_Q(σ)`. -/
theorem ordI_differentIdeal_eq_sum_ramFn :
    ordI Q (differentIdeal R S) = ∑ σ ∈ Finset.univ.erase (1 : Q.asIdeal.inertia G),
      ((Swan.inertiaLocData (R := R) hc Q).ramFn.i σ).toNat := by
  obtain ⟨ϖ, h1, h2⟩ := exists_unif Q
  rw [ordI_differentIdeal (R := R) (G := G) Q h1 h2]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [ramFn_i_eq_ordI hc Q h1 h2 σ (Finset.ne_of_mem_erase hσ), ENat.toNat_natCast]

end Ram

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Hil =====
section

/-!
# S4-GOS-B, part Hil: Hilbert's formula and `e = |I|` on the charts of a Galois extension

For `IsGaloisGroup G K L` (function fields over `Fq`): the ramification function `iQ`, Hilbert's formula for the
different of `Rinf Fq K → Rinf Fq L`, its vanishing on `Rfin` when the finite inertia groups are trivial,
`deg Diff(L/K) = Σ_{Q | ∞} d_Q deg Q`, and `Σ_{Q | R} |I_Q| deg Q = |G| deg R`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

open RamanujanPetersson.Places (Place Divisor Rfin Rinf Oinf)
open RamanujanPetersson.CupDuality

section Ram

variable (L : Type*) [Field L] {G : Type*} [Group G] [MulSemiringAction G L]
variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra S L] [IsFractionRing S L]

/-- The uniformizer at `Q` chosen by `Swan.inertiaLocData`. -/
def unifQ (Q : HeightOneSpectrum S) : L := Classical.choose (Swan.exists_adicAdd_eq_one L Q)

/-- The ramification function `i_Q(σ) = v_Q(σ ϖ_Q - ϖ_Q)` as a natural number. -/
def iQ (σ : G) (Q : HeightOneSpectrum S) : ℕ :=
  (Swan.toENat (Swan.adicAdd (L := L) Q (σ • unifQ L Q - unifQ L Q))).toNat

end Ram

section Hil

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type*) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]
variable [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower Fq[X] K L] [IsScalarTower (RatFunc Fq) K L]
variable (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

open Classical in
/-- **Hilbert's formula** at a place over `∞`: `d_Q = Σ_{σ ∈ I_Q, σ ≠ 1} i_Q(σ)`. -/
theorem ordI_differentIdeal_rinf (Q : HeightOneSpectrum (Rinf Fq L)) :
    letI := actRinf Fq K L G
    ordI Q (differentIdeal (Rinf Fq K) (Rinf Fq L)) =
      ∑ σ ∈ (Finset.univ.erase (1 : G)).filter (· ∈ Q.asIdeal.inertia G), iQ L σ Q := by
  letI := actRinf Fq K L G
  haveI := isGaloisGroup_rinf Fq K L G
  letI : Fintype (Q.asIdeal.inertia G) := Fintype.ofFinite _
  rw [ordI_differentIdeal_eq_sum_ramFn (R := Rinf Fq K) (G := G) (L := L) (fun _ _ => rfl) Q]
  have hmap : (Finset.univ.erase (1 : Q.asIdeal.inertia G)).map (Function.Embedding.subtype _) =
      (Finset.univ.erase (1 : G)).filter (· ∈ Q.asIdeal.inertia G) := by
    ext σ
    simp only [Finset.mem_map, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_filter,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨fun h => hτ (Subtype.ext h), τ.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨σ, h2⟩, fun h => h1 (congrArg Subtype.val h), rfl⟩
  rw [← hmap, Finset.sum_map]
  rfl

/-- `e_Q = |I_Q|` at a place over `∞`. -/
theorem ramificationIdx'_rinf (Q : HeightOneSpectrum (Rinf Fq L)) :
    letI := actRinf Fq K L G
    (Q.under (Rinf Fq K)).asIdeal.ramificationIdx' Q.asIdeal = Nat.card (Q.asIdeal.inertia G) := by
  letI := actRinf Fq K L G
  haveI := isGaloisGroup_rinf Fq K L G
  exact Swan.ramificationIdx'_under_eq_card (A := Rinf Fq K) G Q

/-- The different of `Rfin Fq K → Rfin Fq L` vanishes where the inertia group is trivial. -/
theorem ordI_differentIdeal_rfin_eq_zero (Q : HeightOneSpectrum (Rfin Fq L))
    (hQ : letI := actRfin Fq K L G; Q.asIdeal.inertia G = ⊥) :
    ordI Q (differentIdeal (Rfin Fq K) (Rfin Fq L)) = 0 := by
  classical
  letI := actRfin Fq K L G
  haveI := isGaloisGroup_rfin Fq K L G
  letI : Fintype (Q.asIdeal.inertia G) := Fintype.ofFinite _
  rw [ordI_differentIdeal_eq_sum_ramFn (R := Rfin Fq K) (G := G) (L := L) (fun _ _ => rfl) Q]
  refine Finset.sum_eq_zero fun σ hσ => absurd ?_ (Finset.ne_of_mem_erase hσ)
  exact Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 hQ σ σ.2)

/-- `deg Diff(L/K) = Σ_{Q | ∞} d_Q deg Q` when all finite places are unramified. -/
theorem deg_diffDiv (hfin : letI := actRfin Fq K L G;
      ∀ Q : HeightOneSpectrum (Rfin Fq L), Q.asIdeal.inertia G = ⊥) :
    (diffDiv Fq K L).deg = ∑ Q : HeightOneSpectrum (Rinf Fq L),
      (ordI Q (differentIdeal (Rinf Fq K) (Rinf Fq L)) : ℤ) * Places.deg Fq Q := by
  have := finiteDimensional_ff Fq K L
  have := isSeparable_ff Fq K L
  have h0 : ordDiv (differentIdeal (Rfin Fq K) (Rfin Fq L)) = 0 := by
    ext Q
    rw [ordDiv_apply (differentIdeal_ne_bot' (L := L) (Rfin Fq K) K (Rfin Fq L)),
      ordI_differentIdeal_rfin_eq_zero Fq K L G Q (hfin Q)]
    rfl
  unfold diffDiv
  rw [Places.Divisor.deg_sumElim, h0]
  unfold Places.degS
  rw [Finsupp.sum_zero_index, zero_add, Finsupp.sum_fintype _ _ (fun _ => by simp)]
  exact Finset.sum_congr rfl fun Q _ => by
    rw [ordDiv_apply (differentIdeal_ne_bot' (L := L) (Rinf Fq K) K (Rinf Fq L))]

/-- The fundamental identity at `R | ∞` in inertia form: `Σ_{Q | R} |I_Q| deg Q = |G| deg R`. -/
theorem sum_card_inertia_deg (R : HeightOneSpectrum (Rinf Fq K)) :
    letI := actRinf Fq K L G
    ∑ Q ∈ (finite_under_eq (Rinf Fq K) (B := Rinf Fq L) R).toFinset,
      (Nat.card (Q.asIdeal.inertia G) : ℤ) * (Places.deg Fq Q : ℤ) =
      (Nat.card G : ℤ) * Places.deg Fq R := by
  letI := actRinf Fq K L G
  have := finiteDimensional_ff Fq K L
  have := isSeparable_ff Fq K L
  rw [IsGaloisGroup.card_eq_finrank G K L, ← sum_under_eq_deg Fq (Rinf Fq K) (K := K) (L := L) (B := Rinf Fq L) R]
  exact Finset.sum_congr rfl fun Q _ => by rw [ramificationIdx'_rinf Fq K L G Q]

end Hil

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Tow =====
section

/-!
# S4-GOS-B, part Tow: the global character `Φ` and the tower identity

For `IsGaloisGroup G K L` (function fields over `Fq`, all finite places of `L` unramified over `K`):
`χ_c(F) = 2 ℓ_F(0) - 2 g_F - Σ_{R | ∞} deg R` (`chiC`), the global character
`Φ(1) = χ_c(L)`, `Φ(σ) = Σ_{Q | ∞, σ ∈ I_Q} deg Q (i_Q(σ) - 1)` (`Phi`), and the identity
**`Σ_{σ ∈ G} Φ(σ) = |G| χ_c(K)`** (`sum_Phi_eq`), from Riemann-Hurwitz and Hilbert's different formula.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial IsDedekindDomain Classical

namespace RamanujanPetersson.GOS

open RamanujanPetersson.Places (Place Divisor Rfin Rinf Oinf)
open RamanujanPetersson.RR

section Chi

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

end Chi

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

/-- The global character: `Φ(1) = χ_c(L)`, `Φ(σ) = Σ_{Q | ∞, σ ∈ I_Q} deg Q (i_Q(σ) - 1)` for `σ ≠ 1`. -/
def Phi (σ : G) : ℤ :=
  letI := actRinf Fq K L G
  if σ = 1 then chiC Fq L else
    ∑ Q : HeightOneSpectrum (Rinf Fq L),
      if σ ∈ Q.asIdeal.inertia G then (Places.deg Fq Q : ℤ) * ((iQ L σ Q : ℤ) - 1) else 0

theorem Phi_one : Phi Fq K L G 1 = chiC Fq L := if_pos rfl

theorem Phi_of_ne_one {σ : G} (hσ : σ ≠ 1) :
    letI := actRinf Fq K L G
    Phi Fq K L G σ = ∑ Q : HeightOneSpectrum (Rinf Fq L),
      if σ ∈ Q.asIdeal.inertia G then (Places.deg Fq Q : ℤ) * ((iQ L σ Q : ℤ) - 1) else 0 :=
  if_neg hσ

/-- `Σ_{Q | ∞} |I_Q| deg Q = |G| Σ_{R | ∞} deg R`. -/
theorem sum_card_inertia_deg_all :
    letI := actRinf Fq K L G
    ∑ Q : HeightOneSpectrum (Rinf Fq L), (Nat.card (Q.asIdeal.inertia G) : ℤ) * (Places.deg Fq Q : ℤ) =
      (Nat.card G : ℤ) * ∑ R : HeightOneSpectrum (Rinf Fq K), (Places.deg Fq R : ℤ) := by
  letI := actRinf Fq K L G
  rw [← Finset.sum_fiberwise Finset.univ (fun Q : HeightOneSpectrum (Rinf Fq L) => Q.under (Rinf Fq K)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [← sum_card_inertia_deg Fq K L G R]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext Q
  simp

/-- **The tower identity** `Σ_{σ ∈ G} Φ(σ) = |G| χ_c(K)` (finite places unramified). -/
theorem sum_Phi_eq (hfin : letI := actRfin Fq K L G;
      ∀ Q : HeightOneSpectrum (Rfin Fq L), Q.asIdeal.inertia G = ⊥) :
    ∑ σ : G, Phi Fq K L G σ = (Nat.card G : ℤ) * chiC Fq K := by
  letI := actRinf Fq K L G
  have hRH := riemannHurwitz Fq K L
  rw [deg_diffDiv Fq K L G hfin, ← IsGaloisGroup.card_eq_finrank G K L] at hRH
  have hB := sum_card_inertia_deg_all Fq K L G
  have hrest : ∑ σ ∈ Finset.univ.erase (1 : G), Phi Fq K L G σ =
      ∑ Q : HeightOneSpectrum (Rinf Fq L),
        (ordI Q (differentIdeal (Rinf Fq K) (Rinf Fq L)) : ℤ) * Places.deg Fq Q -
      ∑ Q : HeightOneSpectrum (Rinf Fq L), (Nat.card (Q.asIdeal.inertia G) : ℤ) * (Places.deg Fq Q : ℤ) +
      ∑ Q : HeightOneSpectrum (Rinf Fq L), (Places.deg Fq Q : ℤ) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl fun σ hσ => Phi_of_ne_one Fq K L G (Finset.ne_of_mem_erase hσ), Finset.sum_comm]
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [← Finset.sum_filter, ordI_differentIdeal_rinf Fq K L G Q, Nat.cast_sum]
    have hc := card_filter_erase_inertia Fq K L G Q
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [hc]
    ring
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G)), Phi_one, hrest]
  unfold chiC
  linear_combination (-1 : ℤ) * hRH - hB

end Tow

end RamanujanPetersson.GOS

end

end

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

/-- The global character of `H` on `L / L^H` is the restriction of that of `G`. -/
theorem Phi_subgroup (h : H) : Phi Fq (fixF Fq L G H) L H h = Phi Fq (RatFunc Fq) L G h := by
  unfold Phi
  by_cases h1 : h = 1
  · rw [if_pos h1, if_pos (by rw [h1]; rfl)]
  · have h1' : (h : G) ≠ 1 := fun e => h1 (Subtype.ext e)
    rw [if_neg h1, if_neg h1']
    exact Finset.sum_congr rfl fun Q _ => if_congr (inertia_subgroup_iff Fq L G H h Q) rfl rfl

end TowH

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Lvl =====
section

/-!
# S4-GOS-B, part Lvl: `𝔽_{q^m}`-points as Frobenius-fixed points (O6c, generic)

For an algebraically closed `𝔽_q`-algebra `Ω` and `m > 0`:
* `exists_prim_level_alg`: a primitive `(q^m - 1)`-th root of unity in `Ω`;
* `finrank_levelField_alg`, `finite_levelField_alg`: `[𝔽_{q^m} : 𝔽_q] = m` for `levelField 𝔽_q Ω m`;
* **`card_fixed_eq_card_algHom`**: `#{v : C → Ω | v|_{𝔽_q} = alg, v^{q^m} = v} = #Hom_{𝔽_q}(C, levelField 𝔽_q Ω m)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.GOS

noncomputable section

open CP4a

section Lvl

variable {Fq : Type} [Field Fq] [Fintype Fq] {Ω : Type} [Field Ω] [Algebra Fq Ω]

theorem finrank_levelField_alg [IsAlgClosed Ω] {m : ℕ} (hm : 0 < m) :
    Module.finrank Fq (levelField Fq Ω m) = m := by
  obtain ⟨ζ, hζ⟩ := exists_prim_level_alg (Fq := Fq) (Ω := Ω) hm
  exact finrank_levelField hm hζ

theorem finite_levelField_alg [IsAlgClosed Ω] {m : ℕ} (hm : 0 < m) : Finite (levelField Fq Ω m) := by
  obtain ⟨ζ, hζ⟩ := exists_prim_level_alg (Fq := Fq) (Ω := Ω) hm
  have hc := card_levelField hm hζ
  exact Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ Fintype.card_ne_zero)

/-- **Fixed points as algebra maps into `𝔽_{q^m}`.** -/
theorem card_fixed_eq_card_algHom (C : Type) [CommRing C] [Algebra Fq C] (m : ℕ) :
    Nat.card {v : C →+* Ω // v.comp (algebraMap Fq C) = algebraMap Fq Ω ∧
      ∀ r, v r ^ (Fintype.card Fq ^ m) = v r} = Nat.card (C →ₐ[Fq] levelField Fq Ω m) := by
  refine Nat.card_congr
    { toFun := fun v => toLevelHom v.1 (fun r => mem_levelField.2 (v.2.2 r))
        (fun a => RingHom.congr_fun v.2.1 a)
      invFun := fun φ => ⟨(levelField Fq Ω m).val.toRingHom.comp φ.toRingHom,
        RingHom.ext fun a => by
          show ((φ (algebraMap Fq C a) : levelField Fq Ω m) : Ω) = algebraMap Fq Ω a
          rw [φ.commutes]
          rfl,
        fun r => mem_levelField.1 (φ r).2⟩
      left_inv := fun v => Subtype.ext (RingHom.ext fun r => rfl)
      right_inv := fun φ => AlgHom.ext fun r => Subtype.ext rfl }

end Lvl

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_Bij =====
section

/-!
# S4-GOS-B, part Bij: the Frobenius of the perfect complex is bijective

* `frob1_surjective`: `frob1 ψ t h` is onto for bijective `t` (explicit right inverse via `frob1_comp`);
* `frobPC_surjective`: every `frobPC Λ π Γ I ψ t h hI i` is onto (bijective `t`, exact boundary conjugation);
* **`frobPC_bijective_true`**: for the true boundary data of any `ψ` and finite `Λ`, every `frobPC` is bijective.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace RamanujanPetersson.GOS

open CurveCoh PerfectCx Lefschetz CupDuality

section Gen

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M)
variable (Γ : Subgroup G) [Γ.Normal] {S : Type}

end Gen

section PC

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)
  (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

theorem regRep_surjective : Function.Surjective (regRep Λ π ψ) := fun y =>
  ⟨regRep Λ π ψ⁻¹ y, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩

end PC

section True

open Places CP4a
open scoped Polynomial

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

end True

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_B1a =====
section

/-!
# S4-GOS-C, part B1a: idempotents of `End(Y)[C]` and traces on projective modules (abelian `C`)

For a finite commutative group `C`, a free finite `Λ`-module `Y` with a `C`-representation `ρ` and a Higman element `E`
(`∑ c, ρ c ∘ E ∘ ρ c⁻¹ = id`):
* `tauC c x = Tr(x_c)` is a trace functional on `R = End(Y)[C]` (`tauC_mul_comm`, `tauC_conj`);
* `eRep ρ E = ∑ c, single c (E * ρ c⁻¹)` is idempotent (`eRep_idem`) and `Tr(ρ g) = |C| τ_{g⁻¹}(eRep)`
  (`trace_eq_card_tauC`);
* idempotents congruent modulo a central nilpotent are conjugate (`exists_unit_conj_of_idem`), and
  `single b 1 - 1` is nilpotent when `b` has `l`-power order and `l ^ N = 0` in `Λ` (`isNilpotent_z`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open HattoriStallings MonoidAlgebra

section Ring

end Ring

section Alg

variable {Λ : Type*} [CommRing Λ] {Y : Type*} [AddCommGroup Y] [Module Λ Y] [Module.Free Λ Y]
  [Module.Finite Λ Y] {C : Type*} [Group C] [Fintype C]

theorem higman_mul {ρ : Representation Λ C Y} {E : Y →ₗ[Λ] Y} (hE : IsHigman ρ E) :
    ∑ h : C, ρ h * (E * ρ h⁻¹) = 1 := hE

theorem higman_inv {ρ : Representation Λ C Y} {E : Y →ₗ[Λ] Y} (hE : IsHigman ρ E) :
    ∑ h : C, ρ h⁻¹ * (E * ρ h) = 1 := by
  rw [← higman_mul hE]
  exact Fintype.sum_equiv (Equiv.inv C) _ _ (fun h => by simp)

theorem eRep_idem (hC : ∀ a b : C, a * b = b * a) {ρ : Representation Λ C Y} {E : Y →ₗ[Λ] Y}
    (hE : IsHigman ρ E) : IsIdempotentElem (eRep ρ E) := by
  unfold IsIdempotentElem
  ext1
  ext1 c
  rw [coeff_mul_fintype, eRep_coeff]
  have hh : ∀ h : C, (eRep ρ E).coeff h * (eRep ρ E).coeff (h⁻¹ * c) =
      E * (ρ h⁻¹ * (E * ρ h)) * ρ c⁻¹ := by
    intro h
    rw [eRep_coeff, eRep_coeff, mul_inv_rev, inv_inv, hC c⁻¹ h, map_mul ρ]
    simp only [mul_assoc]
  calc _ = ∑ h : C, E * (ρ h⁻¹ * (E * ρ h)) * ρ c⁻¹ := Fintype.sum_congr _ _ hh
    _ = E * (∑ h : C, ρ h⁻¹ * (E * ρ h)) * ρ c⁻¹ := by rw [Finset.mul_sum, Finset.sum_mul]
    _ = E * ρ c⁻¹ := by rw [higman_inv hE, mul_one]

theorem trace_eq_card_tauC (hC : ∀ a b : C, a * b = b * a) {ρ : Representation Λ C Y} {E : Y →ₗ[Λ] Y}
    (hE : IsHigman ρ E) (g : C) :
    LinearMap.trace Λ Y (ρ g) = (Fintype.card C : Λ) * tauC g⁻¹ (eRep ρ E) := by
  unfold tauC
  rw [eRep_coeff, inv_inv]
  have h2 : ∀ h : C, LinearMap.trace Λ Y (ρ g * (ρ h * (E * ρ h⁻¹))) =
      LinearMap.trace Λ Y (E * ρ g) := by
    intro h
    have e1 : ρ g * (ρ h * (E * ρ h⁻¹)) = (ρ g * ρ h * E) * ρ h⁻¹ := by simp only [mul_assoc]
    rw [e1, LinearMap.trace_mul_comm Λ (ρ g * ρ h * E) (ρ h⁻¹), ← mul_assoc, ← mul_assoc,
      ← map_mul ρ, ← map_mul ρ, hC h⁻¹ g, inv_mul_cancel_right, LinearMap.trace_mul_comm Λ (ρ g) E]
  calc LinearMap.trace Λ Y (ρ g) = LinearMap.trace Λ Y (∑ h : C, ρ g * (ρ h * (E * ρ h⁻¹))) := by
        rw [← Finset.mul_sum, higman_mul hE, mul_one]
    _ = ∑ h : C, LinearMap.trace Λ Y (E * ρ g) := by rw [map_sum]; exact Fintype.sum_congr _ _ h2
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Alg

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_B1b =====
section

/-!
# S4-GOS-C, part B1b: the conjugation argument and restriction of Higman elements

* `exists_sub_mapDomain`: if `φ x = x b^{j(x)}` then `φ_* x - x ∈ R (single b 1 - 1)` in `R = End(Y)[C]`;
* `tauC_eq_tauC_map`: `τ_c(e) = τ_c(φ_* e)` for an idempotent `e` (conjugate idempotents, `exists_unit_conj_of_idem`);
* **`trace_eq_zero_of_proj`**: `Tr(ρ g) = 0` when `g⁻¹ ∉ range φ` (abelian `C`, Higman element `E`);
* `isHigman_res`: restriction of a Higman element to a subgroup (`E_C = ∑_{q ∈ G/C} ρ q⁻¹ ∘ E ∘ ρ q`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open HattoriStallings MonoidAlgebra

section Alg

variable {Λ : Type*} [CommRing Λ] {Y : Type*} [AddCommGroup Y] [Module Λ Y] [Module.Free Λ Y]
  [Module.Finite Λ Y] {C : Type*} [Group C] [Fintype C]

/-- **Traces of elements outside the `l'`-part vanish on projective modules** (abelian group, abstract form). -/
theorem trace_eq_zero_of_proj {l a N : ℕ} (hl : l.Prime) (hC : ∀ a b : C, a * b = b * a)
    {ρ : Representation Λ C Y} {E : Y →ₗ[Λ] Y} (hE : IsHigman ρ E) (hΛ : ((l ^ N : ℕ) : Λ) = 0)
    (φ : C →* C) {b : C} (hb : b ^ (l ^ a) = 1) (hφ : ∀ x : C, ∃ j : ℕ, φ x = x * b ^ j) (g : C)
    (hg : g⁻¹ ∉ Set.range φ) : LinearMap.trace Λ Y (ρ g) = 0 := by
  rw [trace_eq_card_tauC hC hE, tauC_eq_tauC_map hl hC hΛ φ hb hφ (eRep_idem hC hE),
    tauC_map_eq_zero φ _ hg, mul_zero]

end Alg

section Res

variable {Λ : Type*} [CommRing Λ] {Y : Type*} [AddCommGroup Y] [Module Λ Y] [Module.Free Λ Y]
  [Module.Finite Λ Y] {G : Type*} [Group G] [Fintype G]

theorem isHigman_res {ρ : Representation Λ G Y} {E : Y →ₗ[Λ] Y} (hE : IsHigman ρ E) (C : Subgroup G)
    [Fintype C] [Fintype (G ⧸ C)] :
    IsHigman (ρ.comp C.subtype) (∑ q : G ⧸ C, ρ (q.out)⁻¹ * (E * ρ q.out)) := by
  show ∑ c : C, ρ c * ((∑ q : G ⧸ C, ρ (q.out)⁻¹ * (E * ρ q.out)) * ρ ((c⁻¹ : C) : G)) = 1
  calc _ = ∑ c : C, ∑ q : G ⧸ C, ρ (quotProdEquiv C (q, c⁻¹))⁻¹ * (E * ρ (quotProdEquiv C (q, c⁻¹))) := by
        refine Fintype.sum_congr _ _ (fun c => ?_)
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Fintype.sum_congr _ _ (fun q => ?_)
        simp only [quotProdEquiv, Equiv.coe_fn_mk, mul_inv_rev, map_mul, InvMemClass.coe_inv, inv_inv, mul_assoc]
    _ = ∑ c : C, ∑ q : G ⧸ C, ρ (quotProdEquiv C (q, c))⁻¹ * (E * ρ (quotProdEquiv C (q, c))) :=
        Fintype.sum_equiv (Equiv.inv C) _ _ (fun _ => rfl)
    _ = ∑ g : G, ρ g⁻¹ * (E * ρ g) := by
        rw [← Equiv.sum_comp (quotProdEquiv C), Fintype.sum_prod_type_right]
    _ = 1 := higman_inv hE

end Res

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_TLIFT =====
section

/-!
# S4-GOS-C, part TLIFT: reductions, `1 ⊗ q = 0`, and tensor products of lifts

For `Λ → Λ'` onto with kernel `t Λ`:
* **`ker_one_tmul`**: `1 ⊗ₜ q = 0` in `Λ' ⊗[Λ] Q` forces `q ∈ t • Q` (via `Λ' ≅ Λ ⧸ ker`, `quotTensorEquivQuotSMul`);
* **`exists_tensor_lift`**: if `fP : P → P'`, `fM : M → M'` are onto with kernels in `t •`, there is a `Λ`-linear
  `T : P ⊗[Λ] M → P' ⊗[Λ'] M'` with `T (p ⊗ m) = fP p ⊗ fM m`, onto, with kernel in `t •`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.GOS

open TensorProduct

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ']

variable {P P' M M' : Type} [AddCommGroup P] [Module Λ P] [AddCommGroup P'] [Module Λ' P'] [Module Λ P']
  [IsScalarTower Λ Λ' P'] [AddCommGroup M] [Module Λ M] [AddCommGroup M'] [Module Λ' M'] [Module Λ M']
  [IsScalarTower Λ Λ' M']

/-- **Tensor products of lifts are lifts.** -/
theorem exists_tensor_lift (t : Λ) (hsurj : Function.Surjective (algebraMap Λ Λ')) (ht : algebraMap Λ Λ' t = 0)
    (hker : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = t * s)
    (fP : P →ₗ[Λ] P') (hfP : Function.Surjective fP) (hkP : ∀ x, fP x = 0 → ∃ y, x = t • y)
    (fM : M →ₗ[Λ] M') (hfM : Function.Surjective fM) (hkM : ∀ x, fM x = 0 → ∃ y, x = t • y) :
    ∃ T : P ⊗[Λ] M →ₗ[Λ] P' ⊗[Λ'] M', (∀ p m, T (p ⊗ₜ m) = fP p ⊗ₜ fM m) ∧ Function.Surjective T ∧
      (∀ x, T x = 0 → ∃ y, x = t • y) := by
  let eP := PerfectCx.redEquiv t hsurj ht fP hfP hkP
  let eM := PerfectCx.redEquiv t hsurj ht fM hfM hkM
  let Ψ : Λ' ⊗[Λ] (P ⊗[Λ] M) ≃ₗ[Λ'] P' ⊗[Λ'] M' :=
    (AlgebraTensorModule.distribBaseChange Λ Λ' P M).trans (TensorProduct.congr eP eM)
  refine ⟨(Ψ.toLinearMap.restrictScalars Λ) ∘ₗ TensorProduct.mk Λ Λ' (P ⊗[Λ] M) 1, fun p m => ?_,
    fun y => ?_, fun x hx => ?_⟩
  · show Ψ (1 ⊗ₜ (p ⊗ₜ m)) = fP p ⊗ₜ fM m
    simp only [Ψ, LinearEquiv.trans_apply, AlgebraTensorModule.distribBaseChange_tmul,
      TensorProduct.congr_tmul]
    rw [PerfectCx.redEquiv_one_tmul, PerfectCx.redEquiv_one_tmul]
  · obtain ⟨u, rfl⟩ := Ψ.surjective y
    obtain ⟨x, rfl⟩ := PerfectCx.exists_one_tmul_of_surj hsurj u
    exact ⟨x, rfl⟩
  · refine ker_one_tmul hsurj hker x ?_
    have hx' : Ψ (1 ⊗ₜ x) = 0 := hx
    exact (LinearEquiv.map_eq_zero_iff Ψ).mp hx'

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_EUL =====
section

/-!
# S4-GOS-C, part EUL: the Euler characteristic of the perfect complex is `h²_c - h¹_c`

`finrank_euler3`: for a complex `K⁰ → K¹ → K²` of finite-dimensional spaces with `d⁰` injective,
`dim K⁰ - dim K¹ + dim K² = dim H² - dim H¹`. With the term isomorphisms `pcIso0/1/2`, `H¹ = H¹_c` (`hc1Equiv`) and
`H² ≅ H²_c` (`h2Equiv_lisse`): **`chi_eq_h2c_sub_h1c`**: `Σ_i (-1)^i dim (PC i ⊗ M)_{Gf} = h²_c(M) - h¹_c(M)` over `ℤ/l`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Lefschetz

section Dim

variable {k : Type*} [Field k] {K0 K1 K2 : Type*} [AddCommGroup K0] [Module k K0] [AddCommGroup K1]
  [Module k K1] [AddCommGroup K2] [Module k K2] [FiniteDimensional k K0] [FiniteDimensional k K1]
  [FiniteDimensional k K2]

/-- Euler characteristic of a three-term complex with injective first map. -/
theorem finrank_euler3 (d0 : K0 →ₗ[k] K1) (d1 : K1 →ₗ[k] K2) (hd : ∀ x, d1 (d0 x) = 0)
    (hinj : Function.Injective d0) :
    (Module.finrank k K0 : ℤ) - Module.finrank k K1 + Module.finrank k K2 =
      (Module.finrank k (K2 ⧸ LinearMap.range d1) : ℤ) - Module.finrank k (Lefschetz.Hc1 d0 d1 hd) := by
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range d1)
  have h2 : Module.finrank k (Lefschetz.Hc1 d0 d1 hd) +
      Module.finrank k (LinearMap.range (Lefschetz.d0Z d0 d1 hd)) = Module.finrank k (LinearMap.ker d1) :=
    Submodule.finrank_quotient_add_finrank _
  have h3 := LinearMap.finrank_range_add_finrank_ker d1
  have hinjZ : Function.Injective (Lefschetz.d0Z d0 d1 hd) := fun x y h => hinj (congrArg Subtype.val h)
  have h4 := LinearMap.finrank_range_of_inj hinjZ
  omega

end Dim

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_C_RAT =====
section

/-!
# S4-GOS-C, part RAT: the projective line `𝔽_q(x)`

For `F = 𝔽_q(x)`: `Σ_{P | ∞} ord_P(1/x) deg P = 1` (`degS_rat`), so there is exactly one place over `∞`
(`Subsingleton`), of degree one (`deg_PinfR`); `ℓ(0) = 1` (`ellF_zero_rat`); polynomials of degree `≤ k` lie in
`L(k P_∞)` (`le_ellF_DkR`), so Riemann-Roch gives **`genus_rat : g = 0`** and **`chiC_rat : χ_c(𝔸¹) = 1`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

noncomputable section

open Places ZetaSB RR CP4a.Hyp2

section RAT

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]

theorem deg_DkR (k : ℕ) : (DkR Fq k).deg = k := by
  rw [Places.Divisor.deg_single, Place.deg_inr, deg_PinfR, Nat.cast_one, mul_one]

theorem poly_mem_LF (k : ℕ) {a : Fq[X]} (hk : a.natDegree ≤ k) :
    algebraMap Fq[X] (RatFunc Fq) a ∈ LF Fq (RatFunc Fq) (DkR Fq k) := by
  by_cases ha : a = 0
  · rw [ha, map_zero]; exact zero_mem _
  have hinj := IsFractionRing.injective Fq[X] (RatFunc Fq)
  rw [mem_LF ((map_ne_zero_iff _ hinj).mpr ha), Finsupp.le_def]
  rintro (Q | Q)
  · simpa [DkR] using ord_fin_poly_nonneg Fq Q a
  · rw [Subsingleton.elim Q (PinfR Fq)]
    have := ord_inf_poly_ge Fq (PinfR Fq) k ha hk
    simp [DkR]
    omega

/-- `ℓ(k P_∞) ≥ k + 1`. -/
theorem le_ellF_DkR (k : ℕ) : k + 1 ≤ ellF Fq (RatFunc Fq) (DkR Fq k) := by
  have hle : LinearMap.range (polyLin Fq k) ≤ LF Fq (RatFunc Fq) (DkR Fq k) := by
    rintro _ ⟨a, rfl⟩
    refine poly_mem_LF Fq k ?_
    show (a : Fq[X]).natDegree ≤ k
    by_cases ha : (a : Fq[X]) = 0
    · rw [ha, natDegree_zero]; exact Nat.zero_le _
    have h := mem_degreeLT.mp a.2
    rw [degree_eq_natDegree ha] at h
    have : (a : Fq[X]).natDegree < k + 1 := by exact_mod_cast h
    omega
  have := finiteDimensional_LF (Fq := Fq) (F := RatFunc Fq) (DkR Fq k)
  have h := Submodule.finrank_mono hle
  rw [LinearMap.finrank_range_of_inj (polyLin_injective Fq k), (degreeLTEquiv Fq (k + 1)).finrank_eq,
    Module.finrank_fin_fun] at h
  exact h

/-- **`𝔽_q(x)` has genus 0.** -/
theorem genus_rat : genusF Fq (RatFunc Fq) = 0 := by
  have h := ellF_eq_of_deg (constField_rat Fq) (D := DkR Fq (2 * genusF Fq (RatFunc Fq) + 1))
    (by rw [deg_DkR]; push_cast; omega)
  have h2 := le_ellF_DkR Fq (2 * genusF Fq (RatFunc Fq) + 1)
  rw [deg_DkR] at h
  push_cast at h
  omega

/-- **`χ_c(𝔸¹) = 1`.** -/
theorem chiC_rat : chiC Fq (RatFunc Fq) = 1 := by
  rw [chiC, ellF_zero_rat, genus_rat, sum_deg_rat]
  norm_num

end RAT

end

end RamanujanPetersson.GOS


end


