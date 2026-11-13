-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1
-- name    : OddOrder_Peterfalvi_S08_CoherenceCorePart1
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:17:17.798551+00:00
-- url     : https://prove2.me/theorems/0aa2e1da-6dda-448d-98d7-baa8b86ace14
-- title:
--   Peterfalvi §8: degree arithmetic and the Sibley–Dade carrier
-- statement:
--   Degree arithmetic, $p$-group recognition, and the Sibley–Dade carrier for the Peterfalvi §8 coherence proof, together with the generic enumeration primitive `exists_finEnum_general` for finite sets of class functions, consumed by both the case-(B) machinery and the general (6.2) leaf.
--
--   The main definition is `SibleyDadeHypothesis` (Peterfalvi (6.8): the Dade-based carrier, a faithful replacement for the Sibley hypothesis).
--
--   The bundle also proves 24 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CoherenceCorePart1.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CoherenceCorePart1.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ChiefFactor
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1_CoherentAdjoin

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

/-- **Peterfalvi (6.3) degree-bound arithmetic core.**  The real/integer inequality at the heart of
Theorem (6.3) (mmd 04.8 L33): from the (6.2) consequence `b·x − 1 ≤ 2·a·b·√x` (with `a = |L:K|`,
`b = |K:H| ≥ 1`, `x = |H:A| ≥ 1`) one gets `x ≤ 4a² + 1`.

Proof: dividing by `b` and using `b ≥ 1` gives `x − 1 ≤ 2a√x`; squaring (`x − 1 ≥ 0`) gives
`(x − 1)² ≤ 4a²x`, i.e. `x² − (4a² + 2)x + 1 ≤ 0`; for a natural `x`, `x ≥ 4a² + 2` would give
`x² − (4a² + 2)x + 1 = x·(x − (4a² + 2)) + 1 ≥ 1 > 0`, a contradiction.  This is what (6.3) combines
with its hypothesis `|H:H₁| > 4|L:K|² + 1 ≤ x` to reach a contradiction (so `𝒮(M)` is coherent). -/
theorem degreeBound_le_of_sqrt_bound {a b x : ℕ} (hb : 1 ≤ b) (hx : 1 ≤ x)
    (h : (b : ℝ) * x - 1 ≤ 2 * a * b * Real.sqrt x) : x ≤ 4 * a ^ 2 + 1 := by
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hsx : Real.sqrt x ^ 2 = (x : ℝ) := Real.sq_sqrt hx0
  have hsx0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  -- `x − 1 ≤ 2a√x` (divide `h` by `b`, drop `1/b ≤ 1`).
  have key : (x : ℝ) - 1 ≤ 2 * a * Real.sqrt x := by
    have hbx : (b : ℝ) * ((x : ℝ) - 1) ≤ (b : ℝ) * (2 * a * Real.sqrt x) := by
      have e1 : (b : ℝ) * ((x : ℝ) - 1) = (b : ℝ) * x - b := by ring
      have e2 : (b : ℝ) * (2 * a * Real.sqrt x) = 2 * a * b * Real.sqrt x := by ring
      rw [e1, e2]; nlinarith [h, hb1]
    exact le_of_mul_le_mul_left hbx hbpos
  -- `(x − 1)² ≤ (2a√x)² = 4a²x`.
  have hkey0 : (0 : ℝ) ≤ (x : ℝ) - 1 := by linarith
  have hrhs0 : (0 : ℝ) ≤ 2 * a * Real.sqrt x := by positivity
  have hsq : ((x : ℝ) - 1) ^ 2 ≤ 4 * (a : ℝ) ^ 2 * x := by
    have hprod := mul_le_mul key key hkey0 hrhs0
    have hrw : (2 * (a : ℝ) * Real.sqrt x) * (2 * (a : ℝ) * Real.sqrt x) = 4 * (a : ℝ) ^ 2 * x := by
      rw [show (2 * (a : ℝ) * Real.sqrt x) * (2 * (a : ℝ) * Real.sqrt x)
          = 4 * (a : ℝ) ^ 2 * (Real.sqrt x * Real.sqrt x) by ring, Real.mul_self_sqrt hx0]
    rw [hrw] at hprod
    nlinarith [hprod]
  -- `x² − 2x + 1 ≤ 4a²x` gives `x² < (4a²+2)x`, so `x < 4a²+2`, i.e. `x ≤ 4a²+1`.
  have hxlt : (x : ℝ) < 4 * (a : ℝ) ^ 2 + 2 := by
    have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
    nlinarith [hsq, hxpos]
  have hxltN : x < 4 * a ^ 2 + 2 := by exact_mod_cast hxlt
  omega

/-- **Peterfalvi (6.5)(a) chief-factor arithmetic.**  If `c` and `a` are odd, `c ∣ a − 1`, and
`a > 1`, then `a ≥ 2c + 1` (mmd 04.8 L40).  Indeed `a − 1 = c·m` is even (as `a` is odd) and `c` is
odd, so `m` is even and nonzero, hence `m ≥ 2` and `a − 1 = c·m ≥ 2c`.

This is the step in (6.5)(a) ruling out an intermediate normal subgroup `H₁ ⊊ H₂ ⊊ K`: with
`a = |K : H₂|` (odd, dividing the odd `|L|`) and `c = |L : K|`, hypothesis (6.4.c) gives
`c ∣ a − 1`,
so `|K : H₂| ≥ 2|L : K| + 1`; likewise `|H₂ : H₁| ≥ 2|L : K| + 1`, whence
`|K : H₁| ≥ (2|L : K| + 1)² > 4|L : K|² + 1`, contradicting the (6.3) bound. -/
theorem two_mul_add_one_le_of_odd_dvd {c a : ℕ} (hc : Odd c) (ha : Odd a) (hdvd : c ∣ a - 1)
    (ha1 : 1 < a) : 2 * c + 1 ≤ a := by
  obtain ⟨m, hm⟩ := hdvd
  have hcodd : c % 2 = 1 := Nat.odd_iff.mp hc
  have haodd : a % 2 = 1 := Nat.odd_iff.mp ha
  have hmeven : m % 2 = 0 := by
    have h1 : (c * m) % 2 = 0 := by
      have h2 : (a - 1) % 2 = 0 := by omega
      rwa [hm] at h2
    rw [Nat.mul_mod, hcodd, one_mul] at h1
    omega
  have hm2 : 2 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hz | hpos
    · rw [hz, mul_zero] at hm; omega
    · omega
  have h2c : 2 * c ≤ c * m := by nlinarith [hm2]
  omega

/-- **Peterfalvi (6.3)** index reduction.  From the degree bound (6.2) applied
with `C = H, D = A`, in index form `|K:H|·|H:A| − 1 ≤ 2·|L:K|·|K:H|·√|H:A|`,
together with `|H:H₁| ≤ |H:A|` (from `A ⊆ H₁`), the index `|H:H₁|` is at most
`4|L:K|² + 1`.  (Peterfalvi states the contrapositive: `|H:H₁| > 4|L:K|² + 1`
forces `S(M)` coherent.)  The `√`-manipulation is `degreeBound_le_of_sqrt_bound`
with `a = |L:K|, b = |K:H|, x = |H:A|`. -/
theorem six_three_HH1_le {LK KH HA HH1 : ℕ} (hKH : 1 ≤ KH) (hHH1le : HH1 ≤ HA)
    (hbound : (KH : ℝ) * (HA : ℝ) - 1 ≤ 2 * (LK : ℝ) * (KH : ℝ) * Real.sqrt (HA : ℝ)) :
    HH1 ≤ 4 * LK ^ 2 + 1 := by
  rcases Nat.eq_zero_or_pos HA with hHA0 | hHA
  · subst hHA0; omega
  · have hx := degreeBound_le_of_sqrt_bound hKH hHA hbound
    omega

/-- Arithmetic core of **Peterfalvi (6.5)(a),(c)**: since
`(2c+1)² = 4c²+4c+1 > 4c²+1` for `c ≥ 1`, an index `n` cannot satisfy both
`(2c+1)² ≤ n` and `n ≤ 4c²+1`. -/
theorem six_five_index_contradiction {LK n : ℕ} (hLK : 1 ≤ LK)
    (hge : (2 * LK + 1) * (2 * LK + 1) ≤ n) (hle : n ≤ 4 * LK ^ 2 + 1) : False := by
  nlinarith [hge, hle, hLK]

/-- **Peterfalvi (6.5)(a)** chief-factor step.  If a normal subgroup `H₂` sits
strictly between `H₁` and `K`, then (6.4.c) + odd order force
`|K:H₂|, |H₂:H₁| ≥ 2|L:K|+1` (via `two_mul_add_one_le_of_odd_dvd`), so
`|K:H₁| = |K:H₂|·|H₂:H₁| ≥ (2|L:K|+1)² > 4|L:K|²+1`, contradicting the (6.3)
bound `|K:H₁| ≤ 4|L:K|²+1`.  Hence `K/H₁` is a chief factor of `L`. -/
theorem six_five_chief_factor_contradiction {LK KH2 H2H1 KH1 : ℕ} (hLK : 1 ≤ LK)
    (hKH2 : 2 * LK + 1 ≤ KH2) (hH2H1 : 2 * LK + 1 ≤ H2H1)
    (hmul : KH1 = KH2 * H2H1) (hKH1le : KH1 ≤ 4 * LK ^ 2 + 1) :
    False :=
  six_five_index_contradiction hLK
    (by rw [hmul]; exact Nat.mul_le_mul hKH2 hH2H1) hKH1le

/-- **Extension of `p`-groups is a `p`-group.**  If a normal subgroup `N` and the quotient `Γ ⧸ N`
are both `p`-groups (and `Γ` is finite), then `Γ` is a `p`-group: `|Γ| = |Γ ⧸ N|·|N| = p^b·p^a`
(Lagrange, `card_eq_card_quotient_mul_card_subgroup`), so `|Γ|` is a `p`-power
(`IsPGroup.iff_card`).

A general group-theory brick; used by Peterfalvi (6.5)(b) to assemble "`K/M` is a `p`-group" from
its commutator subgroup `H₁/M` and the chief factor `K/H₁` (a `p`-group). -/
theorem isPGroup_of_quotient_of_subgroup {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ] [Finite Γ]
    {N : Subgroup Γ} [N.Normal] (hN : IsPGroup p ↥N) (hQ : IsPGroup p (Γ ⧸ N)) :
    IsPGroup p Γ := by
  rw [IsPGroup.iff_card] at hN hQ ⊢
  obtain ⟨a, ha⟩ := hN
  obtain ⟨b, hb⟩ := hQ
  exact ⟨b + a, by rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hb, ha, pow_add]⟩

/-- `Abelianization.map` of a surjective homomorphism is surjective. -/
theorem Abelianization.map_surjective {Γ Δ : Type*} [Group Γ] [Group Δ] {f : Γ →* Δ}
    (hf : Function.Surjective f) : Function.Surjective (Abelianization.map f) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | _ b =>
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨Abelianization.of a, Abelianization.map_of f a⟩

/-- A finite `p`-group whose order is coprime to `p` is trivial. -/
theorem subsingleton_of_isPGroup_of_not_dvd {p : ℕ} [Fact p.Prime] {Δ : Type*} [Group Δ] [Finite Δ]
    (hΔ : IsPGroup p Δ) (hnd : ¬ p ∣ Nat.card Δ) : Subsingleton Δ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hΔ
  have hk0 : k = 0 := by
    by_contra hk0
    exact hnd (by rw [hk]; exact dvd_pow_self p hk0)
  rw [hk0, pow_zero] at hk
  exact (Nat.card_eq_one_iff_unique.mp hk).1

/-- **Peterfalvi (6.5)(b) reduction core: a finite nilpotent group with `p`-group abelianization is
a `p`-group.**

Let `P` be the Sylow `p`-subgroup, normal since `Γ` is nilpotent.  The quotient `Q = Γ ⧸ P` has
order
`[Γ:P]` coprime to `p`, so `Abelianization Q` — both a `p`-group (a homomorphic image of
`Abelianization Γ`, `Abelianization.map` of `Γ ↠ Q`) and of order dividing `[Γ:P]` — is trivial.
Hence `Q` is perfect (`commutator Q = ⊤`); being nilpotent (a quotient of `Γ`) and hence solvable,
it
is therefore trivial (`commutator_lt_top` for a nontrivial solvable group).  So `P = ⊤` and `Γ` is a
`p`-group (`isPGroup_of_quotient_of_subgroup`).

This is the (6.5)(b) step "since `K/M` is nilpotent with commutator `H₁/M` and `K/H₁` a chief
factor,
`K/M` is a `p`-group" (mmd 04.8 L45). -/
theorem isPGroup_of_isNilpotent_of_isPGroup_abelianization {p : ℕ} [Fact p.Prime]
    {Γ : Type*} [Group Γ] [Finite Γ] [Group.IsNilpotent Γ]
    (h : IsPGroup p (Abelianization Γ)) : IsPGroup p Γ := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow p Γ) := inferInstance
  have hPnormal : (↑P : Subgroup Γ).Normal := by
    have htfae := (Group.isNilpotent_of_finite_tfae (G := Γ)).out 0 3
    exact htfae.mp ‹_› p ‹_› P
  -- `Abelianization Q` is a `p`-group (image of `Abelianization Γ`).
  have hQab_p : IsPGroup p (Abelianization (Γ ⧸ (↑P : Subgroup Γ))) :=
    h.of_surjective _ (Abelianization.map_surjective (QuotientGroup.mk'_surjective _))
  -- ... and trivial: its order divides `Nat.card Q = [Γ:P]`, coprime to `p`.
  have hofsurj : Function.Surjective (Abelianization.of :
      (Γ ⧸ (↑P : Subgroup Γ)) →* Abelianization (Γ ⧸ (↑P : Subgroup Γ))) :=
    fun y => QuotientGroup.induction_on y fun a => ⟨a, rfl⟩
  have hQab_triv : Subsingleton (Abelianization (Γ ⧸ (↑P : Subgroup Γ))) :=
    subsingleton_of_isPGroup_of_not_dvd hQab_p
      (fun hp => P.not_dvd_index (hp.trans (Subgroup.card_dvd_of_surjective _ hofsurj)))
  -- `Abelianization Q` trivial ⟹ `commutator Q = ⊤` ⟹ (nilpotent ⟹ solvable) `Q` trivial.
  have hQ_triv : Subsingleton (Γ ⧸ (↑P : Subgroup Γ)) := by
    rcases subsingleton_or_nontrivial (Γ ⧸ (↑P : Subgroup Γ)) with hs | hns
    · exact hs
    · exfalso
      have := hns
      have hlt : commutator (Γ ⧸ (↑P : Subgroup Γ)) < ⊤ :=
        Group.IsSolvable.commutator_lt_top_of_nontrivial (G := Γ ⧸ (↑P : Subgroup Γ))
      refine absurd ?_ hlt.ne
      rw [← Subgroup.index_eq_one]
      exact @Nat.card_of_subsingleton (Abelianization (Γ ⧸ (↑P : Subgroup Γ))) 1 hQab_triv
  -- `Q` trivial ⟹ `Γ` is a `p`-group (Sylow `P` is `p`, quotient `Q` trivially `p`).
  refine isPGroup_of_quotient_of_subgroup P.isPGroup' ?_
  rw [IsPGroup.iff_card]
  exact ⟨0, by rw [pow_zero]; exact @Nat.card_of_subsingleton (Γ ⧸ (↑P : Subgroup Γ)) 1 hQ_triv⟩

/-- **Group-theory core of Peterfalvi (6.5)(a),(b): a Frobenius-acted abelian section obeying the
(6.3) index bound is a `p`-group.**

Let a finite group `R` act on a finite abelian group `A` by automorphisms, *fixed-point-freely*
(`IsFrobeniusAction R A`: no nonidentity `r ∈ R` fixes a nonidentity `a ∈ A`).  If `|A|` and `|R|`
are odd and `|A| ≤ 4|R|² + 1`, then `A` is a `p`-group for some prime `p`.

This is the abstract content of Peterfalvi (6.5).  In the Sibley setting `A = K/H₁` is the
abelianization section and `R = L/K` is the Frobenius complement; (6.5)(a) says `K/H₁` is a chief
factor.  Here the chief-factor argument is run through the `p`-primary component: if `A` had a prime
divisor `p` whose Sylow subgroup `P` were proper (i.e. `A` were not a `p`-group), then `P`
(characteristic in the abelian `A`, hence `R`-invariant) and the quotient index `|A : P|` would both
be nontrivial, odd, and `≡ 1 (mod |R|)` — the first two by Frobenius `card_modEq_one` applied to the
whole action and the restricted action on `P` (`IsFrobeniusAction.subgroup`), the index by the
arithmetic `|A| = |A:P|·|P|`, `|A| ≡ |P| ≡ 1`.  Oddness then forces `|P|, |A:P| ≥ 2|R| + 1`
(`two_mul_add_one_le_of_odd_dvd`), so `|A| = |A:P|·|P| ≥ (2|R|+1)² > 4|R|² + 1`, contradicting the
bound (`six_five_chief_factor_contradiction`).

The `|A| ≤ 4|R|² + 1` bound is the single character-theoretic input ((6.2)/(6.3); in the Sibley
setup supplied by `theta_degree_le_index_mul_sqrt_index`).  Everything else is discharged here. -/
theorem isPGroup_of_card_le_of_isFrobeniusAction {A R : Type*} [CommGroup A] [Finite A]
    [Group R] [Finite R] [MulDistribMulAction R A]
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusAction R A)
    (hAodd : Odd (Nat.card A)) (hRodd : Odd (Nat.card R))
    (hbound : Nat.card A ≤ 4 * Nat.card R ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p A := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have : Fintype R := Fintype.ofFinite R
  by_contra hcon
  -- `A` is nontrivial: a trivial group is a `p`-group for every prime.
  rcases eq_or_ne (Nat.card A) 1 with hA1 | hA1
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hcon ⟨2, Nat.prime_two, IsPGroup.iff_card.mpr ⟨0, by rw [pow_zero, hA1]⟩⟩
  -- Otherwise take a prime divisor `p` of `|A|` and its Sylow `p`-subgroup `P`.
  obtain ⟨p, hp, hpdvd⟩ := (Nat.card A).exists_prime_and_dvd hA1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p A) := inferInstance
  -- `|P| > 1` because `p ∣ |P|`.
  have hpP : p ∣ Nat.card (P : Subgroup A) := P.dvd_card_of_dvd_card hpdvd
  have hcardP : 1 < Nat.card (P : Subgroup A) :=
    lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd Nat.card_pos hpP)
  -- `P` is normal (abelian ambient), hence characteristic.
  have hPnormal : (P : Subgroup A).Normal :=
    ⟨fun n hn g => by
      have heq : g * n * g⁻¹ = n := by rw [mul_comm g n, mul_assoc, mul_inv_cancel, mul_one]
      rw [heq]; exact hn⟩
  have hPchar : (P : Subgroup A).Characteristic := P.characteristic_of_normal hPnormal
  -- `R` acts by automorphisms, which fix the characteristic `P` setwise: `P` is `R`-invariant.
  have hinv : ∀ r : R, ∀ m ∈ (P : Subgroup A), r • m ∈ (P : Subgroup A) := by
    intro r m hm
    have hmap : (P : Subgroup A).map (MulDistribMulAction.toMulAut R A r).toMonoidHom
        = (P : Subgroup A) :=
      Subgroup.characteristic_iff_map_eq.mp hPchar (MulDistribMulAction.toMulAut R A r)
    have hmem : (MulDistribMulAction.toMulAut R A r).toMonoidHom m ∈ (P : Subgroup A) := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  -- `A` not a `p`-group ⟹ `P ≠ ⊤` ⟹ `|A : P| > 1`.
  have hindex : 1 < (P : Subgroup A).index := by
    by_contra hle
    have h : (P : Subgroup A).index ≤ 1 := Nat.not_lt.mp hle
    have hidxpos : 0 < (P : Subgroup A).index := by
      have hmc := Subgroup.index_mul_card (P : Subgroup A)
      rcases Nat.eq_zero_or_pos (P : Subgroup A).index with h0 | h0
      · rw [h0, zero_mul] at hmc; exact absurd hmc.symm Nat.card_pos.ne'
      · exact h0
    have hidx1 : (P : Subgroup A).index = 1 := by omega
    have hPtop : (P : Subgroup A) = ⊤ := Subgroup.index_eq_one.mp hidx1
    have hcardeq : Nat.card (P : Subgroup A) = Nat.card A := by
      rw [hPtop]; exact Nat.card_congr (Subgroup.topEquiv).toEquiv
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
    exact hcon ⟨p, hp, IsPGroup.iff_card.mpr ⟨n, by rw [← hcardeq, hn]⟩⟩
  -- Frobenius `card ≡ 1 (mod |R|)` for the whole action and the restricted action on `P`.
  have : Fintype (P : Subgroup A) := Fintype.ofFinite _
  have hAmod : Nat.card A ≡ 1 [MOD Nat.card R] := by
    simpa only [Fintype.card_eq_nat_card] using hFrob.card_modEq_one
  let instP : MulDistribMulAction R (P : Subgroup A) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantSubgroupMulDistribMulAction
      (P : Subgroup A) hinv
  have hFrobP : @OddOrder.Isaacs.Ch06.IsFrobeniusAction R (P : Subgroup A) _ _ instP :=
    hFrob.subgroup (P : Subgroup A) hinv
  have hPmod : Nat.card (P : Subgroup A) ≡ 1 [MOD Nat.card R] := by
    simpa only [Fintype.card_eq_nat_card] using hFrobP.card_modEq_one
  -- `|R| ∣ |P| - 1` and (via `|A| = |A:P|·|P|`) `|R| ∣ |A:P| - 1`.
  have hRdvdP : Nat.card R ∣ Nat.card (P : Subgroup A) - 1 :=
    (Nat.modEq_iff_dvd' (by omega)).mp hPmod.symm
  have hmul : (P : Subgroup A).index * Nat.card (P : Subgroup A) = Nat.card A :=
    Subgroup.index_mul_card _
  have hidxmod : (P : Subgroup A).index ≡ 1 [MOD Nat.card R] := by
    have h1 : (P : Subgroup A).index * Nat.card (P : Subgroup A)
        ≡ (P : Subgroup A).index * 1 [MOD Nat.card R] := Nat.ModEq.mul_left _ hPmod
    rw [mul_one, hmul] at h1
    exact h1.symm.trans hAmod
  have hRdvdidx : Nat.card R ∣ (P : Subgroup A).index - 1 :=
    (Nat.modEq_iff_dvd' (by omega)).mp hidxmod.symm
  -- Oddness of both factors (they multiply to the odd `|A|`).
  have hAodd' : Odd ((P : Subgroup A).index * Nat.card (P : Subgroup A)) := by
    rw [hmul]; exact hAodd
  obtain ⟨hidxodd, hcardPodd⟩ := Nat.odd_mul.mp hAodd'
  -- Each factor is `≥ 2|R| + 1`; their product exceeds the bound — contradiction.
  have hbP : 2 * Nat.card R + 1 ≤ Nat.card (P : Subgroup A) :=
    two_mul_add_one_le_of_odd_dvd hRodd hcardPodd hRdvdP hcardP
  have hbidx : 2 * Nat.card R + 1 ≤ (P : Subgroup A).index :=
    two_mul_add_one_le_of_odd_dvd hRodd hidxodd hRdvdidx hindex
  exact six_five_chief_factor_contradiction Nat.card_pos hbidx hbP hmul.symm hbound

/-- **Peterfalvi (6.5)(b) reduction: `H` is a `p`-group.**  Assemble the chief-factor core
`isPGroup_of_card_le_of_isFrobeniusAction` (the abelianization `Abelianization H` is a `p`-group)
with `isPGroup_of_isNilpotent_of_isPGroup_abelianization` (a nilpotent group with `p`-group
abelianization is a `p`-group).

Let `H` be a finite nilpotent group whose abelianization `Abelianization H` carries a
fixed-point-free action of a finite group `R` (in the Sibley setting `R = L/H` is the Frobenius
complement acting on `H/H'` by conjugation), with `|Abelianization H|` and `|R|` odd and
`|Abelianization H| ≤ 4|R|² + 1`.  Then `H` is a `p`-group for some prime `p`.

This is the group-theory conclusion of Peterfalvi (6.5) ("we may assume `H` is a non-abelian
`p`-group") in the form the (6.8) capstone consumes; the `≤ 4|R|² + 1` bound is the single
character-theoretic input ((6.2)/(6.3)), and the fixed-point-free `R`-action on `Abelianization H`
is supplied from the Frobenius alternative (6.8)(c1) / (6.4.c). -/
theorem isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization
    {H : Type*} [Group H] [Finite H] [Group.IsNilpotent H]
    {R : Type*} [Group R] [Finite R] [MulDistribMulAction R (Abelianization H)]
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusAction R (Abelianization H))
    (hHodd : Odd (Nat.card (Abelianization H))) (hRodd : Odd (Nat.card R))
    (hbound : Nat.card (Abelianization H) ≤ 4 * Nat.card R ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p H := by
  obtain ⟨p, hp, hPab⟩ :=
    isPGroup_of_card_le_of_isFrobeniusAction hFrob hHodd hRodd hbound
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨p, hp, isPGroup_of_isNilpotent_of_isPGroup_abelianization hPab⟩

/-- **Peterfalvi (6.5)(b) reduction in the Frobenius case (6.8)(c1): the kernel is a `p`-group.**
If `G = N ⋊ A` is a Frobenius group with nilpotent kernel `N`, `|Abelianization N|` and `|A|` are
odd, and `|Abelianization N| ≤ 4|A|² + 1`, then `N` is a `p`-group for some prime `p`.

This is `isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization` with the fixed-point-free
`A`-action on `Abelianization N` supplied directly from the Frobenius group: `A` acts
fixed-point-freely on `N` by conjugation (`toFrobeniusAction`), and since `⁅N,N⁆` is characteristic
in `N` (hence `A`-invariant), the action descends fixed-point-freely to the abelianization
`N / ⁅N,N⁆` (`IsFrobeniusAction.quotient`).  In the (6.8) capstone this is the Frobenius alternative
`hyp.cases.inl : IsFrobeniusGroup ↥L H W₁` (with `N = H`, `A = W₁`); the only remaining input is the
`≤ 4|W₁|² + 1` bound from the character theory ((6.2)/(6.3)). -/
theorem isPGroup_of_isFrobeniusGroup_of_card_le {G : Type*} [Group G] [Finite G]
    {N A : Subgroup G} [Group.IsNilpotent ↥N]
    (h : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G N A)
    (hHodd : Odd (Nat.card (Abelianization ↥N))) (hAodd : Odd (Nat.card ↥A))
    (hbound : Nat.card (Abelianization ↥N) ≤ 4 * Nat.card ↥A ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p ↥N := by
  let : N.Normal := h.isNormal
  let actN : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp A.subtype)
  have hFrobN : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥A ↥N := h.toFrobeniusAction
  -- `⁅N,N⁆` is characteristic in `N`, hence preserved by the automorphism `A`-action.
  have hM : ∀ a : ↥A, ∀ m ∈ commutator ↥N, a • m ∈ commutator ↥N := by
    intro a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (commutator ↥N).Characteristic) (MulDistribMulAction.toMulAut ↥A ↥N a)
    have hmem : (MulDistribMulAction.toMulAut ↥A ↥N a).toMonoidHom m ∈ commutator ↥N := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  -- The fixed-point-free action descends to the abelianization quotient.
  let actAb : MulDistribMulAction ↥A (Abelianization ↥N) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantQuotientMulDistribMulAction (commutator ↥N) hM
  have hFrobAb : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥A (Abelianization ↥N) :=
    hFrobN.quotient (commutator ↥N) hM
  exact isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization hFrobAb hHodd hAodd hbound

/-- **Peterfalvi (6.5)(b) reduction in the certain-type case (6.8)(c2): the kernel is a `p`-group.**
If a finite group `W` acts on a finite nilpotent group `H` with `(|W|, |H|) = 1`, such that for
every nonidentity `w ∈ W` the `w`-fixed points of `H` lie in `⁅H,H⁆` (the certain-type centralizer
condition `C_H(x) = W₂ ⊆ ⁅H,H⁆`), and `|Abelianization H|`, `|W|` are odd with
`|Abelianization H| ≤ 4|W|² + 1`, then `H` is a `p`-group for some prime `p`.

This is the (6.8)(c2) analogue of `isPGroup_of_isFrobeniusGroup_of_card_le`.  Here `W` does *not*
act fixed-point-freely on `H` (the fixed points `C_H(x) = W₂` are nontrivial), but since
`W₂ ⊆ ⁅H,H⁆` the action descends fixed-point-freely to `Abelianization H` (`IsFrobeniusAction`'s
`quotient_of_fixedPoints_le`, via the coprime fixed-point lifting Isaacs Cor 3.28); then the
(6.5)(b) reduction `isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization` applies.  In the
(6.8) capstone the fixed-points hypothesis is discharged from the certain-type fields
`centralizer_W2` (`C_L(x) ⊓ H = W₂`) and `W₂ ⊆ ⁅H,H⁆`, and the coprimality from the Hall datum
`gcd(|H|, |W₁|) = 1`. -/
theorem isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator {H W : Type*}
    [Group H] [Finite H] [Group.IsNilpotent H] [Group W] [Finite W] [MulDistribMulAction W H]
    (hCop : Nat.Coprime (Nat.card W) (Nat.card H))
    (hfix : ∀ w : W, w ≠ 1 → ∀ x : H, w • x = x → x ∈ commutator H)
    (hHodd : Odd (Nat.card (Abelianization H))) (hWodd : Odd (Nat.card W))
    (hbound : Nat.card (Abelianization H) ≤ 4 * Nat.card W ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p H := by
  have hMinv : ∀ a : W, ∀ m ∈ commutator H, a • m ∈ commutator H := by
    intro a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (commutator H).Characteristic) (MulDistribMulAction.toMulAut W H a)
    have hmem : (MulDistribMulAction.toMulAut W H a).toMonoidHom m ∈ commutator H := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  let actAb : MulDistribMulAction W (Abelianization H) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantQuotientMulDistribMulAction (commutator H) hMinv
  have hFrobAb : OddOrder.Isaacs.Ch06.IsFrobeniusAction W (Abelianization H) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.quotient_of_fixedPoints_le hCop (commutator H) hMinv hfix
  exact isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization hFrobAb hHodd hWodd hbound

/-- A finite group with non-trivial abelianization carries a non-trivial linear character
`Γ →* ℂˣ`. Equivalently (via `Group.IsSolvable.commutator_lt_top_of_nontrivial`) every non-trivial
finite solvable group has one.

This is the existence ingredient feeding **Peterfalvi (6.2)**: the section `K/A` (solvable and
non-trivial, since `A ⊊ K`) carries an irreducible character of degree `1`, which is what makes
`S(A)` non-empty so the degree bound `2|L:C|√|C:D| ≥ |K:A| − 1` has content. The proof reduces to
the abelianization `Γ ⧸ ⁅Γ,Γ⁆` (non-trivial exactly when `⁅Γ,Γ⁆ ≠ ⊤`) and uses that `ℂ` is
separably closed of characteristic zero, hence has enough roots of unity
(`IsSepClosed.hasEnoughRootsOfUnity`, instantiated at `n = exponent` via the supplied `NeZero`). -/
theorem exists_monoidHom_units_ne_one_of_commutator_ne_top {Γ : Type*} [Group Γ] [Finite Γ]
    (h : commutator Γ ≠ ⊤) : ∃ χ : Γ →* ℂˣ, χ ≠ 1 := by
  -- `Abelianization Γ = Γ ⧸ ⁅Γ,Γ⁆` is non-trivial precisely because `⁅Γ,Γ⁆ ≠ ⊤`.
  have : Nontrivial (Abelianization Γ) := by
    by_contra hns
    rw [not_nontrivial_iff_subsingleton] at hns
    exact h (by
      rw [← Subgroup.index_eq_one]
      exact @Nat.card_of_subsingleton (Abelianization Γ) 1 hns)
  obtain ⟨a, ha⟩ := exists_ne (1 : Abelianization Γ)
  -- `ℂ` separably closed + characteristic zero ⟹ enough roots of unity at `n = exponent`.
  have : NeZero ((Monoid.exponent (Abelianization Γ) : ℂ)) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨φ, hφ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Abelianization Γ) ℂ ha
  -- Pull `φ` back along the surjection `Abelianization.of`; non-triviality transports.
  refine ⟨φ.comp Abelianization.of, fun hcon => hφ ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g : Γ, Abelianization.of g = a := QuotientGroup.mk_surjective a
  simpa using DFunLike.congr_fun hcon g

/-- A finite group with non-trivial abelianization carries a non-trivial **degree-one irreducible
character**. This is the `IrreducibleCharacter`-level form of the **Peterfalvi (6.2)** existence
ingredient: bridging `exists_monoidHom_units_ne_one_of_commutator_ne_top` through the linear
character functor `linearIrreducibleCharacter`. Applied to the section `K/A` (non-trivial solvable)
and inflated to `K`, it furnishes a non-trivial `θ ∈ Irr K` with `A ⊆ ker θ`, i.e. a member of
`S(A)`. -/
theorem exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top {Γ : Type*}
    [Group Γ] [Finite Γ] (h : commutator Γ ≠ ⊤) :
    ∃ χ : IrreducibleCharacter Γ,
      χ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ ∧
      (χ : ClassFunction Γ ℂ) (1 : Γ) = 1 := by
  obtain ⟨φ, hφ⟩ := exists_monoidHom_units_ne_one_of_commutator_ne_top h
  refine ⟨OddOrder.RepresentationTheory.linearIrreducibleCharacter φ, ?_,
    OddOrder.RepresentationTheory.linearIrreducibleCharacter_apply_one φ⟩
  rw [Ne, OddOrder.RepresentationTheory.linearIrreducibleCharacter_eq_trivial_iff]
  exact hφ

/-- **Peterfalvi (6.2): `S(A)` is non-empty when `K/A` is non-trivial.**  If `A ◁ K` is normal with
`K/A` of non-trivial abelianization (in particular when `K/A` is a non-trivial solvable group, e.g.
`A ⊊ K` with `K` solvable), then `K` carries a non-trivial irreducible character `θ` of degree `1`
with `A ⊆ ker θ` — i.e. a member of `S(A) = {Ind_K^L θ | θ ∈ Irr K, A ⊆ ker θ, θ ≠ 1}`.

This is the concrete, `(K, A)`-level existence ingredient for the (6.2) degree bound: it inflates
the degree-one character produced on the section `K/A`
(`exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top`) back up to `K` via
`OddOrder.RepresentationTheory.inflate`, transporting non-triviality
(`inflate_eq_trivial_iff`), the kernel containment (`subset_characterKernel_inflate`) and the
degree (`inflate_apply_one`). -/
theorem exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top {K : Type*}
    [Group K] [Finite K] (N : Subgroup K) [N.Normal] (h : commutator (K ⧸ N) ≠ ⊤) :
    ∃ θ : IrreducibleCharacter K,
      θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter K ∧
      (N : Set K) ⊆ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction K ℂ) ∧
      (θ : ClassFunction K ℂ) (1 : K) = 1 := by
  obtain ⟨χbar, hne, hdeg⟩ :=
    exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top h
  refine ⟨OddOrder.RepresentationTheory.inflate N χbar, ?_,
    OddOrder.RepresentationTheory.subset_characterKernel_inflate N χbar, ?_⟩
  · rw [Ne, OddOrder.RepresentationTheory.inflate_eq_trivial_iff]; exact hne
  · rw [OddOrder.RepresentationTheory.inflate_apply_one]; exact hdeg

/-- **Peterfalvi (6.8): Dade-based carrier** (T1, faithful replacement of `SibleySetup`).

The legacy `SibleySetup` carried an opaque `coherence.tau` with a *global* `IsIntegralIsometry`,
which does not exist in Feit–Thompson (`dim CF(L) > dim CF(G)`); its `CoherenceTarget` was
therefore undischargeable. This carrier instead packages the genuine §4 Dade datum
`dade : S04.Hypothesis G H^# L`, so the coherence map `tau` is the **real**
`dadeIntegralCharacterMap` and `CoherenceTarget` is `IsCoherent` for that map — exactly the shape
the §7 coherence engine produces (`coherentUnion_of_glued`, `coherentEqualDegree_fromDade`, …),
realizing "τ coincides with the Dade isometry relative to (A,L,G)" (mmd 04.8 L150).

**Migration status (T1, `notes/peterfalvi/s08_6_8_assembly_plan.md`)**: this commit lands the
re-parametrization (`L : Subgroup G`, source type `↥L`) and the real-`tau` `CoherenceTarget`. The
remaining (6.8) hypotheses — `S = {Ind_H^L θ | θ ≠ 1}`, the split `L = H ⋊ W₁`, `H` nilpotent, and
the case (c1)/(c2) disjunction (`S06.CertainTypeHypothesis`) — are added next, after which
`sibleySetup_is_coherent` is restated against this carrier and the legacy `SibleySetup` removed. -/
structure SibleyDadeHypothesis (G : Type*) [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (L : Subgroup G) [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    (H : Subgroup ↥L) [Invertible (Nat.card ↥H : ℂ)] where
  /-- A complement-side subgroup `W₁`; the split `L = H ⋊ W₁` is added in the next migration step.
  -/
  W1 : Subgroup ↥L
  H_ne_bot : H ≠ ⊥
  H_normal : H.Normal
  /-- `H` is nilpotent (Peterfalvi (6.8.a)). -/
  H_nilpotent : Group.IsNilpotent ↥H
  /-- `L = H ⋊ W₁`: `W₁` is a complement to the normal `H` (Peterfalvi (6.8.a)). -/
  split : Subgroup.IsComplement' H W1
  W1_nontrivial : W1 ≠ ⊥
  card_L_odd : Odd (Nat.card L)
  /-- `H^#` is a TI-subset of `G` relative to `L` (corrected ambient: TI in `G`, not in `↥L`). -/
  H_sharp_ti : OddOrder.GroupTheory.IsTISubset (sharpImage H) L
  /-- The §4 Dade datum on `A = H^#`; its Dade isometry *is* `tau`. -/
  dade : OddOrder.Peterfalvi.S04.Hypothesis G (sharpImage H) L
  /-- In the TI situation ((6.8.a): `H^#` is a TI-subset of `G` with normalizer `L`), the §4 Dade
  datum's local subgroups are trivial, `dade.H a = ⊥` — i.e. `dade` is the Dade map of the
  TI-subset construction (`S04.of_isTISubset`, whose `H a = ⊥`, S04:308).  This faithful (6.8.a)
  fact makes the Dade map agree with `Ind_L^G` on the supported lattice, yielding the (2.7)
  reciprocity `⟨α^τ, ψ⟩_G = ⟨α, Res_L^G ψ⟩_L` (`inner_tau_eq_inner_restrict`), the gateway to the
  (6.8.1) `Res_L(η₁^{τ₁})` decomposition. -/
  dade_H_eq_bot : ∀ a : {a : G // a ∈ sharpImage H}, dade.H a = ⊥
  /-- The base character set `S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` (Peterfalvi (6.8.b)). -/
  S : Set (ClassFunction ↥L ℂ)
  /-- `S` is exactly the set of characters induced from nontrivial irreducibles of `H`. -/
  S_eq : S = {φ : ClassFunction ↥L ℂ | ∃ θ : IrreducibleCharacter ↥H,
    θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H ∧
    φ = OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ)}
  /-- Peterfalvi (6.8)(c): the configuration is one of two cases.

  * **(c1)** `L` is a Frobenius group with kernel `H` and complement `W₁`.
  * **(c2)** Hypothesis (4.6) holds — encoded **faithfully** by a `S06.Hypothesis46` (the *full*
    (4.6): the (4.2) structure plus the ambient (3.1) TI-cyclic `tic` for `(G, W)` (4.6.b), the
    covering `A_covers` (4.6.d), and the enlarged Dade datum `dade0`/`tau` on `A₀ = A ∪ Vᴸ`) on
    the *same* Dade datum (`h46.dade = dade`) whose kernel is `K = H` — with `w₂ = |W₂|` prime,
    `W₂ ⊆ [H,H]`, and the Hall coprimality `gcd(|H|, |W₁|) = 1` (Peterfalvi (4.2.a): `W₁` is a
    cyclic *Hall* subgroup of `L = H ⋊ W₁`, so its order is coprime to `|H| = [L : W₁]`).  This
    coprimality is the input to Isaacs (3.28) that lifts a `W₁`-fixed coset of `H/[H,H]` to a
    `W₁`-fixed element of `H`.

  The (4.6)↔(6.8) renaming sets the (4.6)-kernel `K` to the (6.8) `H` (hence `h46.K = H`), and the
  (4.2)/(6.8) complement is shared (`h46.W1 = W1`, both giving `L = H ⋊ W₁`).

  **Faithfulness note (2026-06-13):** the textbook (6.8)(c2) literally reads "Hypothesis (4.6)
  holds" (mmd 04.8 L146), and (4.6) (mmd 04.6 L53-63) includes (4.6.b) "G and W satisfy (3.1)" —
  i.e. the ambient TI-cyclic on `W − W₂`.  This is *not* derivable from a bare
  `CertainTypeHypothesis` (which carries only the (4.2) structure on `↥L` plus the §4 Dade datum on
  `A`): TI in the ambient `G` quantifies over all of `G`, not just `↥L`, so it cannot be lifted from
  the (4.3.a) TI in `↥L`.  The earlier `cases` encoding used the *weaker* `CertainTypeHypothesis`,
  which made the c2 X-coherence un-constructible (the impossible "build the ambient TI from
  nothing").  Strengthening `cases` to `Hypothesis46` restores faithfulness and moves the
  (4.6)-construction obligation to the `SibleyDadeHypothesis` *producer* (the §9 (7.10) application,
  where the maximal-subgroup structure supplies it), exactly as the textbook does. -/
  cases :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H W1 ∨
    ∃ h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L,
      h46.dade = dade ∧ h46.K = H ∧ h46.W1 = W1 ∧
        (Nat.card h46.W2).Prime ∧ h46.W2 ≤ ⁅H, H⁆ ∧
        Nat.Coprime (Nat.card ↥H) (Nat.card W1)

/-- **(T7-c2 case A, brick ①)** A multiplicative `ℂ`-valued function `f` (e.g. a linear character)
that is *invariant* under a fixed-point-free endomorphism `σ` is identically `1`.  Indeed
`z ↦ z·(σ z)⁻¹` is surjective (`MonoidHom.FixedPointFree.commutatorMap_surjective`), and
`f (z₀·(σ z₀)⁻¹) = f z₀ · f (σ z₀)⁻¹ = f z₀ · (f z₀)⁻¹ = 1` using `f ∘ σ = f`. -/
theorem eq_one_of_fixedPointFree_invariant {Z : Type*} [Group Z] [Finite Z]
    {F : Type*} [FunLike F Z Z] [MonoidHomClass F Z Z] {σ : F}
    (hσ : MonoidHom.FixedPointFree σ)
    {f : Z → ℂ} (hf_mul : ∀ a b, f (a * b) = f a * f b) (hf_one : f 1 = 1)
    (hinv : ∀ z, f (σ z) = f z) (z : Z) : f z = 1 := by
  have hne : ∀ a : Z, f a ≠ 0 := fun a ha => one_ne_zero
    (show (1 : ℂ) = 0 by rw [← hf_one, ← mul_inv_cancel a, hf_mul, ha, zero_mul])
  have hf_inv : ∀ a : Z, f a⁻¹ = (f a)⁻¹ := fun a =>
    eq_inv_of_mul_eq_one_right (by rw [← hf_mul, mul_inv_cancel, hf_one])
  obtain ⟨z₀, hz₀⟩ := hσ.commutatorMap_surjective z
  rw [MonoidHom.commutatorMap_apply, div_eq_mul_inv] at hz₀
  calc f z = f (z₀ * (σ z₀)⁻¹) := by rw [hz₀]
    _ = f z₀ * f (σ z₀)⁻¹ := hf_mul _ _
    _ = f z₀ * (f (σ z₀))⁻¹ := by rw [hf_inv]
    _ = f z₀ * (f z₀)⁻¹ := by rw [hinv]
    _ = 1 := mul_inv_cancel₀ (hne z₀)

/-- A natural witness for the degree of an irreducible character is positive. -/
theorem natDegree_pos_of_irreducibleCharacter_apply_one_eq
    {G : Type*} [Group G] {χ : IrreducibleCharacter G} {d : ℕ}
    (hχone : (χ : ClassFunction G ℂ) 1 = (d : ℂ)) : 0 < d := by
  obtain ⟨e, hepos, heq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  have hde : d = e := Nat.cast_injective (hχone.symm.trans heq)
  rwa [hde]

/-- A common index in a factorization of an irreducible character degree is positive. -/
theorem commonIndex_pos_of_natDegree_factor
    {G : Type*} [Group G] {χ : IrreducibleCharacter G} {idx d θ : ℕ}
    (hχone : (χ : ClassFunction G ℂ) 1 = (d : ℂ)) (hd : d = idx * θ) :
    0 < idx := by
  have hdpos : 0 < d := natDegree_pos_of_irreducibleCharacter_apply_one_eq hχone
  by_contra hidx
  have hidx0 : idx = 0 := Nat.eq_zero_of_not_pos hidx
  have hd0 : d = 0 := by simp [hd, hidx0]
  omega

/-- A common index coprime to `p` is coprime to any residual degree that is a power of `p`. -/
theorem coprime_commonIndex_primePower
    {idx p θ m : ℕ} (hidx_p : Nat.Coprime idx p) (hθ : θ = p ^ m) :
    Nat.Coprime idx θ := by
  rw [hθ]
  exact hidx_p.pow_right m

/-- **Peterfalvi (6.5)(c) — the arithmetic contradiction.**  The numeric heart of (6.5)(c): a
non-abelian `p`-group kernel is incompatible with `|L:H| ∣ p − 1` under the (6.5)(a) index bound.

Given a prime `p` that is odd, an odd `d` (playing `|L:H|`) with `d ∣ p − 1`, and naturals with
`p² ≤ HH'` (the non-abelian `p`-group bound `p² ≤ |H:H′|`) and `HH' ≤ 4·d² + 1` (the (6.5)(a) index
bound `|H:H′| ≤ 4|L:H|² + 1`), we derive `False`.

Peterfalvi's argument (mmd 04.8 L72): `d ∣ p − 1` with `d` odd and `p − 1` even forces the quotient
`(p−1)/d` to be even, hence `≥ 2`, so `p − 1 ≥ 2d`, `p ≥ 2d + 1`, and
`p² ≥ (2d+1)² = 4d² + 4d + 1 > 4d² + 1 ≥ p²`.  This is exactly (6.5)(c): if `|L:K| ∣ p − 1` then the
(6.5)(a) bound `|K:H₁| ≤ 4|L:K|² + 1` fails for the non-abelian `p`-group `K/M`. -/
theorem six_five_c_arith {d p HH' : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hdodd : Odd d) (hdvd : d ∣ p - 1) (hpsq : p ^ 2 ≤ HH')
    (hbound : HH' ≤ 4 * d ^ 2 + 1) : False := by
  have hp2 : 2 ≤ p := hp.two_le
  have hdpos : 0 < d := hdodd.pos
  obtain ⟨k, hk⟩ := hdvd
  -- `p − 1` is even; `d` odd with `d·k = p − 1` even forces `k` even, hence `k ≥ 2`.
  have hp1even : Even (p - 1) := Nat.Odd.sub_odd hpodd odd_one
  have hkeven : Even k :=
    (Nat.even_mul.mp (hk ▸ hp1even)).resolve_left (Nat.not_even_iff_odd.mpr hdodd)
  have hk0 : k ≠ 0 := by rintro rfl; simp only [mul_zero] at hk; omega
  have hk2 : 2 ≤ k := by obtain ⟨m, rfl⟩ := hkeven; omega
  -- `p ≥ 2d + 1`.
  have hpk : p = d * k + 1 := by omega
  have hdk : 2 * d ≤ d * k := by
    calc 2 * d = d * 2 := by ring
      _ ≤ d * k := by gcongr
  have hpge : 2 * d + 1 ≤ p := by omega
  -- square it against the (6.5)(a) bound.
  have hsq : (2 * d + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hpge 2
  have hexp : (2 * d + 1) ^ 2 = 4 * d ^ 2 + 4 * d + 1 := by ring
  omega

/-- A member-family square sum is positive once it contains one irreducible character. -/
theorem natDegreeSquareSum_pos_of_memberFamily
    {G : Type*} [Group G] {ι : Type*} {s : Finset ι}
    {χmem : ι → IrreducibleCharacter G} {i₁ : ι} {D : ℕ} {dmem : ι → ℕ}
    (hi₁ : i₁ ∈ s)
    (hmemone : ∀ i ∈ s, (χmem i : ClassFunction G ℂ) 1 = (dmem i : ℂ))
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D) :
    0 < D := by
  have hpos_i₁ : 0 < dmem i₁ :=
    natDegree_pos_of_irreducibleCharacter_apply_one_eq (hmemone i₁ hi₁)
  have hterm_pos : 0 < dmem i₁ * dmem i₁ := Nat.mul_pos hpos_i₁ hpos_i₁
  have hsum_pos : 0 < ∑ i ∈ s, dmem i * dmem i := by
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨i₁, hi₁, hterm_pos⟩
  exact hDsum ▸ hsum_pos

/-- A common-index factorization of every member degree makes the common-index square divide the
member degree square sum. -/
theorem sq_dvd_natDegreeSquareSum_of_commonIndex
    {ι : Type*} {s : Finset ι} {idx D : ℕ}
    {dmem θmem : ι → ℕ}
    (hDsum : ∑ i ∈ s, dmem i * dmem i = D)
    (hdmem : ∀ i ∈ s, dmem i = idx * θmem i) :
    idx * idx ∣ D := by
  rw [← hDsum]
  apply Finset.dvd_sum
  intro i hi
  refine ⟨θmem i * θmem i, ?_⟩
  rw [hdmem i hi]
  ring

/-- **General finite enumeration of a set of class functions** (the case-(B) analogue of
`exists_finEnum_irreducible`, dropping the irreducibility requirement).

For a finite set `S : Set (ClassFunction Γ ℂ)` produces an injective `Fin k`-indexed family whose
range is `S` — **without** requiring its members to be irreducible.  This is the enumeration
primitive for the case-(B) norm-weighted member family, whose coherent set `X ∪ Y` contains the
*reducible* certain-type columns `μ_j = columnSum h46 χ₂` (so the `IrreducibleCharacter`-typed
`exists_finEnum_irreducible` does not apply).  Pure formalization (no character theory): the `Fin`
enumeration of a `Fintype` via `Fintype.equivFin`. -/
theorem exists_finEnum_general {Γ : Type*} [Group Γ] {S : Set (ClassFunction Γ ℂ)}
    (hSfin : S.Finite) :
    ∃ (k : ℕ) (f : Fin k → ClassFunction Γ ℂ),
      Function.Injective f ∧ Set.range f = S := by
  classical
  have : Fintype S := hSfin.fintype
  refine ⟨Fintype.card S, fun j => ((Fintype.equivFin S).symm j : ClassFunction Γ ℂ), ?_, ?_⟩
  · intro i j hij
    exact (Fintype.equivFin S).symm.injective (Subtype.ext hij)
  · ext φ
    constructor
    · rintro ⟨j, rfl⟩
      exact ((Fintype.equivFin S).symm j).2
    · intro hφ
      exact ⟨Fintype.equivFin S ⟨φ, hφ⟩, by simp⟩

end OddOrder.Peterfalvi.S08


