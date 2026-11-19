-- Prove2me | Definitions.Def_RPLib_S4_CDPack14
-- name    : RPLib_S4_CDPack14
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:17:21.966201+00:00
-- url     : https://prove2.me/theorems/d712c759-f2ee-498f-92d4-ff54995255ad
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 14 of 71
-- statement:
--   Part 14 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_CoreA_Pic`: S4-CoreA part Pic (G1a): the Tate module of `Pic⁰(X̄)` is free of rank `2g`
--   * `Def_RP_CoreA`: S4-CoreA (gate G1a): `T_l Pic⁰(X̄)` is free of rank `2g`, without a Jacobian (review R3)
--   * `Def_RP_Kummer_PicA`: S4-Kummer K5d (part A): `div(a) / N` and its class in `Pic(X̄)`
--   * `Def_RP_Kummer_PicMap`: S4-Kummer K5d (part B): `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack13
import Definitions.Def_RPLib_S4_CDPack11
import Definitions.Def_RPLib_S4_CDPack12

/-!
# Curve-duality library package, part 14 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_CoreA_Pic`: S4-CoreA part Pic (G1a): the Tate module of `Pic⁰(X̄)` is free of rank `2g`
* `Def_RP_CoreA`: S4-CoreA (gate G1a): `T_l Pic⁰(X̄)` is free of rank `2g`, without a Jacobian (review R3)
* `Def_RP_Kummer_PicA`: S4-Kummer K5d (part A): `div(a) / N` and its class in `Pic(X̄)`
* `Def_RP_Kummer_PicMap`: S4-Kummer K5d (part B): `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CoreA_Pic =====
section

/-!
# S4-CoreA part Pic (G1a): the Tate module of `Pic⁰(X̄)` is free of rank `2g`

`A = Pic(X̄)[l^∞]` (`AddCommGroup.primaryComponent`, automatically inside `Pic⁰(X̄)`: `primary_le_PicBar0`),
`π = piBar` restricted to it (`piA`). The fixed points of `π ^ m` on `A` are the `l`-primary part of
`Pic⁰(X̄)^(π^m) = Pic⁰(X_m)`, of order `l ^ v_l(h_m)` (`card_fix_piA`, from `card_primaryComponent`).
With `card c = 2g`, `Π c_i = q^g` (`card_eq_two_genus`) and the valuation growth of `h_m = Π (1 - c_i^m)`
(`valuation_growth_padic`), the abstract `tate_rank` gives **`tate_rank_Pic`**: `T_l` of the divisible part of
`A` is free of rank `2g` over `ℤ_[l]`, with the Frobenius matrix `M`, `v det (1 - M^n)` equal to `v_l(h_n)` up to the
bounded contribution of the finite part `Phi = A ⧸ D`, and `Phi = 0 ↔ A` divisible `↔ #A[l] = l ^ 2g`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial Matrix

namespace RamanujanPetersson.CoreA

/-- The `l`-primary part of a finite abelian group has order `l ^ v_l(#G)`. -/
theorem card_primaryComponent {G : Type*} [AddCommGroup G] [Finite G] (l : ℕ) [hl : Fact l.Prime] :
    Nat.card (AddCommGroup.primaryComponent G l) = l ^ padicValNat l (Nat.card G) := by
  set T := AddCommGroup.primaryComponent G l
  have hT0 : Nat.card T ≠ 0 := Nat.card_pos.ne'
  have hT := Nat.eq_prime_pow_of_unique_prime_dvd hT0 (p := l) fun {d} hd hdvd => by
    have := Fact.mk hd
    obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' d hdvd
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp y.2
    have h1 : l ^ k • y = 0 := Subtype.ext (by rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact hk)
    have h2 := addOrderOf_dvd_of_nsmul_eq_zero h1
    rw [hy] at h2
    exact (Nat.prime_dvd_prime_iff_eq hd hl.out).mp (hd.dvd_of_dvd_pow h2)
  obtain ⟨a, ha⟩ : ∃ a, Nat.card T = l ^ a := ⟨_, hT⟩
  have hQ : ¬ l ∣ Nat.card (G ⧸ T) := by
    intro h
    obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card' l h
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
    have h1 : ((l • y : G) : G ⧸ T) = 0 := by
      rw [QuotientAddGroup.mk_nsmul, ← hz]
      exact addOrderOf_nsmul_eq_zero _
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp ((QuotientAddGroup.eq_zero_iff _).mp h1)
    have h2 : (y : G ⧸ T) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr
      (AddCommGroup.mem_primaryComponent.mpr ⟨k + 1, by rw [pow_succ, mul_smul, hk]⟩)
    rw [h2, addOrderOf_zero] at hz
    exact hl.out.one_lt.ne hz
  have hQ0 : Nat.card (G ⧸ T) ≠ 0 := Nat.card_pos.ne'
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup T, padicValNat.mul hQ0 hT0,
    padicValNat.eq_zero_of_not_dvd hQ, zero_add, ha, padicValNat.prime_pow]

open Places ZetaSB PicDescent RR

section Pic

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)

variable (Ω) in
/-- **`A = Pic(X̄)[l^∞]`**, the `l`-primary torsion of `Pic(X̄)` (inside `Pic⁰(X̄)`). -/
abbrev Aℓ (l : ℕ) : Type _ := AddCommGroup.primaryComponent (PicBar Ω hk) l

theorem primary_le_PicBar0 {l : ℕ} (hl : l ≠ 0) :
    AddCommGroup.primaryComponent (PicBar Ω hk) l ≤ PicBar0 Ω hk := by
  intro x hx
  obtain ⟨k, hx⟩ := AddCommGroup.mem_primaryComponent.mp hx
  rw [mem_PicBar0]
  have h := congrArg (degBar Ω hk) hx
  rw [map_nsmul, map_zero, nsmul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr (pow_ne_zero k hl))

variable (Ω) in
/-- The Frobenius `π` on `A = Pic(X̄)[l^∞]`. -/
noncomputable def piA (l : ℕ) : Aℓ Ω hk l →+ Aℓ Ω hk l :=
  ((piBar Ω hk).comp (AddCommGroup.primaryComponent (PicBar Ω hk) l).subtype).codRestrict _ fun x => by
    obtain ⟨k, hx⟩ := AddCommGroup.mem_primaryComponent.mp x.2
    exact AddCommGroup.mem_primaryComponent.mpr ⟨k, by
      rw [AddMonoidHom.comp_apply, ← map_nsmul, AddSubgroup.coe_subtype, hx, map_zero]⟩

theorem piA_iterate_coe (l m : ℕ) (x : Aℓ Ω hk l) :
    (((piA Ω hk l)^[m] x : Aℓ Ω hk l) : PicBar Ω hk) = (piBar Ω hk)^[m] x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]; rfl

section Descent

variable [IsAlgClosed Ω]

/-- Every class of `Pic(X̄)` is fixed by some power of `π` (it is defined over some `F_(q^n)`). -/
theorem exists_piBar_iterate_eq (z : PicBar Ω hk) : ∃ m, 0 < m ∧ (piBar Ω hk)^[m] z = z := by
  refine AddCommGroup.DirectLimit.induction_on z fun j y => ⟨lev j, NeZero.pos _, ?_⟩
  show (piBar Ω hk)^[lev j] (ofBar Ω hk j y) = ofBar Ω hk j y
  have : Fact (lev j ∣ lev j) := ⟨dvd_rfl⟩
  have h1 := frobN_iterate_conNN (Ω := Ω) hk (n := lev j) (N := lev j) y
  rw [conNN_self] at h1
  rw [piBar_iterate_of, h1]

/-- **`A^(π^m)` is the `l`-primary part of `Pic⁰(X_m)`**, of order `l ^ v_l(h_m)`. -/
theorem card_fix_piA (l : ℕ) [hl : Fact l.Prime] (m : ℕ) [NeZero m]
    [Finite (fixedBar Ω hk m ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk))] :
    Nat.card {x : Aℓ Ω hk l // (piA Ω hk l)^[m] x = x} =
      l ^ padicValNat l (Nat.card (fixedBar Ω hk m ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk))) := by
  rw [← card_primaryComponent]
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x.1.1, AddSubgroup.mem_inf.mpr ⟨?_, primary_le_PicBar0 hk hl.out.ne_zero x.1.2⟩⟩, ?_⟩
      invFun := fun y => ⟨⟨y.1.1, ?_⟩, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  · rw [mem_fixedBar, ← piA_iterate_coe, x.2]
  · obtain ⟨k, hx⟩ := AddCommGroup.mem_primaryComponent.mp x.1.2
    exact AddCommGroup.mem_primaryComponent.mpr ⟨k, Subtype.ext (by
      rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact hx)⟩
  · obtain ⟨k, hy⟩ := AddCommGroup.mem_primaryComponent.mp y.2
    have := congrArg Subtype.val hy
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero] at this
    exact AddCommGroup.mem_primaryComponent.mpr ⟨k, this⟩
  · exact Subtype.ext (by rw [piA_iterate_coe]; exact (AddSubgroup.mem_inf.mp y.1.2).1)

variable (Ω) in
/-- `h_n = #Pic⁰(X̄)^(π^n) = #Pic⁰(X_n)`. -/
noncomputable def hBar (n : ℕ) : ℕ := Nat.card (fixedBar Ω hk n ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk))

/-- **G1a (Core A): `T_l Pic⁰(X̄)` is free of rank `2g`** (`l ≠ char`). `A = Pic(X̄)[l^∞]`, `D = l^k0 A` its divisible
part (`A ⧸ D = Phi` finite), `b1` an `F_l`-basis of `D[l]` with `2g` elements (so `T_l D ≅ ℤ_[l]^(2g)`), `M` the
matrix of `π` on `T_l D`; `v det (1 - M^n) ≤ v_l(h_n) ≤ v det (1 - M^n) + K0`, with equality for all `n` when
`Phi = 0`, and `Phi = 0 ↔ A` is `l`-divisible `↔ #A[l] = l ^ 2g`. -/
theorem tate_rank_Pic (l : ℕ) [hl : Fact l.Prime] (hq : ¬ l ∣ Fintype.card Fq) :
    ∃ (k0 : ℕ) (hdiv : ∀ y : (smulHom (Aℓ Ω hk l) (l ^ k0)).range, ∃ z, l • z = y)
      (b1 : Fin (2 * genusF Fq F) → (smulHom (Aℓ Ω hk l) (l ^ k0)).range) (hb1 : ∀ i, l • b1 i = 0)
      (M : Matrix (Fin (2 * genusF Fq F)) (Fin (2 * genusF Fq F)) ℤ_[l]),
      (∀ d : Fin (2 * genusF Fq F) → ℤ, ∑ i, d i • b1 i = 0 → ∀ i, (l : ℤ) ∣ d i) ∧
      (∀ x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range, l • x = 0 →
        ∃ d : Fin (2 * genusF Fq F) → ℤ, ∑ i, d i • b1 i = x) ∧
      IsTateMat hdiv b1 hb1 (endD (piA Ω hk l) (l ^ k0)) M ∧
      Finite (Aℓ Ω hk l ⧸ (smulHom (Aℓ Ω hk l) (l ^ k0)).range) ∧
      (∃ K0, ∀ n, 0 < n → (1 - M ^ n).det ≠ 0 ∧ (1 - M ^ n).det.valuation ≤ padicValNat l (hBar Ω hk n) ∧
        padicValNat l (hBar Ω hk n) ≤ (1 - M ^ n).det.valuation + K0) ∧
      ((smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤ ↔ ∀ y : Aℓ Ω hk l, ∃ z, l • z = y) ∧
      (Nat.card {x : Aℓ Ω hk l // l • x = 0} = l ^ (2 * genusF Fq F) ↔
        (smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤) ∧
      ((smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤ →
        ∀ n, 0 < n → (1 - M ^ n).det.valuation = padicValNat l (hBar Ω hk n)) := by
  obtain ⟨c, hcard, -, hN, hfin⟩ := classNumber_bar (Ω := Ω) hk
  obtain ⟨hc2g, hprod, L, hL⟩ := card_eq_two_genus hk c hN hcard
  have hh : ∀ N, 0 < N → (hBar Ω hk N : ℂ) = (c.map fun z => 1 - z ^ N).prod := fun N hN0 => by
    have : NeZero N := ⟨hN0.ne'⟩
    obtain ⟨-, h1, h2⟩ := hfin N
    exact h1.trans h2
  have hh0 : ∀ N, 0 < N → hBar Ω hk N ≠ 0 := fun N hN0 => by
    have : NeZero N := ⟨hN0.ne'⟩
    have := (hfin N).1
    exact Nat.card_pos.ne'
  obtain ⟨⟨C₀, hnu⟩, hgrow⟩ :=
    valuation_growth_padic (l := l) hq (genusF Fq F) c hprod L hL (hBar Ω hk) hh hh0
  rw [hc2g] at hnu hgrow
  refine tate_rank (piA Ω hk l) (fun n => padicValNat l (hBar Ω hk n)) C₀ (2 * genusF Fq F) ?_ ?_ ?_ hnu hgrow
  · intro x
    obtain ⟨k, hx⟩ := AddCommGroup.mem_primaryComponent.mp x.2
    exact ⟨k, Subtype.ext (by rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact hx)⟩
  · intro x
    obtain ⟨m, hm, hx⟩ := exists_piBar_iterate_eq hk x.1
    exact ⟨m, hm, Subtype.ext (by rw [piA_iterate_coe]; exact hx)⟩
  · intro m hm
    have : NeZero m := ⟨hm.ne'⟩
    have := (hfin m).1
    exact card_fix_piA hk l m

end Descent

end Pic

end RamanujanPetersson.CoreA

end

-- ===== S4.Def_RP_CoreA =====
section

/-!
# S4-CoreA (gate G1a): `T_l Pic⁰(X̄)` is free of rank `2g`, without a Jacobian (review R3)

Umbrella file of the unit (namespace `RamanujanPetersson.CoreA`). `F / Fq` is a function field with
`constField Fq F = ⊥`, genus `g`, `q = #Fq`; `Ω` is algebraically closed over `F`; `l` is a prime with `l ∤ q`.
`A = Pic(X̄)[l^∞]` (`Aℓ Ω hk l`, inside `Pic⁰(X̄)`), `π = piA` the arithmetic Frobenius, `h_n = hBar Ω hk n =
#Pic⁰(X̄)^(π^n) = #Pic⁰(X_n) = Π (1 - ω_i ^ n)`.

Parts (each file below 150 user-s):
* abstract Core A for an `l`-primary group with a Frobenius: `Ord` (orders in `GL_D(F_l)`), `Fin` (`A[l]` finite),
  `Div` (divisible part `D = l^k0 A`, `A ⧸ D` finite), `Basis`/`Tate` (Tate coordinates `tateMap`, matrices
  `IsTateMat` over `ℤ_[l]`), `Det` (`#ker = l ^ v det`), `Grow` (`v det (1 - M^(d l^j))` grows by `s` per step),
  `Rank`, `Main` (**`tate_rank`**: rank `s = e`);
* zeta inputs: `ZInt` (**`card_eq_two_genus`**: `#ω = 2g`, `Π ω_i = q^g`, `Π (1 - ω_i X) ∈ ℤ[X]`),
  `Val`/`ValZ` (**`valuation_growth_padic`**: `v_l(h_N) ≤ C + 2g v_l(N)`, `v_l(h(d l^j)) = C' + 2g j`, in `ℂ_l`);
* `Pic`: `card_primaryComponent`, `piA`, `card_fix_piA` (`#A^(π^n) = l ^ v_l(h_n)`), **`tate_rank_Pic`**.

Main result here, **`tate_module_Pic`**: with `D = l^k0 A` divisible and `Phi = A ⧸ D` finite, the level maps
`tateMap N : (ℤ/l^N)^(2g) → D` are injective with image `D[l^N]` (so `T_l A = T_l D ≅ ℤ_[l]^(2g)`), `π` acts on
`T_l` by the matrix `M`, `v det (1 - M^n) ≤ v_l(h_n) ≤ v det (1 - M^n) + K0` (the `Phi` contribution), with
equality for all `n` when `Phi = 0`; and `Phi = 0 ↔ A` is `l`-divisible `↔ #A[l] = l ^ 2g` (the divisibility that
S4-CoreB supplies).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial Matrix

namespace RamanujanPetersson.CoreA

open Places ZetaSB PicDescent RR

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω] [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

/-- **G1a: `T_l Pic⁰(X̄)` is free of rank `2g` over `ℤ_[l]`** (`l ∤ q`), with the Frobenius matrix `M`, the
valuation of `det (1 - M^n)` against `v_l(h_n)`, and `Phi = 0 ↔ A` divisible `↔ #A[l] = l ^ 2g`. -/
theorem tate_module_Pic (l : ℕ) [Fact l.Prime] (hq : ¬ l ∣ Fintype.card Fq) :
    ∃ (k0 : ℕ) (hdiv : ∀ y : (smulHom (Aℓ Ω hk l) (l ^ k0)).range, ∃ z, l • z = y)
      (b1 : Fin (2 * genusF Fq F) → (smulHom (Aℓ Ω hk l) (l ^ k0)).range) (hb1 : ∀ i, l • b1 i = 0)
      (M : Matrix (Fin (2 * genusF Fq F)) (Fin (2 * genusF Fq F)) ℤ_[l]),
      (∀ N, Function.Injective (tateMap hdiv b1 hb1 N) ∧
        ∀ x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range, l ^ N • x = 0 → ∃ cb, tateMap hdiv b1 hb1 N cb = x) ∧
      IsTateMat hdiv b1 hb1 (endD (piA Ω hk l) (l ^ k0)) M ∧
      Finite (Aℓ Ω hk l ⧸ (smulHom (Aℓ Ω hk l) (l ^ k0)).range) ∧
      (∃ K0, ∀ n, 0 < n → (1 - M ^ n).det ≠ 0 ∧ (1 - M ^ n).det.valuation ≤ padicValNat l (hBar Ω hk n) ∧
        padicValNat l (hBar Ω hk n) ≤ (1 - M ^ n).det.valuation + K0) ∧
      ((smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤ ↔ ∀ y : Aℓ Ω hk l, ∃ z, l • z = y) ∧
      (Nat.card {x : Aℓ Ω hk l // l • x = 0} = l ^ (2 * genusF Fq F) ↔
        (smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤) ∧
      ((smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤ →
        ∀ n, 0 < n → (1 - M ^ n).det.valuation = padicValNat l (hBar Ω hk n)) := by
  obtain ⟨k0, hdiv, b1, hb1, M, h1inj, h1span, hrest⟩ := tate_rank_Pic (Ω := Ω) hk l hq
  exact ⟨k0, hdiv, b1, hb1, M, fun N => ⟨tateMap_injective hdiv b1 hb1 h1inj N,
    exists_tateMap_eq hdiv b1 hb1 h1span N⟩, hrest⟩

end RamanujanPetersson.CoreA

end

-- ===== S4.Def_RP_Kummer_PicA =====
section

/-!
# S4-Kummer K5d (part A): `div(a) / N` and its class in `Pic(X̄)`

Generic function field `F / Fq` (PicDescent setting), any `Ω` with `F ⊆ Ω`.
* `divN Fq N f`: the divisor `div(f) / N` (integer division of every order); `zsmul_divN` (`N • div(f)/N = div f` when
  `N` divides every order), `divN_pow` (`div(f^N)/N = div f`), `divN_mul`, `div_pow_eq`.
* `conormNN_divN`, `toBar_conNN` (level independence), `psiAt Ω hk N m a = [div(a)/N] ∈ Pic(X̄)`, `psiAt_algebraMap`,
  `psiAt_congr` (only the element of `Ω` matters), `psiAt_mul`, `nsmul_psiAt` (`N`-torsion), `psiAt_mem_PicBar0`.
* `PicBar0N Ω hk N = Pic⁰(X̄)[N]`; `ofBar_eq_toBar`, `exists_lev_toBar`; `exists_psiAt_eq` (every `N`-torsion class of
  `Pic(F_m)` is `[div(a)/N]`), `exists_of_psiAt_eq_zero` (`[div(a)/N] = 0` ⇒ `a / b ^ N` is a constant).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open PicDescent Places ZetaSB
open scoped Polynomial

noncomputable section

section DivN

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable (Fq) in
/-- `div(f) / N`: integer division of every order by `N`. -/
def divN (N : ℕ) (f : F) : Divisor Fq F :=
  (Places.div f : Divisor Fq F).mapRange (fun z => z / (N : ℤ)) (by simp)

theorem divN_apply (N : ℕ) (f : F) (P : Place Fq F) : divN Fq N f P = P.ord f / N := by
  rw [divN, Finsupp.mapRange_apply, Places.div_apply]

/-- `N • (div(f) / N) = div f` when `N` divides every order of `f`. -/
theorem zsmul_divN {N : ℕ} {f : F} (h : ∀ P : Place Fq F, (N : ℤ) ∣ P.ord f) :
    (N : ℤ) • divN Fq N f = Places.div f := by
  ext P
  rw [Finsupp.smul_apply, smul_eq_mul, divN_apply, Places.div_apply, Int.mul_ediv_cancel' (h P)]

theorem ord_pow_place (P : Place Fq F) {f : F} (hf : f ≠ 0) (k : ℕ) : P.ord (f ^ k) = k * P.ord f := by
  induction k with
  | zero => rw [pow_zero, P.ord_one, Nat.cast_zero, zero_mul]
  | succ k ih => rw [pow_succ, P.ord_mul (pow_ne_zero _ hf) hf, ih]; push_cast; ring

theorem div_pow_eq {f : F} (hf : f ≠ 0) (k : ℕ) :
    (Places.div (f ^ k) : Divisor Fq F) = (k : ℤ) • Places.div f := by
  ext P
  rw [Finsupp.smul_apply, smul_eq_mul, Places.div_apply, Places.div_apply, ord_pow_place P hf]

theorem divN_pow {N : ℕ} [NeZero N] {f : F} (hf : f ≠ 0) : divN Fq N (f ^ N) = Places.div f := by
  ext P
  rw [divN_apply, ord_pow_place P hf, Places.div_apply,
    Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.2 (NeZero.ne N))]

theorem divN_mul {N : ℕ} {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : ∀ P : Place Fq F, (N : ℤ) ∣ P.ord f) :
    divN Fq N (f * g) = divN Fq N f + divN Fq N g := by
  ext P
  rw [Finsupp.add_apply, divN_apply, divN_apply, divN_apply, P.ord_mul hf hg, Int.add_ediv_of_dvd_left (h P)]

end DivN

section Lev

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)

theorem conormNN_divN {n n' : ℕ} [NeZero n] [NeZero n'] [Fact (n ∣ n')] (N : ℕ) (f : Fc Fq F Ω n) :
    conormNN Ω hk n n' (divN (Lc Fq Ω n) N f) =
      divN (Lc Fq Ω n') N (algebraMap (Fc Fq F Ω n) (Fc Fq F Ω n') f) := by
  ext P
  rw [conormNN_apply, divN_apply, divN_apply, ord_contractNN]

/-- `toBar` is compatible with conorm (level independence). -/
theorem toBar_conNN {n n' : ℕ} [NeZero n] [NeZero n'] [Fact (n ∣ n')] (x : Pic (Lc Fq Ω n) (Fc Fq F Ω n)) :
    toBar Ω hk n' (conNN Ω hk n n' x) = toBar Ω hk n x := by
  have hle : n ≤ n' := Nat.le_of_dvd (NeZero.pos n') Fact.out
  have : Fact (n' ∣ lev n') := ⟨dvd_lev (NeZero.pos n') le_rfl⟩
  have : Fact (n ∣ lev n') := ⟨dvd_trans (Fact.out : n ∣ n') (dvd_lev (NeZero.pos n') le_rfl)⟩
  rw [toBar_eq hk n' le_rfl, toBar_eq hk n hle, conNN_trans]

variable (Ω) in
/-- `[div(a) / N] ∈ Pic(X̄)` for `a ∈ F_m`. -/
def psiAt (N m : ℕ) [NeZero m] (a : Fc Fq F Ω m) : PicBar Ω hk :=
  toBar Ω hk m (QuotientAddGroup.mk (divN (Lc Fq Ω m) N a))

theorem psiAt_algebraMap (N : ℕ) {n n' : ℕ} [NeZero n] [NeZero n'] [Fact (n ∣ n')] (a : Fc Fq F Ω n) :
    psiAt Ω hk N n' (algebraMap (Fc Fq F Ω n) (Fc Fq F Ω n') a) = psiAt Ω hk N n a := by
  rw [psiAt, psiAt, ← conormNN_divN hk, ← conNN_mk, toBar_conNN]

/-- `psiAt` depends only on the element of `Ω`. -/
theorem psiAt_congr (N : ℕ) {n n' : ℕ} [NeZero n] [NeZero n'] (a : Fc Fq F Ω n) (a' : Fc Fq F Ω n')
    (h : (a : Ω) = a') : psiAt Ω hk N n a = psiAt Ω hk N n' a' := by
  have : NeZero (n * n') := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne n')⟩
  have : Fact (n ∣ n * n') := ⟨dvd_mul_right n n'⟩
  have : Fact (n' ∣ n * n') := ⟨dvd_mul_left n' n⟩
  rw [← psiAt_algebraMap hk N (n' := n * n') a, ← psiAt_algebraMap hk N (n' := n * n') a']
  exact congrArg _ (Subtype.ext (by rw [coe_algebraMap_FF, coe_algebraMap_FF, h]))

theorem psiAt_mul {N m : ℕ} [NeZero m] {a b : Fc Fq F Ω m} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ P : Place (Lc Fq Ω m) (Fc Fq F Ω m), (N : ℤ) ∣ P.ord a) :
    psiAt Ω hk N m (a * b) = psiAt Ω hk N m a + psiAt Ω hk N m b := by
  rw [psiAt, divN_mul ha hb h, QuotientAddGroup.mk_add, map_add]
  rfl

theorem nsmul_psiAt {N m : ℕ} [NeZero m] {a : Fc Fq F Ω m} (ha : a ≠ 0)
    (h : ∀ P : Place (Lc Fq Ω m) (Fc Fq F Ω m), (N : ℤ) ∣ P.ord a) : N • psiAt Ω hk N m a = 0 := by
  have h0 : (QuotientAddGroup.mk (Places.div a : Divisor (Lc Fq Ω m) (Fc Fq F Ω m)) :
      Pic (Lc Fq Ω m) (Fc Fq F Ω m)) = 0 := (QuotientAddGroup.eq_zero_iff _).2 ⟨a, ha, rfl⟩
  rw [psiAt, ← map_nsmul, ← QuotientAddGroup.mk_nsmul, ← natCast_zsmul, zsmul_divN h, h0, map_zero]

theorem psiAt_pow {N m : ℕ} [NeZero N] [NeZero m] {b : Fc Fq F Ω m} (hb : b ≠ 0) :
    psiAt Ω hk N m (b ^ N) = 0 := by
  have h0 : (QuotientAddGroup.mk (Places.div b : Divisor (Lc Fq Ω m) (Fc Fq F Ω m)) :
      Pic (Lc Fq Ω m) (Fc Fq F Ω m)) = 0 := (QuotientAddGroup.eq_zero_iff _).2 ⟨b, hb, rfl⟩
  rw [psiAt, divN_pow hb, h0, map_zero]

theorem psiAt_mem_PicBar0 {N m : ℕ} [NeZero N] [NeZero m] {a : Fc Fq F Ω m} (ha : a ≠ 0)
    (h : ∀ P : Place (Lc Fq Ω m) (Fc Fq F Ω m), (N : ℤ) ∣ P.ord a) : psiAt Ω hk N m a ∈ PicBar0 Ω hk := by
  rw [psiAt, toBar_mem_PicBar0, mem_Pic0, degPic_mk]
  have h1 := congrArg Divisor.deg (zsmul_divN h)
  rw [deg_zsmul, deg_div ha] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 (NeZero.ne N))

variable (Ω) in
/-- `Pic⁰(X̄)[N]`. -/
def PicBar0N (N : ℕ) : AddSubgroup (PicBar Ω hk) where
  carrier := {z | z ∈ PicBar0 Ω hk ∧ N • z = 0}
  add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by rw [nsmul_add, hx.2, hy.2, add_zero]⟩
  zero_mem' := ⟨zero_mem _, nsmul_zero N⟩
  neg_mem' := fun {x} hx => ⟨neg_mem hx.1, by rw [smul_neg, hx.2, neg_zero]⟩

theorem mem_PicBar0N (N : ℕ) (z : PicBar Ω hk) : z ∈ PicBar0N Ω hk N ↔ z ∈ PicBar0 Ω hk ∧ N • z = 0 := Iff.rfl

theorem ofBar_eq_toBar (j : ℕ) (y : PicL Fq F Ω j) : ofBar Ω hk j y = toBar Ω hk (lev j) y := by
  have : Fact (lev j ∣ lev (lev j)) := ⟨dvd_lev (NeZero.pos _) le_rfl⟩
  have hj : j ≤ lev j := by
    unfold lev
    exact (Nat.le_succ j).trans (Nat.self_le_factorial _)
  rw [toBar_apply hk (lev j) y, ← tr_apply hk hj]
  exact (AddCommGroup.DirectLimit.of_f hj y).symm

/-- Every class of `Pic(X̄)` comes from a finite level. -/
theorem exists_lev_toBar (z : PicBar Ω hk) : ∃ j : ℕ, ∃ y : PicL Fq F Ω j, toBar Ω hk (lev j) y = z :=
  AddCommGroup.DirectLimit.induction_on z fun j y => ⟨j, y, (ofBar_eq_toBar hk j y).symm⟩

/-- An `N`-torsion class of `Pic(F_m)` (in `Pic(X̄)`) is `[div(a) / N]` with `N ∣ div a`. -/
theorem exists_psiAt_eq {N m : ℕ} [NeZero N] [NeZero m] (x : Pic (Lc Fq Ω m) (Fc Fq F Ω m))
    (hx : N • toBar Ω hk m x = 0) : ∃ a : Fc Fq F Ω m, a ≠ 0 ∧
      (∀ P : Place (Lc Fq Ω m) (Fc Fq F Ω m), (N : ℤ) ∣ P.ord a) ∧ psiAt Ω hk N m a = toBar Ω hk m x := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [← map_nsmul, ← QuotientAddGroup.mk_nsmul, ← map_zero (toBar Ω hk m)] at hx
  obtain ⟨a, ha, haD⟩ := (QuotientAddGroup.eq_zero_iff _).1 (toBar_injective hk m hx)
  have hord : ∀ P : Place (Lc Fq Ω m) (Fc Fq F Ω m), P.ord a = N * D P := fun P => by
    rw [← Places.div_apply, haD, Finsupp.smul_apply, nsmul_eq_mul]
  have hD : divN (Lc Fq Ω m) N a = D := by
    ext P
    rw [divN_apply, hord, Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.2 (NeZero.ne N))]
  exact ⟨a, ha, fun P => ⟨D P, hord P⟩, by rw [psiAt, hD]⟩

/-- `[div(a) / N] = 0` ⇒ `a = c · b ^ N` with `c` a constant. -/
theorem exists_of_psiAt_eq_zero {N m : ℕ} [NeZero m] {a : Fc Fq F Ω m} (ha : a ≠ 0)
    (h : ∀ P : Place (Lc Fq Ω m) (Fc Fq F Ω m), (N : ℤ) ∣ P.ord a) (h0 : psiAt Ω hk N m a = 0) :
    ∃ b : Fc Fq F Ω m, b ≠ 0 ∧ ∃ c : Lc Fq Ω m, algebraMap (Lc Fq Ω m) (Fc Fq F Ω m) c = a / b ^ N := by
  rw [psiAt, ← map_zero (toBar Ω hk m)] at h0
  obtain ⟨b, hb, hbD⟩ := (QuotientAddGroup.eq_zero_iff _).1 (toBar_injective hk m h0)
  refine ⟨b, hb, ?_⟩
  have hdiv : (Places.div (a / b ^ N) : Divisor (Lc Fq Ω m) (Fc Fq F Ω m)) = 0 := by
    rw [Places.div_div ha (pow_ne_zero _ hb), div_pow_eq hb, hbD, zsmul_divN h, sub_self]
  have hc := (Places.div_eq_zero_iff _ _ (div_ne_zero ha (pow_ne_zero _ hb))).1 hdiv
  rw [constField_Fc Fq F Ω hk m] at hc
  exact IntermediateField.mem_bot.1 hc

end Lev

end

end Kummer
end RamanujanPetersson

end

-- ===== S4.Def_RP_Kummer_PicMap =====
section

/-!
# S4-Kummer K5d (part B): `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`

Session 10 (compiled). `Psi hk N α = [div(α ^ N) / N]`; parabolic radicals have `N ∣ ord` everywhere
(`dvd_ord_of_par`: finite places by Lev, infinite places by InfMain); `Psi_mul`, `Psi_congr` (depends only on the class),
`Psi_mem`, `mem_fixUnits_of_Psi_eq_zero` (kernel), `exists_Psi_eq` (surjective), `exists_kummerPicEquiv`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh IsDedekindDomain Polynomial PicDescent Places

noncomputable section

section Generic

theorem pow_mod_eq_of_pow_eq_one {L : Type*} [Monoid L] {u : L} {M : ℕ} (hM : u ^ M = 1) (k : ℕ) :
    u ^ (k % M) = u ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k M]
  rw [pow_add, pow_mul, hM, one_pow, mul_one]

theorem coprime_pow_sub_one {r m : ℕ} (hr : 0 < r) (hm : 0 < m) : Nat.Coprime r (r ^ m - 1) := by
  have h1 : 1 ≤ r ^ m := Nat.one_le_pow _ _ hr
  have h2 : Nat.Coprime (r ^ m - 1) (r ^ m - 1 + 1) :=
    Nat.coprime_self_add_right.2 (Nat.coprime_one_right _)
  rw [Nat.sub_add_cancel h1] at h2
  exact (h2.coprime_dvd_right (dvd_pow_self r hm.ne')).symm

/-- An `N`-th root (`N` prime to `r`) of a nonzero `c` with `c ^ (r ^ m) = c` is a constant. -/
theorem isConst_of_pow_eq {L : Type} [Field L] {r N m : ℕ} [NeZero N] (hr : 1 < r) (hm : 0 < m)
    (hrN : Nat.Coprime r N) {c u : L} (hc : c ^ (r ^ m) = c) (hc0 : c ≠ 0) (hu : u ^ N = c) : IsConst r u := by
  have hQ : 1 ≤ r ^ m := Nat.one_le_pow _ _ (by omega)
  have hM : u ^ (N * (r ^ m - 1)) = 1 := by rw [pow_mul, hu, pow_pred_eq_one hQ hc hc0]
  have hcop : Nat.Coprime r (N * (r ^ m - 1)) := Nat.Coprime.mul_right hrN (coprime_pow_sub_one (by omega) hm)
  have hpos : 0 < N * (r ^ m - 1) :=
    Nat.mul_pos (NeZero.pos N) (by have := Nat.one_lt_pow hm.ne' hr; omega)
  refine ⟨Nat.totient (N * (r ^ m - 1)), Nat.totient_pos.2 hpos, ?_⟩
  have h := Nat.ModEq.pow_totient hcop
  unfold Nat.ModEq at h
  rw [← pow_mod_eq_of_pow_eq_one hM, h, pow_mod_eq_of_pow_eq_one hM, pow_one]

theorem coe_unit_ne_zero {A K : Type} [CommRing A] [Field K] [Algebra A K] (α : (maxUnram A K)ˣ) :
    ((α : maxUnram A K) : AlgebraicClosure K) ≠ 0 := by
  exact_mod_cast α.ne_zero

/-- Every `N`-th root of `α ^ N` (`α ∈ K_U`) lies in `K_U` (`μ_N ⊆ K_U`). -/
theorem mem_maxUnram_of_pow_eq {A K : Type} [CommRing A] [Field K] [Algebra A K] {N : ℕ} [NeZero N]
    {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N) (α : (maxUnram A K)ˣ) {γ : AlgebraicClosure K}
    (hγ : γ ^ N = ((α : maxUnram A K) : AlgebraicClosure K) ^ N) : γ ∈ maxUnram A K := by
  have hα0 := coe_unit_ne_zero α
  have hζ' : IsPrimitiveRoot ((maxUnram A K).val ζ) N :=
    (IsPrimitiveRoot.map_iff_of_injective (f := (maxUnram A K).val) Subtype.val_injective).2 hζ
  have h1 : (γ / ((α : maxUnram A K) : AlgebraicClosure K)) ^ N = 1 := by
    rw [div_pow, hγ, div_self (pow_ne_zero _ hα0)]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h1
  have hγ' : γ = (maxUnram A K).val ζ ^ i * ((α : maxUnram A K) : AlgebraicClosure K) := by
    rw [hi, div_mul_cancel₀ _ hα0]
  rw [hγ']
  exact mul_mem (pow_mem ζ.2 i) (α : maxUnram A K).2

theorem kclass_congr {K E : Type} [Field K] [Field E] [Algebra K E] [Algebra.IsIntegral K E] {N : ℕ} [NeZero N]
    {Γ : Subgroup (E ≃ₐ[K] E)} {ζ : E} (hζ : IsPrimitiveRoot ζ N) (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ) {α β : Eˣ}
    (h : α = β) (hα : α ∈ rad Γ N) (hβ : β ∈ rad Γ N) : kclass hζ hζΓ hα = kclass hζ hζΓ hβ := by
  subst h
  rfl

end Generic

section Curve

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)

open Classical in
/-- **Ψ**: `α ↦ [div(α ^ N) / N] ∈ Pic(X̄)` at any constant level `F_m ∋ α ^ N` (`0` if there is none). -/
def Psi (N : ℕ) (α : (maxUnram (Rfin Fq F) F)ˣ) : PicBar (AlgebraicClosure F) hk :=
  if h : ∃ m : ℕ, 0 < m ∧
      ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N ∈ Fc Fq F (AlgebraicClosure F) m then
    haveI : NeZero h.choose := ⟨h.choose_spec.1.ne'⟩
    psiAt (AlgebraicClosure F) hk N h.choose ⟨_, h.choose_spec.2⟩
  else 0

theorem Psi_eq {N m : ℕ} [NeZero m] (α : (maxUnram (Rfin Fq F) F)ˣ) (a : Fc Fq F (AlgebraicClosure F) m)
    (haα : ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N = a) :
    Psi hk N α = psiAt (AlgebraicClosure F) hk N m a := by
  have h : ∃ m : ℕ, 0 < m ∧
      ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N ∈ Fc Fq F (AlgebraicClosure F) m :=
    ⟨m, NeZero.pos m, by rw [haα]; exact a.2⟩
  have : NeZero h.choose := ⟨h.choose_spec.1.ne'⟩
  rw [Psi, dif_pos h]
  exact psiAt_congr hk N _ a haα

theorem Psi_of_mem_Fc {N m : ℕ} [NeZero N] [NeZero m] (α : (maxUnram (Rfin Fq F) F)ˣ)
    (b : Fc Fq F (AlgebraicClosure F) m) (hb : ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) = b) :
    Psi hk N α = 0 := by
  have hb0 : b ≠ 0 := by
    have := coe_unit_ne_zero α
    rw [hb] at this
    exact_mod_cast this
  rw [Psi_eq hk α (b ^ N) (by rw [hb, SubmonoidClass.coe_pow]), psiAt_pow hk hb0]

theorem kFc_ne_zero {m : ℕ} {a : Fc Fq F (AlgebraicClosure F) m} {x : AlgebraicClosure F}
    (h : (a : AlgebraicClosure F) = x) (hx : x ≠ 0) : a ≠ 0 := by
  rintro rfl
  exact hx (h.symm.trans (ZeroMemClass.coe_zero _))

section PsiMap

variable {p e : ℕ} [Fact p.Prime] [CharP F p]

/-- `π₁^geo`-fixed elements of `K_U` lie in a constant level `F_m`. -/
theorem exists_Fc_of_fixed (hq : Fintype.card Fq = p ^ e) (he : 0 < e) {x : maxUnram (Rfin Fq F) F}
    (hx : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ x = x) :
    ∃ m : ℕ, 0 < m ∧ (x : AlgebraicClosure F) ∈ Fc Fq F (AlgebraicClosure F) m := by
  rw [hq] at hx
  obtain ⟨k, hk0, hkx⟩ := exists_constLevel_of_fixed he hx
  exact ⟨k, hk0, by rw [Fc_eq_constLevel hq (Nat.mul_pos he hk0)]; exact hkx⟩

theorem exists_Fc_of_rad (hq : Fintype.card Fq = p ^ e) (he : 0 < e) {N : ℕ} {α : (maxUnram (Rfin Fq F) F)ˣ}
    (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N) :
    ∃ m : ℕ, 0 < m ∧
      ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N ∈ Fc Fq F (AlgebraicClosure F) m := by
  obtain ⟨m, hm, h⟩ := exists_Fc_of_fixed hq he ((mem_rad _ _ α).1 hα)
  rw [SubmonoidClass.coe_pow] at h
  exact ⟨m, hm, h⟩

theorem Psi_eq_zero_of_mem_fixUnits (hq : Fintype.card Fq = p ^ e) (he : 0 < e) {N : ℕ} [NeZero N]
    {α : (maxUnram (Rfin Fq F) F)ˣ} (hα : α ∈ fixUnits (pi1geo (Rfin Fq F) F (Fintype.card Fq))) :
    Psi hk N α = 0 := by
  obtain ⟨m, hm, h⟩ := exists_Fc_of_fixed hq he ((mem_fixUnits _ α).1 hα)
  have : NeZero m := ⟨hm.ne'⟩
  exact Psi_of_mem_Fc hk α ⟨_, h⟩ rfl

variable (hq : Fintype.card Fq = p ^ e) (he : 0 < e) {N : ℕ} [NeZero N]
  (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)

include hk hq he hNf hNi hDB hlift

/-- A parabolic radical: `N ∣ ord_P (α ^ N)` at every place `P` of a constant level containing `α ^ N`. -/
theorem dvd_ord_of_par (m : ℕ) [NeZero m] {a : Fc Fq F (AlgebraicClosure F) m} (ha : a ≠ 0)
    {α : (maxUnram (Rfin Fq F) F)ˣ} (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
    (haα : ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N = a)
    (hpar : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) :
    ∀ P : Place (Lc Fq (AlgebraicClosure F) m) (Fc Fq F (AlgebraicClosure F) m), (N : ℤ) ∣ P.ord a := by
  rintro (v | v)
  · exact (forall_dvd_ord_iff hk hq he m hNf ha).2
      (fun γ hγ => mem_maxUnram_of_pow_eq hζ α (hγ.trans haα.symm)) v
  · exact ((kclass_mem_curveH1par_iff_ord hk hq he m hNi hζ hζΓ D hDB hlift ha hα haα).2.1 hpar) v

theorem Psi_mul {α β : (maxUnram (Rfin Fq F) F)ˣ} (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
    (hβ : β ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
    (hpar : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) :
    Psi hk N (α * β) = Psi hk N α + Psi hk N β := by
  obtain ⟨m1, hm1, h1⟩ := exists_Fc_of_rad hq he hα
  obtain ⟨m2, hm2, h2⟩ := exists_Fc_of_rad hq he hβ
  have : NeZero (m1 * m2) := ⟨(Nat.mul_pos hm1 hm2).ne'⟩
  obtain ⟨a, ha_eq⟩ : ∃ a : Fc Fq F (AlgebraicClosure F) (m1 * m2),
      (a : AlgebraicClosure F) = ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N :=
    ⟨⟨_, Fc_le (Fq := Fq) (F := F) (Ω := AlgebraicClosure F) (hnN := dvd_mul_right m1 m2) h1⟩, rfl⟩
  obtain ⟨b, hb_eq⟩ : ∃ b : Fc Fq F (AlgebraicClosure F) (m1 * m2),
      (b : AlgebraicClosure F) = ((β : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N :=
    ⟨⟨_, Fc_le (Fq := Fq) (F := F) (Ω := AlgebraicClosure F) (hnN := dvd_mul_left m2 m1) h2⟩, rfl⟩
  have ha := kFc_ne_zero ha_eq (pow_ne_zero _ (coe_unit_ne_zero α))
  have hb := kFc_ne_zero hb_eq (pow_ne_zero _ (coe_unit_ne_zero β))
  have hdiv := dvd_ord_of_par hk hq he hNf hNi hζ hζΓ D hDB hlift (m1 * m2) ha hα ha_eq.symm hpar
  rw [Psi_eq hk (α * β) (a * b) ?_, Psi_eq hk α a ha_eq.symm, Psi_eq hk β b hb_eq.symm, psiAt_mul hk ha hb hdiv]
  simp only [Units.val_mul, MulMemClass.coe_mul, mul_pow]
  rw [ha_eq, hb_eq]

theorem Psi_congr {α β : (maxUnram (Rfin Fq F) F)ˣ} (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
    (hβ : β ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
    (hβpar : kclass hζ hζΓ hβ ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D)
    (h : kclass hζ hζΓ hα = kclass hζ hζΓ hβ) : Psi hk N α = Psi hk N β := by
  have hc : β⁻¹ * α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N := mul_mem (inv_mem hβ) hα
  have h1 : kclass hζ hζΓ hα = kclass hζ hζΓ hβ + kclass hζ hζΓ hc := by
    rw [← kclass_mul]
    exact kclass_congr hζ hζΓ (mul_inv_cancel_left β α).symm hα _
  have h0 : kclass hζ hζΓ hc = 0 := by
    have h2 : kclass hζ hζΓ hβ + kclass hζ hζΓ hc = kclass hζ hζΓ hβ + 0 := by rw [add_zero, ← h1, h]
    exact add_left_cancel h2
  have hfix := (kclass_eq_zero_iff hζ hζΓ hc).1 h0
  calc Psi hk N α = Psi hk N (β * (β⁻¹ * α)) := by rw [mul_inv_cancel_left]
    _ = Psi hk N β + Psi hk N (β⁻¹ * α) := Psi_mul hk hq he hNf hNi hζ hζΓ D hDB hlift hβ hc hβpar
    _ = Psi hk N β := by rw [Psi_eq_zero_of_mem_fixUnits hk hq he hfix, add_zero]

theorem Psi_mem_PicBar0N {α : (maxUnram (Rfin Fq F) F)ˣ}
    (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
    (hpar : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) :
    Psi hk N α ∈ PicBar0N (AlgebraicClosure F) hk N := by
  obtain ⟨m, hm, h1⟩ := exists_Fc_of_rad hq he hα
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨a, ha_eq⟩ : ∃ a : Fc Fq F (AlgebraicClosure F) m,
      (a : AlgebraicClosure F) = ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N := ⟨⟨_, h1⟩, rfl⟩
  have ha := kFc_ne_zero ha_eq (pow_ne_zero _ (coe_unit_ne_zero α))
  have hdiv := dvd_ord_of_par hk hq he hNf hNi hζ hζΓ D hDB hlift m ha hα ha_eq.symm hpar
  rw [Psi_eq hk α a ha_eq.symm]
  exact ⟨psiAt_mem_PicBar0 hk ha hdiv, nsmul_psiAt hk ha hdiv⟩

include hNF in
/-- **Kernel**: a parabolic radical with `Ψ α = 0` is a `π₁^geo`-fixed unit (`α = u · b`, `u` constant, `b ∈ F_m`). -/
theorem mem_fixUnits_of_Psi_eq_zero {α : (maxUnram (Rfin Fq F) F)ˣ}
    (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
    (hpar : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D)
    (h0 : Psi hk N α = 0) : α ∈ fixUnits (pi1geo (Rfin Fq F) F (Fintype.card Fq)) := by
  obtain ⟨m, hm, h1⟩ := exists_Fc_of_rad hq he hα
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨a, ha_eq⟩ : ∃ a : Fc Fq F (AlgebraicClosure F) m,
      (a : AlgebraicClosure F) = ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N := ⟨⟨_, h1⟩, rfl⟩
  have hα0 := coe_unit_ne_zero α
  have ha := kFc_ne_zero ha_eq (pow_ne_zero _ hα0)
  have hdiv := dvd_ord_of_par hk hq he hNf hNi hζ hζΓ D hDB hlift m ha hα ha_eq.symm hpar
  rw [Psi_eq hk α a ha_eq.symm] at h0
  obtain ⟨b, hb, c, hc⟩ := exists_of_psiAt_eq_zero hk ha hdiv h0
  have hb0 : (b : AlgebraicClosure F) ≠ 0 := fun h => hb (Subtype.ext (h.trans (ZeroMemClass.coe_zero _).symm))
  have hcΩ : ((c : Lc Fq (AlgebraicClosure F) m) : AlgebraicClosure F) =
      ((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N / (b : AlgebraicClosure F) ^ N := by
    have h3 := congrArg Subtype.val hc
    rw [coe_algebraMap_LF, IntermediateField.coe_div, IntermediateField.coe_pow, ha_eq] at h3
    exact h3
  have hu : (((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) / (b : AlgebraicClosure F)) ^ N =
      ((c : Lc Fq (AlgebraicClosure F) m) : AlgebraicClosure F) := by rw [div_pow, hcΩ]
  have hc0 : ((c : Lc Fq (AlgebraicClosure F) m) : AlgebraicClosure F) ≠ 0 := by
    rw [hcΩ]; exact div_ne_zero (pow_ne_zero _ hα0) (pow_ne_zero _ hb0)
  have hrN : Nat.Coprime (Fintype.card Fq) N := by rw [hq]; exact coprime_q F p N hNF
  have hconst := isConst_of_pow_eq Fintype.one_lt_card hm hrN (mem_Lc.1 c.2) hc0 hu
  have hconst' : IsConst (p ^ e) (((α : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) / (b : AlgebraicClosure F)) := by
    rw [← hq]; exact hconst
  have huU := mem_maxUnram_of_isConst (Rfin Fq F) he hconst'
  have hFc : Fc Fq F (AlgebraicClosure F) m ≤ maxUnram (Rfin Fq F) F := by
    rw [maxUnram_eq_sSup]; exact le_sSup (Fc_mem_unramSet hq he m)
  have hbU := hFc b.2
  have hconstU : IsConst (Fintype.card Fq) (⟨_, huU⟩ : maxUnram (Rfin Fq F) F) := by
    obtain ⟨n, hn, hpow⟩ := hconst
    exact ⟨n, hn, Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hpow)⟩
  have hαeq : (α : maxUnram (Rfin Fq F) F) = ⟨_, huU⟩ * ⟨_, hbU⟩ := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul]
    exact (div_mul_cancel₀ _ hb0).symm
  refine (mem_fixUnits _ α).2 fun σ hσ => ?_
  rw [hαeq, map_mul, (mem_pi1geo _ _ _ σ).1 hσ _ hconstU, fixed_of_mem_Fc hq he m σ hσ ⟨_, hbU⟩ b.2]

/-- **Surjectivity**: every `z ∈ Pic⁰(X̄)[N]` is `Ψ α` for a parabolic radical `α`. -/
theorem exists_Psi_eq {z : PicBar (AlgebraicClosure F) hk} (hz : z ∈ PicBar0N (AlgebraicClosure F) hk N) :
    ∃ α : (maxUnram (Rfin Fq F) F)ˣ, ∃ hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N,
      kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D ∧ Psi hk N α = z := by
  obtain ⟨j, y, rfl⟩ := exists_lev_toBar hk z
  obtain ⟨a, ha, hdiv, hpsi⟩ := exists_psiAt_eq hk y hz.2
  have ha0 : (a : AlgebraicClosure F) ≠ 0 := fun h => ha (Subtype.ext (h.trans (ZeroMemClass.coe_zero _).symm))
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (a : AlgebraicClosure F) (NeZero.pos N)
  have hγU : γ ∈ maxUnram (Rfin Fq F) F :=
    (forall_dvd_ord_iff hk hq he (lev j) hNf ha).1 (fun v => hdiv (Sum.inl v)) γ hγ
  have hγ0 : (⟨γ, hγU⟩ : maxUnram (Rfin Fq F) F) ≠ 0 := by
    intro h
    have hγ' : γ = 0 := (congrArg Subtype.val h).trans (ZeroMemClass.coe_zero _)
    apply ha0
    rw [← hγ, hγ', zero_pow (NeZero.ne N)]
  have haα : (((Units.mk0 _ hγ0 : (maxUnram (Rfin Fq F) F)ˣ) : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) ^ N =
      a := hγ
  have hα : Units.mk0 _ hγ0 ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N := by
    refine (mem_rad _ _ _).2 fun σ hσ => fixed_of_mem_Fc hq he (lev j) σ hσ _ ?_
    rw [SubmonoidClass.coe_pow, haα]
    exact a.2
  refine ⟨_, hα, (kclass_mem_curveH1par_iff_ord hk hq he (lev j) hNi hζ hζΓ D hDB hlift ha hα haα).2.2
    (fun v => hdiv (Sum.inr v)), ?_⟩
  rw [Psi_eq hk _ a haα, hpsi]

include hNF in
/-- **K5d**: `H¹_par(π₁^geo, Z/N) ≃+ Pic⁰(X̄)[N]`, `[kchar α] ↦ [div(α ^ N) / N]`. -/
theorem exists_kummerPicEquiv :
    ∃ Φ : curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D ≃+ PicBar0N (AlgebraicClosure F) hk N,
      ∀ (α : (maxUnram (Rfin Fq F) F)ˣ) (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N)
        (hpar : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D),
        (Φ ⟨kclass hζ hζΓ hα, hpar⟩ : PicBar (AlgebraicClosure F) hk) = Psi hk N α := by
  choose r hr hrx using fun x : curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D =>
    kclass_surjective hζ hζΓ x.1
  have hrpar : ∀ x, kclass hζ hζΓ (hr x) ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D :=
    fun x => by rw [hrx x]; exact x.2
  let f : curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D →+ PicBar0N (AlgebraicClosure F) hk N :=
    AddMonoidHom.mk'
      (fun x => ⟨Psi hk N (r x), Psi_mem_PicBar0N hk hq he hNf hNi hζ hζΓ D hDB hlift (hr x) (hrpar x)⟩)
      (fun x y => Subtype.ext (by
        show Psi hk N (r (x + y)) = Psi hk N (r x) + Psi hk N (r y)
        rw [← Psi_mul hk hq he hNf hNi hζ hζΓ D hDB hlift (hr x) (hr y) (hrpar x)]
        refine Psi_congr hk hq he hNf hNi hζ hζΓ D hDB hlift (hr (x + y)) (mul_mem (hr x) (hr y)) ?_ ?_
        · rw [kclass_mul hζ hζΓ (hr x) (hr y), hrx x, hrx y]; exact add_mem x.2 y.2
        · exact ((hrx (x + y)).trans (Submodule.coe_add x y)).trans
            ((congrArg₂ (· + ·) (hrx x) (hrx y)).symm.trans (kclass_mul hζ hζΓ (hr x) (hr y)).symm)))
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : Psi hk N (r x) = 0 := congrArg Subtype.val hx
    have hfix := mem_fixUnits_of_Psi_eq_zero hk hq he hNf hNi hζ hζΓ D hDB hlift hNF (hr x) (hrpar x) h0
    exact Subtype.ext ((hrx x).symm.trans ((kclass_eq_zero_iff hζ hζΓ (hr x)).2 hfix))
  have hsurj : Function.Surjective f := by
    intro z
    have key := exists_Psi_eq hk hq he hNf hNi hζ hζΓ D hDB hlift z.2
    obtain ⟨α, hα, hpar, hΨ⟩ := key
    exact ⟨⟨kclass hζ hζΓ hα, hpar⟩, Subtype.ext
      ((Psi_congr hk hq he hNf hNi hζ hζΓ D hDB hlift (hr _) hα hpar (hrx _)).trans hΨ)⟩
  exact ⟨AddEquiv.ofBijective f ⟨hinj, hsurj⟩, fun α hα hpar =>
    Psi_congr hk hq he hNf hNi hζ hζΓ D hDB hlift (hr _) hα hpar (hrx _)⟩

end PsiMap

end Curve

end

end Kummer
end RamanujanPetersson

end


