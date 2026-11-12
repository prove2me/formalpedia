-- Prove2me | Definitions.Def_OddOrder_GroupTheory_PRank
-- name    : OddOrder_GroupTheory_PRank
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:46:37.134751+00:00
-- url     : https://prove2.me/theorems/b53798c6-b96a-4fd9-bff6-2fc79c18f040
-- title:
--   The $p$-rank of a group
-- statement:
--   Introduces the $p$-rank $r_p(G)$ of Bender–Glauberman and Isaacs: the largest $n$ for which $G$ contains an elementary abelian subgroup of order $p^n$, and the rank $r(G)=\sup_p r_p(G)$. Mathlib's `Group.rank` is the minimal number of generators, a different notion, hence the name `pRank`. Needed for BG §4 (Blackburn rank theory) and §5 (narrow $p$-groups).
--
--   Main definitions: `pRank` and `rank`, together with the linear-algebra bridge for elementary abelian groups: `IsElementaryAbelian.zmodModule` (an elementary abelian $p$-group as a $\mathbb{Z}/p$-module), `AddAut.toZModLinearEquiv`, and the isomorphisms $\mathrm{Aut}(M)\cong GL(n,\mathbb{F}_p)$ (`addAutEquivGL`, `mulAutEquivGeneralLinearGroup`).
--
--   The bundle also proves 32 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/PRank.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/PRank.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Free

open scoped IsMulCommutative

namespace OddOrder.GroupTheory

section Bridge

variable {p : ℕ} {G : Type*} [Group G]

/-- An elementary abelian `p`-group, viewed additively, is a `ZMod p`-module:
its commutativity gives `AddCommGroup (Additive G)`, and `x ^ p = 1` becomes `p • x = 0`. -/
@[reducible] noncomputable def IsElementaryAbelian.zmodModule [NeZero p]
    (h : IsElementaryAbelian p G) :
    letI : IsMulCommutative G := IsMulCommutative.of_comm h.comm
    Module (ZMod p) (Additive G) :=
  letI : IsMulCommutative G := IsMulCommutative.of_comm h.comm
  letI : CommGroup G := inferInstance
  AddCommGroup.zmodModule (G := Additive G) (n := p) (by
    intro x
    -- `p • x = 0` in `Additive G` ⟺ `x.toMul ^ p = 1` in `G`.
    have hx : (Additive.toMul x) ^ p = 1 := h.pow_eq_one _
    have h2 : Additive.ofMul ((Additive.toMul x) ^ p) = Additive.ofMul (1 : G) := by
      rw [hx]
    rw [ofMul_pow, ofMul_one, ofMul_toMul] at h2
    exact h2)

/-- **BG `m(A)` for elementary abelian `A`** (`p` prime): the order of an elementary
abelian `p`-group equals `p ^ m(A)`, where `m(A) = finrank (ZMod p) (Additive A)`.

Since `Ω₁(A) = A` for elementary abelian `A`, this is BG's identity `|Ω₁(A)| = p^{m(A)}`. -/
theorem IsElementaryAbelian.card_eq_pow_finrank [Fact p.Prime] [Finite G]
    (h : IsElementaryAbelian p G) :
    letI : IsMulCommutative G := IsMulCommutative.of_comm h.comm
    letI := h.zmodModule
    Nat.card G = p ^ Module.finrank (ZMod p) (Additive G) := by
  let : IsMulCommutative G := IsMulCommutative.of_comm h.comm
  let := h.zmodModule
  have hcard : Nat.card (Additive G) = Nat.card G := Nat.card_congr Additive.toMul
  have := FiniteField.pow_finrank_eq_natCard p (Additive G)
  rw [hcard] at this
  exact this.symm

/-- **`log_p |A| = m(A)`** for elementary abelian `A` (`p` prime): the `p`-logarithm of the
order recovers the `F_p`-dimension `m(A) = finrank (ZMod p) (Additive A)`.

This is the half of the BG two-form bridge feeding `pRank`: the summand `Nat.log p |A|` in the
`pRank` `iSup` equals BG's `m(A)`. -/
theorem IsElementaryAbelian.log_card_eq_finrank [Fact p.Prime] [Finite G]
    (h : IsElementaryAbelian p G) :
    letI : IsMulCommutative G := IsMulCommutative.of_comm h.comm
    letI := h.zmodModule
    Nat.log p (Nat.card G) = Module.finrank (ZMod p) (Additive G) := by
  let : IsMulCommutative G := IsMulCommutative.of_comm h.comm
  let := h.zmodModule
  rw [h.card_eq_pow_finrank, Nat.log_pow (Fact.out : p.Prime).one_lt]

end Bridge

section AutGL

/-- The automorphism group of a `ZMod p`-module `M` (as an additive group) is multiplicatively
equivalent to the group of `ZMod p`-linear automorphisms of `M`. (`AddAut M` is an *additive*
group in mathlib, so its multiplicative incarnation is `Multiplicative (AddAut M)`.)

Every additive automorphism of `M` is automatically `ZMod p`-linear, because an additive map
preserves the `ZMod p`-scalar action (`ZMod.map_smul`): the action `c • x` is determined by the
group structure (`c • x = (c.val) • x` as an iterated sum), which any `AddMonoidHom` respects. -/
noncomputable def AddAut.toZModLinearEquiv {p : ℕ} {M : Type*}
    [AddCommGroup M] [Module (ZMod p) M] :
    Multiplicative (AddAut M) ≃* (M ≃ₗ[ZMod p] M) where
  toFun e := { e.toAdd with map_smul' := ZMod.map_smul e.toAdd.toAddMonoidHom }
  invFun e := Multiplicative.ofAdd { e.toAddEquiv with }
  left_inv _ := rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- **`Aut(M) ≅ GL(n, F_p)` for a finite `ZMod p`-module** (`p` prime,
`n = finrank (ZMod p) M`): the additive automorphism group of a finite `F_p`-vector space `M` is
multiplicatively equivalent to the general linear group `GL(Fin n, ZMod p)`.

This is the abstract `[Module (ZMod p) M]` form. Keeping the module abstract (rather than the
`letI`-bound `zmodModule` structure on `Additive E`) is essential: with a `letI`-bound local
module instance, the `Module.Finite` / `Module.Free` / basis instance synthesis gets stuck on the
shared module argument. The `Additive E`-specific form is obtained in
`IsElementaryAbelian.mulAutEquivGeneralLinearGroup` by composing with `AddAutAdditive`. -/
noncomputable def IsElementaryAbelian.addAutEquivGL {p : ℕ} [Fact p.Prime] {M : Type*}
    [AddCommGroup M] [Module (ZMod p) M] [Finite M] :
    Multiplicative (AddAut M) ≃* GL (Fin (Module.finrank (ZMod p) M)) (ZMod p) := by
  haveI : Module.Finite (ZMod p) M := Module.Finite.of_finite
  let b : Module.Basis (Fin (Module.finrank (ZMod p) M)) (ZMod p) M :=
    Module.finBasisOfFinrankEq (ZMod p) M rfl
  exact (AddAut.toZModLinearEquiv).trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) M).symm.trans
      (Matrix.GeneralLinearGroup.toLin' b).symm)

/-- **`Aut(E) ≅ GL(m(E), F_p)`** for an elementary abelian `p`-group `E` (`p` prime), where
`m(E) = finrank (ZMod p) (Additive E)` is BG's `m(E)`.

This is the standard bridge underlying BG Lem 4.13 and Thm 4.16: viewing `E` additively as an
`F_p`-vector space, `MulAut E` is multiplicatively equivalent to the general linear group of
dimension `m(E)` over `F_p`. The multiplicativity is honest (no anti-homomorphism flip): the
`AddAutAdditive` leg is a genuine `≃+` in the direction `AddAut (Additive E) → Additive (MulAut E)`,
transported to a `≃*` by `AddEquiv.toMultiplicativeLeft`. -/
noncomputable def IsElementaryAbelian.mulAutEquivGeneralLinearGroup
    {p : ℕ} {E : Type*} [Group E] [Finite E] [Fact p.Prime]
    (hE : IsElementaryAbelian p E) :
    letI : IsMulCommutative E := IsMulCommutative.of_comm hE.comm
    letI := hE.zmodModule
    MulAut E ≃* GL (Fin (Module.finrank (ZMod p) (Additive E))) (ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : IsMulCommutative E := IsMulCommutative.of_comm hE.comm
  letI := hE.zmodModule
  haveI : Finite (Additive E) := inferInstanceAs (Finite E)
  -- `AddAutAdditive : AddAut (Additive E) ≃+ Additive (MulAut E)`;
  -- `AddEquiv.toMultiplicativeLeft` turns it into
  -- `Multiplicative (AddAut (Additive E)) ≃* MulAut E`.
  exact (AddEquiv.toMultiplicativeLeft (AddAutAdditive (G := E))).symm.trans
    IsElementaryAbelian.addAutEquivGL

/-- **`|Aut(E)| = ∏ (pⁿ - pⁱ)`** for an elementary abelian `p`-group `E` (`p` prime), where
`n = m(E) = finrank (ZMod p) (Additive E)`.

This is the standard order formula underlying BG Thm 4.16: `|Aut(E)| = |GL(n, p)|`. For `n = 2`
(BG's case `|E| = p²`) the product is `(p² - 1)(p² - p) = p(p² - 1)(p - 1)`, matching BG's
`|GL(2, p)| = p(p² - 1)(p - 1)` (via `Fin.prod_univ_two`). -/
theorem IsElementaryAbelian.card_mulAut
    {p : ℕ} {E : Type*} [Group E] [Finite E] [Fact p.Prime]
    (hE : IsElementaryAbelian p E) :
    letI : IsMulCommutative E := IsMulCommutative.of_comm hE.comm
    letI := hE.zmodModule
    Nat.card (MulAut E) =
      ∏ i : Fin (Module.finrank (ZMod p) (Additive E)),
        (p ^ Module.finrank (ZMod p) (Additive E) - p ^ (i : ℕ)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let : IsMulCommutative E := IsMulCommutative.of_comm hE.comm
  let := hE.zmodModule
  rw [Nat.card_congr (hE.mulAutEquivGeneralLinearGroup).toEquiv,
      Matrix.card_GL_field, ZMod.card]

/-- A `p`-subgroup `K` of a finite group whose order is **not** divisible by `p²` has
`|K| ≤ p`. This is the abstract heart of the rank-`≤ 2` squeeze: a `p`-subgroup of
`GL(n, p)` with `n ≤ 2` has order `≤ p`, because `p² ∤ |GL(n, p)|` for `n ≤ 2`. -/
theorem card_le_prime_of_isPGroup_of_not_sq_dvd {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {K : Subgroup G} (hK : IsPGroup p K) (hnsq : ¬ p ^ 2 ∣ Nat.card G) :
    Nat.card K ≤ p := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK
  rw [hk]
  by_contra hlt
  push Not at hlt
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    have hle : p ^ k ≤ p := by
      calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le (by omega)
        _ = p := pow_one p
    omega
  exact hnsq ((pow_dvd_pow p hk2).trans (hk ▸ K.card_subgroup_dvd_card))

/-- `p² ∤ ∏_{i<n}(pⁿ - pⁱ)` for `n ≤ 2` (`p` prime). This is the order of `GL(n, p)`; its
`p`-adic valuation is `n(n-1)/2 ≤ 1` when `n ≤ 2`. -/
private theorem not_sq_dvd_prod_pow_sub {p n : ℕ} (hp : p.Prime) (hn : n ≤ 2) :
    ¬ p ^ 2 ∣ ∏ i : Fin n, (p ^ n - p ^ (i : ℕ)) := by
  have h2p : 2 ≤ p := hp.two_le
  interval_cases n
  · -- n = 0: empty product = 1
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    intro h
    have hle := Nat.le_of_dvd one_pos h
    have h4 : (2 : ℕ) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left h2p 2
    norm_num at h4
    omega
  · -- n = 1: product = p - 1
    simp only [Fin.prod_univ_one, Fin.val_zero, pow_zero, pow_one]
    intro h
    have hle := Nat.le_of_dvd (by omega) h
    have hps : p ≤ p ^ 2 := Nat.le_self_pow two_ne_zero p
    omega
  · -- n = 2: product = (p² - 1)(p² - p)
    simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    have hpp : p ^ 2 - p = p * (p - 1) := by rw [Nat.mul_sub_one, pow_two]
    have hfac : (p ^ 2 - 1) * (p ^ 2 - p) = p * ((p ^ 2 - 1) * (p - 1)) := by
      rw [hpp]; ring
    intro hdvd
    rw [hfac, pow_two] at hdvd
    have hM : p ∣ (p * p - 1) * (p - 1) := (Nat.mul_dvd_mul_iff_left hp.pos).mp hdvd
    rcases hp.dvd_mul.mp hM with h1 | h2
    · -- p ∣ p*p - 1 : impossible since p ∣ p*p
      have hpsq : p ∣ p * p := dvd_mul_right p p
      have hd1 : p ∣ p * p - (p * p - 1) := Nat.dvd_sub hpsq h1
      have hX1 : 1 ≤ p * p := by nlinarith
      have : p * p - (p * p - 1) = 1 := by omega
      rw [this] at hd1
      exact hp.one_lt.ne' (Nat.dvd_one.mp hd1)
    · -- p ∣ p - 1 : impossible since 0 < p - 1 < p
      have := Nat.le_of_dvd (by omega) h2
      omega

/-- **`|p`-subgroup of `Aut(E)| ≤ p`** for an elementary abelian `E` of order `≤ p²`
(`p` prime): since `p² ∤ |Aut(E)|` when `m(E) ≤ 2`, any `p`-subgroup of `MulAut E` has
order `≤ p`. This is the rank-`≤ 2` GL squeeze, packaged for the conjugation action in
Gorenstein Theorem 4.15(i). -/
theorem card_pSubgroup_mulAut_le_prime_of_card_le_prime_sq
    {E : Type*} [Group E] [Finite E] {p : ℕ} [Fact p.Prime]
    (hE : IsElementaryAbelian p E) (hcard : Nat.card E ≤ p ^ 2)
    {K : Subgroup (MulAut E)} (hK : IsPGroup p K) :
    Nat.card K ≤ p := by
  have hp := (Fact.out : p.Prime)
  refine card_le_prime_of_isPGroup_of_not_sq_dvd hK ?_
  rw [hE.card_mulAut]
  refine not_sq_dvd_prod_pow_sub hp ?_
  have hcardE := hE.card_eq_pow_finrank
  rw [hcardE] at hcard
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcard

/-- **GL number-theory kernel for BG Lemma 4.13 / Gorenstein Theorem 4.15(ii).** Let `E` be an
elementary abelian `p`-group of order `≤ p²` and `σ : MulAut E` an automorphism of prime order
`q ≠ p`. Then `q ∣ p² - 1`.

Here `Aut(E) = GL(m, p)` with `m = m(E) ≤ 2`, and `|GL(m, p)| = ∏_{i<m}(pᵐ - pⁱ)`. For `m ≤ 2`
the `p`-free part of this order divides `(p² - 1)(p - 1)`, so a prime `q ≠ p` dividing it divides
`p² - 1` (using `p - 1 ∣ p² - 1`). This is the rank-`≤ 2` half of BG's `q ∣ p² - 1` and is used
once `q` is realized as acting on the elementary abelian quotient `D / Φ(D)` of the minimal
special subgroup `D` of precursor 2. -/
theorem prime_dvd_prime_sq_sub_one_of_orderOf_mulAut {p q : ℕ} [Fact p.Prime] (hq : q.Prime)
    (hqp : q ≠ p) {E : Type*} [Group E] [Finite E] (hE : IsElementaryAbelian p E)
    (hcard : Nat.card E ≤ p ^ 2) {σ : MulAut E} (hσ : orderOf σ = q) :
    q ∣ p ^ 2 - 1 := by
  have hp := (Fact.out : p.Prime)
  let : IsMulCommutative E := IsMulCommutative.of_comm hE.comm
  let := hE.zmodModule
  -- `q = |σ| ∣ |MulAut E| = ∏_{i<n}(pⁿ - pⁱ)`, `n = m(E) ≤ 2`.
  set n := Module.finrank (ZMod p) (Additive E) with hn
  have hcardE : Nat.card E = p ^ n := hE.card_eq_pow_finrank
  have hn2 : n ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcardE ▸ hcard)
  have hqdvd : q ∣ ∏ i : Fin n, (p ^ n - p ^ (i : ℕ)) := by
    rw [← hE.card_mulAut, ← hσ]; exact orderOf_dvd_natCard σ
  -- `p - 1 ∣ p² - 1`.
  have hp1dvd : p - 1 ∣ p ^ 2 - 1 := by
    rcases p with _ | b
    · simp
    · rw [Nat.succ_sub_one, show (b + 1) ^ 2 = b * (b + 2) + 1 from by ring, Nat.add_sub_cancel]
      exact dvd_mul_right b (b + 2)
  -- Split on `m(E) ∈ {0, 1, 2}`.
  interval_cases n
  · simp only [Finset.univ_eq_empty, Finset.prod_empty, Nat.dvd_one] at hqdvd
    exact absurd hqdvd hq.ne_one
  · simp only [Fin.prod_univ_one, Fin.val_zero, pow_zero, pow_one] at hqdvd
    exact hqdvd.trans hp1dvd
  · simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      show p ^ 2 - p = p * (p - 1) from by rw [Nat.mul_sub_one, pow_two]] at hqdvd
    rcases hq.dvd_mul.mp hqdvd with h1 | h2
    · exact h1
    · rcases hq.dvd_mul.mp h2 with hpp | hp1
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp hpp) hqp
      · exact hp1.trans hp1dvd

/-- **`q < p` companion** for BG Lemma 4.13 (`p` odd). If `p, q` are primes, `p` is odd,
`q ≠ p`, and `q ∣ p² - 1`, then `q < p`.

`p² - 1 = (p-1)(p+1)`; a prime `q ≠ p` dividing it divides `p-1` (giving `q ≤ p-1 < p`) or
`p+1`. For odd `p` the factor `p+1` is even and `> 2`, so it is not prime, hence `q ≠ p+1` and
`q ≤ p+1` forces `q ≤ p-1 < p`. (Pairs with `prime_dvd_prime_sq_sub_one_of_orderOf_mulAut`.) -/
theorem lt_of_prime_dvd_prime_sq_sub_one {p q : ℕ} (hp : p.Prime) (hpo : Odd p) (hq : q.Prime)
    (hqp : q ≠ p) (hdvd : q ∣ p ^ 2 - 1) : q < p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hfac : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    rcases p with _ | b
    · simp
    · rw [Nat.succ_sub_one, show (b + 1) ^ 2 = b * (b + 2) + 1 from by ring, Nat.add_sub_cancel]
  rw [hfac] at hdvd
  rcases hq.dvd_mul.mp hdvd with h1 | h2
  · exact lt_of_le_of_lt (Nat.le_of_dvd (by omega) h1) (by omega)
  · have hle : q ≤ p + 1 := Nat.le_of_dvd (by omega) h2
    have hqne1 : q ≠ p + 1 := by
      intro hq1
      have hev : Even (p + 1) := hpo.add_one
      rw [← hq1] at hev
      have : q = 2 := (Nat.Prime.even_iff hq).mp hev
      omega
    omega

end AutGL

variable (G : Type*) [Group G]

/-- **p-Rank of a group**: the maximum `n` such that `G` contains an elementary abelian
`p`-subgroup of order `p^n`.

For `G = ⊥` or no elementary abelian `p`-subgroup besides `⊥`, this is `0`.

**注**: mathlib v4.30.0-rc2 の `Group.rank G` は **minimum generators 数** で別概念.
本 def の命名 `pRank` で衝突回避. -/
noncomputable def pRank (p : ℕ) : ℕ :=
  ⨆ A : {A : Subgroup G // A.IsElementaryAbelian p}, Nat.log p (Nat.card (A.val : Subgroup G))

/-- **Rank of a group** `r(G) = ⨆_{p prime} pRank G p` (BG §4, p.33): the
supremum of the `p`-ranks over all primes `p`.

The indexing type records primality explicitly. This matches BG's convention and prevents
composite exponents from contributing spurious `pRank` summands. -/
noncomputable def rank : ℕ :=
  ⨆ p : {p : ℕ // p.Prime}, pRank G p.1

variable {G}

section Properties

variable {p : ℕ}

/-- The trivial subgroup `⊥` is elementary abelian (every element is `1`). -/
theorem bot_isElementaryAbelian : (⊥ : Subgroup G).IsElementaryAbelian p :=
  ⟨fun x y => by
      have hx : (x : G) = 1 := Subgroup.mem_bot.mp x.2
      have hy : (y : G) = 1 := Subgroup.mem_bot.mp y.2
      apply Subtype.ext
      push_cast
      rw [hx, hy],
    fun x => by
      have hx : (x : G) = 1 := Subgroup.mem_bot.mp x.2
      apply Subtype.ext
      push_cast
      rw [hx, one_pow]⟩

/-- The index type of the `pRank` supremum is nonempty: the trivial subgroup `⊥` is
elementary abelian. -/
theorem pRank_index_nonempty :
    Nonempty {A : Subgroup G // A.IsElementaryAbelian p} :=
  ⟨⟨⊥, bot_isElementaryAbelian⟩⟩

/-- **BddAbove for `pRank`** (`[Finite G]`): every elementary abelian subgroup `A` satisfies
`log_p |A| ≤ log_p |G|`, so the family defining `pRank G p` is bounded above by `log_p |G|`.

Without finiteness the family can be unbounded and the `iSup` collapses to `0` (the `ℕ`
`sSup` convention), so this hypothesis is essential for `pRank` to be meaningful. -/
theorem pRank_bddAbove [Finite G] :
    BddAbove (Set.range fun A : {A : Subgroup G // A.IsElementaryAbelian p} =>
      Nat.log p (Nat.card (A.val : Subgroup G))) := by
  refine ⟨Nat.log p (Nat.card G), ?_⟩
  rintro _ ⟨A, rfl⟩
  exact Nat.log_mono_right (Subgroup.card_le_card_group A.val)

/-- The `pRank` summand of any elementary abelian subgroup is `≤ pRank G p` (`[Finite G]`). -/
theorem le_pRank [Finite G] (A : Subgroup G) (hA : A.IsElementaryAbelian p) :
    Nat.log p (Nat.card A) ≤ pRank G p :=
  le_ciSup pRank_bddAbove (⟨A, hA⟩ : {A : Subgroup G // A.IsElementaryAbelian p})

/-- **Evaluation lemma for `pRank`** (`[Finite G]`):
`pRank G p ≤ n ⟺ ∀ elementary abelian `A ≤ G`, `log_p |A| ≤ n`.

This is the workhorse characterisation used throughout BG §4: bounding the `p`-rank is
equivalent to bounding `log_p` of the order of every elementary abelian `p`-subgroup. -/
theorem pRank_le_iff [Finite G] {n : ℕ} :
    pRank G p ≤ n ↔ ∀ A : Subgroup G, A.IsElementaryAbelian p → Nat.log p (Nat.card A) ≤ n := by
  have := pRank_index_nonempty (G := G) (p := p)
  rw [pRank, ciSup_le_iff pRank_bddAbove]
  constructor
  · intro h A hA
    exact h ⟨A, hA⟩
  · intro h A
    exact h A.val A.2

/-- **Existence side for a positive `pRank` lower bound** (`[Finite G]`).
If `n ≤ pRank G p` and `n > 0`, then some elementary abelian subgroup has
`p`-logarithmic order at least `n`. This is the contrapositive form of
`pRank_le_iff`, avoiding direct manipulation of the `iSup` witness. -/
theorem exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank [Finite G] {n : ℕ}
    (hnpos : 0 < n) (hn : n ≤ pRank G p) :
    ∃ A : Subgroup G, A.IsElementaryAbelian p ∧ n ≤ Nat.log p (Nat.card A) := by
  by_contra hnone
  push Not at hnone
  have hrank_le : pRank G p ≤ n - 1 := by
    rw [pRank_le_iff]
    intro A hA
    have hlt : Nat.log p (Nat.card A) < n := hnone A hA
    omega
  omega

/-- An elementary abelian subgroup whose logarithmic `p`-size is at least two is noncyclic.

This is stated without a primality hypothesis on `p`; the logarithmic lower bound rules out
`p = 0, 1`, and cyclicity would force the cardinality to divide `p`, contradicting
`p ^ 2 ≤ |A|`. -/
theorem not_isCyclic_of_isElementaryAbelian_of_two_le_log_card [Finite G] {p : ℕ}
    {A : Subgroup G} (hA : A.IsElementaryAbelian p)
    (hlog : 2 ≤ Nat.log p (Nat.card A)) :
    ¬ IsCyclic ↥A := by
  intro hcyc
  have hp_gt_one : 1 < p := by
    by_contra hpnot
    have hp_le : p ≤ 1 := by omega
    interval_cases p
    · simp at hlog
    · simp at hlog
  have hcard_ge : p ^ 2 ≤ Nat.card A :=
    (Nat.le_log_iff_pow_le hp_gt_one Nat.card_pos.ne').mp hlog
  have : IsCyclic ↥A := hcyc
  have hExp_eq : Monoid.exponent ↥A = Nat.card ↥A := IsCyclic.exponent_eq_card
  have hExp_dvd_p : Monoid.exponent ↥A ∣ p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    exact hA.pow_eq_one
  have hcard_dvd_p : Nat.card ↥A ∣ p := by
    simpa [hExp_eq] using hExp_dvd_p
  have hcard_le_p : Nat.card ↥A ≤ p := Nat.le_of_dvd (by omega : 0 < p) hcard_dvd_p
  have hp_lt_sq : p < p ^ 2 := by
    have := pow_lt_pow_right₀ hp_gt_one (by norm_num : (1 : ℕ) < 2)
    simpa using this
  exact (not_lt_of_ge (hcard_ge.trans hcard_le_p)) hp_lt_sq

/-- A `pRank` lower bound of two gives a noncyclic elementary abelian subgroup. -/
theorem exists_isElementaryAbelian_not_isCyclic_of_two_le_pRank [Finite G] {p : ℕ}
    (hpRank : 2 ≤ pRank G p) :
    ∃ A : Subgroup G, A.IsElementaryAbelian p ∧ ¬ IsCyclic ↥A := by
  obtain ⟨A, hA, hlog⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := G) (p := p) (n := 2) (by norm_num) hpRank
  exact ⟨A, hA, not_isCyclic_of_isElementaryAbelian_of_two_le_log_card hA hlog⟩

/-- **`pRank ≤ 1` from cyclic elementary abelian subgroups** (`[Finite G]`): if every
elementary abelian `p`-subgroup of `G` is cyclic, then `pRank G p ≤ 1`.

A cyclic elementary abelian `p`-group has order `1` or `p`, so its `log_p`-size is `≤ 1`
(`not_isCyclic_of_isElementaryAbelian_of_two_le_log_card` rules out size `≥ 2`).  The Sylow
form of "rank one" (`p`-Sylow cyclic) feeds in through this, since every elementary abelian
`p`-subgroup embeds in a (cyclic) Sylow `p`-subgroup. -/
theorem pRank_le_one_of_forall_isElementaryAbelian_isCyclic [Finite G]
    (h : ∀ A : Subgroup G, A.IsElementaryAbelian p → IsCyclic ↥A) :
    pRank G p ≤ 1 := by
  rw [pRank_le_iff]
  intro A hA
  by_contra hlt
  exact not_isCyclic_of_isElementaryAbelian_of_two_le_log_card hA (by omega) (h A hA)

/-- **`pRank` lower bound** (`[Finite G]`, `p` prime): an elementary abelian subgroup of
order `p ^ n` witnesses `n ≤ pRank G p`. This is the existence-side companion to the
evaluation lemma `pRank_le_iff`. -/
theorem pow_le_card_of_le_pRank [Finite G] [Fact p.Prime] {n : ℕ} (A : Subgroup G)
    (hA : A.IsElementaryAbelian p) (hcard : Nat.card A = p ^ n) :
    n ≤ pRank G p := by
  have := le_pRank A hA
  rwa [hcard, Nat.log_pow (Fact.out : p.Prime).one_lt] at this

/-- For an elementary abelian `p`-group, `log_p |G| ≤ pRank G p`: `G` is its own maximal
elementary abelian subgroup, so its rank is realised. Lets one bound `|G|` by a `pRank`
bound (`|G| = p^{log_p|G|} ≤ p^{pRank}`). -/
theorem IsElementaryAbelian.log_card_le_pRank [Finite G] [Fact p.Prime]
    (hG : IsElementaryAbelian p G) :
    Nat.log p (Nat.card G) ≤ pRank G p := by
  have : IsMulCommutative G := IsMulCommutative.of_comm hG.comm
  have htop : (⊤ : Subgroup G).IsElementaryAbelian p :=
    IsElementaryAbelian.of_mulEquiv Subgroup.topEquiv.symm hG
  refine pow_le_card_of_le_pRank ⊤ htop ?_
  rw [Subgroup.card_top, hG.log_card_eq_finrank]
  exact hG.card_eq_pow_finrank

/-- **Monotonicity under subgroup inclusion** (`[Finite G]`): an injective homomorphism
`f : H →* G` (e.g. a subgroup inclusion) cannot increase the `p`-rank: `pRank H p ≤ pRank G p`.

Elementary abelian subgroups of `H` map injectively to elementary abelian subgroups of `G`
of the same order, so every `pRank H p` summand is realised in `G`. -/
theorem pRank_le_of_injective [Finite G] {H : Type*} [Group H] [Finite H]
    {f : H →* G} (hf : Function.Injective f) :
    pRank H p ≤ pRank G p := by
  rw [pRank_le_iff]
  intro A hA
  -- `A.map f ≤ G` is elementary abelian of the same order as `A`.
  have hmap : (A.map f).IsElementaryAbelian p := Subgroup.IsElementaryAbelian.map hf hA
  have hcard : Nat.card (A.map f) = Nat.card A :=
    Subgroup.card_map_of_injective hf
  calc
    Nat.log p (Nat.card A) = Nat.log p (Nat.card (A.map f)) := by rw [hcard]
    _ ≤ pRank G p := le_pRank (A.map f) hmap

/-- **Monotonicity under subgroup inclusion** (`[Finite G]`), subgroup form:
`pRank H p ≤ pRank G p` for `H ≤ G`, via the inclusion `H.subtype`. -/
theorem pRank_mono_of_le [Finite G] (H : Subgroup G) :
    pRank H p ≤ pRank G p :=
  pRank_le_of_injective H.subtype_injective

/-- The `p`-rank is realised inside any Sylow `p`-subgroup.

Every elementary abelian `p`-subgroup lies in some Sylow subgroup, and Sylow subgroups are
conjugate, so bounding one Sylow subgroup bounds the ambient `p`-rank. -/
theorem pRank_le_pRank_sylow [Finite G] [Fact p.Prime] (S : Sylow p G) :
    pRank G p ≤ pRank ↥(S : Subgroup G) p := by
  classical
  rw [pRank_le_iff]
  intro E hE
  have hE_pg : IsPGroup p ↥E := fun x => ⟨1, by rw [pow_one]; exact hE.pow_eq_one x⟩
  obtain ⟨Q, hQle⟩ := hE_pg.exists_le_sylow
  have h1 : Nat.log p (Nat.card ↥E) ≤ pRank ↥(Q : Subgroup G) p := by
    have hsub : (E.subgroupOf (Q : Subgroup G)).IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQle).symm hE
    have hcard : Nat.card ↥(E.subgroupOf (Q : Subgroup G)) = Nat.card ↥E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv
    rw [← hcard]
    exact le_pRank _ hsub
  exact h1.trans
    (pRank_le_of_injective (f := (Sylow.equiv Q S).toMonoidHom)
      (Sylow.equiv Q S).injective)

/-- A Sylow `p`-subgroup has the same `p`-rank as the ambient finite group. -/
theorem pRank_sylow_eq [Finite G] [Fact p.Prime] (S : Sylow p G) :
    pRank ↥(S : Subgroup G) p = pRank G p :=
  le_antisymm (pRank_mono_of_le (S : Subgroup G)) (pRank_le_pRank_sylow S)

/-- **`p`-rank is unchanged under passing to a subgroup of coprime index.** If `H ≤ K` and the
prime `r` does not divide the index `[K : H]`, then a Sylow `r`-subgroup of `H` has full `r`-power
order in `K`, hence is a Sylow `r`-subgroup of `K`; so `r_r(H) = r_r(K)`.  Typical use: a Hall
subgroup `H` of `K` with `r ∈ π(H)` satisfies `r ∤ [K : H]`, giving `r_r(H) = r_r(K)`. -/
theorem pRank_eq_of_le_of_not_dvd_index [Finite G] {r : ℕ}
    [Fact r.Prime] {H K : Subgroup G} (hHK : H ≤ K)
    (hidx : ¬ r ∣ (H.subgroupOf K).index) : pRank ↥H r = pRank ↥K r := by
  obtain ⟨R⟩ : Nonempty (Sylow r ↥H) := inferInstance
  set Rincl : Subgroup ↥K := (R : Subgroup ↥H).map (Subgroup.inclusion hHK) with hRincl
  have hcardRincl : Nat.card ↥Rincl = r ^ (Nat.card ↥K).factorization r := by
    have hidxcard : Nat.card ↥H * (H.subgroupOf K).index = Nat.card ↥K := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv]
      exact (H.subgroupOf K).card_mul_index
    have hidx_ne : (H.subgroupOf K).index ≠ 0 := by
      intro h; rw [h, mul_zero] at hidxcard; exact (Nat.card_pos).ne' hidxcard.symm
    have hfact : (Nat.card ↥K).factorization r = (Nat.card ↥H).factorization r := by
      rw [← hidxcard, Nat.factorization_mul (Nat.card_pos).ne' hidx_ne, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
    rw [hRincl, Subgroup.card_map_of_injective (Subgroup.inclusion_injective hHK),
      R.card_eq_multiplicity, hfact]
  have eR : ↥(R : Subgroup ↥H) ≃* ↥Rincl :=
    hRincl ▸ Subgroup.equivMapOfInjective _ (Subgroup.inclusion hHK)
      (Subgroup.inclusion_injective hHK)
  have hSylK : pRank ↥Rincl r = pRank ↥K r := by
    have h := pRank_sylow_eq (Sylow.ofCard Rincl hcardRincl)
    rwa [Sylow.coe_ofCard] at h
  rw [← pRank_sylow_eq R, ← hSylK]
  exact le_antisymm (pRank_le_of_injective (f := eR.toMonoidHom) eR.injective)
    (pRank_le_of_injective (f := eR.symm.toMonoidHom) eR.symm.injective)

end Properties

section Rank

variable {p : ℕ}

/-- **Uniform `pRank` bound** (`[Finite G]`, `2 ≤ p`): `pRank G p ≤ Nat.log 2 |G|`.

Since any elementary abelian `p`-subgroup `A` has `|A| ≤ |G|` and `Nat.log p ≤ Nat.log 2`
for `p ≥ 2`, every `p`-rank is bounded by `Nat.log 2 |G|` *independently of `p`*; this is the
key bound making the all-primes supremum `rank G` well-defined (`rank_bddAbove`). -/
theorem pRank_le_log_two [Finite G] (hp : 2 ≤ p) :
    pRank G p ≤ Nat.log 2 (Nat.card G) := by
  rw [pRank_le_iff]
  intro A _
  calc
    Nat.log p (Nat.card A) ≤ Nat.log 2 (Nat.card A) :=
      Nat.log_anti_left (by norm_num) hp
    _ ≤ Nat.log 2 (Nat.card G) := Nat.log_mono_right (Subgroup.card_le_card_group A)

/-- **BddAbove for `rank`** (`[Finite G]`): prime-indexed `pRank` summands are uniformly
bounded by `log₂ |G|`. -/
theorem rank_bddAbove [Finite G] :
    BddAbove (Set.range fun p : {p : ℕ // p.Prime} => pRank G p.1) := by
  refine ⟨Nat.log 2 (Nat.card G), ?_⟩
  rintro _ ⟨p, rfl⟩
  exact pRank_le_log_two p.2.two_le

/-- The `p`-rank is `≤ rank G` for every prime `p` (`[Finite G]`). -/
theorem pRank_le_rank [Finite G] (p : ℕ) [Fact p.Prime] : pRank G p ≤ rank G :=
  le_ciSup rank_bddAbove (⟨p, (Fact.out : p.Prime)⟩ : {p : ℕ // p.Prime})

/-- **Evaluation lemma for `rank`** (`[Finite G]`):
`rank G ≤ n ⟺ ∀ p` prime, `pRank G p ≤ n`. -/
theorem rank_le_iff [Finite G] {n : ℕ} :
    rank G ≤ n ↔ ∀ p : ℕ, p.Prime → pRank G p ≤ n := by
  have : Nonempty {p : ℕ // p.Prime} := ⟨⟨2, Nat.prime_two⟩⟩
  rw [rank, ciSup_le_iff rank_bddAbove]
  constructor
  · intro h p hp
    exact h ⟨p, hp⟩
  · intro h p
    exact h p.1 p.2

/-- **Monotonicity of `rank` under an injective homomorphism** (`[Finite G]`):
`rank H ≤ rank G` whenever `f : H →* G` is injective. -/
theorem rank_le_of_injective [Finite G] {H : Type*} [Group H] [Finite H]
    {f : H →* G} (hf : Function.Injective f) :
    rank H ≤ rank G := by
  rw [rank_le_iff]
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  exact (pRank_le_of_injective hf).trans (pRank_le_rank (G := G) p)

/-- **A nontrivial elementary abelian subgroup of a rank-≤-2 subgroup has order `p` or `p²`**
(`[Finite G]`): its order is `p^k` with `1 ≤ k = log_p |A| ≤ pRank B ≤ rank B ≤ 2`. -/
theorem card_eq_prime_or_sq_of_isElementaryAbelian_le [Finite G] {p : ℕ} [Fact p.Prime]
    {A B : Subgroup G} (hA : A.IsElementaryAbelian p) (hAB : A ≤ B)
    (hrank : rank ↥B ≤ 2) (hne : A ≠ ⊥) :
    Nat.card ↥A = p ∨ Nat.card ↥A = p ^ 2 := by
  obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥A = p ^ k := ⟨_, hA.card_eq_pow_finrank⟩
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    exact hne (Subgroup.card_eq_one.mp (by rw [hk, hk0, pow_zero]))
  have hk2 : k ≤ 2 := by
    have hsub : (A.subgroupOf B).IsElementaryAbelian p :=
      Subgroup.IsElementaryAbelian.of_map (f := B.subtype) B.subtype_injective
        (by rwa [Subgroup.map_subgroupOf_eq_of_le hAB])
    have hle := le_pRank (A.subgroupOf B) hsub
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv, hk,
      Nat.log_pow (Fact.out : p.Prime).one_lt] at hle
    exact hle.trans ((pRank_le_rank p).trans hrank)
  interval_cases k
  · exact Or.inl (by rw [hk, pow_one])
  · exact Or.inr hk

/-- **Existence side for a positive `rank` lower bound** (`[Finite G]`).
If `n ≤ rank G` and `n > 0`, then some prime `p` has `pRank G p ≥ n`. -/
theorem exists_pRank_ge_of_pos_le_rank [Finite G] {n : ℕ} (hnpos : 0 < n)
    (hn : n ≤ rank G) :
    ∃ p : ℕ, p.Prime ∧ n ≤ pRank G p := by
  by_contra hnone
  have hrank_le : rank G ≤ n - 1 := by
    rw [rank_le_iff]
    intro p hp
    have hnot : ¬ n ≤ pRank G p := by
      intro hpRank
      exact hnone ⟨p, hp, hpRank⟩
    omega
  omega

/-- A subgroup of ambient rank at least two contains a noncyclic elementary abelian subgroup,
viewed back in the ambient group.

Because `rank` is indexed over primes, the extracted `p` is immediately suitable for
BG Theorem 9.1 statements requiring `[Fact p.Prime]`. -/
theorem exists_isElementaryAbelian_not_isCyclic_le_of_two_le_rank [Finite G]
    (K : Subgroup G) (hr : 2 ≤ rank ↥K) :
    ∃ p : ℕ, p.Prime ∧
      ∃ A : Subgroup G, A.IsElementaryAbelian p ∧ A ≤ K ∧ ¬ IsCyclic ↥A := by
  obtain ⟨p, hp, hpRank⟩ :=
    exists_pRank_ge_of_pos_le_rank (G := ↥K) (n := 2) (by norm_num) hr
  obtain ⟨A, hA, hAnc⟩ :=
    exists_isElementaryAbelian_not_isCyclic_of_two_le_pRank (G := ↥K) (p := p) hpRank
  let B : Subgroup G := A.map K.subtype
  have hBea : B.IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.map K.subtype_injective hA
  have hBle : B ≤ K := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  have hBnc : ¬ IsCyclic ↥B := by
    intro hBcyc
    exact hAnc
      ((Subgroup.equivMapOfInjective A K.subtype K.subtype_injective).isCyclic.mpr hBcyc)
  exact ⟨p, hp, B, hBea, hBle, hBnc⟩

end Rank

end OddOrder.GroupTheory


