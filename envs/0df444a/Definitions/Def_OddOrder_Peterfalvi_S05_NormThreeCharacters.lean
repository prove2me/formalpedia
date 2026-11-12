-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S05_NormThreeCharacters
-- name    : OddOrder_Peterfalvi_S05_NormThreeCharacters
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:46:31.41777+00:00
-- url     : https://prove2.me/theorems/0e6e1508-55f1-4fea-b5cc-85d306648452
-- title:
--   Peterfalvi §5: norm-3 virtual characters and the signed-triple-grid statement
-- statement:
--   The abstract layer of Peterfalvi §5 before the `IsSignedTripleGrid` namespace: norm-3 virtual characters orthogonal to $1_G$ and the grid combinatorics they satisfy.
--
--   Main definition: `IsSignedNontrivialIrr`, the set $\pm(\mathrm{Irr}(G)-\{1_G\})$ of signed nontrivial irreducible characters, with lemmas such as `isSignedNontrivialIrr_inner` (orthonormality of $\pm\mathrm{Irr}$), `IsSignedNontrivialIrr.inner_self` (unit norm) and `IsSignedNontrivialIrr.mem_ZIrr`.
--
--   The bundle also proves 12 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S05_NormThreeCharacters.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S05_NormThreeCharacters.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S05_NormThree

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

/-- Finite integer-vector combinatorics: if integer coefficients on a finite set `s` are all
nonzero and their squares sum to `3`, then `s` has exactly three elements, each with coefficient
`±1`.  (`3` is a sum of nonzero integer squares only as `1 + 1 + 1`: a square `≥ 2` is `≥ 4`.)
Companion to `OddOrder.RepresentationTheory.exists_pair_of_sum_sq_eq_two`. -/
theorem card_eq_three_of_sum_sq_eq_three {ι : Type*} {s : Finset ι} {c : ι → ℤ}
    (hne : ∀ a ∈ s, c a ≠ 0) (hsum : ∑ a ∈ s, c a ^ 2 = 3) :
    s.card = 3 ∧ ∀ a ∈ s, c a = 1 ∨ c a = -1 := by
  have hle : ∀ a ∈ s, c a ^ 2 ≤ 3 := fun a ha =>
    le_of_le_of_eq (Finset.single_le_sum (fun b _ => sq_nonneg (c b)) ha) hsum
  have hsign : ∀ a ∈ s, c a = 1 ∨ c a = -1 := fun a ha => by
    have hane := hne a ha
    have hb := hle a ha
    -- `c a ^ 2 ≤ 3` forces `|c a| ≤ 1` (a square `≥ 2 ` is `≥ 4`), and `c a ≠ 0`.
    have habs1 : |c a| ≤ 1 := by
      by_contra h
      have h2 : (2 : ℤ) ≤ |c a| := by omega
      have h4 : (4 : ℤ) ≤ c a ^ 2 :=
        calc (4 : ℤ) = 2 ^ 2 := by norm_num
          _ ≤ |c a| ^ 2 := by gcongr
          _ = c a ^ 2 := sq_abs (c a)
      omega
    rcases abs_le.mp habs1 with ⟨h1, h2⟩
    omega
  have hone : ∀ a ∈ s, c a ^ 2 = 1 := fun a ha => by
    rcases hsign a ha with h | h <;> rw [h] <;> norm_num
  refine ⟨?_, hsign⟩
  have hcard : (s.card : ℤ) = 3 :=
    calc (s.card : ℤ) = ∑ _a ∈ s, (1 : ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ a ∈ s, c a ^ 2 := (Finset.sum_congr rfl hone).symm
      _ = 3 := hsum
  exact_mod_cast hcard

/-- The set `±(Irr(G) - {1_G})` of *signed nontrivial irreducible characters*, as class functions:
`x` is `±χ` for some nontrivial irreducible character `χ`.  This is the type of the elements of
Peterfalvi's set `A_{ij}` in (3.5.1). -/
def IsSignedNontrivialIrr (x : ClassFunction G ℂ) : Prop :=
  ∃ χ : IrreducibleCharacter G, χ ≠ trivialIrreducibleCharacter G ∧
    (x = (χ : ClassFunction G ℂ) ∨ x = -(χ : ClassFunction G ℂ))

/-- **Peterfalvi (3.5.1)** (abstract form): a virtual character `φ ∈ ℤ[Irr G]` of squared norm `3`
orthogonal to `1_G` is `φ = ∑_{x ∈ A} x` for a `3`-element set `A` of pairwise-orthogonal signed
nontrivial irreducibles.  Indeed `φ = ∑ c_a · a` over irreducibles with `∑ c_a² = 3`, so the
support has three elements with `c_a = ±1` (`card_eq_three_of_sum_sq_eq_three`); orthogonality to
`1_G` excludes the trivial character from the support, and the signed irreducibles `c_a · a` form
the set `A`.  Companion to the norm-`2` lemma `exists_irr_sub_irr_of_inner_self_two`. -/
theorem exists_signedTriple_of_inner_self_three [Invertible (Nat.card G : ℂ)]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) (hnorm : ClassFunction.inner φ φ = 3)
    (htriv : ClassFunction.inner φ (trivialClassFunction G) = 0) :
    ∃ A : Finset (ClassFunction G ℂ),
      A.card = 3 ∧ (∀ x ∈ A, IsSignedNontrivialIrr x) ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → ClassFunction.inner x y = 0) ∧
      φ = ∑ x ∈ A, x := by
  classical
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hφ
  have hsumC : ∑ a ∈ c.support, (c a : ℂ) ^ 2 = 3 := hsq.symm.trans hnorm
  have hsumZ : ∑ a ∈ c.support, c a ^ 2 = 3 := by exact_mod_cast hsumC
  have hne : ∀ a ∈ c.support, c a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
  obtain ⟨hcard3, hsign⟩ := card_eq_three_of_sum_sq_eq_three hne hsumZ
  -- the trivial character is not in the support (else `⟨φ, 1_G⟩ = c_{1_G} ≠ 0`)
  have htrivnot : trivialClassFunction G ∉ c.support := by
    intro hmem
    have hcoeff : ClassFunction.inner φ (trivialClassFunction G) =
        (c (trivialClassFunction G) : ℂ) := by
      rw [hrepr]; exact inner_eq_coeff_of_repr (trivialIrreducibleCharacter G) hsupp
    rw [htriv] at hcoeff
    exact (Finsupp.mem_support_iff.mp hmem) (by exact_mod_cast hcoeff.symm)
  -- the signed-irreducible map `a ↦ (c a) • a` is injective on the support
  have hinj : Set.InjOn (fun a => (c a : ℂ) • a) (c.support : Set (ClassFunction G ℂ)) := by
    intro a ha b hb hfab
    by_contra hab
    have haa : a ∈ irreducibleCharacters G := hsupp ha
    have hba : b ∈ irreducibleCharacters G := hsupp hb
    have e1 : ClassFunction.inner ((c a : ℂ) • a) a = (c a : ℂ) := by
      rw [ClassFunction.inner_smul_left, irr_cf_inner haa haa, if_pos rfl, mul_one]
    have e2 : ClassFunction.inner ((c b : ℂ) • b) a = 0 := by
      rw [ClassFunction.inner_smul_left, irr_cf_inner hba haa, if_neg (Ne.symm hab), mul_zero]
    change (c a : ℂ) • a = (c b : ℂ) • b at hfab
    have hca0 : (c a : ℂ) = 0 := by rw [← e1, hfab, e2]
    exact hne a (Finset.mem_coe.mp ha) (by exact_mod_cast hca0)
  refine ⟨c.support.image (fun a => (c a : ℂ) • a), ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinj]; exact hcard3
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have haa : a ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr ha)
    have hane : a ≠ trivialClassFunction G := fun h => htrivnot (h ▸ ha)
    refine ⟨⟨a, haa⟩, fun h => hane (Subtype.ext_iff.mp h), ?_⟩
    rcases hsign a ha with h | h
    · refine Or.inl ?_
      change (c a : ℂ) • a = a
      rw [h, Int.cast_one, one_smul]
    · refine Or.inr ?_
      change (c a : ℂ) • a = -a
      rw [h, Int.cast_neg, Int.cast_one, neg_one_smul]
  · intro x hx y hy hxy
    rw [Finset.mem_image] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have haa : a ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr ha)
    have hbb : b ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr hb)
    have hab : a ≠ b := fun h => hxy (by rw [h])
    change ClassFunction.inner ((c a : ℂ) • a) ((c b : ℂ) • b) = 0
    rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      irr_cf_inner haa hbb, if_neg hab, mul_zero, mul_zero]
  · rw [Finset.sum_image hinj]; exact hrepr

omit [Fintype G] in
/-- A signed nontrivial irreducible character is nonzero at `1`: its value there is `±d` with
`d > 0` the degree. -/
theorem IsSignedNontrivialIrr.apply_one_ne_zero {x : ClassFunction G ℂ}
    (hx : IsSignedNontrivialIrr x) : x 1 ≠ 0 := by
  obtain ⟨χ, _, hx⟩ := hx
  obtain ⟨d, hd, hd1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  rcases hx with rfl | rfl
  · rw [hd1]; exact_mod_cast hd.ne'
  · rw [ClassFunction.neg_apply, hd1, neg_ne_zero]; exact_mod_cast hd.ne'

omit [Fintype G] in
/-- The coercion of an irreducible character is never the negative of the coercion of an
irreducible character: at `1` one value is `+d` and the other `-d'` with `d, d' > 0`. -/
theorem irreducibleCharacter_coe_ne_neg (χ ψ : IrreducibleCharacter G) :
    (χ : ClassFunction G ℂ) ≠ -(ψ : ClassFunction G ℂ) := by
  obtain ⟨dχ, hdχ, hχ1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  obtain ⟨dψ, hdψ, hψ1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ψ
  intro h
  have h1 : (χ : ClassFunction G ℂ) (1 : G) = (-(ψ : ClassFunction G ℂ)) (1 : G) := by rw [h]
  rw [hχ1, ClassFunction.neg_apply, hψ1] at h1
  have hsum : ((dχ + dψ : ℕ) : ℂ) = 0 := by push_cast; rw [h1]; ring
  have : dχ + dψ = 0 := by exact_mod_cast hsum
  omega

open Classical in
/-- **Inner product of two signed nontrivial irreducibles** (the orthonormality of `±Irr`):
`⟨x, c⟩` is `1` if `x = c`, `-1` if `x = -c`, and `0` otherwise. -/
theorem isSignedNontrivialIrr_inner [Invertible (Nat.card G : ℂ)] {x c : ClassFunction G ℂ}
    (hx : IsSignedNontrivialIrr x) (hc : IsSignedNontrivialIrr c) :
    ClassFunction.inner x c = (if x = c then 1 else 0) - (if x = -c then 1 else 0) := by
  obtain ⟨χ, -, hxχ⟩ := hx
  obtain ⟨ψ, -, hcψ⟩ := hc
  set X : ClassFunction G ℂ := (χ : ClassFunction G ℂ) with hX
  set Y : ClassFunction G ℂ := (ψ : ClassFunction G ℂ) with hY
  have hXY : ClassFunction.inner X Y = if X = Y then (1 : ℂ) else 0 :=
    irr_cf_inner χ.mem_irreducibleCharacters ψ.mem_irreducibleCharacters
  have hXnegY : ¬ (X = -Y) := irreducibleCharacter_coe_ne_neg χ ψ
  rcases hxχ with rfl | rfl <;> rcases hcψ with rfl | rfl
  · rw [hXY, if_neg hXnegY, sub_zero]
  · rw [ClassFunction.inner_neg_right, hXY, neg_neg, if_neg hXnegY, zero_sub]
  · rw [ClassFunction.inner_neg_left, hXY, neg_inj,
      if_neg (fun h => hXnegY (neg_eq_iff_eq_neg.mp h)), zero_sub]
  · rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg, hXY, neg_inj,
      neg_neg, if_neg (fun h => hXnegY (neg_eq_iff_eq_neg.mp h)), sub_zero]

omit [Fintype G] in
/-- A signed nontrivial irreducible is not its own negative (it is nonzero). -/
theorem IsSignedNontrivialIrr.ne_neg_self {x : ClassFunction G ℂ}
    (hx : IsSignedNontrivialIrr x) : x ≠ -x := by
  intro h
  apply hx.apply_one_ne_zero
  have hval : x 1 = -(x 1) := by
    conv_lhs => rw [h]
    rw [ClassFunction.neg_apply]
  linear_combination hval / 2

open Classical in
/-- A signed nontrivial irreducible has unit norm: `⟨x, x⟩ = 1`. -/
theorem IsSignedNontrivialIrr.inner_self [Invertible (Nat.card G : ℂ)] {x : ClassFunction G ℂ}
    (hx : IsSignedNontrivialIrr x) : ClassFunction.inner x x = 1 := by
  rw [isSignedNontrivialIrr_inner hx hx, if_pos rfl, if_neg (fun h => hx.ne_neg_self h), sub_zero]

omit [Fintype G] in
/-- A signed nontrivial irreducible is a virtual character (`x = ±χ`, both in `ℤ[Irr G]`). -/
theorem IsSignedNontrivialIrr.mem_ZIrr {x : ClassFunction G ℂ} (hx : IsSignedNontrivialIrr x) :
    x ∈ ZIrr G := by
  obtain ⟨χ, _, hx⟩ := hx
  rcases hx with rfl | rfl
  · exact χ.mem_ZIrr
  · exact Submodule.neg_mem _ χ.mem_ZIrr

/-- A signed nontrivial irreducible is orthogonal to `1_G` (its underlying irreducible is
nontrivial). -/
theorem IsSignedNontrivialIrr.inner_trivial [Invertible (Nat.card G : ℂ)]
    {x : ClassFunction G ℂ} (hx : IsSignedNontrivialIrr x) :
    ClassFunction.inner x (trivialClassFunction G) = 0 := by
  obtain ⟨χ, hχ, hx⟩ := hx
  have h0 : ClassFunction.inner (χ : ClassFunction G ℂ) (trivialClassFunction G) = 0 := by
    rw [← IrreducibleCharacter.coe_trivialIrreducibleCharacter, irreducibleCharacter_inner,
      if_neg hχ]
  rcases hx with rfl | rfl
  · exact h0
  · rw [ClassFunction.inner_neg_left, h0, neg_zero]

/-- A family `X : τ → ±Irr(G)` of signed nontrivial irreducibles is **orthonormal** as soon as it is
*injective* and *no member is another's negative*: the diagonal inner products are `1` and the
off-diagonal ones are `0`.  This is the bridge from the combinatorial facts of (3.5.5) (distinctness
and "no negated coincidence") to the analytic orthonormality of the family `(χ_{ij})` that powers
the
isometry `σ` of (3.2).  (Stated diagonal/off-diagonal rather than via `if a = b` to stay free of any
`DecidableEq τ` instance.) -/
theorem orthonormal_of_injective_of_no_neg [Invertible (Nat.card G : ℂ)] {τ : Type*}
    (X : τ → ClassFunction G ℂ) (hsig : ∀ a, IsSignedNontrivialIrr (X a))
    (hinj : Function.Injective X) (hneg : ∀ a b, X a ≠ -X b) :
    (∀ a, ClassFunction.inner (X a) (X a) = 1) ∧
      (∀ a b, a ≠ b → ClassFunction.inner (X a) (X b) = 0) := by
  classical
  refine ⟨fun a => (hsig a).inner_self, fun a b hab => ?_⟩
  rw [isSignedNontrivialIrr_inner (hsig a) (hsig b), if_neg (fun h => hab (hinj h)),
    if_neg (hneg a b), sub_zero]

/-- A *signed triple*: `β` is the sum of a 3-element set `A` of pairwise-orthogonal signed
nontrivial irreducible characters.  This is the structure of each `β_{ij}` of Peterfalvi (3.5.1)
(`exists_betaSet`); the `A_{ij}` of the (3.5.2)-(3.5.5) combinatorics are the carriers `A`. -/
structure IsSignedTriple [Invertible (Nat.card G : ℂ)] (β : ClassFunction G ℂ)
    (A : Finset (ClassFunction G ℂ)) : Prop where
  card_eq_three : A.card = 3
  signed : ∀ x ∈ A, IsSignedNontrivialIrr x
  pairwise_orthogonal : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ClassFunction.inner x y = 0
  sum_eq : β = ∑ x ∈ A, x

/-- Packaging of `exists_signedTriple_of_inner_self_three` as an `IsSignedTriple`. -/
theorem exists_isSignedTriple_of_inner_self_three [Invertible (Nat.card G : ℂ)]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) (hnorm : ClassFunction.inner φ φ = 3)
    (htriv : ClassFunction.inner φ (trivialClassFunction G) = 0) :
    ∃ A : Finset (ClassFunction G ℂ), IsSignedTriple φ A := by
  obtain ⟨A, hcard, hsig, horth, hsum⟩ := exists_signedTriple_of_inner_self_three hφ hnorm htriv
  exact ⟨A, ⟨hcard, hsig, horth, hsum⟩⟩

/-- In a signed triple, the negative of a member is not a member (else the member and its
negative, both in `A`, would not be orthogonal: `⟨x, -x⟩ = -1 ≠ 0`). -/
theorem IsSignedTriple.neg_not_mem [Invertible (Nat.card G : ℂ)]
    {β : ClassFunction G ℂ} {A : Finset (ClassFunction G ℂ)} (hA : IsSignedTriple β A)
    {x : ClassFunction G ℂ} (hx : x ∈ A) : -x ∉ A := by
  intro hnx
  have hxsig := hA.signed x hx
  have h0 := hA.pairwise_orthogonal x hx (-x) hnx (fun h => hxsig.ne_neg_self h)
  rw [ClassFunction.inner_neg_right, hxsig.inner_self] at h0
  exact one_ne_zero (neg_eq_zero.mp h0)

open Classical in
/-- **(3.5.2) coefficient formula**: for a signed triple `β = ∑ A` and a signed irreducible `c`,
`⟨β, c⟩ = [c ∈ A] - [-c ∈ A]`. -/
theorem IsSignedTriple.inner_right_signed [Invertible (Nat.card G : ℂ)]
    {β : ClassFunction G ℂ} {A : Finset (ClassFunction G ℂ)} (hA : IsSignedTriple β A)
    {c : ClassFunction G ℂ} (hc : IsSignedNontrivialIrr c) :
    ClassFunction.inner β c = (if c ∈ A then 1 else 0) - (if -c ∈ A then 1 else 0) := by
  rw [hA.sum_eq, inner_sum_left,
    Finset.sum_congr rfl (fun x hx => isSignedNontrivialIrr_inner (hA.signed x hx) hc),
    Finset.sum_sub_distrib, Finset.sum_ite_eq' A c (fun _ => (1 : ℂ)),
    Finset.sum_ite_eq' A (-c) (fun _ => (1 : ℂ))]

/-- **(3.5.1) norm**: a signed triple has `⟨β, β⟩ = |A| = 3`. -/
theorem IsSignedTriple.inner_self [Invertible (Nat.card G : ℂ)]
    {β : ClassFunction G ℂ} {A : Finset (ClassFunction G ℂ)} (hA : IsSignedTriple β A) :
    ClassFunction.inner β β = (A.card : ℂ) := by
  classical
  nth_rewrite 2 [hA.sum_eq]
  rw [inner_sum_right]
  rw [Finset.sum_congr rfl (fun x hx => by
    rw [hA.inner_right_signed (hA.signed x hx), if_pos hx,
      if_neg (hA.neg_not_mem hx), sub_zero])]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Peterfalvi (3.5.2)** (no-negatives half): if two signed triples `β = ∑ A`, `β' = ∑ A'` have
`⟨β, β'⟩ = 1` and agree at `1` (`β 1 = β' 1`), then no `c ∈ A` has `-c ∈ A'`.  Were there such a
`c`, then `⟨β, c⟩ = 1`, `⟨β', c⟩ = -1`, so `⟨β - β', c⟩ = 2`; with `‖β - β'‖² = 4`, the vector
`(β - β') - 2c` has zero norm, hence `β - β' = 2c`.  But `(β - β')(1) = β(1) - β'(1) = 0` while
`2 · c(1) ≠ 0` (signed irreducibles are nonzero at `1`) — a contradiction.  (Peterfalvi's
`2χ₃ = Ind(α₁₁ - α₁₂)` vanishing at `1 ∈ G`.) -/
theorem IsSignedTriple.no_neg_of_inner_one [Invertible (Nat.card G : ℂ)]
    {β β' : ClassFunction G ℂ} {A A' : Finset (ClassFunction G ℂ)}
    (hA : IsSignedTriple β A) (hA' : IsSignedTriple β' A')
    (hinner : ClassFunction.inner β β' = 1) (hone : β 1 = β' 1)
    {c : ClassFunction G ℂ} (hcA : c ∈ A) (hcA' : -c ∈ A') : False := by
  have hcsig : IsSignedNontrivialIrr c := hA.signed c hcA
  -- `⟨β, c⟩ = 1` and `⟨β', c⟩ = -1`.
  have hbc : ClassFunction.inner β c = 1 := by
    rw [hA.inner_right_signed hcsig, if_pos hcA, if_neg (hA.neg_not_mem hcA), sub_zero]
  have hcnA' : c ∉ A' := fun h => hA'.neg_not_mem h hcA'
  have hb'c : ClassFunction.inner β' c = -1 := by
    rw [hA'.inner_right_signed hcsig, if_neg hcnA', if_pos hcA', zero_sub]
  -- norms: `⟨β,β⟩ = ⟨β',β'⟩ = 3`, `⟨β',β⟩ = 1`.
  have hbb : ClassFunction.inner β β = 3 := by rw [hA.inner_self, hA.card_eq_three]; norm_num
  have hb'b' : ClassFunction.inner β' β' = 3 := by rw [hA'.inner_self, hA'.card_eq_three]; norm_num
  have hb'b : ClassFunction.inner β' β = 1 := by rw [inner_conj_symm β β', hinner, star_one]
  set g : ClassFunction G ℂ := β - β' with hg
  -- `⟨g, c⟩ = 2`, `⟨c, g⟩ = 2`, `⟨g, g⟩ = 4`.
  have hgc : ClassFunction.inner g c = 2 := by
    rw [hg, ClassFunction.inner_sub_left, hbc, hb'c]; ring
  have hcg : ClassFunction.inner c g = 2 := by rw [inner_conj_symm g c, hgc]; norm_num
  have hgg : ClassFunction.inner g g = 4 := by
    rw [hg, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hbb, hb'b', hinner, hb'b]; norm_num
  -- `(β - β') - 2c` has zero norm, so it is `0`.
  have hs2 : star (2 : ℂ) = 2 := by norm_num
  have hzero : ClassFunction.inner (g - (2 : ℂ) • c) (g - (2 : ℂ) • c) = 0 := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hgg, hgc, hcg, hcsig.inner_self, hs2]
    ring
  have hg2c : g = (2 : ℂ) • c :=
    sub_eq_zero.mp (eq_zero_of_inner_self_re_eq_zero (by rw [hzero]; exact Complex.zero_re))
  -- evaluate at `1`: `0 = g(1) = 2 · c(1)`, contradicting `c(1) ≠ 0`.
  have hg1 : g 1 = 0 := by rw [hg, ClassFunction.sub_apply, hone, sub_self]
  rw [hg2c, ClassFunction.smul_apply] at hg1
  exact hcsig.apply_one_ne_zero ((mul_eq_zero.mp hg1).resolve_left (by norm_num))

open Classical in
/-- **Peterfalvi (3.5.2)** `L(ij, i'j')`: two signed triples with `⟨β, β'⟩ = 1` that agree at `1`
share exactly one element (`|A ∩ A'| = 1`) and no element of one is the negative of an element of
the other (`∀ x ∈ A, -x ∉ A'`).  The no-negatives half is `no_neg_of_inner_one`; given it,
`⟨β', β⟩ = ∑_{x ∈ A} [x ∈ A'] = |A ∩ A'|`, which equals `⟨β, β'⟩* = 1`. -/
theorem IsSignedTriple.L_of_inner_one [Invertible (Nat.card G : ℂ)]
    {β β' : ClassFunction G ℂ} {A A' : Finset (ClassFunction G ℂ)}
    (hA : IsSignedTriple β A) (hA' : IsSignedTriple β' A')
    (hinner : ClassFunction.inner β β' = 1) (hone : β 1 = β' 1) :
    (A ∩ A').card = 1 ∧ ∀ x ∈ A, -x ∉ A' := by
  have hno : ∀ x ∈ A, -x ∉ A' :=
    fun x hx hnx => hA.no_neg_of_inner_one hA' hinner hone hx hnx
  refine ⟨?_, hno⟩
  have key : ClassFunction.inner β' β = ((A ∩ A').card : ℂ) := by
    conv_lhs => rw [hA.sum_eq]
    rw [inner_sum_right, Finset.sum_congr rfl (fun x hx => by
      rw [hA'.inner_right_signed (hA.signed x hx), if_neg (hno x hx), sub_zero]),
      Finset.sum_boole, Finset.filter_mem_eq_inter]
  have : ((A ∩ A').card : ℂ) = 1 := by rw [← key, inner_conj_symm β β', hinner, star_one]
  exact_mod_cast this

open Classical in
/-- **Peterfalvi (3.5.2)** `O(ij, i'j')`: two signed triples that are orthogonal (`⟨β, β'⟩ = 0`)
have `|A ∩ A'| = |{x ∈ A : -x ∈ A'}|`.  (Expanding `⟨β', β⟩ = ∑_{x ∈ A}([x ∈ A'] - [-x ∈ A'])`
gives `|A ∩ A'| - |{x ∈ A : -x ∈ A'}|`, which equals `⟨β, β'⟩* = 0`.)  Downstream this is used as:
a shared element of `A` and `A'` forces a *negated* shared element too. -/
theorem IsSignedTriple.O_card_inter_eq [Invertible (Nat.card G : ℂ)]
    {β β' : ClassFunction G ℂ} {A A' : Finset (ClassFunction G ℂ)}
    (hA : IsSignedTriple β A) (hA' : IsSignedTriple β' A')
    (hinner : ClassFunction.inner β β' = 0) :
    (A ∩ A').card = (A.filter (fun x => -x ∈ A')).card := by
  have key : ClassFunction.inner β' β =
      ((A ∩ A').card : ℂ) - ((A.filter (fun x => -x ∈ A')).card : ℂ) := by
    conv_lhs => rw [hA.sum_eq]
    rw [inner_sum_right,
      Finset.sum_congr rfl (fun x hx => hA'.inner_right_signed (hA.signed x hx)),
      Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, Finset.filter_mem_eq_inter]
  rw [inner_conj_symm β β', hinner, star_zero] at key
  have hpm : ((A ∩ A').card : ℂ) = ((A.filter (fun x => -x ∈ A')).card : ℂ) :=
    sub_eq_zero.mp key.symm
  exact_mod_cast hpm

/-- A 3-element finset containing two distinct elements `a, b` is `{a, b, c}` for a (unique)
third element `c ∉ {a, b}`.  Used to name "the third element" of each `A_{ij}` in (3.5.4). -/
theorem exists_third_of_card_three {α : Type*} [DecidableEq α] {s : Finset α} (hs : s.card = 3)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    ∃ c, c ∈ s ∧ c ≠ a ∧ c ≠ b ∧ s = {a, b, c} := by
  have hsub : ({a, b} : Finset α) ⊆ s := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    · rw [Finset.mem_singleton] at hx; exact hx ▸ hb
  have hcard2 : ({a, b} : Finset α).card = 2 := by
    rw [Finset.card_insert_of_notMem (Finset.notMem_singleton.mpr hab), Finset.card_singleton]
  have hd : (s \ {a, b}).card = 1 := by rw [Finset.card_sdiff_of_subset hsub, hs, hcard2]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hd
  have hcmem : c ∈ s \ {a, b} := hc ▸ Finset.mem_singleton_self c
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcmem
  obtain ⟨hcs, hcab⟩ := hcmem
  refine ⟨c, hcs, hcab.1, hcab.2, ?_⟩
  apply Finset.ext
  intro x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    · by_cases hxb : x = b
      · exact Or.inr (Or.inl hxb)
      · refine Or.inr (Or.inr ?_)
        have : x ∈ s \ {a, b} := by
          rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨hx, fun h => h.elim hxa hxb⟩
        rw [hc, Finset.mem_singleton] at this; exact this
  · rintro (rfl | rfl | rfl)
    · exact ha
    · exact hb
    · exact hcs

/-- The number of a 3-element list `{a, b, c}` of distinct elements that lie in `s`, as a sum of
indicators.  Used to turn the `(3.5.4)` cardinality relations into a linear-arithmetic system. -/
theorem card_inter_triple {α : Type*} [DecidableEq α] (s : Finset α) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (s ∩ {a, b, c}).card =
      (if a ∈ s then 1 else 0) + (if b ∈ s then 1 else 0) + (if c ∈ s then 1 else 0) := by
  rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter,
    Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, add_assoc]

/-- The number of `x ∈ s` whose negative lies in a 3-element set `{a, b, c}` of distinct elements,
as a sum of indicators (`-x ∈ {a,b,c} ↔ x ∈ {-a,-b,-c}`).  The "negated" companion of
`card_inter_triple`, for the `filter` side of the `O`-relation. -/
theorem card_filter_neg_triple {α : Type*} [AddGroup α] [DecidableEq α] (s : Finset α)
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (s.filter (fun x => -x ∈ ({a, b, c} : Finset α))).card =
      (if -a ∈ s then 1 else 0) + (if -b ∈ s then 1 else 0) + (if -c ∈ s then 1 else 0) := by
  have heq : s.filter (fun x => -x ∈ ({a, b, c} : Finset α)) = s ∩ {-a, -b, -c} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      neg_eq_iff_eq_neg]
  rw [heq, card_inter_triple s (neg_injective.ne hab) (neg_injective.ne hac) (neg_injective.ne hbc)]

/-- From `card {a,b,c} = 3`, the three elements are pairwise distinct. -/
theorem triple_distinct {α : Type*} [DecidableEq α] {a b c : α}
    (h : ({a, b, c} : Finset α).card = 3) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have key : ∀ x y z : α, x ∈ ({y, z} : Finset α) → ({x, y, z} : Finset α).card ≠ 3 := by
    intro x y z hx
    rw [show ({x, y, z} : Finset α) = {y, z} from Finset.insert_eq_self.mpr hx]
    have := Finset.card_insert_le y ({z} : Finset α)
    rw [Finset.card_singleton] at this; omega
  refine ⟨fun hab => key a b c ?_ h, fun hac => key a b c ?_ h, fun hbc => ?_⟩
  · rw [hab]; exact Finset.mem_insert_self b {c}
  · rw [hac]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self c)
  · exact key b a c (by rw [hbc]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self c))
      (by rw [Finset.insert_comm]; exact h)

open scoped Classical in
/-- An abstract *grid of signed triples*: a family `A i j` (rows `i : ι`, columns `j : κ`) of
signed-triple sets satisfying the Peterfalvi relations.  `card_eq_three`/`signed`/`orthogonal` are
the per-cell `IsSignedTriple` data; `inter_L`/`noNeg_L` are `L(ij,i'j')` (index pairs sharing
exactly one coordinate) and `inter_O` is `O(ij,i'j')` (both coordinates differing).  This is the
data the (3.5.4) sunflower argument consumes; the concrete `β`-family `Afam` is an instance
(`Afam_isSignedTripleGrid`). -/
structure IsSignedTripleGrid [Invertible (Nat.card G : ℂ)] {ι κ : Type*}
    (A : ι → κ → Finset (ClassFunction G ℂ)) : Prop where
  card_eq_three : ∀ i j, (A i j).card = 3
  signed : ∀ i j, ∀ x ∈ A i j, IsSignedNontrivialIrr x
  orthogonal : ∀ i j, ∀ x ∈ A i j, ∀ y ∈ A i j, x ≠ y → ClassFunction.inner x y = 0
  inter_L : ∀ (i i' : ι) (j j' : κ), (i = i' ∧ j ≠ j') ∨ (i ≠ i' ∧ j = j') →
    (A i j ∩ A i' j').card = 1
  noNeg_L : ∀ (i i' : ι) (j j' : κ), (i = i' ∧ j ≠ j') ∨ (i ≠ i' ∧ j = j') →
    ∀ x ∈ A i j, -x ∉ A i' j'
  inter_O : ∀ (i i' : ι) (j j' : κ), i ≠ i' → j ≠ j' →
    (A i j ∩ A i' j').card = ((A i j).filter (fun x => -x ∈ A i' j')).card

end OddOrder.Peterfalvi.S05


