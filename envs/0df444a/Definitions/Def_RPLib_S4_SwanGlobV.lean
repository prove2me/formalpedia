-- Prove2me | Definitions.Def_RPLib_S4_SwanGlobV
-- name    : RPLib_S4_SwanGlobV
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:19:35.974703+00:00
-- url     : https://prove2.me/theorems/8ad0c8f7-3cd2-4133-b045-2df3d156b0dd
-- title:
--   The $\mathfrak{P}$-adic additive valuation of a Dedekind domain and local data of an inertia group
-- statement:
--   For a Dedekind domain $B$ with fraction field $L$ and a height-one prime $\mathfrak{P}$, the additive valuation $v_\mathfrak{P} : L \to \mathbb{Z} \cup \{\infty\}$ is characterised by $$n \le v_\mathfrak{P}(b) \iff b \in \mathfrak{P}^n \qquad (b \in B,\ n \in \mathbb{N}).$$ The file constructs it from Mathlib's multiplicative valuation, proves its basic properties, existence of a uniformiser, and that for a finite group acting on $B$ the inertia group of $\mathfrak{P}$ (elements acting trivially on $B/\mathfrak{P}$ and fixing $\mathfrak{P}$) together with $v_\mathfrak{P}$ forms local data in the sense of totally ramified local data.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter I, Section 9 (Hilbert's ramification theory); J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter I

import Mathlib
import Definitions.Def_RPLib_S4_SwanLoc

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

theorem withTop_eq_of_natCast_le_iff {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ n : ℕ, (n : WithTop ℤ) ≤ a ↔ (n : WithTop ℤ) ≤ b) : a = b := by
  induction a with
  | top =>
    induction b with
    | top => rfl
    | coe b =>
      have := (h (b.toNat + 1)).1 le_top
      rw [← WithTop.coe_natCast, WithTop.coe_le_coe] at this
      omega
  | coe a =>
    induction b with
    | top =>
      have := (h (a.toNat + 1)).2 le_top
      rw [← WithTop.coe_natCast, WithTop.coe_le_coe] at this
      omega
    | coe b =>
      have ha' : 0 ≤ a := by exact_mod_cast ha
      have hb' : 0 ≤ b := by exact_mod_cast hb
      have h1 := (h a.toNat).1 (by rw [← WithTop.coe_natCast, WithTop.coe_le_coe]; omega)
      have h2 := (h b.toNat).2 (by rw [← WithTop.coe_natCast, WithTop.coe_le_coe]; omega)
      rw [← WithTop.coe_natCast, WithTop.coe_le_coe] at h1 h2
      congr 1
      omega

section AdicAdd

variable {S : Type*} [CommRing S] [IsDedekindDomain S] {L : Type*} [Field L] [Algebra S L]
  [IsFractionRing S L] (P : HeightOneSpectrum S)

open Classical in
/-- `-log` of the `P`-adic valuation, with `⊤` at `0`. -/
def negLogV (x : L) : WithTop ℤ :=
  if x = 0 then ⊤ else ((-log (P.valuation L x) : ℤ) : WithTop ℤ)

theorem negLogV_of_ne {x : L} (hx : x ≠ 0) :
    negLogV P x = ((-log (P.valuation L x) : ℤ) : WithTop ℤ) := if_neg hx

theorem negLogV_zero : negLogV P (0 : L) = ⊤ := if_pos rfl

theorem negLogV_mul (x y : L) : negLogV P (x * y) = negLogV P x + negLogV P y := by
  by_cases hx : x = 0
  · rw [hx, zero_mul, negLogV_zero, WithTop.top_add]
  by_cases hy : y = 0
  · rw [hy, mul_zero, negLogV_zero, WithTop.add_top]
  have h1 : P.valuation L x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have h2 : P.valuation L y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [negLogV_of_ne P (mul_ne_zero hx hy), negLogV_of_ne P hx, negLogV_of_ne P hy, map_mul,
    log_mul h1 h2, neg_add, WithTop.coe_add]

theorem negLogV_add (x y : L) : min (negLogV P x) (negLogV P y) ≤ negLogV P (x + y) := by
  by_cases hx : x = 0
  · rw [hx, zero_add]; exact min_le_right _ _
  by_cases hy : y = 0
  · rw [hy, add_zero]; exact min_le_left _ _
  by_cases hxy : x + y = 0
  · rw [hxy, negLogV_zero]; exact le_top
  have h := Valuation.map_add (P.valuation L) x y
  have h1 : P.valuation L x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have h2 : P.valuation L y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have h3 : P.valuation L (x + y) ≠ 0 := (Valuation.ne_zero_iff _).2 hxy
  rw [← exp_log h1, ← exp_log h2, ← exp_log h3, le_max_iff, exp_le_exp, exp_le_exp] at h
  rw [negLogV_of_ne P hx, negLogV_of_ne P hy, negLogV_of_ne P hxy, ← WithTop.coe_min,
    WithTop.coe_le_coe]
  rcases h with h | h
  · exact min_le_of_left_le (by omega)
  · exact min_le_of_right_le (by omega)

/-- The `P`-adic valuation of `L = Frac S` as an additive valuation with values in `ℤ ∪ {⊤}`. -/
def adicAdd : AddValuation L (WithTop ℤ) :=
  AddValuation.of (negLogV P) (negLogV_zero P)
    (by rw [negLogV_of_ne P one_ne_zero, map_one, log_one, neg_zero, WithTop.coe_zero])
    (negLogV_add P) (negLogV_mul P)

theorem adicAdd_apply (x : L) : adicAdd P x = negLogV P x := rfl

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

include R in
attribute [local instance] Ideal.Quotient.field in
/-- Every element of `S` is congruent mod `Q` to an element fixed by the inertia group of `Q`. -/
theorem exists_inertia_fixed_sub_mem (Q : Ideal S) [Q.IsMaximal] [Finite (S ⧸ Q)] (b : S) :
    ∃ a : S, (∀ σ ∈ Q.inertia G, σ • a = a) ∧ b - a ∈ Q := by
  set I := Q.inertia G with hI
  let A := FixedPoints.subalgebra R S I
  haveI : Algebra.IsInvariant A S I := IsGaloisGroup.isInvariant
  haveI : Algebra.IsIntegral A S := Algebra.IsInvariant.isIntegral A S I
  let p := Q.under A
  have : Finite (A ⧸ p) :=
    Finite.of_injective (algebraMap (A ⧸ p) (S ⧸ Q)) (RingHom.injective _)
  have : Finite p.ResidueField :=
    Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField p).2
  have hcard := Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := I) p Q
  have hinert : Q.inertia I = ⊤ := by
    ext σ
    simp only [Subgroup.mem_top, iff_true]
    exact σ.2
  rw [hinert, Subgroup.card_top] at hcard
  have hle : Nat.card I * Q.inertiaDeg A ≤ Nat.card I * 1 := by
    rw [mul_one, ← hcard]; exact Subgroup.card_le_card_group _
  rw [Ideal.inertiaDeg_eq_of_isMaximal p Q] at hle
  haveI : Module.Finite (A ⧸ p) (S ⧸ Q) := Module.Finite.of_finite
  haveI : Module.Free (A ⧸ p) (S ⧸ Q) := Module.Free.of_divisionRing _ _
  have hpos : 0 < Module.finrank (A ⧸ p) (S ⧸ Q) := Module.finrank_pos
  have h1 : Module.finrank (A ⧸ p) (S ⧸ Q) = 1 := by
    have := Nat.le_of_mul_le_mul_left hle Nat.card_pos
    omega
  have hsurj : Function.Surjective (algebraMap (A ⧸ p) (S ⧸ Q)) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1).2
  obtain ⟨c, hc⟩ := hsurj (Ideal.Quotient.mk Q b)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨(a : S), fun σ hσ => a.2 ⟨σ, hσ⟩, ?_⟩
  rw [← Ideal.Quotient.eq, ← hc, Ideal.Quotient.algebraMap_mk_of_liesOver]
  rfl

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


