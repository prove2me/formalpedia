-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic__ForcedNavierStokesComputation
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic__ForcedNavierStokesComputation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:56:21.970171+00:00
-- url     : https://prove2.me/theorems/986f595d-5a33-42d0-839d-46ad3d279a9e
-- title:
--   Computable integer and rational arithmetic
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   This module establishes the computability facts used by the effective bounds. Casts between $\mathbb N$ and $\mathbb Z$, integer negation, absolute value, addition and multiplication are primitive recursive. So are divisibility, $\gcd$ and coprimality on $\mathbb N$. Unbounded search is computable: if $p(a,n)$ is computably decidable and every $a$ has a witness, then $a\mapsto\min\{n:p(a,n)\}$ is computable.
--
--   A rational $q$ is coded by the pair (code of its numerator, its denominator). A natural number is a valid code when its denominator part is positive and coprime to the absolute value of its numerator part. The rank of $n$, the number of valid codes below $n$, recovers the standard encoding of $\mathbb Q$. With this, numerator, denominator, $(n,d)\mapsto n/d$, rational addition, multiplication and negation are computable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EffectiveArithmetic.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EffectiveArithmetic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForcedNavierStokesComputation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Model

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Encodable

lemma primrec_int_ofNat : Primrec (Int.ofNat : ℕ → ℤ) := by
  apply Primrec.encode_iff.mp
  exact Primrec.nat_double

lemma primrec_int_negSucc : Primrec (Int.negSucc : ℕ → ℤ) := by
  apply Primrec.encode_iff.mp
  exact Primrec.nat_double_succ

lemma primrec_int_cases {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → ℤ} {g h : α → ℕ → β} (hf : Primrec f) (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec fun a => Int.casesOn (motive := fun _ => β) (f a) (g a) (h a) := by
  refine (Primrec.cond (Primrec.nat_bodd.comp (Primrec.encode.comp hf))
    (hh.comp Primrec.id (Primrec.nat_div2.comp (Primrec.encode.comp hf)))
    (hg.comp Primrec.id (Primrec.nat_div2.comp (Primrec.encode.comp hf)))).of_eq ?_
  intro a
  generalize he : f a = z
  cases z with
  | ofNat n =>
    change (bif (2*n).bodd then h a (2*n).div2 else g a (2*n).div2) = g a n
    simp [Nat.div2_val]
  | negSucc n =>
    change (bif (2*n+1).bodd then h a (2*n+1).div2 else g a (2*n+1).div2) = h a n
    simp [Nat.div2_val]

lemma primrec_int_natAbs : Primrec Int.natAbs := by
  exact (primrec_int_cases Primrec.id Primrec.snd.to₂
    (Primrec.succ.comp Primrec.snd).to₂).of_eq (fun z => by cases z <;> rfl)

lemma primrec_int_toNat : Primrec Int.toNat := by
  exact (primrec_int_cases Primrec.id Primrec.snd.to₂
    (Primrec.const 0).to₂).of_eq (fun z => by cases z <;> rfl)

lemma primrec_int_neg : Primrec (fun z : ℤ => -z) := by
  have h₀ : Primrec (fun n : ℕ => -(n : ℤ)) := by
    refine (Primrec.nat_casesOn Primrec.id (Primrec.const (0 : ℤ))
      (primrec_int_negSucc.comp Primrec.snd).to₂).of_eq ?_
    intro n; cases n <;> rfl
  exact (primrec_int_cases Primrec.id (h₀.comp Primrec.snd).to₂
    (primrec_int_ofNat.comp (Primrec.succ.comp Primrec.snd)).to₂).of_eq
      (fun z => by cases z <;> rfl)

lemma primrec_int_natSub : Primrec₂ (fun a b : ℕ => (a : ℤ) - b) := by
  refine (Primrec.ite Primrec.nat_le
    (primrec_int_neg.comp (primrec_int_ofNat.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst)))
    (primrec_int_ofNat.comp Primrec.nat_sub)).of_eq ?_
  intro ⟨a,b⟩
  dsimp
  split_ifs with h
  · rw [Int.ofNat_sub h]; ring
  · rw [Int.ofNat_sub (by omega)]

lemma primrec_int_add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  have h₀ : Primrec₂ (fun a : ℕ => fun z : ℤ => (a : ℤ) + z) := by
    refine (primrec_int_cases Primrec.snd
      (primrec_int_ofNat.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
      (primrec_int_natSub.comp (Primrec.fst.comp Primrec.fst) (Primrec.succ.comp Primrec.snd)).to₂).of_eq ?_
    intro ⟨a,z⟩; cases z <;> simp [Int.negSucc_eq, sub_eq_add_neg]
  have h₁ : Primrec₂ (fun a : ℕ => fun z : ℤ => Int.negSucc a + z) := by
    refine (primrec_int_neg.comp
      (h₀.comp (Primrec.succ.comp Primrec.fst) (primrec_int_neg.comp Primrec.snd))).of_eq ?_
    intro ⟨a,z⟩; simp; omega
  exact (primrec_int_cases Primrec.fst
    (h₀.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
    (h₁.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).of_eq
      (fun ⟨z,w⟩ => by cases z <;> rfl)

lemma primrec_int_mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  have h₀ : Primrec₂ (fun a : ℕ => fun z : ℤ => (a : ℤ) * z) := by
    refine (primrec_int_cases Primrec.snd
      (primrec_int_ofNat.comp (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
      (primrec_int_neg.comp (primrec_int_ofNat.comp
        (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.succ.comp Primrec.snd)))).to₂).of_eq ?_
    intro ⟨a,z⟩; cases z <;> simp [Int.negSucc_eq, mul_add]
  have h₁ : Primrec₂ (fun a : ℕ => fun z : ℤ => Int.negSucc a * z) := by
    refine (primrec_int_neg.comp
      (h₀.comp (Primrec.succ.comp Primrec.fst) Primrec.snd)).of_eq ?_
    intro ⟨a,z⟩; simp only [Int.negSucc_eq]; push_cast; ring
  exact (primrec_int_cases Primrec.fst
    (h₀.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
    (h₁.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).of_eq
      (fun ⟨z,w⟩ => by cases z <;> rfl)

lemma computable_find {α : Type*} [Primcodable α] {p : α → ℕ → Prop}
    [DecidableRel p] (hp : Computable₂ (fun a n => decide (p a n)))
    (hex : ∀ a, ∃ n, p a n) : Computable (fun a => Nat.find (hex a)) := by
  have hp' : Partrec₂ (fun a n => Part.some (decide (p a n))) := hp.partrec
  refine (Partrec.rfind hp').of_eq_tot ?_
  intro a
  apply Nat.mem_rfind.mpr
  constructor
  · simpa using Nat.find_spec (hex a)
  · intro m hm
    simpa using Nat.find_min (hex a) hm

lemma primrec_nat_dvd : PrimrecRel ((· ∣ ·) : ℕ → ℕ → Prop) := by
  exact (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst)
    (Primrec.const 0)).of_eq (fun _ => Nat.dvd_iff_mod_eq_zero.symm)

lemma primrec_nat_gcd : Primrec₂ Nat.gcd := by
  have hp : PrimrecRel (fun ab : ℕ × ℕ => fun k => k ∣ ab.1 ∧ k ∣ ab.2) :=
    (primrec_nat_dvd.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).and
      (primrec_nat_dvd.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
  refine (Primrec.nat_findGreatest Primrec.nat_add hp).of_eq ?_
  intro ⟨a,b⟩
  dsimp only
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨?_, (fun _ => ⟨Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩), ?_⟩
  · rcases eq_or_lt_of_le (Nat.zero_le (a+b)) with h | h
    · have : a = 0 ∧ b = 0 := by omega
      simp [this.1, this.2]
    · exact Nat.le_of_dvd h (dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _))
  · intro k hk hkb ⟨hka, hkb'⟩
    have hd := Nat.dvd_gcd hka hkb'
    have hg : 0 < a.gcd b := by
      by_contra hn
      have : a = 0 ∧ b = 0 := Nat.gcd_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hn)
      omega
    exact (not_le_of_gt hk) (Nat.le_of_dvd hg hd)

lemma primrec_nat_coprime : PrimrecRel Nat.Coprime := by
  exact (Primrec.eq.comp primrec_nat_gcd (Primrec.const 1)).of_eq
    (fun _ => Iff.rfl)

def rawRatCode (q : ℚ) : ℕ := Nat.pair (Encodable.encode q.num) q.den

def validRatCode (n : ℕ) : Prop :=
  0 < n.unpair.2 ∧ (Denumerable.ofNat ℤ n.unpair.1).natAbs.Coprime n.unpair.2

instance : DecidablePred validRatCode := fun _ => inferInstanceAs (Decidable (_ ∧ _))

lemma primrec_validRatCode : PrimrecPred validRatCode := by
  exact (Primrec.nat_lt.comp (Primrec.const 0) (Primrec.snd.comp Primrec.unpair)).and
    (primrec_nat_coprime.comp
      (primrec_int_natAbs.comp ((Primrec.ofNat ℤ).comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.snd.comp Primrec.unpair))

lemma rawRatCode_eq (q : ℚ) : rawRatCode q = @Encodable.encode ℚ Rat.instEncodable q := rfl

lemma validRatCode_iff (n : ℕ) :
    validRatCode n ↔ n ∈ Set.range (@Encodable.encode ℚ Rat.instEncodable) := by
  constructor
  · rintro ⟨hp, hc⟩
    let q : ℚ := ⟨Denumerable.ofNat ℤ n.unpair.1, n.unpair.2, hp.ne', hc⟩
    refine ⟨q, ?_⟩
    change Nat.pair (Encodable.encode (Denumerable.ofNat ℤ n.unpair.1)) n.unpair.2 = n
    exact (congrArg (fun k => Nat.pair k n.unpair.2) (Denumerable.encode_ofNat _)).trans (Nat.pair_unpair _)
  · rintro ⟨q, rfl⟩
    change validRatCode (rawRatCode q)
    simpa only [validRatCode, rawRatCode, Nat.unpair_pair, Denumerable.ofNat_encode] using And.intro q.pos q.reduced

def ratRank (n : ℕ) : ℕ := ((List.range n).filter (fun n => decide (validRatCode n))).length

lemma primrec_ratRank : Primrec ratRank :=
  Primrec.list_length.comp ((Primrec.listFilter primrec_validRatCode).comp Primrec.list_range)

lemma ratRank_code (q : ℚ) : ratRank (rawRatCode q) =
    @Encodable.encode ℚ (inferInstance : Primcodable ℚ).toEncodable q := by
  let := @Encodable.decidableRangeEncode ℚ Rat.instEncodable
  change ((List.range (rawRatCode q)).filter _).length =
    (List.range (rawRatCode q)).countP (fun n => decide
      (n ∈ Set.range (@Encodable.encode ℚ Rat.instEncodable)))
  rw [List.countP_eq_length_filter]
  simp only [validRatCode_iff]

lemma ratRank_injective_valid {m n : ℕ} (hm : validRatCode m) (hn : validRatCode n)
    (h : ratRank m = ratRank n) : m = n := by
  obtain ⟨a, rfl⟩ := (validRatCode_iff m).mp hm
  obtain ⟨b, rfl⟩ := (validRatCode_iff n).mp hn
  rw [← rawRatCode_eq, ← rawRatCode_eq, ratRank_code, ratRank_code] at h
  exact congrArg (@Encodable.encode ℚ Rat.instEncodable)
    (@Encodable.encode_injective ℚ (inferInstance : Primcodable ℚ).toEncodable _ _ h)

lemma computable_rawRatCode : Computable rawRatCode := by
  have hx : ∀ n : ℕ, ∃ k, validRatCode k ∧ ratRank k = n := by
    intro n
    refine ⟨rawRatCode (Denumerable.ofNat ℚ n), ?_, ?_⟩
    · exact (validRatCode_iff _).mpr ⟨_, rfl⟩
    · rw [ratRank_code, Denumerable.encode_ofNat]
  have hp : PrimrecRel (fun n k => validRatCode k ∧ ratRank k = n) :=
    (primrec_validRatCode.comp Primrec.snd).and
      (Primrec.eq.comp (primrec_ratRank.comp Primrec.snd) Primrec.fst)
  refine ((computable_find hp.decide.to_comp hx).comp Primrec.encode.to_comp).of_eq ?_
  intro q
  apply ratRank_injective_valid (Nat.find_spec (hx _)).1 ((validRatCode_iff _).mpr ⟨q,rfl⟩)
  exact (Nat.find_spec (hx _)).2.trans (ratRank_code q).symm

lemma computable_rat_num : Computable Rat.num := by
  refine (((Primrec.ofNat ℤ).to_comp.comp
    (Primrec.fst.to_comp.comp (Primrec.unpair.to_comp.comp computable_rawRatCode)))).of_eq ?_
  intro q
  simp only [rawRatCode, Nat.unpair_pair, Denumerable.ofNat_encode]

lemma computable_rat_den : Computable Rat.den := by
  exact ((Primrec.snd.to_comp.comp (Primrec.unpair.to_comp.comp computable_rawRatCode))).of_eq
    (fun q => by simp [rawRatCode])

lemma rat_fraction_eq_iff (q : ℚ) (n : ℤ) (d : ℕ) (hd : d ≠ 0) :
    q = (n : ℚ) / d ↔ q.num * (d : ℤ) = n * (q.den : ℤ) := by
  have hden : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd
  have h := @Rat.divInt_eq_divInt_iff q.den d q.num n hden hd'
  simpa only [Rat.num_divInt_den, Rat.divInt_eq_div, Rat.intCast_natCast, Rat.num_div_den] using h

lemma computable_rat_of_parts {α : Type*} [Primcodable α]
    {n : α → ℤ} {d : α → ℕ} (hn : Computable n) (hd : Computable d)
    (hpos : ∀ a, d a ≠ 0) : Computable (fun a => (n a : ℚ) / d a) := by
  let p : α → ℕ → Prop := fun a k =>
    (Denumerable.ofNat ℚ k).num * (d a : ℤ) =
      n a * ((Denumerable.ofNat ℚ k).den : ℤ)
  have hn' : Computable (fun k => (Denumerable.ofNat ℚ k).num) :=
    computable_rat_num.comp (Computable.ofNat ℚ)
  have hd' : Computable (fun k => ((Denumerable.ofNat ℚ k).den : ℤ)) :=
    primrec_int_ofNat.to_comp.comp (computable_rat_den.comp (Computable.ofNat ℚ))
  have hl : Computable (fun ak : α × ℕ => (Denumerable.ofNat ℚ ak.2).num * (d ak.1 : ℤ)) :=
    primrec_int_mul.to_comp.comp (hn'.comp Computable.snd)
      ((primrec_int_ofNat.to_comp.comp hd).comp Computable.fst)
  have hr : Computable (fun ak : α × ℕ => n ak.1 * ((Denumerable.ofNat ℚ ak.2).den : ℤ)) :=
    primrec_int_mul.to_comp.comp (hn.comp Computable.fst) (hd'.comp Computable.snd)
  have hp : Computable₂ (fun a k => decide (p a k)) :=
    Primrec.eq.decide.to_comp.comp hl hr
  have hx : ∀ a, ∃ k, p a k := by
    intro a
    refine ⟨@Encodable.encode ℚ (inferInstance : Primcodable ℚ).toEncodable ((n a : ℚ) / d a), ?_⟩
    dsimp [p]
    rw [Denumerable.ofNat_encode]
    exact (rat_fraction_eq_iff _ _ _ (hpos a)).mp rfl
  refine ((Computable.ofNat ℚ).comp (computable_find hp hx)).of_eq ?_
  intro a
  exact (rat_fraction_eq_iff _ _ _ (hpos a)).mpr (Nat.find_spec (hx a))

lemma computable_rat_add : Computable₂ ((· + ·) : ℚ → ℚ → ℚ) := by
  have ha : Computable (fun p : ℚ × ℚ => p.1.num * (p.2.den : ℤ)) :=
    primrec_int_mul.to_comp.comp (computable_rat_num.comp Computable.fst)
      ((primrec_int_ofNat.to_comp.comp computable_rat_den).comp Computable.snd)
  have hb : Computable (fun p : ℚ × ℚ => p.2.num * (p.1.den : ℤ)) :=
    primrec_int_mul.to_comp.comp (computable_rat_num.comp Computable.snd)
      ((primrec_int_ofNat.to_comp.comp computable_rat_den).comp Computable.fst)
  have hn : Computable (fun p : ℚ × ℚ => p.1.num * (p.2.den : ℤ) + p.2.num * (p.1.den : ℤ)) :=
    primrec_int_add.to_comp.comp ha hb
  have hd : Computable (fun p : ℚ × ℚ => p.1.den * p.2.den) :=
    Primrec.nat_mul.to_comp.comp (computable_rat_den.comp Computable.fst) (computable_rat_den.comp Computable.snd)
  refine (computable_rat_of_parts hn hd (fun p => mul_ne_zero p.1.den_ne_zero p.2.den_ne_zero)).of_eq ?_
  intro ⟨a,b⟩
  dsimp
  push_cast
  rw [add_div, mul_div_mul_right _ _ (by exact_mod_cast b.den_ne_zero : (b.den : ℚ) ≠ 0)]
  rw [mul_comm (a.den : ℚ), mul_div_mul_right _ _ (by exact_mod_cast a.den_ne_zero : (a.den : ℚ) ≠ 0)]
  rw [Rat.num_div_den, Rat.num_div_den]

lemma computable_rat_mul : Computable₂ ((· * ·) : ℚ → ℚ → ℚ) := by
  have hn : Computable (fun p : ℚ × ℚ => p.1.num * p.2.num) :=
    primrec_int_mul.to_comp.comp (computable_rat_num.comp Computable.fst) (computable_rat_num.comp Computable.snd)
  have hd : Computable (fun p : ℚ × ℚ => p.1.den * p.2.den) :=
    Primrec.nat_mul.to_comp.comp (computable_rat_den.comp Computable.fst) (computable_rat_den.comp Computable.snd)
  refine (computable_rat_of_parts hn hd (fun p => mul_ne_zero p.1.den_ne_zero p.2.den_ne_zero)).of_eq ?_
  intro ⟨a,b⟩
  dsimp
  push_cast
  rw [mul_div_mul_comm, Rat.num_div_den, Rat.num_div_den]

lemma computable_rat_neg : Computable (fun q : ℚ => -q) := by
  exact (computable_rat_of_parts (primrec_int_neg.to_comp.comp computable_rat_num)
    computable_rat_den Rat.den_ne_zero).of_eq (fun q => by
      push_cast
      rw [neg_div, Rat.num_div_den])

end BalancedTransport.Effectivity
end

end OAI


