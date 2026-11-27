-- Prove2me | solution 1 for AbelianCayleyHDX.explicit_relation_complexes
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:40:20.006523+00:00
-- url     : https://prove2.me/submissions/2a5e52bd-49ba-49c3-8109-e35feef6d415

import Definitions.Def_OAIQ053K038
import Definitions.Def_OAIQ053K039
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_AbelianCayleyHDX_encRat
import Definitions.Def_HMBinPacking_OutputsWithin
import Theorems.Thm_ShiTM_comp_outputsInTime
import Mathlib
import Definitions.Def_AbelianCayleyHDX_kerF2
import Definitions.Def_AbelianCayleyHDX_rowspan
import Definitions.Def_ReplParity_Vec
import Definitions.Def_AbelianCayleyHDX_IsGoodRelationMatrix
import Definitions.Def_AbelianCayleyHDX_relationComplex
import Definitions.Def_AbelianCayleyHDX_Htilde
import Definitions.Def_AbelianCayleyHDX_IsCayleyComplex
import Definitions.Def_AbelianCayleyHDX_IsTranslationInvariant
import Definitions.Def_AbelianCayleyHDX_linkVerts
import Definitions.Def_AbelianCayleyHDX_linkWeight
import Definitions.Def_AbelianCayleyHDX_PH
import Definitions.Def_AbelianCayleyHDX_HasLocalSpectralNorm
import Theorems.Thm_AbelianCayleyHDX_triangle_orbits
import Definitions.Def_AbelianCayleyHDX_IsExplicitFamily

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

namespace AbelianCayleyHDX.XP

/-! ### General `Poly` combinators -/

theorem foldl_append_eq {α : Type} (xs : List (List α)) (acc : List α) :
    List.foldl (fun b a => b ++ a) acc xs = acc ++ xs.flatten := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih, List.append_assoc]

theorem poly_flatten {α : Type} [Coding α] [Inhabited α] : Poly (List.flatten : List (List α) → List α) := by
  let P : PolyProgram (encodePair (encodeList (encodeList (enc : α → List Bool)))
      (encodeList (enc : α → List Bool))) (encodeList (enc : α → List Bool))
      (fun x : List (List α) × List α => List.foldl (fun b a => (b, a).1 ++ (b, a).2) x.2 x.1) :=
    PolyProgram.listFoldLinear (PolyProgram.listAppend (enc : α → List Bool) default) [] 1 (by
      intro b a
      simp only [EncodedList.append, List.length_append]
      omega)
  have h1 : Poly (fun xs : List (List α) => (xs, ([] : List α))) :=
    Poly.pair Poly.identity (OAI.MetricKMedian.Binary.Automatic.Poly.const ([] : List α))
  have h2 : Poly (fun x : List (List α) × List α =>
      List.foldl (fun b a => (b, a).1 ++ (b, a).2) x.2 x.1) := ⟨P⟩
  have := Poly.comp h2 h1
  convert this using 1
  funext xs
  simp only
  rw [foldl_append_eq, List.nil_append]

attribute [fun_prop] poly_flatten

variable {γ α β δ : Type} [Coding γ] [Coding α] [Coding β] [Coding δ]

@[fun_prop] theorem flatMap_ctx [Inhabited β] [Inhabited δ] {f : γ → β → List δ} {as : γ → List β}
    (hf : Poly (fun x : γ × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).flatMap (f x)) := by
  have h := Poly.comp poly_flatten (Poly.list_map hf ha)
  convert h using 2 with x
  rw [List.flatMap_def]

@[fun_prop] theorem map_ctx [Inhabited β] [Inhabited δ] {f : γ → β → δ} {as : γ → List β}
    (hf : Poly (fun x : γ × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).map (f x)) := Poly.list_map hf ha

@[fun_prop] theorem append_comp [Inhabited α] {f g : γ → List α} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x ++ g x) := Poly.comp Poly.list_append (Poly.pair hf hg)

@[fun_prop] theorem cons_comp {f : γ → α} {g : γ → List α} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x :: g x) := Poly.comp Poly.list_cons (Poly.pair hf hg)

@[fun_prop] theorem length_comp [Inhabited α] {f : γ → List α} (hf : Poly f) :
    Poly (fun x => (f x).length) := Poly.comp Poly.list_length hf

@[fun_prop] theorem range_length_comp [Inhabited α] {f : γ → List α} (hf : Poly f) :
    Poly (fun x => List.range (f x).length) :=
  Poly.comp (f := fun xs : List α => List.range xs.length) Poly.list_indices hf

@[fun_prop] theorem nat_eq_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x = g x)) := Poly.comp Poly.nat_eq (Poly.pair hf hg)

@[fun_prop] theorem nat_add_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x + g x) := Poly.comp Poly.nat_add (Poly.pair hf hg)

@[fun_prop] theorem nat_sub_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x - g x) := Poly.comp Poly.nat_sub (Poly.pair hf hg)

@[fun_prop] theorem rat_mul_comp {f g : γ → ℚ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x * g x) := Poly.comp Poly.rat_mul (Poly.pair hf hg)

@[fun_prop] theorem rat_div_comp {f g : γ → ℚ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x / g x) := Poly.comp Poly.rat_div (Poly.pair hf hg)

@[fun_prop] theorem rat_lt_comp' {f g : γ → ℚ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x < g x)) := Poly.comp Poly.rat_lt (Poly.pair hf hg)

@[fun_prop] theorem rat_ofNat_comp {f : γ → ℕ} (hf : Poly f) : Poly (fun x => ((f x : ℕ) : ℚ)) :=
  Poly.comp Poly.rat_ofNat hf

@[fun_prop] theorem bits_comp {f : γ → ℕ} (hf : Poly f) : Poly (fun x => Nat.bits (f x)) :=
  Poly.comp (⟨PolyProgram.natAsList⟩ : Poly (Nat.bits : ℕ → List Bool)) hf

@[fun_prop] theorem value_comp {f : γ → List Bool} (hf : Poly f) : Poly (fun x => Word.value (f x)) :=
  Poly.comp (⟨BooleanLists.valueProgram⟩ : Poly (Word.value : List Bool → ℕ)) hf

@[fun_prop] theorem num_abs_comp {f : γ → ℚ} (hf : Poly f) : Poly (fun x => (f x).num.natAbs) :=
  Poly.comp (⟨PolyProgram.intAbs⟩ : Poly (Int.natAbs : ℤ → ℕ))
    (Poly.comp (⟨PolyProgram.ratNum⟩ : Poly (Rat.num : ℚ → ℤ)) hf)

@[fun_prop] theorem den_comp {f : γ → ℚ} (hf : Poly f) : Poly (fun x => (f x).den) :=
  Poly.comp (⟨PolyProgram.ratDen⟩ : Poly (Rat.den : ℚ → ℕ)) hf

@[fun_prop] theorem const' (b : β) : Poly (fun _ : γ => b) :=
  OAI.MetricKMedian.Binary.Automatic.Poly.const b

@[fun_prop] theorem id' : Poly (fun x : γ => x) := Poly.identity

@[fun_prop] theorem fst' : Poly (fun x : γ × β => x.1) := Poly.fst

@[fun_prop] theorem snd' : Poly (fun x : γ × β => x.2) := Poly.snd

@[fun_prop] theorem fst_comp {f : γ → α × β} (hf : Poly f) : Poly (fun x => (f x).1) :=
  Poly.comp Poly.fst hf

@[fun_prop] theorem snd_comp {f : γ → α × β} (hf : Poly f) : Poly (fun x => (f x).2) :=
  Poly.comp Poly.snd hf

@[fun_prop] theorem pair' {f : γ → α} {g : γ → β} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => (f x, g x)) := Poly.pair hf hg

@[fun_prop] theorem ite' {p : γ → Bool} {f g : γ → α} (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x = true then f x else g x) := Poly.ite hp hf hg

end AbelianCayleyHDX.XP

namespace AbelianCayleyHDX.XP
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

variable {γ α : Type} [Coding γ] [Coding α]

@[fun_prop] theorem tail_comp [Inhabited α] {f : γ → List α} (hf : Poly f) :
    Poly (fun x => (f x).tail) := Poly.comp Poly.list_tail hf

/-! ### The output function -/

/-- `encNat`, written with `Nat.bits`. -/
def encNatB (m : ℕ) : List Bool := (Nat.bits m).flatMap (fun b => [false, b]) ++ [true, false]

/-- `encNat 0` / `encNat 1`. -/
def cbit (b : Bool) : List Bool := if b then [false, true, true, false] else [true, false]

def encRatB (q : ℚ) : List Bool := decide (q < 0) :: (encNatB q.num.natAbs ++ encNatB q.den)

def vecB (n : ℕ) (cs : List Bool) : List Bool := encNatB n ++ cs.flatMap cbit

def posZero (k : ℕ) : List Bool := (List.range k).map (fun _ => false)

def posE (k i : ℕ) : List Bool := (List.range k).map (fun r => decide (r = i))

def pow2B (k : ℕ) : ℕ := Word.value (((List.range k).tail.map (fun _ => false)) ++ [true])

/-- The normalization `Z(k) = k · 2^{k-1} · K`. -/
def ZB (Kc : ℚ) (k : ℕ) : ℚ := (k : ℚ) * (pow2B k : ℚ) * Kc

def gensC (labNZ : List (List Bool)) (k : ℕ) : List (List Bool) :=
  (posZero k :: (List.range k).map (posE k)).flatMap (fun p => labNZ.map (fun b => p ++ b))

def repsC (T1 : List (List (List Bool))) (T2 : List (List (List Bool) × List (List Bool) × ℚ))
    (ws : ℚ) (k : ℕ) : List (List (List Bool) × ℚ) :=
  T1.map (fun L => (L.map (fun b => posZero k ++ b), ws * (k : ℚ))) ++
    (List.range k).flatMap (fun i => T2.map (fun e =>
      (e.1.map (fun b => posZero k ++ b) ++ e.2.1.map (fun b => posE k i ++ b), e.2.2)))

def outB (a : ℕ) (labNZ : List (List Bool)) (T1 : List (List (List Bool)))
    (T2 : List (List (List Bool) × List (List Bool) × ℚ)) (ws Kc : ℚ) (k : ℕ) : List Bool :=
  encNatB (k + a) ++
    (encNatB (gensC labNZ k).length ++ (gensC labNZ k).flatMap (vecB (k + a))) ++
    (encNatB (repsC T1 T2 ws k).length ++ (repsC T1 T2 ws k).flatMap (fun e =>
      encNatB e.1.length ++ e.1.flatMap (vecB (k + a)) ++ encRatB (e.2 / ZB Kc k)))

@[fun_prop] theorem encNatB_comp {f : γ → ℕ} (hf : Poly f) : Poly (fun x => encNatB (f x)) := by
  unfold encNatB; fun_prop

@[fun_prop] theorem cbit_comp {f : γ → Bool} (hf : Poly f) : Poly (fun x => cbit (f x)) := by
  unfold cbit; fun_prop

@[fun_prop] theorem encRatB_comp {f : γ → ℚ} (hf : Poly f) : Poly (fun x => encRatB (f x)) := by
  unfold encRatB; fun_prop

@[fun_prop] theorem vecB_comp {f : γ → ℕ} {g : γ → List Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => vecB (f x) (g x)) := by
  unfold vecB; fun_prop

theorem poly_outB (a : ℕ) (labNZ : List (List Bool)) (T1 : List (List (List Bool)))
    (T2 : List (List (List Bool) × List (List Bool) × ℚ)) (ws Kc : ℚ) :
    Poly (fun w : List Bool => outB a labNZ T1 T2 ws Kc w.length) := by
  unfold outB gensC repsC ZB pow2B posE posZero
  fun_prop

end AbelianCayleyHDX.XP

namespace AbelianCayleyHDX.XP
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem poly_eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i))

/-- A `Poly` function on Boolean words is computed by a multi-stack machine within a polynomial
time bound in any upper bound of the input length. -/
theorem outputsWithin_of_poly {F : List Bool → List Bool}
    (hF : Poly (fun w : List Bool => F w)) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (p : Polynomial ℕ), ∀ (w : List Bool) (N : ℕ),
      w.length ≤ N → HMBinPacking.OutputsWithin M w (F w) (p.eval N) := by
  let P : PolyProgram id id (id ∘ (F ∘ id)) :=
    BooleanLists.packProgram.comp (hF.program.comp BooleanLists.unpackProgram)
  refine ⟨⟨P.machine.tm, Equiv.refl _, Equiv.refl _⟩, P.time, fun w N hN => ?_⟩
  have h := P.outputs w
  have h' : Turing.TM2OutputsInTime P.machine.tm w (some (F w)) (P.time.eval N) :=
    ⟨h.toEvalsTo, le_trans h.steps_le_m (poly_eval_mono _ hN)⟩
  unfold HMBinPacking.OutputsWithin
  change Nonempty (Turing.TM2OutputsInTime P.machine.tm
    (List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₀)).symm) w)
    (some (List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₁)).symm) (F w))) (P.time.eval N))
  have e1 : List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₀)).symm) w = w := List.map_id w
  have e2 : List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₁)).symm) (F w) = F w :=
    List.map_id (F w)
  rw [e1, e2]
  exact ⟨h'⟩

end AbelianCayleyHDX.XP


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

namespace AbelianCayleyHDX.XP

/-- **Post-processing a machine's output by a polynomial-time function.** If `Mach` turns `x a`
into `W a` within `T a` steps and `F` is `Poly`, then one machine turns `x a` into `F (W a)` within
`T a + 2|W a| + 2 + P(|W a|)` steps. -/
theorem outputsWithin_comp {α : Type*} {Mach : Turing.TM2ComputableAux Bool Bool}
    {x W : α → List Bool} {T : α → ℕ}
    (hM : ∀ a, HMBinPacking.OutputsWithin Mach (x a) (W a) (T a))
    {F : List Bool → List Bool} (hF : Poly (fun w : List Bool => F w)) :
    ∃ (M' : Turing.TM2ComputableAux Bool Bool) (P : Polynomial ℕ), ∀ a,
      HMBinPacking.OutputsWithin M' (x a) (F (W a))
        (T a + (2 * (W a).length + 2) + P.eval (W a).length) := by
  classical
  let P0 : PolyProgram id id (id ∘ (F ∘ id)) :=
    BooleanLists.packProgram.comp (hF.program.comp BooleanLists.unpackProgram)
  let tm₂ := P0.machine.tm
  let tr : Mach.tm.Γ Mach.tm.k₁ → tm₂.Γ tm₂.k₀ := fun s => Mach.outputAlphabet s
  let M' : Turing.TM2ComputableAux Bool Bool :=
    ⟨ShiTM2.comp Mach.tm tm₂ tr false,
      (ShiTM2.compInputAlphabet Mach.tm tm₂ tr false).trans Mach.inputAlphabet,
      (ShiTM2.compOutputAlphabet Mach.tm tm₂ tr false).trans (Equiv.refl Bool)⟩
  refine ⟨M', P0.time, fun a => ?_⟩
  obtain ⟨h₁⟩ := hM a
  have h₂ : Turing.TM2OutputsInTime tm₂
      (((W a).map Mach.outputAlphabet.symm).map tr) (some (F (W a)))
      (P0.time.eval ((W a).map Mach.outputAlphabet.symm).length) := by
    have e : ((W a).map Mach.outputAlphabet.symm).map tr = W a := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (W a)]
      congr 1; funext s
      show Mach.outputAlphabet (Mach.outputAlphabet.symm s) = s
      exact Equiv.apply_symm_apply _ _
    rw [e, List.length_map]
    exact P0.outputs (W a)
  obtain ⟨h⟩ := ShiTM.comp_outputsInTime (inst := ShiTM2.compKDecEq Mach.tm tm₂) Mach.tm tm₂ tr
    false _ _ _ _ _ h₁ h₂
  rw [List.length_map] at h
  unfold HMBinPacking.OutputsWithin
  have e2 : List.map (⇑M'.outputAlphabet.symm) (F (W a)) = F (W a) := List.map_id _
  rw [e2]
  exact ⟨h⟩

end AbelianCayleyHDX.XP


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX.XP

/-! ### Decoding a stream of `encNat` tokens -/

lemma value_bits (t : ℕ) : Word.value (Nat.bits t) = t := by
  induction t using Nat.binaryRec with
  | zero => simp [Word.value]
  | bit b n ih =>
    by_cases h : Nat.bit b n = 0
    · rw [h]; simp [Word.value]
    · rw [Nat.bits_append_bit n b (fun hn => by
        subst hn; cases b
        · exact absurd (by simp [Nat.bit]) h
        · rfl)]
      simp only [Word.value, ih]
      cases b <;> simp [Nat.bit] <;> ring

lemma bits_length_value_le (cur : List Bool) : (Nat.bits (Word.value cur)).length ≤ cur.length := by
  rw [Nat.size_eq_bits_len, Nat.size_le]
  induction cur with
  | nil => simp [Word.value]
  | cons b bs ih =>
    simp only [Word.value, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-- The decoder state: (inside a pair?, first bit of the pair, current bits, tokens so far). -/
abbrev DState := Bool × Bool × List Bool × List ℕ

def dstep (s : DState) (c : Bool) : DState :=
  if s.1 then
    (if s.2.1 then (false, s.2.1, [], s.2.2.2 ++ [Word.value s.2.2.1])
      else (false, s.2.1, s.2.2.1 ++ [c], s.2.2.2))
  else (true, c, s.2.2.1, s.2.2.2)

def decTokens (w : List Bool) : List ℕ := (w.foldl dstep (false, false, [], [])).2.2.2

lemma fold_pairs (bs : List Bool) (f : Bool) (cur : List Bool) (acc : List ℕ) (rest : List Bool) :
    (bs.flatMap (fun b => [false, b]) ++ rest).foldl dstep (false, f, cur, acc) =
      rest.foldl dstep (false, (if bs = [] then f else false), cur ++ bs, acc) := by
  induction bs generalizing f cur with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.foldl_cons]
    rw [show dstep (dstep (false, f, cur, acc) false) b = (false, false, cur ++ [b], acc) by
      simp [dstep]]
    rw [ih]
    simp only [List.cons_ne_nil, if_false, List.append_assoc, List.singleton_append]
    by_cases hbs : bs = [] <;> simp [hbs]

lemma fold_encNat (t : ℕ) (f : Bool) (acc : List ℕ) (rest : List Bool) :
    (encNat t ++ rest).foldl dstep (false, f, [], acc) =
      rest.foldl dstep (false, true, [], acc ++ [t]) := by
  unfold encNat encBits
  rw [List.append_assoc, fold_pairs]
  simp only [List.cons_append, List.nil_append, List.foldl_cons, List.nil_append]
  congr 1
  simp only [dstep, if_true, Bool.false_eq_true, if_false]
  congr
  rw [Nat.digits_two_eq_bits, List.map_map]
  conv_rhs => rw [← value_bits t]
  congr 1
  conv_rhs => rw [← List.map_id t.bits]
  congr 1; funext b; cases b <;> rfl

lemma fold_tokens (L : List ℕ) (f : Bool) (acc : List ℕ) :
    ∃ f', (L.flatMap encNat).foldl dstep (false, f, [], acc) = (false, f', [], acc ++ L) := by
  induction L generalizing f acc with
  | nil => exact ⟨f, by simp⟩
  | cons t L ih =>
    rw [List.flatMap_cons, fold_encNat]
    obtain ⟨f', h⟩ := ih true (acc ++ [t])
    exact ⟨f', by rw [h, List.append_assoc, List.singleton_append]⟩

theorem decTokens_flatMap (L : List ℕ) : decTokens (L.flatMap encNat) = L := by
  unfold decTokens
  obtain ⟨f', h⟩ := fold_tokens L false []
  rw [h]; simp

lemma encList_length_append {α : Type} (ea : α → List Bool) (l : List α) (x : α) :
    (encodeList ea (l ++ [x])).length = (encodeList ea l).length + 2 * (ea x).length + 1 := by
  rw [EncodedList.append, List.length_append]
  simp [encodeList, quote_length]; omega

lemma encList_bool_length (l : List Bool) : (encodeList encodeBool l).length = 3 * l.length := by
  induction l with
  | nil => simp [encodeList]
  | cons b l ih => simp [encodeList, quote_length, encodeBool, ih]; ring

theorem dstep_size (st : DState) (c : Bool) :
    ((enc : DState → List Bool) (dstep st c)).length ≤
      ((enc : DState → List Bool) st).length + 2 * (2 * (encodeBool c).length + 1) := by
  obtain ⟨p, f, cur, acc⟩ := st
  change (encodePair encodeBool (encodePair encodeBool (encodePair (encodeList encodeBool)
      (encodeList Nat.bits))) (dstep (p, f, cur, acc) c)).length ≤
    (encodePair encodeBool (encodePair encodeBool (encodePair (encodeList encodeBool)
      (encodeList Nat.bits))) (p, f, cur, acc)).length + 2 * (2 * (encodeBool c).length + 1)
  unfold dstep
  cases p <;> cases f <;>
    simp only [Bool.false_eq_true, if_false, if_true, encodePair_length, encodeBool,
      List.length_singleton, encList_length_append, encList_bool_length, List.length_append,
      List.length_nil, mul_zero] <;> try omega
  all_goals (have := bits_length_value_le cur; omega)

theorem poly_decTokens : Poly (fun w : List Bool => decTokens w) := by
  let P : PolyProgram (encodePair (enc : DState → List Bool) encodeBool) (enc : DState → List Bool)
      (fun x : DState × Bool => dstep x.1 x.2) := by
    have h : Poly (fun x : DState × Bool => dstep x.1 x.2) := by unfold dstep; fun_prop
    exact h.program
  let Q := P.listFoldLinear false 2 (fun b a => dstep_size b a)
  have hQ : Poly (fun x : List Bool × DState => x.1.foldl (fun b a => dstep b a) x.2) := ⟨Q⟩
  have h2 : Poly (fun w : List Bool => (w.foldl (fun b a => dstep b a)
      ((false, false, [], []) : DState))) :=
    Poly.comp (f := fun x : List Bool × DState => x.1.foldl (fun b a => dstep b a) x.2) hQ
      (Poly.pair Poly.identity (OAI.MetricKMedian.Binary.Automatic.Poly.const _))
  have h3 := snd_comp (snd_comp (snd_comp h2))
  exact h3

end AbelianCayleyHDX.XP


namespace AbelianCayleyHDX.XK

open Matrix

variable {M : ℕ}

abbrev V (M : ℕ) := Fin M → ZMod 2

lemma z2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide

lemma z2_add_self (c : ZMod 2) : c + c = 0 := by revert c; decide

/-- One step of the incremental kernel computation. -/
def kstep (h : V M) (K : List (V M)) : List (V M) :=
  K.map (fun k => k + (h ⬝ᵥ k) • K.getD (K.findIdx (fun k => decide (h ⬝ᵥ k ≠ 0))) 0)

/-- The common kernel of a list of rows. -/
def U (S : List (V M)) : Submodule (ZMod 2) (V M) :=
  ⨅ h ∈ S, LinearMap.ker (dotProductBilin (ZMod 2) (ZMod 2) h)

lemma mem_U {S : List (V M)} {v : V M} : v ∈ U S ↔ ∀ h ∈ S, h ⬝ᵥ v = 0 := by
  simp [U, Submodule.mem_iInf]

def Inv (S K : List (V M)) : Prop :=
  Submodule.span (ZMod 2) {x | x ∈ K} = U S ∧
    (K.filter (· ≠ 0)).length = Module.finrank (ZMod 2) (U S)

lemma span_filter (K : List (V M)) :
    Submodule.span (ZMod 2) {x | x ∈ K.filter (· ≠ 0)} = Submodule.span (ZMod 2) {x | x ∈ K} := by
  apply le_antisymm
  · apply Submodule.span_mono; intro x hx; exact (List.mem_filter.1 hx).1
  · rw [Submodule.span_le]
    intro x hx
    by_cases h0 : x = 0
    · rw [h0]; exact Submodule.zero_mem _
    · exact Submodule.subset_span (List.mem_filter.2 ⟨hx, by simpa using h0⟩)

/-- Under the invariant, the nonzero entries are linearly independent. -/
lemma inv_li {S K : List (V M)} (hI : Inv S K) :
    LinearIndependent (ZMod 2) (fun i : Fin (K.filter (· ≠ 0)).length => (K.filter (· ≠ 0)).get i) := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
  have hr : Set.range (fun i : Fin (K.filter (· ≠ 0)).length => (K.filter (· ≠ 0)).get i) =
      {x | x ∈ K.filter (· ≠ 0)} := by
    ext x; simp only [Set.mem_range, Set.mem_setOf_eq, List.mem_iff_get]
  unfold Set.finrank
  rw [hr, span_filter, hI.1, hI.2]

lemma inv_nodup {S K : List (V M)} (hI : Inv S K) : (K.filter (· ≠ 0)).Nodup := by
  have hli := inv_li hI
  rw [List.nodup_iff_injective_get]
  exact hli.injective

/-- **The step preserves the invariant.** -/
theorem inv_step {S K : List (V M)} (hI : Inv S K) (h : V M) : Inv (h :: S) (kstep h K) := by
  classical
  by_cases hall : ∀ k ∈ K, h ⬝ᵥ k = 0
  · -- nothing changes
    have hidx : K.findIdx (fun k => decide (h ⬝ᵥ k ≠ 0)) = K.length := by
      rw [List.findIdx_eq_length]; intro k hk; simpa using hall k hk
    have hK : kstep h K = K := by
      unfold kstep; rw [hidx]
      conv_rhs => rw [← List.map_id K]
      apply List.map_congr_left; intro k hk; simp [hall k hk]
    have hU : U (h :: S) = U S := by
      apply le_antisymm
      · intro v hv; rw [mem_U] at hv ⊢; exact fun g hg => hv g (List.mem_cons_of_mem _ hg)
      · intro v hv
        rw [mem_U]
        intro g hg
        rcases List.mem_cons.1 hg with rfl | hg
        · rw [← hI.1] at hv
          refine Submodule.span_induction (p := fun v _ => g ⬝ᵥ v = 0) ?_ ?_ ?_ ?_ hv
          · intro x hx; exact hall x hx
          · simp
          · intro x y _ _ hx hy; rw [dotProduct_add, hx, hy, add_zero]
          · intro c x _ hx; rw [dotProduct_smul, hx, smul_zero]
        · exact (mem_U.1 hv) g hg
    rw [hK, Inv, hU]; exact hI
  · push Not at hall
    obtain ⟨k0, hk0, hk0v⟩ := hall
    set l0 := K.findIdx (fun k => decide (h ⬝ᵥ k ≠ 0)) with hl0
    have hlt : l0 < K.length := List.findIdx_lt_length_of_exists ⟨k0, hk0, by simpa using hk0v⟩
    set kp := K.getD l0 0 with hkp
    have hkpK : kp = K[l0] := by rw [hkp, List.getD_eq_getElem _ _ hlt]
    have hkpv : h ⬝ᵥ kp = 1 := by
      have := List.findIdx_getElem (w := hlt)
      rw [← hkpK] at this
      simpa using (z2_cases _).resolve_left (by simpa using this)
    have hkpmem : kp ∈ K := by rw [hkpK]; exact List.getElem_mem _
    set K' := kstep h K with hK'
    have hK'eq : K' = K.map (fun k => k + (h ⬝ᵥ k) • kp) := rfl
    -- the new subspace
    have hsub : Submodule.span (ZMod 2) {x | x ∈ K'} ≤ U (h :: S) := by
      rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_setOf_eq, hK'eq, List.mem_map] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      rw [SetLike.mem_coe, mem_U]
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · rw [dotProduct_add, dotProduct_smul, hkpv, smul_eq_mul, mul_one, z2_add_self]
      · have hkU : k ∈ U S := hI.1 ▸ Submodule.subset_span hk
        have hpU : kp ∈ U S := hI.1 ▸ Submodule.subset_span hkpmem
        rw [dotProduct_add, dotProduct_smul, (mem_U.1 hkU) g hg, (mem_U.1 hpU) g hg]; simp
    have hspan : Submodule.span (ZMod 2) {x | x ∈ K'} = U (h :: S) := by
      refine le_antisymm hsub (fun v hv => ?_)
      have hvU : v ∈ U S := by
        rw [mem_U] at hv ⊢; exact fun g hg => hv g (List.mem_cons_of_mem _ hg)
      rw [← hI.1] at hvU
      -- `span K ≤ span K' ⊔ span {kp}`
      have hle : Submodule.span (ZMod 2) {x | x ∈ K} ≤
          Submodule.span (ZMod 2) {x | x ∈ K'} ⊔ Submodule.span (ZMod 2) {kp} := by
        rw [Submodule.span_le]
        intro k hk
        have e : k = (k + (h ⬝ᵥ k) • kp) + (h ⬝ᵥ k) • kp := by
          rw [add_assoc, ← add_smul, z2_add_self, zero_smul, add_zero]
        rw [SetLike.mem_coe, e]
        refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ?_))
          (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
        simp only [Set.mem_setOf_eq, hK'eq, List.mem_map]; exact ⟨k, hk, rfl⟩
      obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 (hle hvU)
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      have hwU : w ∈ U (h :: S) := hsub hw
      have h1 := (mem_U.1 hv) h (List.mem_cons_self)
      have h2 := (mem_U.1 hwU) h (List.mem_cons_self)
      rw [dotProduct_add, h2, zero_add, dotProduct_smul, hkpv, smul_eq_mul, mul_one] at h1
      rw [h1, zero_smul, add_zero]; exact hw
    refine ⟨hspan, ?_⟩
    -- counting nonzero entries
    have hnd := inv_nodup hI
    have hkp0 : kp ≠ 0 := by intro h0; rw [h0, dotProduct_zero] at hkpv; exact zero_ne_one hkpv
    have hkpf : kp ∈ K.filter (· ≠ 0) := List.mem_filter.2 ⟨hkpmem, by simpa using hkp0⟩
    have hfun : (fun k => decide ((k + (h ⬝ᵥ k) • kp) ≠ 0)) =
        (fun k => decide (k ≠ 0) && decide (k ≠ kp)) := by
      funext k
      by_cases hk0 : k = 0
      · subst hk0; simp
      · rcases z2_cases (h ⬝ᵥ k) with hc | hc
        · have hne : k ≠ kp := by intro hkk; rw [hkk, hkpv] at hc; exact one_ne_zero hc
          simp only [hc, zero_smul, add_zero, hk0, hne, ne_eq, not_false_eq_true, decide_true,
            Bool.and_self]
        · have : k + kp = 0 ↔ k = kp := by
            constructor
            · intro hh
              have hkk : kp + kp = 0 := by ext i; exact z2_add_self _
              calc k = k + (kp + kp) := by rw [hkk, add_zero]
                _ = (k + kp) + kp := (add_assoc _ _ _).symm
                _ = kp := by rw [hh, zero_add]
            · rintro rfl; ext i; exact z2_add_self _
          simp only [hc, one_smul, ne_eq, this, hk0, not_false_eq_true, decide_true, Bool.true_and]
    have hcount : (K'.filter (· ≠ 0)).length + 1 = (K.filter (· ≠ 0)).length := by
      rw [hK'eq, List.filter_map, List.length_map]
      have e : K.filter ((fun k => decide (k ≠ 0)) ∘ fun k => k + (h ⬝ᵥ k) • kp) =
          (K.filter (· ≠ 0)).filter (fun k => k ≠ kp) := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro k _
        have := congrFun hfun k
        simp only [Function.comp] at this ⊢
        rw [this, Bool.and_comm]
      have e2 : (K.filter (· ≠ 0)).filter (fun k => k ≠ kp) = (K.filter (· ≠ 0)).erase kp := by
        rw [List.Nodup.erase_eq_filter hnd]
        apply List.filter_congr; intro k _; by_cases hk : k = kp <;> simp [hk]
      rw [e, e2, List.length_erase_of_mem hkpf]
      have : 0 < (K.filter (· ≠ 0)).length := List.length_pos_of_mem hkpf
      omega
    -- the dimension drops by one
    let f : V M →ₗ[ZMod 2] ZMod 2 := dotProductBilin (ZMod 2) (ZMod 2) h
    have hf : ∀ v, f v = h ⬝ᵥ v := fun v => rfl
    have hW : U (h :: S) = LinearMap.ker f ⊓ U S := by
      ext v; simp only [Submodule.mem_inf, LinearMap.mem_ker, hf, mem_U, List.mem_cons]
      constructor
      · intro hv; exact ⟨hv h (Or.inl rfl), fun g hg => hv g (Or.inr hg)⟩
      · rintro ⟨h1, h2⟩ g (rfl | hg); exacts [h1, h2 g hg]
    have hsup : LinearMap.ker f ⊔ U S = ⊤ := by
      rw [eq_top_iff]; intro v _
      have hpU : kp ∈ U S := hI.1 ▸ Submodule.subset_span hkpmem
      have e : v = (v - (h ⬝ᵥ v) • kp) + (h ⬝ᵥ v) • kp := by abel
      rw [e]
      refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
        (Submodule.mem_sup_right (Submodule.smul_mem _ _ hpU))
      rw [LinearMap.mem_ker, hf, dotProduct_sub, dotProduct_smul, hkpv, smul_eq_mul, mul_one,
        sub_self]
    have hrange : Module.finrank (ZMod 2) (LinearMap.range f) = 1 := by
      have : LinearMap.range f = ⊤ := by
        rw [eq_top_iff]; intro c _; exact ⟨c • kp, by rw [map_smul, hf, hkpv, smul_eq_mul, mul_one]⟩
      rw [this, finrank_top, Module.finrank_self]
    have hker := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange] at hker
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker f) (U S)
    rw [hsup, finrank_top, ← hW] at hdim
    have hlen := hI.2
    omega

/-! ### The whole computation -/

def K0 (M : ℕ) : List (V M) := (List.finRange M).map (fun i => Pi.single i 1)

def kernelList (rows : List (V M)) : List (V M) := rows.foldl (fun K h => kstep h K) (K0 M)

lemma U_nil : U ([] : List (V M)) = ⊤ := by
  ext v; simp [mem_U]

lemma inv_init : Inv [] (K0 M) := by
  refine ⟨?_, ?_⟩
  · rw [U_nil, eq_top_iff]
    have h := (Pi.basisFun (ZMod 2) (Fin M)).span_eq
    rw [← h]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    simp only [Pi.basisFun_apply, Set.mem_setOf_eq, K0, List.mem_map, List.mem_finRange, true_and]
    exact ⟨i, rfl⟩
  · rw [U_nil, finrank_top, Module.finrank_fin_fun]
    have : (K0 M).filter (· ≠ 0) = K0 M := by
      rw [List.filter_eq_self]
      intro x hx
      simp only [K0, List.mem_map, List.mem_finRange, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      simp only [ne_eq, decide_eq_true_eq]
      intro h0; have := congrFun h0 i; simp at this
    rw [this, K0, List.length_map, List.length_finRange]

lemma U_congr {S S' : List (V M)} (h : ∀ g, g ∈ S ↔ g ∈ S') : U S = U S' := by
  ext v; simp only [mem_U]; exact ⟨fun hv g hg => hv g ((h g).2 hg), fun hv g hg => hv g ((h g).1 hg)⟩

lemma inv_fold (rows : List (V M)) {S K : List (V M)} (hI : Inv S K) :
    Inv (rows.reverse ++ S) (rows.foldl (fun K h => kstep h K) K) := by
  induction rows generalizing S K with
  | nil => simpa using hI
  | cons h rows ih =>
    rw [List.foldl_cons, List.reverse_cons, List.append_assoc]
    exact ih (by simpa using inv_step hI h)

lemma U_ofFn {R : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) (S : List (V M))
    (hS : ∀ g, g ∈ S ↔ g ∈ List.ofFn H) : U S = AbelianCayleyHDX.kerF2 H := by
  ext v
  rw [mem_U, AbelianCayleyHDX.kerF2, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hv; funext r
    exact hv (H r) ((hS _).2 (List.mem_ofFn.2 ⟨r, rfl⟩))
  · intro hv g hg
    obtain ⟨r, rfl⟩ := List.mem_ofFn.1 ((hS g).1 hg)
    exact congrFun hv r

/-- The computed basis of `ker H`. -/
def basisList {R : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) : List (V M) :=
  (kernelList (List.ofFn H)).filter (· ≠ 0)

theorem basisList_spec {R : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) :
    Submodule.span (ZMod 2) {x | x ∈ basisList H} = AbelianCayleyHDX.kerF2 H ∧
    (basisList H).length = Module.finrank (ZMod 2) (AbelianCayleyHDX.kerF2 H) ∧
    LinearIndependent (ZMod 2) (fun i : Fin (basisList H).length => (basisList H).get i) := by
  have hI := inv_fold (List.ofFn H) inv_init
  have hU : U ((List.ofFn H).reverse ++ []) = AbelianCayleyHDX.kerF2 H :=
    U_ofFn H _ (fun g => by simp)
  refine ⟨?_, ?_, inv_li hI⟩
  · unfold basisList; rw [span_filter, ← hU]; exact hI.1
  · unfold basisList; rw [← hU]; exact hI.2

/-- The quotient map `v ↦ (bₗ ⬝ v)ₗ`. -/
noncomputable def phiMat {R : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) :
    Matrix (Fin (Module.finrank (ZMod 2) (AbelianCayleyHDX.kerF2 H))) (Fin M) (ZMod 2) :=
  Matrix.of fun ℓ i => (basisList H).get (ℓ.cast (basisList_spec H).2.1.symm) i

noncomputable def phi {R : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) :
    (Fin M → ZMod 2) →ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) (AbelianCayleyHDX.kerF2 H)) → ZMod 2) :=
  (phiMat H).mulVecLin

theorem phi_spec {R : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) :
    Function.Surjective (phi H) ∧ LinearMap.ker (phi H) = AbelianCayleyHDX.rowspan H := by
  classical
  obtain ⟨hspan, hlen, hli⟩ := basisList_spec H
  set n := Module.finrank (ZMod 2) (AbelianCayleyHDX.kerF2 H)
  have hrows : LinearIndependent (ZMod 2) (fun ℓ : Fin n => phiMat H ℓ) := by
    have := hli.comp (Fin.cast hlen.symm) (Fin.cast_injective _)
    exact this
  have hrank : (phiMat H).rank = n := by
    rw [Matrix.rank_eq_finrank_span_row,
      show (phiMat H).row = fun ℓ => phiMat H ℓ from rfl, finrank_span_eq_card hrows,
      Fintype.card_fin]
  have hsurj : Function.Surjective (phi H) := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hrank
  refine ⟨hsurj, ?_⟩
  -- `rowspan H ≤ ker φ`
  have hle : AbelianCayleyHDX.rowspan H ≤ LinearMap.ker (phi H) := by
    rw [AbelianCayleyHDX.rowspan, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    funext ℓ
    simp only [phi, Matrix.mulVecLin_apply, Pi.zero_apply, Matrix.mulVec, phiMat]
    have hb : (basisList H).get (ℓ.cast hlen.symm) ∈ AbelianCayleyHDX.kerF2 H := by
      rw [← hspan]; exact Submodule.subset_span (List.get_mem _ _)
    rw [AbelianCayleyHDX.kerF2, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hb
    have := congrFun hb r
    simp only [Matrix.mulVec, Pi.zero_apply] at this
    rw [dotProduct_comm]
    exact this
  have h1 := LinearMap.finrank_range_add_finrank_ker (phi H)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fin_fun] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker H.mulVecLin
  have h3 : Module.finrank (ZMod 2) (LinearMap.range H.mulVecLin) =
      Module.finrank (ZMod 2) (AbelianCayleyHDX.rowspan H) := by
    have := Matrix.rank_eq_finrank_span_row H
    rw [Matrix.rank] at this
    rw [this]; rfl
  have h5 : Module.finrank (ZMod 2) (Fin M → ZMod 2) = M := Module.finrank_fin_fun _
  have h4 : Module.finrank (ZMod 2) (LinearMap.ker H.mulVecLin) = n := rfl
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

end AbelianCayleyHDX.XK


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

namespace AbelianCayleyHDX.XK

open Matrix

variable {M : ℕ}

/-! ### Boolean-list implementation -/

def toV (M : ℕ) (l : List Bool) : V M := fun i => if l.getD i false then 1 else 0

def xorv (a b : List Bool) : List Bool := (a.zip b).map (fun p => xor p.1 p.2)

def dotB (a b : List Bool) : Bool :=
  decide (((a.zip b).filter (fun p => p.1 && p.2)).length % 2 = 1)

def kstepB (h : List Bool) (K : List (List Bool)) : List (List Bool) :=
  K.map (fun k => if dotB h k then xorv k (K.getD (K.findIdx (fun k => dotB h k)) []) else k)

def K0B (M : ℕ) : List (List Bool) :=
  (List.range M).map (fun i => (List.range M).map (fun c => decide (c = i)))

def kernelB (M : ℕ) (rows : List (List Bool)) : List (List Bool) :=
  rows.foldl (fun K h => kstepB h K) (K0B M)

def nzB (l : List Bool) : Bool := !((l.filter (fun b => b)).isEmpty)

def basisB (M : ℕ) (rows : List (List Bool)) : List (List Bool) := (kernelB M rows).filter nzB

/-! ### Correspondence -/

lemma toV_nil : toV M [] = 0 := by funext i; simp [toV]

lemma getD_eq (l : List Bool) (hl : l.length = M) (i : Fin M) : l.getD i false = l[i.1]'(by omega) := by
  rw [List.getD_eq_getElem]

lemma getD_xorv {a b : List Bool} (ha : a.length = M) (hb : b.length = M) {i : ℕ} (hi : i < M) :
    (xorv a b).getD i false = xor (a.getD i false) (b.getD i false) := by
  rw [List.getD_eq_getElem _ _ (by simp [xorv, ha, hb]; omega), List.getD_eq_getElem _ _ (by omega),
    List.getD_eq_getElem _ _ (by omega)]
  simp [xorv]

lemma toV_xorv {a b : List Bool} (ha : a.length = M) (hb : b.length = M) :
    toV M (xorv a b) = toV M a + toV M b := by
  funext i
  simp only [toV, Pi.add_apply, getD_xorv ha hb i.2]
  cases a.getD i false <;> cases b.getD i false <;> decide

lemma xorv_length {a b : List Bool} (ha : a.length = M) (hb : b.length = M) :
    (xorv a b).length = M := by simp [xorv, ha, hb]

lemma natCast_z2 (n : ℕ) : ((n : ℕ) : ZMod 2) = if n % 2 = 1 then 1 else 0 := by
  rw [← ZMod.natCast_mod]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> simp

lemma dotB_eq {a b : List Bool} (ha : a.length = M) (hb : b.length = M) :
    dotB a b = decide (toV M a ⬝ᵥ toV M b ≠ 0) := by
  have hA : a = List.ofFn (fun i : Fin M => a[i.1]'(by omega)) := by
    apply List.ext_getElem (by simp [ha]); intro n h1 h2; simp
  have hB : b = List.ofFn (fun i : Fin M => b[i.1]'(by omega)) := by
    apply List.ext_getElem (by simp [hb]); intro n h1 h2; simp
  have hzip : a.zip b = List.ofFn (fun i : Fin M => (a[i.1]'(by omega), b[i.1]'(by omega))) := by
    apply List.ext_getElem (by simp [ha, hb]); intro n h1 h2; simp
  have hcount : ((a.zip b).filter (fun p => p.1 && p.2)).length =
      (Finset.univ.filter fun i : Fin M => (a[i.1]'(by omega) && b[i.1]'(by omega)) = true).card := by
    rw [hzip, OAI.MetricKMedian.EncodingLists.length_filter_ofFn]
  have hdot : toV M a ⬝ᵥ toV M b =
      (((Finset.univ.filter fun i : Fin M => (a[i.1]'(by omega) && b[i.1]'(by omega)) = true).card
        : ℕ) : ZMod 2) := by
    rw [Finset.card_filter, Nat.cast_sum]
    unfold dotProduct toV
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [getD_eq a ha i, getD_eq b hb i]
    cases a[i.1] <;> cases b[i.1] <;> simp
  unfold dotB
  rw [hcount, hdot, natCast_z2]
  generalize (Finset.univ.filter fun i : Fin M => (a[i.1]'(by omega) && b[i.1]'(by omega)) = true).card = c
  by_cases h : c % 2 = 1 <;> simp [h]

lemma toV_ofFn_single (i : ℕ) (hi : i < M) :
    toV M ((List.range M).map (fun c => decide (c = i))) = Pi.single ⟨i, hi⟩ 1 := by
  funext c
  simp only [toV]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_map, List.getElem_range]
  by_cases h : c.1 = i
  · have : c = ⟨i, hi⟩ := Fin.ext h
    subst this; simp
  · have : c ≠ ⟨i, hi⟩ := fun h' => h (by rw [h'])
    simp [h, this]

lemma K0B_spec : (K0B M).map (toV M) = K0 M ∧ ∀ k ∈ K0B M, k.length = M := by
  refine ⟨?_, ?_⟩
  · apply List.ext_getElem (by simp [K0B, K0])
    intro n h1 h2
    have hn : n < M := by simpa [K0B] using h1
    simp only [K0B, K0, List.getElem_map, List.getElem_range, List.getElem_finRange]
    rw [toV_ofFn_single n hn]
    rfl
  · intro k hk
    simp only [K0B, List.mem_map, List.mem_range] at hk
    obtain ⟨i, -, rfl⟩ := hk
    simp

lemma findIdx_congr' {α : Type*} {p q : α → Bool} {l : List α} (h : ∀ x ∈ l, p x = q x) :
    l.findIdx p = l.findIdx q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.findIdx_cons, List.findIdx_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

lemma kstepB_spec {h : List Bool} {K : List (List Bool)} (hh : h.length = M)
    (hK : ∀ k ∈ K, k.length = M) :
    (kstepB h K).map (toV M) = kstep (toV M h) (K.map (toV M)) ∧
      ∀ k ∈ kstepB h K, k.length = M := by
  have hd : ∀ k ∈ K, dotB h k = decide (toV M h ⬝ᵥ toV M k ≠ 0) :=
    fun k hk => dotB_eq hh (hK k hk)
  set l0 := K.findIdx (fun k => dotB h k) with hl0
  have hl0' : (K.map (toV M)).findIdx (fun k => decide (toV M h ⬝ᵥ k ≠ 0)) = l0 := by
    rw [List.findIdx_map, hl0]
    exact (findIdx_congr' (fun k hk => (hd k hk).symm))
  set kp := K.getD l0 [] with hkp
  have hkpV : (K.map (toV M)).getD l0 0 = toV M kp := by
    rw [hkp, ← toV_nil (M := M), List.getD_map]
  -- if some entry pairs to `1`, the pivot is a genuine entry
  have hpiv : ∀ k ∈ K, dotB h k = true → kp ∈ K := by
    intro k hk hdk
    have hlt : l0 < K.length := List.findIdx_lt_length_of_exists ⟨k, hk, hdk⟩
    rw [hkp, List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem _
  refine ⟨?_, ?_⟩
  · unfold kstep kstepB
    rw [hl0', hkpV, List.map_map, List.map_map]
    apply List.map_congr_left
    intro k hk
    simp only [Function.comp]
    rw [← hl0, ← hkp]
    by_cases hdk : dotB h k = true
    · rw [if_pos hdk, toV_xorv (hK k hk) (hK kp (hpiv k hk hdk))]
      have : toV M h ⬝ᵥ toV M k = 1 := by
        rw [hd k hk] at hdk
        exact (z2_cases _).resolve_left (by simpa using hdk)
      rw [this, one_smul]
    · rw [if_neg hdk]
      have : toV M h ⬝ᵥ toV M k = 0 := by
        rw [hd k hk] at hdk; simpa using hdk
      rw [this, zero_smul, add_zero]
  · intro k hk
    simp only [kstepB, List.mem_map] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    rw [← hl0, ← hkp]
    split_ifs with hdk
    · exact xorv_length (hK k' hk') (hK kp (hpiv k' hk' hdk))
    · exact hK k' hk'

lemma fold_spec (rows : List (List Bool)) (hrows : ∀ r ∈ rows, r.length = M)
    (K : List (List Bool)) (hK : ∀ k ∈ K, k.length = M) :
    (rows.foldl (fun K h => kstepB h K) K).map (toV M) =
      (rows.map (toV M)).foldl (fun K h => kstep h K) (K.map (toV M)) ∧
    ∀ k ∈ rows.foldl (fun K h => kstepB h K) K, k.length = M := by
  induction rows generalizing K with
  | nil => exact ⟨rfl, hK⟩
  | cons r rows ih =>
    have hr := hrows r List.mem_cons_self
    obtain ⟨e, hl⟩ := kstepB_spec hr hK
    obtain ⟨e', hl'⟩ := ih (fun r' hr' => hrows r' (List.mem_cons_of_mem _ hr')) _ hl
    refine ⟨?_, hl'⟩
    rw [List.foldl_cons, e', e]; rfl

lemma nzB_eq {k : List Bool} (hk : k.length = M) : nzB k = decide (toV M k ≠ 0) := by
  unfold nzB
  by_cases h : ∃ i, ∃ hi : i < k.length, k[i] = true
  · obtain ⟨i, hi, hki⟩ := h
    have h1 : (k.filter (fun b => b)).isEmpty = false := by
      rw [List.isEmpty_eq_false_iff_exists_mem]
      exact ⟨true, List.mem_filter.2 ⟨by rw [← hki]; exact List.getElem_mem _, rfl⟩⟩
    have h2 : toV M k ≠ 0 := by
      intro h0
      have := congrFun h0 ⟨i, by omega⟩
      simp only [toV, Pi.zero_apply] at this
      rw [List.getD_eq_getElem _ _ hi, hki] at this
      simp at this
    rw [h1]; simp [h2]
  · push Not at h
    have h1 : (k.filter (fun b => b)).isEmpty = true := by
      rw [List.isEmpty_iff, List.filter_eq_nil_iff]
      intro b hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      simpa using h i hi
    have h2 : toV M k = 0 := by
      funext i
      simp only [toV, Pi.zero_apply]
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp [h i.1 (by omega)]
    rw [h1]; simp [h2]

theorem basisB_spec {R : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) (rows : List (List Bool))
    (hrows : ∀ r ∈ rows, r.length = M) (hH : rows.map (toV M) = List.ofFn H) :
    (basisB M rows).map (toV M) = basisList H ∧ ∀ k ∈ basisB M rows, k.length = M := by
  obtain ⟨e, hl⟩ := fold_spec rows hrows (K0B M) K0B_spec.2
  refine ⟨?_, fun k hk => hl k (List.mem_filter.1 hk).1⟩
  unfold basisB basisList kernelList kernelB
  rw [← hH, ← K0B_spec.1, ← e, List.filter_map]
  congr 1
  apply List.filter_congr
  intro k hk
  simp only [Function.comp]
  rw [nzB_eq (hl k hk)]

/-! ### Polynomial time -/

section PolyK
open AbelianCayleyHDX.XP

variable {γ α β : Type} [Coding γ] [Coding α] [Coding β]

@[fun_prop] theorem zip_comp [Inhabited α] [Inhabited β] {f : γ → List α} {g : γ → List β}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => (f x).zip (g x)) :=
  Poly.comp Poly.list_zip (Poly.pair hf hg)

@[fun_prop] theorem xor_comp {f g : γ → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => xor (f x) (g x)) :=
  Poly.comp (f := fun x : Bool × Bool => xor x.1 x.2)
    (⟨PolyProgram.boolXor⟩ : Poly (fun x : Bool × Bool => xor x.1 x.2)) (Poly.pair hf hg)

@[fun_prop] theorem and_comp {f g : γ → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x && g x) := Poly.comp Poly.bool_and (Poly.pair hf hg)

@[fun_prop] theorem not_comp {f : γ → Bool} (hf : Poly f) : Poly (fun x => !(f x)) :=
  Poly.comp Poly.bool_not hf

@[fun_prop] theorem isEmpty_comp {f : γ → List α} (hf : Poly f) : Poly (fun x => (f x).isEmpty) :=
  Poly.comp Poly.list_empty hf

@[fun_prop] theorem nat_mod_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x % g x) :=
  Poly.comp (⟨PolyProgram.natMod⟩ : Poly (fun x : ℕ × ℕ => x.1 % x.2)) (Poly.pair hf hg)

@[fun_prop] theorem nat_lt_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x < g x)) := Poly.comp Poly.nat_lt (Poly.pair hf hg)

@[fun_prop] theorem nat_mul_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x * g x) := Poly.comp Poly.nat_mul (Poly.pair hf hg)

@[fun_prop] theorem getD_comp [Inhabited α] (a0 : α) {xs : γ → List α} {i : γ → ℕ} (hx : Poly xs)
    (hi : Poly i) : Poly (fun x => (xs x).getD (i x) a0) := by
  have := Poly.list_getD_comp a0 hx hi
  convert this using 2 with x
  rw [List.getD_eq_getElem?_getD]

@[fun_prop] theorem findIdx_ctx [Inhabited γ] [Inhabited β] {f : γ → β → Bool} {as : γ → List β}
    (hf : Poly (fun x : γ × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).findIdx (f x)) := Poly.list_findIdx hf ha

@[fun_prop] theorem filter_ctx [Inhabited γ] [Inhabited β] {f : γ → β → Bool} {as : γ → List β}
    (hf : Poly (fun x : γ × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).filter (f x)) := Poly.list_filter hf ha

@[fun_prop] theorem dotB_comp {f g : γ → List Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => dotB (f x) (g x)) := by unfold dotB; fun_prop

@[fun_prop] theorem xorv_comp {f g : γ → List Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => xorv (f x) (g x)) := by unfold xorv; fun_prop

end PolyK

lemma enc_bools (l : List Bool) :
    ((OAI.MetricKMedian.Binary.Automatic.enc : List Bool → List Bool) l).length = 3 * l.length :=
  AbelianCayleyHDX.XP.encList_bool_length l

lemma enc_map_le (K : List (List Bool)) (f : List Bool → List Bool)
    (hf : ∀ k ∈ K, (f k).length ≤ k.length) :
    ((OAI.MetricKMedian.Binary.Automatic.enc : List (List Bool) → List Bool) (K.map f)).length ≤
      ((OAI.MetricKMedian.Binary.Automatic.enc : List (List Bool) → List Bool) K).length := by
  induction K with
  | nil => simp
  | cons k K ih =>
    change (encodeList (encodeList encodeBool) (f k :: K.map f)).length ≤
      (encodeList (encodeList encodeBool) (k :: K)).length
    rw [EncodedList.cons_length, EncodedList.cons_length]
    have h1 := hf k List.mem_cons_self
    have h2 := ih (fun k' hk' => hf k' (List.mem_cons_of_mem _ hk'))
    change _ ≤ (encodeList (encodeList encodeBool) K).length at h2
    rw [AbelianCayleyHDX.XP.encList_bool_length, AbelianCayleyHDX.XP.encList_bool_length]
    have : (encodeList (encodeList encodeBool) (K.map f)).length ≤
        (encodeList (encodeList encodeBool) K).length := h2
    omega

lemma kstepB_size (K : List (List Bool)) (h : List Bool) :
    ((OAI.MetricKMedian.Binary.Automatic.enc : List (List Bool) → List Bool) (kstepB h K)).length ≤
      ((OAI.MetricKMedian.Binary.Automatic.enc : List (List Bool) → List Bool) K).length +
        0 * (2 * ((OAI.MetricKMedian.Binary.Automatic.enc : List Bool → List Bool) h).length + 1) := by
  rw [zero_mul, add_zero]
  apply enc_map_le
  intro k _
  by_cases hd : dotB h k = true
  · rw [if_pos hd]; simp [xorv]
  · rw [if_neg hd]

def K0B' (r : List ℕ) : List (List Bool) := r.map (fun i => r.map (fun c => decide (c = i)))

def basisB' (r : List ℕ) (rows : List (List Bool)) : List (List Bool) :=
  (rows.foldl (fun K h => kstepB h K) (K0B' r)).filter nzB

lemma basisB'_range (M : ℕ) (rows : List (List Bool)) : basisB' (List.range M) rows = basisB M rows := rfl

theorem poly_basisB' : Poly (fun x : List ℕ × List (List Bool) => basisB' x.1 x.2) := by
  have hstep : Poly (fun x : List (List Bool) × List Bool => kstepB x.2 x.1) := by
    unfold kstepB; fun_prop
  let Q := (hstep.program).listFoldLinear ([] : List Bool) 0 (fun b a => kstepB_size b a)
  have hQ : Poly (fun x : List (List Bool) × List (List Bool) =>
      x.1.foldl (fun b a => kstepB a b) x.2) := ⟨Q⟩
  have hK0 : Poly (fun x : List ℕ × List (List Bool) => K0B' x.1) := by unfold K0B'; fun_prop
  have h2 : Poly (fun x : List ℕ × List (List Bool) =>
      x.2.foldl (fun b a => kstepB a b) (K0B' x.1)) :=
    Poly.comp (f := fun x : List (List Bool) × List (List Bool) =>
      x.1.foldl (fun b a => kstepB a b) x.2) hQ (Poly.pair Poly.snd hK0)
  unfold basisB' nzB
  fun_prop

end AbelianCayleyHDX.XK


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RSListDecodingCapacity.AllRates
open ReplParity (Vec)

namespace AbelianCayleyHDX.XR

open AbelianCayleyHDX.XK AbelianCayleyHDX.XP

variable {R M : ℕ}

/-- The token stream of the machine output. -/
def toks (H : Matrix (Fin R) (Fin M) (ZMod 2)) : List ℕ :=
  [R, M, R] ++ (List.ofFn H).flatMap (fun row => M :: (List.ofFn row).map ZMod.val)

lemma W_eq (H : Matrix (Fin R) (Fin M) (ZMod 2)) :
    encNat R ++ encNat M ++ encList encVec (List.ofFn H) = (toks H).flatMap encNat := by
  have hl : (List.ofFn H).length = R := List.length_ofFn
  unfold toks encList
  rw [hl]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]
  congr 3
  rw [List.flatMap_assoc]
  refine List.flatMap_congr (fun row _ => ?_)
  unfold encVec encList
  rw [List.length_ofFn, List.flatMap_cons, List.flatMap_map]
  rfl

lemma getD_flatMap_uniform {α : Type*} (L : List α) (f : α → List ℕ) (k : ℕ)
    (hf : ∀ x, (f x).length = k) {r t : ℕ} (hr : r < L.length) (ht : t < k) :
    (L.flatMap f).getD (r * k + t) 0 = (f L[r]).getD t 0 := by
  induction L generalizing r with
  | nil => simp at hr
  | cons x L ih =>
    rw [List.flatMap_cons]
    rcases r with _ | r
    · simp only [zero_mul, zero_add, List.getElem_cons_zero]
      rw [List.getD_append _ _ _ _ (by rw [hf]; exact ht)]
    · rw [List.getD_append_right _ _ _ _ (by rw [hf]; nlinarith)]
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hr
      rw [hf, show (r + 1) * k + t - k = r * k + t by rw [add_mul, one_mul]; omega, ih hr]
      rfl

lemma toks_length (H : Matrix (Fin R) (Fin M) (ZMod 2)) : (toks H).length = 3 + R * (M + 1) := by
  have hl : (List.ofFn H).length = R := List.length_ofFn
  unfold toks
  simp only [List.length_append, List.length_flatMap, List.length_cons, List.length_map,
    List.length_ofFn]
  rw [List.map_const', List.sum_replicate, hl, smul_eq_mul]
  simp

lemma toks_entry (H : Matrix (Fin R) (Fin M) (ZMod 2)) (r : Fin R) (c : Fin M) :
    (toks H).getD (3 + r.1 * (M + 1) + 1 + c.1) 0 = (H r c).val := by
  have hl : (List.ofFn H).length = R := List.length_ofFn
  unfold toks
  rw [show 3 + r.1 * (M + 1) + 1 + c.1 = 3 + (r.1 * (M + 1) + (1 + c.1)) by ring,
    List.getD_append_right _ _ _ _ (by simp), show [R, M, R].length = 3 from rfl,
    Nat.add_sub_cancel_left,
    getD_flatMap_uniform _ _ (M + 1) (fun row => by simp) (by rw [hl]; exact r.2) (by omega)]
  have e : (List.ofFn H)[r.1]'(by rw [hl]; exact r.2) = H r := List.getElem_ofFn _
  rw [e, show 1 + c.1 = c.1 + 1 by ring, List.getD_cons_succ]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- The post-processor's view of a row. -/
def bitsOfRow (row : Fin M → ZMod 2) : List Bool := (List.ofFn row).map (fun x => decide (x = 1))

lemma getD_bitsOfRow (row : Fin M → ZMod 2) (c : Fin M) :
    (bitsOfRow row).getD c false = decide (row c = 1) := by
  unfold bitsOfRow
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

lemma toV_bitsOfRow (row : Fin M → ZMod 2) : toV M (bitsOfRow row) = row := by
  funext c
  simp only [toV, getD_bitsOfRow]
  rcases z2_cases (row c) with h | h <;> rw [h] <;> simp

lemma bitsOfRow_length (row : Fin M → ZMod 2) : (bitsOfRow row).length = M := by simp [bitsOfRow]

/-- Range below `n`, computed from a long enough list. -/
def rg (L : List ℕ) (n : ℕ) : List ℕ := (List.range L.length).filter (fun i => decide (i < n))

lemma rg_eq (L : List ℕ) {n : ℕ} (hn : n ≤ L.length) : rg L n = List.range n := by
  unfold rg
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  rw [hm, List.range_add, List.filter_append, List.filter_eq_self.2 (fun i hi => by simpa using hi),
    List.filter_eq_nil_iff.2 (fun i hi => by
      simp only [List.mem_map, List.mem_range] at hi
      obtain ⟨j, -, rfl⟩ := hi; simp), List.append_nil]

end AbelianCayleyHDX.XR

open ReplParity (Vec)
open RSListDecodingCapacity.AllRates
open OAI.MetricKMedian.Binary

namespace AbelianCayleyHDX.XE

open AbelianCayleyHDX.XP

lemma encNat_eq (m : ℕ) : encNat m = encNatB m := by
  unfold encNat encBits encNatB
  congr 2
  rw [Nat.digits_two_eq_bits, List.map_map]
  conv_rhs => rw [← List.map_id m.bits]
  congr 1; funext b; cases b <;> rfl

lemma encZMod_eq (x : ZMod 2) : encZMod x = cbit (decide (x = 1)) := by
  fin_cases x <;> rfl

def bitsOf {m : ℕ} (v : Vec m) : List Bool := (List.ofFn v).map (fun x => decide (x = 1))

lemma encVec_eq {m : ℕ} (v : Vec m) : encVec v = vecB m (bitsOf v) := by
  unfold encVec encList vecB bitsOf
  rw [List.length_ofFn, encNat_eq, List.flatMap_map]
  congr 1
  exact List.flatMap_congr (fun x _ => encZMod_eq x)

lemma encRat_eq (q : ℚ) : AbelianCayleyHDX.encRat q = encRatB q := by
  unfold AbelianCayleyHDX.encRat encRatB; rw [encNat_eq, encNat_eq]

lemma value_pow (m : ℕ) : Word.value (List.replicate m false ++ [true]) = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, List.cons_append, Word.value, ih]; simp [pow_succ]; ring


end AbelianCayleyHDX.XE


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RSListDecodingCapacity.AllRates
open ReplParity (Vec)

namespace AbelianCayleyHDX.XR

open AbelianCayleyHDX.XK AbelianCayleyHDX.XP

/-! ### The post-processor -/

def parseRows (t : List ℕ) : List (List Bool) :=
  (rg t (t.getD 0 0)).map (fun r => (rg t (t.getD 1 0)).map (fun c =>
    decide (t.getD (3 + r * (t.getD 1 0 + 1) + 1 + c) 0 = 1)))

def colB (B : List (List Bool)) (i : ℕ) : List Bool := B.map (fun b => b.getD i false)

def fstIdx (rb : List Bool) : ℕ := rb.findIdx (fun b => b)

def sndIdx (rb : List Bool) : ℕ :=
  ((List.range rb.length).filter (fun c => rb.getD c false && decide (c ≠ fstIdx rb))).getD 0 0

def repB (B : List (List Bool)) (rb : List Bool) : List (List Bool) :=
  [B.map (fun _ => false), colB B (fstIdx rb), xorv (colB B (fstIdx rb)) (colB B (sndIdx rb))]

def postT (t : List ℕ) : List Bool :=
  encNatB (basisB' (rg t (t.getD 1 0)) (parseRows t)).length ++
    (encNatB ((rg t (t.getD 1 0)).map (colB (basisB' (rg t (t.getD 1 0)) (parseRows t)))).length ++
      ((rg t (t.getD 1 0)).map (colB (basisB' (rg t (t.getD 1 0)) (parseRows t)))).flatMap
        (vecB (basisB' (rg t (t.getD 1 0)) (parseRows t)).length)) ++
    (encNatB ((parseRows t).map (repB (basisB' (rg t (t.getD 1 0)) (parseRows t)))).length ++
      ((parseRows t).map (repB (basisB' (rg t (t.getD 1 0)) (parseRows t)))).flatMap (fun r =>
        encNatB r.length ++ r.flatMap (vecB (basisB' (rg t (t.getD 1 0)) (parseRows t)).length) ++
          encRatB (1 / ((t.getD 0 0 : ℚ) * (Word.value
            ((basisB' (rg t (t.getD 1 0)) (parseRows t)).map (fun _ => false) ++ [true]) : ℚ)))))

def postB (w : List Bool) : List Bool := postT (decTokens w)

section PolyR
variable {γ : Type} [Coding γ] [Inhabited γ]

@[fun_prop] theorem nat_ne_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x ≠ g x)) := by
  have : (fun x => decide (f x ≠ g x)) = fun x => !(decide (f x = g x)) := by
    funext x; simp
  rw [this]; fun_prop

@[fun_prop] theorem decTokens_comp {f : γ → List Bool} (hf : Poly f) :
    Poly (fun x => decTokens (f x)) := Poly.comp poly_decTokens hf

@[fun_prop] theorem basisB'_comp {f : γ → List ℕ} {g : γ → List (List Bool)} (hf : Poly f)
    (hg : Poly g) : Poly (fun x => basisB' (f x) (g x)) :=
  Poly.comp (f := fun x : List ℕ × List (List Bool) => basisB' x.1 x.2) poly_basisB' (Poly.pair hf hg)

@[fun_prop] theorem rg_comp {f : γ → List ℕ} {g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => rg (f x) (g x)) := by unfold rg; fun_prop

@[fun_prop] theorem parseRows_comp {f : γ → List ℕ} (hf : Poly f) :
    Poly (fun x => parseRows (f x)) := by unfold parseRows; fun_prop

@[fun_prop] theorem colB_comp {f : γ → List (List Bool)} {g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => colB (f x) (g x)) := by unfold colB; fun_prop

@[fun_prop] theorem fstIdx_comp {f : γ → List Bool} (hf : Poly f) : Poly (fun x => fstIdx (f x)) := by
  unfold fstIdx; fun_prop

@[fun_prop] theorem sndIdx_comp {f : γ → List Bool} (hf : Poly f) : Poly (fun x => sndIdx (f x)) := by
  unfold sndIdx; fun_prop

@[fun_prop] theorem repB_comp {f : γ → List (List Bool)} {g : γ → List Bool} (hf : Poly f)
    (hg : Poly g) : Poly (fun x => repB (f x) (g x)) := by unfold repB; fun_prop

end PolyR

theorem poly_postB : Poly (fun w : List Bool => postB w) := by
  unfold postB postT; fun_prop

end AbelianCayleyHDX.XR


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RSListDecodingCapacity.AllRates
open ReplParity (Vec)
open Matrix

namespace AbelianCayleyHDX.XR

open AbelianCayleyHDX.XK AbelianCayleyHDX.XP

variable {R M : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2))

/-! ### Rows -/

lemma exists_supp {ρ : ℕ} (hH : IsGoodRelationMatrix H ρ) (r : Fin R) : ∃ c, H r c ≠ 0 := by
  have h := hH.2.1 r
  unfold rowWeight at h
  obtain ⟨c, hc⟩ := Finset.card_pos.1 (by rw [h]; norm_num : 0 < (Finset.univ.filter fun c => H r c ≠ 0).card)
  exact ⟨c, (Finset.mem_filter.1 hc).2⟩

lemma fst_spec {ρ : ℕ} (hH : IsGoodRelationMatrix H ρ) (r : Fin R) :
    ∃ h : fstIdx (bitsOfRow (H r)) < M, H r ⟨_, h⟩ = 1 := by
  obtain ⟨c, hc⟩ := exists_supp H hH r
  have hc1 : H r c = 1 := (z2_cases _).resolve_left hc
  have hmem : (bitsOfRow (H r))[c.1]'(by simp [bitsOfRow]) = true := by
    have := getD_bitsOfRow (H r) c
    rw [List.getD_eq_getElem _ _ (by simp [bitsOfRow])] at this
    rw [this, hc1]; rfl
  have hlt : fstIdx (bitsOfRow (H r)) < (bitsOfRow (H r)).length :=
    List.findIdx_lt_length_of_exists ⟨_, List.getElem_mem _, hmem⟩
  rw [bitsOfRow_length] at hlt
  refine ⟨hlt, ?_⟩
  have h2 := List.findIdx_getElem (p := fun b => b) (w := by rw [bitsOfRow_length]; exact hlt)
  have h3 := getD_bitsOfRow (H r) ⟨_, hlt⟩
  rw [List.getD_eq_getElem _ _ (by rw [bitsOfRow_length]; exact hlt)] at h3
  unfold fstIdx at h3
  rw [h3] at h2
  simp only [decide_eq_true_eq] at h2
  exact h2

lemma snd_spec {ρ : ℕ} (hH : IsGoodRelationMatrix H ρ) (r : Fin R) :
    ∃ h : sndIdx (bitsOfRow (H r)) < M, sndIdx (bitsOfRow (H r)) ≠ fstIdx (bitsOfRow (H r)) ∧
      H r ⟨_, h⟩ = 1 := by
  classical
  set rb := bitsOfRow (H r)
  set a := fstIdx rb
  -- a second support column
  obtain ⟨c, hc, hca⟩ : ∃ c : Fin M, H r c ≠ 0 ∧ c.1 ≠ a := by
    by_contra hall; push Not at hall
    have h := hH.2.1 r
    unfold rowWeight at h
    have : (Finset.univ.filter fun c => H r c ≠ 0) ⊆ {⟨a, (fst_spec H hH r).1⟩} := by
      intro c hc'; rw [Finset.mem_filter] at hc'
      rw [Finset.mem_singleton]; exact Fin.ext (hall c hc'.2)
    have := Finset.card_le_card this
    rw [h, Finset.card_singleton] at this; omega
  set L := (List.range rb.length).filter (fun c => rb.getD c false && decide (c ≠ a))
  have hcL : c.1 ∈ L := by
    rw [List.mem_filter, List.mem_range]
    refine ⟨by simp [rb, bitsOfRow], ?_⟩
    rw [getD_bitsOfRow, (z2_cases _).resolve_left hc]; simpa using hca
  have hne : L ≠ [] := List.ne_nil_of_mem hcL
  have hhead : sndIdx rb ∈ L := by
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
    have e : sndIdx rb = L.getD 0 0 := rfl
    rw [e, hx]; simp
  rw [List.mem_filter, List.mem_range] at hhead
  obtain ⟨hlt, hb⟩ := hhead
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  rw [show rb.length = M from bitsOfRow_length _] at hlt
  refine ⟨hlt, hb.2, ?_⟩
  have h1 := hb.1
  rw [show sndIdx rb = (⟨_, hlt⟩ : Fin M).1 from rfl, getD_bitsOfRow] at h1
  simpa using h1

/-! ### The data -/

variable {ρ : ℕ} (hH : IsGoodRelationMatrix H ρ)

noncomputable def aF (r : Fin R) : Fin M := ⟨_, (fst_spec H hH r).1⟩
noncomputable def bF (r : Fin R) : Fin M := ⟨_, (snd_spec H hH r).1⟩

lemma aF_spec (r : Fin R) : H r (aF H hH r) = 1 := (fst_spec H hH r).2
lemma bF_spec (r : Fin R) : H r (bF H hH r) = 1 := (snd_spec H hH r).2.2
lemma aF_ne_bF (r : Fin R) : aF H hH r ≠ bF H hH r := fun h =>
  (snd_spec H hH r).2.1 (congrArg Fin.val h).symm

noncomputable abbrev nK : ℕ := Module.finrank (ZMod 2) (AbelianCayleyHDX.kerF2 H)

noncomputable def gensL : List (Vec (nK H)) := List.ofFn (fun i : Fin M => phi H (Pi.single i 1))

noncomputable def repL (r : Fin R) : List (Vec (nK H)) :=
  [0, phi H (Pi.single (aF H hH r) 1), phi H (Pi.single (aF H hH r) 1) + phi H (Pi.single (bF H hH r) 1)]

noncomputable def repsL : List (List (Vec (nK H))) := List.ofFn (repL H hH)

/-! ### Bits of `φ` -/

def rowsOf : List (List Bool) := (List.ofFn H).map bitsOfRow

lemma rowsOf_spec : (∀ r ∈ rowsOf H, r.length = M) ∧ (rowsOf H).map (toV M) = List.ofFn H := by
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [rowsOf, List.mem_map] at hr; obtain ⟨row, -, rfl⟩ := hr; exact bitsOfRow_length _
  · rw [rowsOf, List.map_map]
    conv_rhs => rw [← List.map_id (List.ofFn H)]
    apply List.map_congr_left; intro row _; exact toV_bitsOfRow row

lemma basis_spec' : (basisB M (rowsOf H)).map (toV M) = basisList H ∧
    ∀ k ∈ basisB M (rowsOf H), k.length = M :=
  basisB_spec H _ (rowsOf_spec H).1 (rowsOf_spec H).2

lemma basisB_length : (basisB M (rowsOf H)).length = nK H := by
  rw [← List.length_map (f := toV M), (basis_spec' H).1, (basisList_spec H).2.1]

lemma ofFn_cast {α β : Type*} (L : List α) {n : ℕ} (h : L.length = n) (g : α → β) :
    List.ofFn (fun ℓ : Fin n => g (L.get (ℓ.cast h.symm))) = L.map g := by
  apply List.ext_getElem (by simp [h])
  intro m h1 h2; simp

lemma phi_apply (v : Fin M → ZMod 2) (ℓ : Fin (nK H)) :
    phi H v ℓ = (basisList H)[ℓ.1]'(by rw [(basisList_spec H).2.1]; exact ℓ.2) ⬝ᵥ v := rfl

lemma bitsOf_phi (v : Fin M → ZMod 2) :
    AbelianCayleyHDX.XE.bitsOf (phi H v) =
      (basisB M (rowsOf H)).map (fun b => decide (toV M b ⬝ᵥ v = 1)) := by
  have hb := (basis_spec' H).1
  apply List.ext_getElem (by simp [AbelianCayleyHDX.XE.bitsOf, basisB_length])
  intro m h1 h2
  simp only [AbelianCayleyHDX.XE.bitsOf, List.getElem_map, List.getElem_ofFn]
  rw [phi_apply]
  congr 2
  have := List.getElem_of_eq hb.symm (i := m) (by rw [(basisList_spec H).2.1]; simpa [AbelianCayleyHDX.XE.bitsOf] using h1)
  rw [this, List.getElem_map]

lemma toV_dot_single (b : List Bool) (i : Fin M) :
    decide (toV M b ⬝ᵥ Pi.single i 1 = 1) = b.getD i false := by
  rw [dotProduct_single, mul_one]; simp only [toV]
  rcases Bool.eq_false_or_eq_true (b.getD i false) with h | h <;> simp [h]

lemma bitsOf_phi_single (i : Fin M) :
    AbelianCayleyHDX.XE.bitsOf (phi H (Pi.single i 1)) = colB (basisB M (rowsOf H)) i := by
  rw [bitsOf_phi, colB]
  apply List.map_congr_left; intro b _; exact toV_dot_single b i

lemma bitsOf_phi_zero :
    AbelianCayleyHDX.XE.bitsOf (phi H 0) = (basisB M (rowsOf H)).map (fun _ => false) := by
  rw [bitsOf_phi]; apply List.map_congr_left; intro b _; simp

lemma xorv_map {α : Type*} (L : List α) (f g : α → Bool) :
    xorv (L.map f) (L.map g) = L.map (fun x => xor (f x) (g x)) := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.map_cons, xorv, List.zip_cons_cons] at ih ⊢; rw [ih]

lemma bitsOf_phi_pair (i j : Fin M) :
    AbelianCayleyHDX.XE.bitsOf (phi H (Pi.single i 1) + phi H (Pi.single j 1)) =
      xorv (colB (basisB M (rowsOf H)) i) (colB (basisB M (rowsOf H)) j) := by
  rw [← map_add, bitsOf_phi, colB, colB, xorv_map]
  apply List.map_congr_left; intro b _
  rw [dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one]
  simp only [toV]
  have key : ∀ x y : Bool, decide (((if x = true then (1 : ZMod 2) else 0) +
      if y = true then 1 else 0) = 1) = xor x y := by decide
  exact key _ _

end AbelianCayleyHDX.XR

open ReplParity (Vec)

namespace AbelianCayleyHDX.RelCx

/-! ### Characteristic two -/

lemma z2_ne_zero_iff (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by revert a; decide

lemma vadd_self {n : ℕ} (x : Vec n) : x + x = 0 := by
  ext k; simp only [Pi.add_apply, Pi.zero_apply]; grind

lemma vadd_cancel_left {n : ℕ} (x y : Vec n) : x + (x + y) = y := by
  rw [← add_assoc, vadd_self, zero_add]

lemma vadd_eq_iff {n : ℕ} (x y z : Vec n) : x + y = z ↔ y = x + z := by
  constructor
  · rintro rfl; rw [vadd_cancel_left]
  · rintro rfl; rw [vadd_cancel_left]

lemma vadd_eq_zero_iff {n : ℕ} (x y : Vec n) : x + y = 0 ↔ x = y := by
  rw [vadd_eq_iff, add_zero, eq_comm]

lemma z2_add_eq_zero_iff (x y : ZMod 2) : x + y = 0 ↔ x = y := by
  revert x y; decide

/-! ### The relation matrix -/

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {n : ℕ}
  (H : Matrix ι κ (ZMod 2)) (φ : (κ → ZMod 2) →ₗ[ZMod 2] Vec n)

/-- The support of a row. -/
def supp (r : ι) : Finset κ := Finset.univ.filter fun i => H r i ≠ 0

/-- The generator `s_i = φ(e_i)`. -/
def s (i : κ) : Vec n := φ (Pi.single i 1)

lemma mem_supp {H : Matrix ι κ (ZMod 2)} {r : ι} {i : κ} : i ∈ supp H r ↔ H r i ≠ 0 := by
  simp [supp]

lemma eq_sum_single (v : κ → ZMod 2) :
    v = ∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), Pi.single i 1 := by
  ext k
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  rw [Finset.sum_ite_eq]
  by_cases hk : v k = 0
  · simp [hk]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_pos hk]
    exact (z2_ne_zero_iff _).1 hk

lemma map_eq_sum (v : κ → ZMod 2) :
    φ v = ∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), s φ i := by
  conv_lhs => rw [eq_sum_single v]
  rw [map_sum]; rfl

variable {H φ}
variable {ρ : ℕ} (hH : IsGoodRelationMatrix H ρ) (hker : LinearMap.ker φ = rowspan H)
include hH hker

lemma weight_ge_three (v : κ → ZMod 2) (hv : φ v = 0) (hne : v ≠ 0) :
    3 ≤ (Finset.univ.filter fun i => v i ≠ 0).card := by
  have : v ∈ rowspan H := by rw [← hker]; exact hv
  exact hH.2.2.2.2 v this hne

lemma s_ne_zero (i : κ) : s φ i ≠ 0 := by
  intro h
  have := weight_ge_three hH hker (Pi.single i 1) h (by
    intro h'; have := congrFun h' i; simp at this)
  have h1 : (Finset.univ.filter fun j => (Pi.single i (1 : ZMod 2) : κ → ZMod 2) j ≠ 0) = {i} := by
    ext j; by_cases hj : j = i <;> simp [Pi.single_apply, hj]
  rw [h1] at this; simp at this

lemma s_inj : Function.Injective (s φ) := by
  intro i j hij
  by_contra hne
  have h0 : φ (Pi.single i 1 + Pi.single j 1) = 0 := by
    rw [map_add]; change s φ i + s φ j = 0; rw [hij, vadd_self]
  have := weight_ge_three hH hker _ h0 (by
    intro h'; have := congrFun h' i; simp [Pi.single_apply, hne] at this)
  have h1 : (Finset.univ.filter fun k =>
      (Pi.single i (1 : ZMod 2) + Pi.single j 1 : κ → ZMod 2) k ≠ 0) ⊆ {i, j} := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    by_contra hk'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
    apply hk; simp [Pi.single_apply, hk'.1, hk'.2]
  have := (Finset.card_le_card h1).trans (Finset.card_le_two)
  omega

lemma supp_card (r : ι) : (supp H r).card = 3 := hH.2.1 r

lemma row_sum (r : ι) : ∑ i ∈ supp H r, s φ i = 0 := by
  have h1 : φ (H r) = 0 := by
    have : H r ∈ rowspan H := Submodule.subset_span ⟨r, rfl⟩
    rw [← hker] at this; exact this
  rw [map_eq_sum] at h1
  exact h1

/-- Distinct rows share at most one column. -/
lemma rows_eq {r r' : ι} {i j : κ} (hij : i ≠ j) (hi : i ∈ supp H r) (hj : j ∈ supp H r)
    (hi' : i ∈ supp H r') (hj' : j ∈ supp H r') : r = r' := by
  by_contra hne
  have hv : H r + H r' ≠ 0 := by
    intro h
    apply hne; apply hH.1
    ext c; have := congrFun h c
    simp only [Pi.add_apply, Pi.zero_apply] at this
    exact (z2_add_eq_zero_iff _ _).1 this
  have hrow : ∀ r'' : ι, H r'' ∈ rowspan H := fun r'' => Submodule.subset_span ⟨r'', rfl⟩
  have hmem : H r + H r' ∈ rowspan H := Submodule.add_mem _ (hrow r) (hrow r')
  have h3 := hH.2.2.2.2 _ hmem hv
  rw [mem_supp] at hi hj hi' hj'
  -- the support of the sum is contained in (supp r ∪ supp r') \ {i, j}
  have hsub : (Finset.univ.filter fun c => (H r + H r') c ≠ 0) ⊆
      (supp H r ∪ supp H r') \ {i, j} := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply] at hc
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      not_or, mem_supp]
    refine ⟨?_, ?_, ?_⟩
    · by_contra h; push Not at h; rw [h.1, h.2] at hc; simp at hc
    · rintro rfl
      rw [(z2_ne_zero_iff _).1 hi, (z2_ne_zero_iff _).1 hi'] at hc; exact hc (by decide)
    · rintro rfl
      rw [(z2_ne_zero_iff _).1 hj, (z2_ne_zero_iff _).1 hj'] at hc; exact hc (by decide)
  have hcard := Finset.card_le_card hsub
  have hij2 : ({i, j} : Finset κ) ⊆ supp H r ∪ supp H r' := by
    intro c hc; simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact Finset.mem_union_left _ (mem_supp.2 hi)
    · exact Finset.mem_union_left _ (mem_supp.2 hj)
  rw [Finset.card_sdiff_of_subset hij2, Finset.card_pair hij] at hcard
  have hu := Finset.card_union_add_card_inter (supp H r) (supp H r')
  have hint : ({i, j} : Finset κ) ⊆ supp H r ∩ supp H r' := by
    intro c hc; simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact Finset.mem_inter.2 ⟨mem_supp.2 hi, mem_supp.2 hi'⟩
    · exact Finset.mem_inter.2 ⟨mem_supp.2 hj, mem_supp.2 hj'⟩
  have hi2 := Finset.card_le_card hint
  rw [Finset.card_pair hij] at hi2
  rw [supp_card hH hker, supp_card hH hker] at hu
  omega

lemma inter_card_le_one {r r' : ι} (hne : r ≠ r') :
    (supp H r ∩ supp H r').card ≤ 1 := by
  by_contra h; push Not at h
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 h
  rw [Finset.mem_inter] at hi hj
  exact hne (rows_eq hH hker hij hi.1 hj.1 hi.2 hj.2)

/-- The third column of a row. -/
lemma third {r : ι} {i j : κ} (hij : i ≠ j) (hi : i ∈ supp H r) (hj : j ∈ supp H r) :
    ∃ k ∈ supp H r, k ≠ i ∧ k ≠ j ∧ supp H r = {i, j, k} ∧ s φ i + s φ j = s φ k := by
  obtain ⟨a, b, c, hab, hac, hbc, he⟩ := Finset.card_eq_three.1 (supp_card hH hker r)
  have hsum := row_sum hH hker r
  rw [he, Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc] at hsum
  rw [he] at hi hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
  all_goals first | exact absurd rfl hij | skip
  · refine ⟨c, by simp [he], hac.symm, hbc.symm, he, ?_⟩
    ext k; have := congrFun hsum k; simp only [Pi.add_apply, Pi.zero_apply] at *; grind
  · refine ⟨b, by simp [he], hab.symm, hbc, by rw [he]; ext; simp; tauto, ?_⟩
    ext k; have := congrFun hsum k; simp only [Pi.add_apply, Pi.zero_apply] at *; grind
  · refine ⟨c, by simp [he], hbc.symm, hac.symm, by rw [he]; ext; simp; tauto, ?_⟩
    ext k; have := congrFun hsum k; simp only [Pi.add_apply, Pi.zero_apply] at *; grind
  · refine ⟨a, by simp [he], hab, hac, by rw [he]; ext; simp; tauto, ?_⟩
    ext k; have := congrFun hsum k; simp only [Pi.add_apply, Pi.zero_apply] at *; grind
  · refine ⟨b, by simp [he], hbc, hab.symm, by rw [he]; ext; simp; tauto, ?_⟩
    ext k; have := congrFun hsum k; simp only [Pi.add_apply, Pi.zero_apply] at *; grind
  · refine ⟨a, by simp [he], hac, hab, by rw [he]; ext; simp; tauto, ?_⟩
    ext k; have := congrFun hsum k; simp only [Pi.add_apply, Pi.zero_apply] at *; grind

omit hH hker in
lemma mem_T {τ : Finset (Vec n)} :
    τ ∈ relationComplex H φ ↔ ∃ (r : ι) (g : Vec n) (i j : κ), i ≠ j ∧ i ∈ supp H r ∧
      j ∈ supp H r ∧ τ = {g, g + s φ i, g + s φ i + s φ j} := by
  simp only [relationComplex, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.exists, mem_supp, s]
  constructor
  · rintro ⟨r, g, i, j, ⟨hij, hi, hj⟩, rfl⟩; exact ⟨r, g, i, j, hij, hi, hj, rfl⟩
  · rintro ⟨r, g, i, j, hij, hi, hj, rfl⟩; exact ⟨r, g, i, j, ⟨hij, hi, hj⟩, rfl⟩

/-- Pairwise sums of a triangle are generators of its row. -/
lemma pair_sum {r : ι} {g : Vec n} {i j : κ} (hij : i ≠ j) (hi : i ∈ supp H r)
    (hj : j ∈ supp H r) {x y : Vec n}
    (hx : x ∈ ({g, g + s φ i, g + s φ i + s φ j} : Finset (Vec n)))
    (hy : y ∈ ({g, g + s φ i, g + s φ i + s φ j} : Finset (Vec n))) (hxy : x ≠ y) :
    ∃ m ∈ supp H r, x + y = s φ m := by
  obtain ⟨k, hk, -, -, -, hijk⟩ := third hH hker hij hi hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals first | exact absurd rfl hxy | skip
  · refine ⟨i, hi, ?_⟩; ext t; simp only [Pi.add_apply]; grind
  · refine ⟨k, hk, ?_⟩; ext t; have := congrFun hijk t; simp only [Pi.add_apply] at *; grind
  · refine ⟨i, hi, ?_⟩; ext t; simp only [Pi.add_apply]; grind
  · refine ⟨j, hj, ?_⟩; ext t; simp only [Pi.add_apply]; grind
  · refine ⟨k, hk, ?_⟩; ext t; have := congrFun hijk t; simp only [Pi.add_apply] at *; grind
  · refine ⟨j, hj, ?_⟩; ext t; simp only [Pi.add_apply]; grind

lemma card_tri {g : Vec n} {i j : κ} (hij : i ≠ j) :
    ({g, g + s φ i, g + s φ i + s φ j} : Finset (Vec n)).card = 3 := by
  have hi := s_ne_zero hH hker i
  have hj := s_ne_zero hH hker j
  have hij' : s φ i ≠ s φ j := fun h => hij (s_inj hH hker h)
  rw [Finset.card_eq_three]
  refine ⟨g, g + s φ i, g + s φ i + s φ j, ?_, ?_, ?_, rfl⟩
  · intro h; apply hi; ext t; have := congrFun h t
    simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; grind
  · intro h; apply hij'; ext t; have := congrFun h t
    simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; grind
  · intro h; apply hj; ext t; have := congrFun h t
    simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; grind

lemma card_of_mem {τ : Finset (Vec n)} (hτ : τ ∈ relationComplex H φ) : τ.card = 3 := by
  obtain ⟨r, g, i, j, hij, -, -, rfl⟩ := mem_T.1 hτ
  exact card_tri hH hker hij

/-- `{g, g + s_i, g + s_j}` is a triangle when `i ≠ j` share a row. -/
lemma tri_mem' {r : ι} (g : Vec n) {i j : κ} (hij : i ≠ j) (hi : i ∈ supp H r)
    (hj : j ∈ supp H r) : ({g, g + s φ i, g + s φ j} : Finset (Vec n)) ∈ relationComplex H φ := by
  obtain ⟨k, hk, hki, hkj, -, hijk⟩ := third hH hker hij hi hj
  rw [mem_T]
  refine ⟨r, g, i, k, hki.symm, hi, hk, ?_⟩
  have : s φ i + s φ k = s φ j := by
    rw [← hijk, vadd_cancel_left]
  rw [add_assoc g, this]

omit hH hker in
/-- Triangle membership is translation invariant. -/
lemma image_add_mem {τ : Finset (Vec n)} (hτ : τ ∈ relationComplex H φ) (x : Vec n) :
    τ.image (· + x) ∈ relationComplex H φ := by
  obtain ⟨r, g, i, j, hij, hi, hj, rfl⟩ := mem_T.1 hτ
  rw [mem_T]
  refine ⟨r, g + x, i, j, hij, hi, hj, ?_⟩
  simp only [Finset.image_insert, Finset.image_singleton]
  congr 1
  · congr 1
    · abel
    · congr 1; abel

/-- The row of a triangle. -/
lemma exists_row_of_mem {τ : Finset (Vec n)} (hτ : τ ∈ relationComplex H φ) :
    ∃ r : ι, ∀ x ∈ τ, ∀ y ∈ τ, x ≠ y → ∃ m ∈ supp H r, x + y = s φ m := by
  obtain ⟨r, g, i, j, hij, hi, hj, rfl⟩ := mem_T.1 hτ
  exact ⟨r, fun x hx y hy hxy => pair_sum hH hker hij hi hj hx hy hxy⟩

end

/-- `j` is a neighbour of `i`: they are distinct and share a row. -/
def IsNbr {ι κ : Type*} [Fintype κ] (H : Matrix ι κ (ZMod 2)) (i j : κ) : Prop :=
  i ≠ j ∧ ∃ r : ι, i ∈ Finset.univ.filter (fun c => H r c ≠ 0) ∧
    j ∈ Finset.univ.filter (fun c => H r c ≠ 0)

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {n : ℕ}
  {H : Matrix ι κ (ZMod 2)} {φ : (κ → ZMod 2) →ₗ[ZMod 2] Vec n}
  {ρ : ℕ} (hH : IsGoodRelationMatrix H ρ) (hker : LinearMap.ker φ = rowspan H)
include hH hker

lemma isNbr_iff {i j : κ} : IsNbr H i j ↔ i ≠ j ∧ ∃ r : ι, i ∈ supp H r ∧ j ∈ supp H r :=
  Iff.rfl

lemma rows_through_card (i : κ) :
    (Finset.univ.filter fun r : ι => i ∈ supp H r).card = ρ := by
  rw [← hH.2.2.2.1 i]; simp [mem_supp, colWeight]

open Classical in
lemma card_nbrs (i : κ) : (Finset.univ.filter fun j => IsNbr H i j).card = 2 * ρ := by
  have heq : (Finset.univ.filter fun j => IsNbr H i j) =
      (Finset.univ.filter fun r : ι => i ∈ supp H r).biUnion fun r => (supp H r).erase i := by
    ext j
    simp only [isNbr_iff hH hker, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_erase]
    constructor
    · rintro ⟨hij, r, hi, hj⟩; exact ⟨r, hi, Ne.symm hij, hj⟩
    · rintro ⟨r, hi, hji, hj⟩; exact ⟨Ne.symm hji, r, hi, hj⟩
  rw [heq, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (g := fun _ => 2)]
    · simp [rows_through_card hH hker, mul_comm]
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      rw [Finset.card_erase_of_mem hr, supp_card hH hker]
  · intro r hr r' hr' hne
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hr hr'
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro j hj hj'
    rw [Finset.mem_erase] at hj hj'
    exact hne (rows_eq hH hker (Ne.symm hj.1) hr hj.2 hr' hj'.2)

/-- Triangles through `0`. -/
lemma zero_tri_iff (u w : Vec n) :
    ({0, u, w} : Finset (Vec n)) ∈ relationComplex H φ ↔
      ∃ i j, u = s φ i ∧ w = s φ j ∧ IsNbr H i j := by
  constructor
  · intro hτ
    have hc := card_of_mem hH hker hτ
    have h0u : (0 : Vec n) ≠ u := by
      intro h; subst h
      have := Finset.card_le_two (a := (0 : Vec n)) (b := w)
      simp only [Finset.insert_eq_of_mem, Finset.mem_insert, true_or] at hc; omega
    have h0w : (0 : Vec n) ≠ w := by
      intro h; subst h
      have := Finset.card_le_two (a := (0 : Vec n)) (b := u)
      have e : ({0, u, 0} : Finset (Vec n)) = {0, u} := by ext; simp; tauto
      rw [e] at hc; omega
    have huw : u ≠ w := by
      intro h; subst h
      have := Finset.card_le_two (a := (0 : Vec n)) (b := u)
      simp at hc; omega
    obtain ⟨r, hr⟩ := exists_row_of_mem hH hker hτ
    obtain ⟨i, hi, hiu⟩ := hr 0 (by simp) u (by simp) h0u
    obtain ⟨j, hj, hjw⟩ := hr 0 (by simp) w (by simp) h0w
    rw [zero_add] at hiu hjw
    refine ⟨i, j, hiu, hjw, ?_, r, hi, hj⟩
    rintro rfl; exact huw (hiu.trans hjw.symm)
  · rintro ⟨i, j, rfl, rfl, hij, r, hi, hj⟩
    have := tri_mem' hH hker (0 : Vec n) hij hi hj
    simpa using this

lemma exists_row_through (m : κ) : ∃ r : ι, ∃ j, m ∈ supp H r ∧ j ∈ supp H r ∧ m ≠ j := by
  have hpos : 0 < (Finset.univ.filter fun r : ι => m ∈ supp H r).card := by
    rw [rows_through_card hH hker]; exact hH.2.2.1
  obtain ⟨r, hr⟩ := Finset.card_pos.1 hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
  have : 1 < (supp H r).card := by rw [supp_card hH hker]; norm_num
  obtain ⟨j, hj, hjm⟩ := Finset.exists_mem_ne this m
  exact ⟨r, j, hr, hj, Ne.symm hjm⟩

lemma linkVerts_zero :
    linkVerts (relationComplex H φ) 0 = Finset.univ.image (s φ) := by
  ext u
  simp only [linkVerts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hu0, τ, hτ, h0, hu⟩
    obtain ⟨r, hr⟩ := exists_row_of_mem hH hker hτ
    obtain ⟨m, -, hm⟩ := hr 0 h0 u hu (Ne.symm hu0)
    exact ⟨m, by rw [zero_add] at hm; exact hm.symm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨s_ne_zero hH hker m, ?_⟩
    obtain ⟨r, j, hm, hj, hmj⟩ := exists_row_through hH hker m
    exact ⟨_, tri_mem' hH hker (0 : Vec n) hmj hm hj, by simp, by simp⟩

open Classical in
lemma linkWeight_zero (i j : κ) :
    linkWeight (relationComplex H φ) 0 (s φ i) (s φ j) = if IsNbr H i j then 1 else 0 := by
  unfold linkWeight
  by_cases h : IsNbr H i j
  · rw [if_pos h, if_pos ((zero_tri_iff hH hker _ _).2 ⟨i, j, rfl, rfl, h⟩)]
  · rw [if_neg h, if_neg]
    rw [zero_tri_iff hH hker]
    rintro ⟨i', j', hi, hj, hn⟩
    rw [s_inj hH hker hi, s_inj hH hker hj] at h; exact h hn

open Classical in
lemma gram_entry (i j : κ) :
    ((Htilde H).transpose * Htilde H - (ρ : ℝ) • (1 : Matrix κ κ ℝ)) i j =
      if IsNbr H i j then 1 else 0 := by
  have hval : ∀ r c, ((H r c).val : ℝ) = if c ∈ supp H r then 1 else 0 := by
    intro r c
    by_cases h : H r c = 0
    · simp [h, mem_supp]
    · rw [if_pos (mem_supp.2 h), (z2_ne_zero_iff _).1 h]; simp [ZMod.val_one]
  have hsum : ∀ i j : κ, ((Htilde H).transpose * Htilde H) i j =
      ((Finset.univ.filter fun r : ι => i ∈ supp H r ∧ j ∈ supp H r).card : ℝ) := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Htilde, Matrix.of_apply, hval]
    rw [Finset.card_filter]; push_cast
    refine Finset.sum_congr rfl (fun r _ => ?_)
    by_cases h1 : i ∈ supp H r <;> by_cases h2 : j ∈ supp H r <;> simp [h1, h2]
  rw [Matrix.sub_apply, hsum, Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp only [and_self, if_true, smul_eq_mul, mul_one, rows_through_card hH hker]
    rw [if_neg (fun h => h.1 rfl)]; ring
  · simp only [hij, if_false, smul_eq_mul, mul_zero, sub_zero]
    by_cases hn : IsNbr H i j
    · rw [if_pos hn]
      obtain ⟨-, r, hi, hj⟩ := (isNbr_iff hH hker).1 hn
      have : (Finset.univ.filter fun r : ι => i ∈ supp H r ∧ j ∈ supp H r) = {r} := by
        ext r'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hi', hj'⟩; exact (rows_eq hH hker hij hi hj hi' hj').symm
        · rintro rfl; exact ⟨hi, hj⟩
      rw [this]; simp
    · rw [if_neg hn]
      have : (Finset.univ.filter fun r : ι => i ∈ supp H r ∧ j ∈ supp H r) = ∅ := by
        ext r'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨hi', hj'⟩; exact hn ((isNbr_iff hH hker).2 ⟨hij, r', hi', hj'⟩)
      rw [this]; simp

open Classical in
lemma linkWeight_sum (i : κ) :
    ∑ w ∈ linkVerts (relationComplex H φ) 0, linkWeight (relationComplex H φ) 0 (s φ i) w =
      2 * (ρ : ℝ) := by
  rw [linkVerts_zero hH hker, Finset.sum_image (fun a _ b _ h => s_inj hH hker h)]
  simp only [linkWeight_zero hH hker, Finset.sum_boole]
  rw [card_nbrs hH hker]; push_cast; ring

/-! ### Triangles containing an edge -/

lemma tri_count (x : Vec n) (m : κ) :
    triCount (relationComplex H φ) {x, x + s φ m} = 2 * ρ := by
  classical
  unfold triCount
  rw [← card_nbrs hH hker m]
  symm
  apply Finset.card_bij (fun j _ => ({x, x + s φ m, x + s φ j} : Finset (Vec n)))
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    obtain ⟨hmj, r, hm, hj⟩ := (isNbr_iff hH hker).1 hj
    refine ⟨tri_mem' hH hker x hmj hm hj, ?_⟩
    intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto
  · intro j hj j' hj' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
    have hmem : x + s φ j ∈ ({x, x + s φ m, x + s φ j'} : Finset (Vec n)) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1 | h1
    · exact absurd (left_eq_add.1 h1.symm) (s_ne_zero hH hker j)
    · rw [add_right_inj] at h1; exact absurd (s_inj hH hker h1) (Ne.symm hj.1)
    · rw [add_right_inj] at h1; exact s_inj hH hker h1
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    obtain ⟨hτT, hsub⟩ := hτ
    have hc := card_of_mem hH hker hτT
    have hxm : x ≠ x + s φ m := by
      intro h; apply s_ne_zero hH hker m
      exact left_eq_add.1 h
    have hx : x ∈ τ := hsub (by simp)
    have hxm' : x + s φ m ∈ τ := hsub (by simp)
    obtain ⟨z, hz, hz1, hz2⟩ : ∃ z ∈ τ, z ≠ x ∧ z ≠ x + s φ m := by
      by_contra hcon; push Not at hcon
      have : τ ⊆ {x, x + s φ m} := by
        intro z hz
        by_cases h1 : z = x
        · simp [h1]
        · simp [hcon z hz h1]
      have := Finset.card_le_card this
      rw [Finset.card_pair hxm] at this; omega
    obtain ⟨r, hr⟩ := exists_row_of_mem hH hker hτT
    obtain ⟨j, hj, hjz⟩ := hr x hx z hz (Ne.symm hz1)
    obtain ⟨m', hm', hm'e⟩ := hr x hx _ hxm' hxm
    rw [vadd_cancel_left] at hm'e
    rw [← s_inj hH hker hm'e] at hm'
    have hzj : z = x + s φ j := by rw [← hjz, vadd_cancel_left]
    refine ⟨j, (isNbr_iff hH hker).2 ⟨?_, r, hm', hj⟩, ?_⟩
    · rintro rfl; exact hz2 hzj
    · apply Finset.eq_of_subset_of_card_le
      · intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact hx
        · exact hxm'
        · rw [← hzj]; exact hz
      · rw [hc]
        have hne3 : x + s φ m ≠ x + s φ j := by
          intro h; apply hz2; rw [hzj, ← h]
        rw [Finset.card_insert_of_notMem, Finset.card_pair hne3]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hxm, fun h => hz1 (hzj.trans h.symm)⟩

/-! ### The edges -/

lemma edges_eq :
    edges (relationComplex H φ) = (Finset.univ ×ˢ Finset.univ.image (s φ)).image
      (fun p : Vec n × Vec n => ({p.1, p.1 + p.2} : Finset (Vec n))) := by
  ext e
  simp only [edges, Finset.mem_biUnion, Finset.mem_powersetCard, Finset.mem_image,
    Finset.mem_product, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨τ, hτ, hsub, hcard⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hcard
    obtain ⟨r, hr⟩ := exists_row_of_mem hH hker hτ
    obtain ⟨m, -, hm⟩ := hr a (hsub (by simp)) b (hsub (by simp)) hab
    refine ⟨a, s φ m, ⟨m, rfl⟩, ?_⟩
    rw [← hm, vadd_cancel_left]
  · rintro ⟨x, u, ⟨m, rfl⟩, rfl⟩
    obtain ⟨r, j, hm, hj, hmj⟩ := exists_row_through hH hker m
    refine ⟨_, tri_mem' hH hker x hmj hm hj, ?_, ?_⟩
    · intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto
    · rw [Finset.card_pair]
      intro h; apply s_ne_zero hH hker m
      exact left_eq_add.1 h

/-! ### Dimension -/

omit hH in
lemma dim_eq (hφ : Function.Surjective φ) : n = Module.finrank (ZMod 2) (kerF2 H) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  rw [LinearMap.range_eq_top.2 hφ, finrank_top, Module.finrank_fin_fun, hker] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker H.mulVecLin
  have h3 : Module.finrank (ZMod 2) (LinearMap.range H.mulVecLin) =
      Module.finrank (ZMod 2) (rowspan H) := by
    have := Matrix.rank_eq_finrank_span_row H
    rw [Matrix.rank] at this
    rw [this]; rfl
  rw [h3] at h2
  unfold kerF2
  omega

end

end AbelianCayleyHDX.RelCx


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RSListDecodingCapacity.AllRates
open ReplParity (Vec)
open Matrix

namespace AbelianCayleyHDX.XR

open AbelianCayleyHDX.XK AbelianCayleyHDX.XP

variable {R M : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) {ρ : ℕ} (hH : IsGoodRelationMatrix H ρ)

/-! ### The output string -/

lemma M_le (hH : IsGoodRelationMatrix H ρ) : M ≤ (toks H).length := by
  rw [toks_length]
  rcases Nat.eq_zero_or_pos M with h | h
  · omega
  · have hc := hH.2.2.2.1 ⟨0, h⟩
    have hρ := hH.2.2.1
    unfold colWeight at hc
    obtain ⟨r, -⟩ := Finset.card_pos.1 (by rw [hc]; exact hρ : 0 < (Finset.univ.filter
      fun r => H r ⟨0, h⟩ ≠ 0).card)
    have : 1 ≤ R := by have := r.2; omega
    nlinarith

lemma parse_toks (hH : IsGoodRelationMatrix H ρ) : parseRows (toks H) = rowsOf H := by
  have h0 : (toks H).getD 0 0 = R := by simp [toks]
  have h1 : (toks H).getD 1 0 = M := by simp [toks]
  have hR : R ≤ (toks H).length := by rw [toks_length]; nlinarith
  unfold parseRows
  rw [h0, h1, rg_eq _ hR, rg_eq _ (M_le H hH)]
  have hlen : (List.ofFn H).length = R := List.length_ofFn
  apply List.ext_getElem (by simp only [List.length_map, List.length_range, rowsOf]; exact hlen.symm)
  intro r h1' h2'
  have hr : r < R := by simpa using h1'
  have e : (List.ofFn H)[r]'(by rw [hlen]; exact hr) = H ⟨r, hr⟩ := List.getElem_ofFn _
  simp only [List.getElem_map, List.getElem_range, rowsOf]
  rw [e]
  apply List.ext_getElem (by simp [bitsOfRow])
  intro c h3 h4
  have hc : c < M := by simpa using h3
  simp only [List.getElem_map, List.getElem_range, bitsOfRow, List.getElem_ofFn]
  rw [show 3 + r * (M + 1) + 1 + c = 3 + (⟨r, hr⟩ : Fin R).1 * (M + 1) + 1 + (⟨c, hc⟩ : Fin M).1
    from rfl, toks_entry]
  rcases z2_cases (H ⟨r, hr⟩ ⟨c, hc⟩) with h | h <;> rw [h] <;> rfl

lemma colB_ofFn :
    (gensL H).map AbelianCayleyHDX.XE.bitsOf = (List.range M).map (colB (basisB M (rowsOf H))) := by
  rw [gensL, List.map_ofFn, ← List.map_coe_finRange_eq_range, List.map_map, List.ofFn_eq_map]
  apply List.map_congr_left
  intro i _
  exact bitsOf_phi_single H i

lemma reps_bits :
    (repsL H hH).map (fun r => r.map AbelianCayleyHDX.XE.bitsOf) =
      (rowsOf H).map (repB (basisB M (rowsOf H))) := by
  have hlen : (List.ofFn H).length = R := List.length_ofFn
  apply List.ext_getElem (by simp [repsL, rowsOf, hlen])
  intro r h1 h2
  have hr : r < R := by simpa [repsL] using h1
  have e : (List.ofFn H)[r]'(by rw [hlen]; exact hr) = H ⟨r, hr⟩ := List.getElem_ofFn _
  simp only [List.getElem_map, repsL, List.getElem_ofFn, rowsOf]
  rw [e]
  simp only [repL, List.map_cons, List.map_nil, repB]
  have hz : AbelianCayleyHDX.XE.bitsOf (0 : Vec (nK H)) =
      (basisB M (rowsOf H)).map (fun _ => false) := by
    rw [← map_zero (phi H)]; exact bitsOf_phi_zero H
  rw [hz, bitsOf_phi_single, bitsOf_phi_pair]
  rfl

theorem post_eq :
    postB (encNat R ++ encNat M ++ encList encVec (List.ofFn H)) =
      encNat (nK H) ++ encList encVec (gensL H) ++
        encList (fun r => encList encVec r ++ AbelianCayleyHDX.encRat (1 / ((R * 2 ^ (nK H) : ℕ) : ℚ)))
          (repsL H hH) := by
  have h0 : (toks H).getD 0 0 = R := by simp [toks]
  have h1 : (toks H).getD 1 0 = M := by simp [toks]
  rw [W_eq, postB, decTokens_flatMap]
  unfold postT
  rw [h0, h1, rg_eq _ (M_le H hH), parse_toks H hH, basisB'_range, basisB_length]
  set B := basisB M (rowsOf H)
  have hwt : (Word.value (B.map (fun _ => false) ++ [true]) : ℚ) = (2 ^ nK H : ℕ) := by
    rw [List.map_const', AbelianCayleyHDX.XE.value_pow, basisB_length]
  rw [hwt, ← AbelianCayleyHDX.XE.encNat_eq]
  unfold encList
  congr 1
  · congr 1
    rw [← colB_ofFn, List.length_map, AbelianCayleyHDX.XE.encNat_eq, List.flatMap_map]
    congr 1
    exact (List.flatMap_congr (fun v _ => AbelianCayleyHDX.XE.encVec_eq v)).symm
  · rw [← reps_bits H hH, List.length_map, AbelianCayleyHDX.XE.encNat_eq, List.flatMap_map]
    congr 1
    refine List.flatMap_congr (fun r _ => ?_)
    rw [AbelianCayleyHDX.XE.encNat_eq, List.length_map, List.flatMap_map,
      AbelianCayleyHDX.XE.encRat_eq]
    push_cast
    congr 2
    exact (List.flatMap_congr (fun v _ => AbelianCayleyHDX.XE.encVec_eq v)).symm

end AbelianCayleyHDX.XR


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RSListDecodingCapacity.AllRates
open ReplParity (Vec)
open Matrix

namespace AbelianCayleyHDX.XR

open AbelianCayleyHDX.XK AbelianCayleyHDX.XP AbelianCayleyHDX.RelCx

variable {R M : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) {ρ : ℕ} (hH : IsGoodRelationMatrix H ρ)

/-- The finset of a representative. -/
lemma repL_toFinset (r : Fin R) :
    (repL H hH r).toFinset = ({0, 0 + s (phi H) (aF H hH r),
      0 + s (phi H) (aF H hH r) + s (phi H) (bF H hH r)} : Finset (Vec (nK H))) := by
  ext x; simp [repL, s]

lemma repL_mem (r : Fin R) : (repL H hH r).toFinset ∈ relationComplex H (phi H) := by
  rw [repL_toFinset, mem_T]
  refine ⟨r, 0, aF H hH r, bF H hH r, aF_ne_bF H hH r, ?_, ?_, rfl⟩
  · rw [mem_supp, aF_spec H hH r]; exact one_ne_zero
  · rw [mem_supp, bF_spec H hH r]; exact one_ne_zero

lemma repL_nodup (r : Fin R) : (repL H hH r).Nodup := by
  have hker := (phi_spec H).2
  have h1 := s_ne_zero hH hker (aF H hH r)
  have h2 := s_ne_zero hH hker (bF H hH r)
  have h3 : s (phi H) (aF H hH r) ≠ s (phi H) (bF H hH r) :=
    fun h => aF_ne_bF H hH r (s_inj hH hker h)
  have h4 : s (phi H) (aF H hH r) ≠ s (phi H) (aF H hH r) + s (phi H) (bF H hH r) := by
    intro h
    apply h2
    have := congrArg (s (phi H) (aF H hH r) + ·) h
    rw [← add_assoc, RelCx.vadd_self, zero_add] at this
    exact this.symm
  have h5 : (0 : Vec (nK H)) ≠ s (phi H) (aF H hH r) + s (phi H) (bF H hH r) := by
    intro h; apply h3; rw [← RelCx.vadd_eq_zero_iff]; exact h.symm
  unfold repL
  refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_singleton _⟩⟩
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
    exact ⟨fun h => h1 h.symm, h5⟩
  · simpa [s] using h4

/-- Representatives of different rows are not translates. -/
lemma repL_translate {r r' : Fin R} {x : Vec (nK H)}
    (h : (repL H hH r).toFinset.image (· + x) = (repL H hH r').toFinset) : r = r' := by
  have hO := (AbelianCayleyHDX.triangle_orbits H ρ hH (phi H) (phi_spec H).1 (phi_spec H).2).2.1
  rw [repL_toFinset, repL_toFinset] at h
  refine hO r r' 0 0 x (aF H hH r) (bF H hH r) (aF H hH r') (bF H hH r') (aF_ne_bF H hH r) ?_ ?_
    (aF_ne_bF H hH r') ?_ ?_ ?_
  · rw [aF_spec H hH r]; exact one_ne_zero
  · rw [bF_spec H hH r]; exact one_ne_zero
  · rw [aF_spec H hH r']; exact one_ne_zero
  · rw [bF_spec H hH r']; exact one_ne_zero
  · simpa [s] using h

lemma image_image_add {n : ℕ} (τ : Finset (Vec n)) (x y : Vec n) :
    (τ.image (· + x)).image (· + y) = τ.image (· + (x + y)) := by
  rw [Finset.image_image]; congr 1; funext z; simp [add_assoc]

lemma image_add_zero {n : ℕ} (τ : Finset (Vec n)) : τ.image (· + 0) = τ := by simp

lemma image_add_self {n : ℕ} (τ : Finset (Vec n)) (x : Vec n) :
    (τ.image (· + x)).image (· + x) = τ := by
  rw [image_image_add, RelCx.vadd_self, image_add_zero]

theorem reps_unique {τ : Finset (Vec (nK H))} (hτ : τ ∈ relationComplex H (phi H)) :
    ∃! l, l ∈ repsL H hH ∧ ∃ g : Vec (nK H), τ = l.toFinset.image (· + g) := by
  classical
  have hTO := AbelianCayleyHDX.triangle_orbits H ρ hH (phi H) (phi_spec H).1 (phi_spec H).2
  set T := relationComplex H (phi H)
  set O : Fin R → Finset (Finset (Vec (nK H))) := fun r =>
    (Finset.univ : Finset (Vec (nK H))).image fun g => (repL H hH r).toFinset.image (· + g)
  have hOsub : ∀ r, O r ⊆ T := by
    intro r t ht
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 ht
    exact RelCx.image_add_mem (repL_mem H hH r) g
  have hOcard : ∀ r, (O r).card = 2 ^ nK H := fun r => hTO.1 _ (repL_mem H hH r)
  have hdisj : ∀ r r', r ≠ r' → Disjoint (O r) (O r') := by
    intro r r' hne
    rw [Finset.disjoint_left]
    intro t ht ht'
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨g', -, hg'⟩ := Finset.mem_image.1 ht'
    apply hne
    apply repL_translate H hH (x := g + g')
    rw [← image_image_add, ← hg', image_add_self]
  have hunion : (Finset.univ.biUnion O) = T := by
    apply Finset.eq_of_subset_of_card_le
    · intro t ht; obtain ⟨r, -, hr⟩ := Finset.mem_biUnion.1 ht; exact hOsub r hr
    · rw [hTO.2.2, Finset.card_biUnion (fun r _ r' _ h => hdisj r r' h)]
      simp [hOcard]
  rw [← hunion] at hτ
  obtain ⟨r, -, hr⟩ := Finset.mem_biUnion.1 hτ
  obtain ⟨g, -, hg⟩ := Finset.mem_image.1 hr
  refine ⟨repL H hH r, ⟨List.mem_ofFn.2 ⟨r, rfl⟩, g, hg.symm⟩, ?_⟩
  rintro l ⟨hl, g', hg'⟩
  obtain ⟨r', rfl⟩ := List.mem_ofFn.1 hl
  have := repL_translate H hH (r := r) (r' := r') (x := g + g')
    (by rw [← image_image_add, hg, hg', image_add_self])
  rw [this]

end AbelianCayleyHDX.XR


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RSListDecodingCapacity.AllRates
open ReplParity (Vec)
open Matrix

namespace AbelianCayleyHDX.XR

open AbelianCayleyHDX.XK AbelianCayleyHDX.XP AbelianCayleyHDX.RelCx

/-! ### Size of the intermediate word -/

lemma digits_len_le (x : ℕ) : (Nat.digits 2 x).length ≤ x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · rw [Nat.digits_def' (by norm_num) hx, List.length_cons]
      have := ih (x / 2) (Nat.div_lt_self hx (by norm_num))
      omega

lemma encNat_len (x : ℕ) : (encNat x).length ≤ 2 * x + 2 := by
  unfold encNat encBits
  simp only [List.length_append, List.length_flatMap, List.length_cons, List.length_nil,
    List.length_map]
  rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map]
  have := digits_len_le x
  omega

lemma encZMod_len (c : ZMod 2) : (encZMod c).length ≤ 4 := by
  fin_cases c <;> decide

lemma R_le {R M ρ : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) (hH : IsGoodRelationMatrix H ρ) :
    R ≤ M ^ 3 := by
  classical
  let f : Fin R → Finset (Fin M) := fun r => Finset.univ.filter fun c => H r c ≠ 0
  have hf : Function.Injective f := by
    intro r r' h
    apply hH.1
    funext c
    have := congrArg (c ∈ ·) h
    simp only [f, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    rcases z2_cases (H r c) with h1 | h1 <;> rcases z2_cases (H r' c) with h2 | h2 <;>
      simp_all
  have hmap : ∀ r, f r ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin M)) := by
    intro r; rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ _, hH.2.1 r⟩
  have := Finset.card_le_card_of_injOn (s := Finset.univ) f (fun r _ => hmap r)
    (fun r _ r' _ h => hf h)
  rw [Finset.card_univ, Fintype.card_fin, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin] at this
  exact this.trans (Nat.choose_le_pow M 3)

lemma W_len {R M ρ : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) (hH : IsGoodRelationMatrix H ρ) :
    (encNat R ++ encNat M ++ encList encVec (List.ofFn H)).length ≤ 20 * (M + 1) ^ 4 := by
  have hR := R_le H hH
  have hrow : ∀ row : Fin M → ZMod 2, (encVec row).length ≤ 6 * M + 2 := by
    intro row
    unfold encVec encList
    rw [List.length_append, List.length_ofFn, List.length_flatMap]
    have h1 := encNat_len M
    have h2 : ((List.ofFn row).map fun c => (encZMod c).length).sum ≤ (List.ofFn row).length * 4 :=
      List.sum_le_card_nsmul _ _ (fun x hx => by
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx; exact encZMod_len c) |>.trans (by simp)
    rw [List.length_ofFn] at h2
    omega
  have hl : (List.ofFn H).length = R := List.length_ofFn
  unfold encList
  simp only [List.length_append, List.length_flatMap]
  rw [hl]
  have h3 : ((List.ofFn H).map fun row => (encVec row).length).sum ≤ R * (6 * M + 2) := by
    have := List.sum_le_card_nsmul ((List.ofFn H).map fun row => (encVec row).length) (6 * M + 2)
      (fun x hx => by obtain ⟨row, -, rfl⟩ := List.mem_map.1 hx; exact hrow row)
    rw [List.length_map, hl, smul_eq_mul] at this
    exact this
  have h4 := encNat_len R
  have h5 := encNat_len M
  have h6 : R * (6 * M + 2) ≤ M ^ 3 * (6 * M + 2) := Nat.mul_le_mul_right _ hR
  have h7 : M ^ 3 * (6 * M + 2) ≤ 6 * (M + 1) ^ 4 := by nlinarith [sq_nonneg (M : ℕ)]
  have h8 : R ≤ (M + 1) ^ 4 := hR.trans (by nlinarith [sq_nonneg (M : ℕ)])
  have h9 : M + 1 ≤ (M + 1) ^ 4 := by
    calc M + 1 = (M + 1) ^ 1 := (pow_one _).symm
      _ ≤ (M + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

lemma outputsWithin_mono {Mach : Turing.TM2ComputableAux Bool Bool} {x y : List Bool} {t t' : ℕ}
    (h : HMBinPacking.OutputsWithin Mach x y t) (ht : t ≤ t') :
    HMBinPacking.OutputsWithin Mach x y t' := by
  obtain ⟨h⟩ := h
  exact ⟨⟨h.toEvalsTo, le_trans h.steps_le_m ht⟩⟩

end AbelianCayleyHDX.XR

open AbelianCayleyHDX AbelianCayleyHDX.XR AbelianCayleyHDX.XK AbelianCayleyHDX.XP AbelianCayleyHDX.RelCx in
theorem solution (R M ρ : ℕ → ℕ)
    (H : ∀ j, Matrix (Fin (R j)) (Fin (M j)) (ZMod 2)) (hH : ∀ j, IsGoodRelationMatrix (H j) (ρ j))
    (Mach : Turing.TM2ComputableAux Bool Bool) (p : Polynomial ℕ)
    (hMach : ∀ j, HMBinPacking.OutputsWithin Mach (encNat j)
      (encNat (R j) ++ encNat (M j) ++ encList encVec (List.ofFn (H j))) (p.eval (M j)))
    (q : Polynomial ℕ) (hq : ∀ j, M j ≤ q.eval (Module.finrank (ZMod 2) (kerF2 (H j)))) :
    ∃ φ : ∀ j, (Fin (M j) → ZMod 2) →ₗ[ZMod 2] Vec (Module.finrank (ZMod 2) (kerF2 (H j))),
      (∀ j, Function.Surjective (φ j) ∧ LinearMap.ker (φ j) = rowspan (H j)) ∧
      IsExplicitFamily (fun j => Module.finrank (ZMod 2) (kerF2 (H j)))
        (fun j => Finset.univ.image fun i => φ j (Pi.single i 1))
        (fun j => relationComplex (H j) (φ j)) := by
  classical
  refine ⟨fun j => phi (H j), fun j => phi_spec (H j), ?_⟩
  obtain ⟨M', P, hM'⟩ := outputsWithin_comp (x := fun j => encNat j)
    (W := fun j => encNat (R j) ++ encNat (M j) ++ encList encVec (List.ofFn (H j))) hMach
    poly_postB
  set wp : Polynomial ℕ := 20 * (Polynomial.X + 1) ^ 4
  have hwp : ∀ m : ℕ, wp.eval m = 20 * (m + 1) ^ 4 := fun m => by simp [wp]
  set F : Polynomial ℕ := p + 2 * wp + 2 + P.comp wp
  refine ⟨M', F.comp q, fun j => ⟨gensL (H j), repsL (H j) (hH j), ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- generators are distinct
    exact List.nodup_ofFn.2 (s_inj (hH j) (phi_spec (H j)).2)
  · ext x; simp [gensL, List.mem_ofFn]
  · -- representatives are distinct
    refine List.nodup_ofFn.2 (fun r r' h => ?_)
    apply repL_translate (H j) (hH j) (x := 0)
    rw [image_add_zero, h]
  · intro l hl
    obtain ⟨r, rfl⟩ := List.mem_ofFn.1 hl
    exact ⟨repL_nodup (H j) (hH j) r, repL_mem (H j) (hH j) r⟩
  · intro τ hτ
    exact reps_unique (H j) (hH j) hτ
  · have hT := (triangle_orbits (H j) (ρ j) (hH j) (phi (H j)) (phi_spec (H j)).1
      (phi_spec (H j)).2).2.2
    rw [hT, Fintype.card_fin]
    have hout := hM' j
    rw [post_eq (H j) (hH j)] at hout
    apply outputsWithin_mono hout
    -- the time bound
    have hW := W_len (H j) (hH j)
    have hm := hq j
    set w := (encNat (R j) ++ encNat (M j) ++ encList encVec (List.ofFn (H j))).length
    have e1 : P.eval w ≤ P.eval (wp.eval (M j)) := poly_eval_mono _ (by rw [hwp]; exact hW)
    have e2 : F.eval (M j) = p.eval (M j) + 2 * wp.eval (M j) + 2 + P.eval (wp.eval (M j)) := by
      simp [F, Polynomial.eval_comp]
    have e3 : F.eval (M j) ≤ F.eval (q.eval (Module.finrank (ZMod 2) (kerF2 (H j)))) :=
      poly_eval_mono _ hm
    rw [Polynomial.eval_comp]
    rw [hwp] at e1 e2
    beta_reduce
    omega
