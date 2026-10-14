-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part08
-- name    : OAI_QuantumFactoring_Part08
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T07:13:39.308662+00:00
-- url     : https://prove2.me/theorems/0e2b5896-6059-460e-98a6-5bf35e8a3bdb
-- title:
--   Exact quantum factoring, part 8 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 8 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `BoundedAKS`, `AKSBounds`, `WordResize`, `AuxiliaryTree`, `FactorEncoding`, `FactorVerifier`, `FactorVerifierBounds`, `FactorGuess`, `FairOracle`, `RecordedHistory`, `ParallelPreparation`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`. This part also makes small compatibility edits for Lean 4.33.1 / Mathlib 0df444a: in AuxiliaryTree.lean, `Finset.prod_le_prod` → `Finset.prod_le_prod'` and `Finset.prod_le_prod_of_subset_of_one_le` → `Finset.prod_le_prod_of_subset_of_one_le'`; in FactorVerifier.lean, `List.prod_le_pow_length` → `List.prod_le_pow_card` (older name); in ParallelPreparation.lean, use the `↓reduceIte` simproc instead of `ite_true` (the classical decidability instance no longer matches `ite_true`).
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BoundedAKS.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/AKSBounds.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/WordResize.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/AuxiliaryTree.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/FactorEncoding.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/FactorVerifier.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/FactorVerifierBounds.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/FactorGuess.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/FairOracle.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/RecordedHistory.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/ParallelPreparation.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 8 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: BoundedAKS.lean, AKSBounds.lean, WordResize.lean, AuxiliaryTree.lean, FactorEncoding.lean, FactorVerifier.lean, FactorVerifierBounds.lean, FactorGuess.lean, FairOracle.lean, RecordedHistory.lean, ParallelPreparation.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted; compatibility edits for the platform Lean/Mathlib versions: in AuxiliaryTree.lean, `Finset.prod_le_prod` → `Finset.prod_le_prod'` and `Finset.prod_le_prod_of_subset_of_one_le` → `Finset.prod_le_prod_of_subset_of_one_le'`; in FactorVerifier.lean, `List.prod_le_pow_length` → `List.prod_le_pow_card` (older name); in ParallelPreparation.lean, use the `↓reduceIte` simproc instead of `ite_true` (the classical decidability instance no longer matches `ite_true`).
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part07

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BoundedAKS.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality

/-- All static search parameters and constants fit polynomial-width words. -/
lemma aks_constants_fit {n : ℕ} (hn : 128 ≤ n) : 8*n^8 < 2^(rootWidth n) := by
  have hp : n < 2^n := Nat.lt_pow_self (by decide)
  have hp8 : n^8 < (2^n)^8 := Nat.pow_lt_pow_left hp (by decide)
  have he : 3+n*8 ≤ rootWidth n := by dsimp [rootWidth]; nlinarith
  calc
    8*n^8 < 8*(2^n)^8 := Nat.mul_lt_mul_of_pos_left hp8 (by decide)
    _ = 2^(3+n*8) := by rw [pow_add,pow_mul]; norm_num
    _ ≤ 2^(rootWidth n) := Nat.pow_le_pow_right (by decide) he

def allCongruences (s w : ℕ) [NeZero s] : BooleanNetwork w 1 :=
  all (List.ofFn (fun i : Fin (8*s) => cyclicTest s w (i.val+1)))

lemma allCongruences_value (s w : ℕ) [NeZero s] (x : Basis w) (hw : 0 < w)
    (hm : 2 ≤ (bitsValue x).toNat) (hs : 8*s < 2^w) :
    (allCongruences s w).eval x 0=true ↔
      ∀ a : ℕ, 1 ≤ a → a ≤ 8*s →
        (cyclicX (R := ZMod (bitsValue x).toNat) s+cyclicC s (a : ZMod (bitsValue x).toNat))^
          (bitsValue x).toNat=cyclicX s^(bitsValue x).toNat+cyclicC s (a : ZMod (bitsValue x).toNat) := by
  rw [allCongruences,all_ofFn_eval]
  constructor
  · intro h a ha has
    have hh := (cyclicTest_correct s w (a-1+1) x hw hm (by omega)).mp
      (h (⟨a-1,by omega⟩ : Fin (8*s)))
    simpa only [show a-1+1=a by omega] using hh
  · intro h i
    rw [cyclicTest_correct s w (i.val+1) x hw hm (by omega)]
    exact h _ (by omega) (by omega)

lemma allCongruences_count (s w : ℕ) [NeZero s] :
    (allCongruences s w).net.count ≤ 8*s*(cyclicTestBound s w+1)+1 := by
  simpa only [allCongruences,List.length_ofFn] using
    all_count (List.ofFn (fun i : Fin (8*s) => cyclicTest s w (i.val+1))) (by
      intro c hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      exact cyclicTest_count s w (i.val+1))

/-- The auxiliary modulus branch. The bounded small-divisor test is performed
before the congruences. Evaluating every modulus is a polynomial unrolling of
(the first qualifying modulus in) the manuscript's bounded search. -/
def aksBranch (n s : ℕ) [NeZero s] : BooleanNetwork (rootWidth n) 1 :=
  let w := rootWidth n
  ((dividesNet w s).bnot.band (orderTests w s (n^2))).band
    ((noSmallDivisor w (8*s)).band (allCongruences s w))

lemma aksBranch_sound {n s : ℕ} [NeZero s] (hn : 128 ≤ n) (hs : s.Prime) (hsn : s ≤ n^8)
    (x : Basis (rootWidth n)) (hm : 2 ≤ (bitsValue x).toNat) (hmb : (bitsValue x).toNat < 2^n)
    (hpow : ¬ PerfectPower (bitsValue x).toNat) (h : (aksBranch n s).eval x 0=true) :
    (bitsValue x).toNat.Prime := by
  have hfit := aks_constants_fit hn
  have hsfit : 8*s < 2^(rootWidth n) := (Nat.mul_le_mul_left 8 hsn).trans_lt hfit
  have hsfit' : s < 2^(rootWidth n) := by omega
  have hkfit : n^2 < 2^(rootWidth n) := by
    have hh : rootWidth n < 2^(rootWidth n) := Nat.lt_pow_self (by decide)
    dsimp [rootWidth] at *
    nlinarith
  rw [aksBranch,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,
    eval_band,Bool.and_eq_true,bnot_value,dividesNet_value _ _ _ hsfit',
    orderTests_value _ _ _ _ hs.two_le hsfit' hkfit,
    noSmallDivisor_value _ _ _ hsfit,
    allCongruences_value _ _ _ (by dsimp [rootWidth];omega) hm hsfit] at h
  have hcop : s.Coprime (bitsValue x).toNat := hs.coprime_iff_not_dvd.mpr h.1.1
  have ho := (order_tests_iff hs hcop).mp h.1.2
  by_cases hb : (bitsValue x).toNat ≤ 8*s
  · exact prime_of_no_small_divisor hm hb h.2.1
  · exact cyclic_large_branch_prime hn hm hmb hs hcop ho hpow
      (fun d hd hdB => h.2.1 d hd hdB (by omega)) h.2.2

lemma aksBranch_complete {n s : ℕ} [NeZero s] (hn : 128 ≤ n) (hs : s.Prime) (hsn : s ≤ n^8)
    (x : Basis (rootWidth n)) (hm : (bitsValue x).toNat.Prime)
    (hcop : s.Coprime (bitsValue x).toNat) (ho : n^2 < orderOf ((bitsValue x).toNat : ZMod s)) :
    (aksBranch n s).eval x 0=true := by
  have hfit := aks_constants_fit hn
  have hsfit : 8*s < 2^(rootWidth n) := (Nat.mul_le_mul_left 8 hsn).trans_lt hfit
  have hsfit' : s < 2^(rootWidth n) := by omega
  have hkfit : n^2 < 2^(rootWidth n) := by
    have hh : rootWidth n < 2^(rootWidth n) := Nat.lt_pow_self (by decide)
    dsimp [rootWidth] at *
    nlinarith
  rw [aksBranch,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,
    eval_band,Bool.and_eq_true,bnot_value,dividesNet_value _ _ _ hsfit',
    orderTests_value _ _ _ _ hs.two_le hsfit' hkfit,
    noSmallDivisor_value _ _ _ hsfit,
    allCongruences_value _ _ _ (by dsimp [rootWidth];omega) hm.two_le hsfit]
  refine ⟨⟨hs.coprime_iff_not_dvd.mp hcop,(order_tests_iff hs hcop).mpr ho⟩,?_,?_⟩
  · intro d hd _hdb hdm hdiv
    have := hm.eq_one_or_self_of_dvd d hdiv
    omega
  · intro a _ha _has
    exact cyclic_prime_test hm a

/-- The condition is on the compile-time parameter s≤n^8, not on the possibly
exponentially large input integer. Decidable primality here is a finite bounded
search; its generation-cost proof is separate from circuit size. -/
def aksStaticBranch (n s : ℕ) : BooleanNetwork (rootWidth n) 1 :=
  if h : s.Prime then
    letI : NeZero s := ⟨h.ne_zero⟩
    aksBranch n s
  else constant false

def primalityNet (n : ℕ) : BooleanNetwork (rootWidth n) 1 :=
  (perfectPowerNet n).bnot.band
    (any (List.ofFn (fun s : Fin (n^8+1) => aksStaticBranch n s.val)))

/-- Full exact bounded AKS primality circuit, not an assumed decision procedure. -/
theorem primalityNet_correct {n : ℕ} (hn : 128 ≤ n) (x : Basis (rootWidth n))
    (hm : 2 ≤ (bitsValue x).toNat) (hmb : (bitsValue x).toNat < 2^n) :
    (primalityNet n).eval x 0=true ↔ (bitsValue x).toNat.Prime := by
  rw [primalityNet,eval_band,Bool.and_eq_true,bnot_value,perfectPowerNet_correct (by omega) _ hmb,
    any_ofFn_eval]
  constructor
  · rintro ⟨hpow,s,h⟩
    by_cases hs : s.val.Prime
    · let : NeZero s.val := ⟨hs.ne_zero⟩
      have he : aksStaticBranch n s.val=aksBranch n s.val := dite_eq_left hs
      rw [he] at h
      exact aksBranch_sound hn hs (by omega) x hm hmb hpow h
    · simp [aksStaticBranch,hs] at h
  · intro hp
    obtain ⟨s,hs,hsn,hcop,ho⟩ := auxiliary_prime_exists hn hm hmb
    let : NeZero s := ⟨hs.ne_zero⟩
    refine ⟨prime_not_perfectPower hp,⟨s,by omega⟩,?_⟩
    have he : aksStaticBranch n s=aksBranch n s := dite_eq_left hs
    change (aksStaticBranch n s).eval x 0=true
    rw [he]
    exact aksBranch_complete hn hs hsn x hp hcop ho

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/AKSBounds.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

abbrev aksBranchBound (n s w : ℕ) :=
  216*w*w+154*w+27+1 + (n^2*(100*w+23+w*(3672*w*w+436*w+36))+1) +
  (8*s*(216*w*w+203*w+38)+1) + (8*s*(cyclicTestBound s w+1)+1) + 3

lemma aksBranch_count (n s : ℕ) [NeZero s] :
    (aksBranch n s).net.count ≤ aksBranchBound n s (rootWidth n) := by
  have hd := dividesNet_count (rootWidth n) s
  have ho := orderTests_count (rootWidth n) s (n^2)
  have hs := noSmallDivisor_count (rootWidth n) (8*s)
  have hc := allCongruences_count s (rootWidth n)
  have hmul : (8*s-1)*(216*rootWidth n*rootWidth n+203*rootWidth n+38) ≤
      (8*s)*(216*rootWidth n*rootWidth n+203*rootWidth n+38) := by gcongr; omega
  simp only [aksBranch,count_band,count_bnot]
  dsimp [aksBranchBound]
  omega

lemma aksBranchBound_mono {n s s' w : ℕ} (hs : s ≤ s') :
    aksBranchBound n s w ≤ aksBranchBound n s' w := by
  unfold aksBranchBound
  gcongr
  exact cyclicTestBound_mono hs le_rfl

lemma aksStaticBranch_count (n s : ℕ) (hs : s ≤ n^8) :
    (aksStaticBranch n s).net.count ≤ aksBranchBound n (n^8) (rootWidth n) := by
  by_cases hp : s.Prime
  · let : NeZero s := ⟨hp.ne_zero⟩
    have he : aksStaticBranch n s = aksBranch n s := dite_eq_left hp
    exact (congrArg (fun c : BooleanNetwork (rootWidth n) 1 => c.net.count) he).trans_le
      ((aksBranch_count n s).trans (aksBranchBound_mono hs))
  · have he : aksStaticBranch n s = constant false := dite_eq_right hp
    rw [he]
    change 1 ≤ aksBranchBound n (n^8) (rootWidth n)
    unfold aksBranchBound
    omega

abbrev primalityBound (n : ℕ) :=
  (n+1)*(perfectCheckBound n+4)+1+1 +
  ((n^8+1)*(aksBranchBound n (n^8) (rootWidth n)+4)+1)+1

/-- Explicit polynomial size for the full exact primality network. -/
theorem primalityNet_count (n : ℕ) : (primalityNet n).net.count ≤ primalityBound n := by
  have hp := perfectPowerNet_count n
  have ha := any_count (c := aksBranchBound n (n^8) (rootWidth n))
    (List.ofFn (fun s : Fin (n^8+1) => aksStaticBranch n s.val)) (by
      intro c hc
      obtain ⟨s,rfl⟩ := List.mem_ofFn.mp hc
      exact aksStaticBranch_count n s.val (by omega))
  simp only [List.length_ofFn] at ha
  simp only [primalityNet,count_band,count_bnot]
  dsimp [primalityBound]
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/WordResize.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

/-- Ordinary zero extension/truncation, without copying a word circuit once per bit. -/
def resizeWord (u w : ℕ) : BooleanNetwork u w :=
  vector (fun i => if h : i.val<u then bit ⟨i.val,h⟩ else constant false)

lemma resizeWord_value (u w : ℕ) (x : Basis u) :
    bitsValue ((resizeWord u w).eval x)=(bitsValue x).setWidth w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((resizeWord u w).eval x)).getLsbD i =
    (resizeWord u w).eval x ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    BitVec.getLsbD_setWidth]
  simp only [hi,decide_true,Bool.true_and,resizeWord,eval_vector]
  by_cases hu : i<u
  · rw [dite_eq_left hu,eval_bit]
    exact (bitsValue_bit x ⟨i,hu⟩).symm
  · rw [dite_eq_right hu]
    simpa only [eval_constant] using (BitVec.getLsbD_of_ge (bitsValue x) i (by omega)).symm

lemma resizeWord_count (u w : ℕ) : (resizeWord u w).net.count≤w := by
  have hh := count_vector_le (c:=1)
    (fun i : Fin w => if h : i.val<u then bit ⟨i.val,h⟩ else constant false) (by
      intro i
      by_cases h : i.val<u
      · have he : (if h : i.val<u then bit (n:=u) ⟨i.val,h⟩ else constant false)=bit ⟨i.val,h⟩ := dite_eq_left h
        exact (congrArg (fun c : BooleanNetwork u 1 => c.net.count) he).trans_le (by simp)
      · have he : (if h : i.val<u then bit (n:=u) ⟨i.val,h⟩ else constant false)=constant false := dite_eq_right h
        exact (congrArg (fun c : BooleanNetwork u 1 => c.net.count) he).trans_le (by simp))
  simpa only [resizeWord,mul_one] using hh

lemma resizeWord_toNat {u w : ℕ} (h : u≤w) (x : Basis u) :
    (bitsValue ((resizeWord u w).eval x)).toNat=(bitsValue x).toNat := by
  rw [resizeWord_value,setWidth_toNat_of_le h]

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/AuxiliaryTree.lean =====
namespace OAI

section
open scoped BigOperators


/-! Occurrence-preserving bounds for the canonical p−1 auxiliary tree in
Section5. Equal labels under different parents remain separate list entries. -/
namespace ExactQuantumFactoring.AuxiliaryTree
open scoped BigOperators

def children (M : ℕ) : List ℕ :=
  ((M.primeFactors.filter (fun p => 2<p)).sort (·≤·)).map (·-1)

lemma mem_children {M d : ℕ} : d ∈ children M ↔
    ∃ p, p.Prime ∧ p ∣ M ∧ M≠0 ∧ 2<p ∧ d=p-1 := by
  simp only [children,List.mem_map,Finset.mem_sort,Finset.mem_filter,Nat.mem_primeFactors]
  constructor
  · rintro ⟨p,⟨⟨hp,hpm,hM⟩,hp2⟩,hd⟩
    exact ⟨p,hp,hpm,hM,hp2,hd.symm⟩
  · rintro ⟨p,hp,hpm,hM,hp2,rfl⟩
    exact ⟨p,⟨⟨hp,hpm,hM⟩,hp2⟩,rfl⟩

lemma child_bounds {M d : ℕ} (hd : d ∈ children M) : 2≤d ∧ d<M := by
  obtain ⟨p,hp,hpm,hM,hp2,rfl⟩ := mem_children.mp hd
  have hpM := Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hpm
  omega

lemma child_even {M d : ℕ} (hd : d ∈ children M) : Even d := by
  obtain ⟨p,hp,_,_,hp2,rfl⟩ := mem_children.mp hd
  have ho := hp.odd_of_ne_two (by omega)
  exact (Nat.even_sub (by omega : 1≤p)).mpr (by simpa using ho)

lemma grandchild_half {M d e : ℕ} (hd : d ∈ children M) (he : e ∈ children d) :
    2*e<M := by
  obtain ⟨p,hp,hpd,hd0,hp2,rfl⟩ := mem_children.mp he
  have hopen := hp.odd_of_ne_two (by omega)
  have hcop : Nat.Coprime 2 p := (Nat.coprime_two_left).mpr hopen
  have hdiv := hcop.mul_dvd_of_dvd_of_dvd (even_iff_two_dvd.mp (child_even hd)) hpd
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hdiv
  have hdm := (child_bounds hd).2
  omega

lemma children_prod_le {M : ℕ} (hM : 0<M) : (children M).prod≤M := by
  unfold children
  rw [← List.prod_toFinset _ (Finset.sort_nodup _ _),Finset.sort_toFinset]
  calc
    (∏ p ∈ M.primeFactors.filter (fun p => 2<p), (p-1)) ≤
      ∏ p ∈ M.primeFactors.filter (fun p => 2<p), p :=
      Finset.prod_le_prod' (fun _ _ => Nat.sub_le _ _)
    _ ≤ ∏ p ∈ M.primeFactors, p := Finset.prod_le_prod_of_subset_of_one_le'
      (Finset.filter_subset _ _)
      (fun p hp _ => (Nat.prime_of_mem_primeFactors hp).one_lt.le)
    _ ≤ M := Nat.le_of_dvd hM (Nat.prod_primeFactors_dvd M)

/-- A level is a list, not a set: multiplicities of occurrences are retained. -/
def level (M : ℕ) : ℕ → List ℕ
  | 0 => [M]
  | k+1 => (children M).flatMap (fun d => level d k)

lemma level_bounds {M d k : ℕ} (hM : 2≤M) (hd : d ∈ level M k) : 2≤d ∧ d≤M := by
  induction k generalizing M with
  | zero =>
    have he : d=M := by simpa [level] using hd
    subst d
    exact ⟨hM,le_rfl⟩
  | succ k ih =>
    obtain ⟨e,he,hd⟩ := List.mem_flatMap.mp hd
    have hb := child_bounds he
    have hh := ih hb.1 hd
    exact ⟨hh.1,hh.2.trans hb.2.le⟩

lemma level_two_step {M d k : ℕ} (hd : d ∈ level M (2*k)) : 2^k*d≤M := by
  induction k generalizing M with
  | zero =>
    have he : d=M := by simpa [level] using hd
    simpa using he.le
  | succ k ih =>
    have heq : 2*(k+1)=2*k+1+1 := by omega
    rw [heq,level] at hd
    obtain ⟨e,he,hd⟩ := List.mem_flatMap.mp hd
    rw [level] at hd
    obtain ⟨f,hf,hd⟩ := List.mem_flatMap.mp hd
    have hx := ih hd
    have hh := grandchild_half he hf
    rw [pow_succ]
    nlinarith

lemma level_empty {M n : ℕ} (hM : 2≤M) (hbound : M<2^n) : level M (2*n)=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro d hd
  have hx := level_two_step hd
  have hy := (level_bounds hM hd).1
  have hp : 0<2^n := by positivity
  nlinarith

lemma prod_flatMap (f : ℕ→List ℕ) (xs : List ℕ) :
    (xs.flatMap f).prod=(xs.map (fun x => (f x).prod)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

lemma level_prod_le {M k : ℕ} (hM : 2≤M) : (level M k).prod≤M := by
  induction k generalizing M with
  | zero => simp [level]
  | succ k ih =>
    rw [level,prod_flatMap]
    calc
      ((children M).map (fun d => (level d k).prod)).prod ≤
        ((children M).map id).prod := List.prod_map_le_prod_map₀ _ _
          (fun _ _ => Nat.zero_le _) (fun d hd => ih (child_bounds hd).1)
      _ = (children M).prod := by simp
      _ ≤ M := children_prod_le (by omega)

lemma pow_length_le_prod (xs : List ℕ) (hxs : ∀ x ∈ xs, 2≤x) : 2^xs.length≤xs.prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have hi := ih (fun y hy => hxs y (by simp [hy]))
    simp only [List.length_cons,List.prod_cons,pow_succ]
    exact (Nat.mul_le_mul hi hx).trans_eq (Nat.mul_comm _ _)

lemma level_length_lt {M n k : ℕ} (hM : 2≤M) (hbound : M<2^n) :
    (level M k).length<n := by
  apply (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
  exact (pow_length_le_prod _ (fun _ hd => (level_bounds hM hd).1)).trans_lt
    ((level_prod_le hM).trans_lt hbound)

def splitWeight (M : ℕ) : ℕ := M.primeFactorsList.length

lemma splitWeight_bound {M n : ℕ} (hM : 0<M) (hbound : M<2^n) : splitWeight M<n := by
  apply (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
  have hh := pow_length_le_prod M.primeFactorsList
    (fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)
  rw [Nat.prod_primeFactorsList hM.ne'] at hh
  exact hh.trans_lt hbound

lemma level_weight_lt {M n k : ℕ} (hM : 2≤M) (hbound : M<2^n) :
    ((level M k).map splitWeight).sum<n := by
  let ps := (level M k).flatMap Nat.primeFactorsList
  have he : ps.prod=(level M k).prod := by
    rw [prod_flatMap]
    congr 1
    conv_rhs => rw [← List.map_id (level M k)]
    apply List.map_congr_left
    intro d hd
    exact Nat.prod_primeFactorsList (by have := (level_bounds hM hd).1; omega)
  have hlen : ps.length=((level M k).map splitWeight).sum := by
    change (List.flatMap Nat.primeFactorsList (level M k)).length = _
    rw [List.length_flatMap]
    rfl
  have hp : 2^ps.length≤ps.prod := pow_length_le_prod ps (by
    intro p hp
    obtain ⟨d,_,hp⟩ := List.mem_flatMap.mp hp
    exact (Nat.prime_of_mem_primeFactorsList hp).two_le)
  rw [he,hlen] at hp
  exact (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
    (hp.trans_lt ((level_prod_le hM).trans_lt hbound))

/-- The source's whole-tree task cap, expressed without real logarithms. -/
def taskBound (M n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2*n+2), ((level M k).map splitWeight).sum

lemma taskBound_le {M n : ℕ} (hM : 2≤M) (hbound : M<2^n) :
    taskBound M n ≤ (2*n+2)*n := by
  unfold taskBound
  calc
    _ ≤ ∑ _k ∈ Finset.range (2*n+2), n := Finset.sum_le_sum
      (fun k _ => (level_weight_lt (k:=k) hM hbound).le)
    _ = _ := by simp

lemma transitions_bound {n : ℕ} (hn : 2≤n) : (2*n+2)*n*(n^5+1)≤6*n^7 := by
  have hnpos : 0<n := by omega
  have hp : 1≤n^5 := Nat.one_le_pow _ _ hnpos
  have h₁ : 2*n+2≤3*n := by omega
  have h₂ : n^5+1≤2*n^5 := by omega
  calc
    _ ≤ (3*n)*n*(2*n^5) := Nat.mul_le_mul (Nat.mul_le_mul_right n h₁) h₂
    _ = 6*n^7 := by ring

lemma transitions_lt_slots {n : ℕ} (hn : 128≤n) : (2*n+2)*n*(n^5+1)<n^10 := by
  have hp : 6<n^3 := by
    have hh := Nat.pow_le_pow_left hn 3
    norm_num at hh
    omega
  have hnpos : 0<n^7 := pow_pos (by omega) _
  calc
    _ ≤ 6*n^7 := transitions_bound (by omega)
    _ < n^3*n^7 := Nat.mul_lt_mul_of_pos_right hp hnpos
    _ = n^10 := by ring

end ExactQuantumFactoring.AuxiliaryTree


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FactorEncoding.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Zero padding follows every positive entry. -/
def PaddedOrder (a b : ℕ) : Prop := b=0 ∨ (a≠0 ∧ a≤b)

def unpadProduct (xs : List ℕ) : ℕ := (xs.map (fun a => if a=0 then 1 else a)).prod

def FactorListValid (N : ℕ) (xs : List ℕ) : Prop :=
  (∀ a ∈ xs, a=0 ∨ a.Prime) ∧ xs.Pairwise PaddedOrder ∧ unpadProduct xs=N

lemma paddedOrder_append (ps : List ℕ) (k : ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hs : ps.Pairwise (·≤·)) : (ps++List.replicate k 0).Pairwise PaddedOrder := by
  rw [List.pairwise_append]
  refine ⟨hs.imp_of_mem ?_,?_,?_⟩
  · intro a b ha _hab hab
    exact Or.inr ⟨(hp a ha).ne_zero,hab⟩
  · apply List.pairwise_replicate.mpr
    exact Or.inr (Or.inl rfl)
  · intro a _ b hb
    have hb0 : b=0 := by simpa using (List.mem_replicate.mp hb).2
    exact Or.inl hb0

lemma unpadProduct_append (ps : List ℕ) (k : ℕ) (hp : ∀ p ∈ ps, p≠0) :
    unpadProduct (ps++List.replicate k 0)=ps.prod := by
  unfold unpadProduct
  rw [List.map_append,List.prod_append,List.map_replicate]
  simp only [ite_true,List.prod_replicate,one_pow,mul_one]
  congr 1
  conv_rhs => rw [← List.map_id ps]
  exact List.map_congr_left (fun p hp' => ite_eq_right (hp p hp'))

lemma FactorListValid.decompose {N : ℕ} {xs : List ℕ} (h : FactorListValid N xs) :
    ∃ ps : List ℕ, (∀ p ∈ ps, p.Prime) ∧ ps.Pairwise (·≤·) ∧ ps.prod=N ∧
      ps.length≤xs.length ∧ xs=ps++List.replicate (xs.length-ps.length) 0 := by
  rcases h with ⟨hp,hs,hprod⟩
  induction xs generalizing N with
  | nil => exact ⟨[],by simp,by simp,by simpa [unpadProduct] using hprod,by simp,by simp⟩
  | cons a xs ih =>
    have hpa : a=0 ∨ a.Prime := hp a (by simp)
    have hps : ∀ p ∈ xs, p=0 ∨ p.Prime := fun p h => hp p (by simp [h])
    have hsw := List.pairwise_cons.mp hs
    rcases hpa with rfl | ha
    · have hz : ∀ b ∈ xs, b=0 := by
        intro b hb
        rcases hsw.1 b hb with h | h
        · exact h
        · exact (h.1 rfl).elim
      have he : xs=List.replicate xs.length 0 := List.eq_replicate_of_mem hz
      have hn : N=1 := by
        rw [he] at hprod
        simpa [unpadProduct] using hprod.symm
      refine ⟨[],by simp,by simp,by simpa using hn.symm,by simp,?_⟩
      simp only [List.length_cons,List.length_nil,Nat.sub_zero,List.nil_append]
      rw [List.replicate_succ,← he]
    · obtain ⟨ps,hpp,hpsort,hpprod,hplen,hxeq⟩ :=
        ih hps hsw.2 (rfl : unpadProduct xs=unpadProduct xs)
      refine ⟨a::ps,?_,?_,?_,by simpa using hplen,?_⟩
      · intro p hp'
        rcases List.mem_cons.mp hp' with rfl | hp'
        · exact ha
        · exact hpp p hp'
      · rw [List.pairwise_cons]
        refine ⟨?_,hpsort⟩
        intro p hpm
        have hpx : p ∈ xs := by rw [hxeq]; exact List.mem_append_left _ hpm
        rcases hsw.1 p hpx with he | he
        · exact ((hpp p hpm).ne_zero he).elim
        · exact he.2
      · simp only [List.prod_cons,hpprod]
        simpa only [unpadProduct,List.map_cons,List.prod_cons,ite_eq_right ha.ne_zero] using hprod
      · simpa only [List.length_cons,Nat.add_sub_add_right,List.cons_append] using congrArg (List.cons a) hxeq

lemma factorListValid_iff {N n : ℕ} {xs : List ℕ} (hlen : xs.length=n) :
    FactorListValid N xs ↔ CorrectEncoding N n xs := by
  constructor
  · intro h
    simpa only [hlen,CorrectEncoding] using h.decompose
  · rintro ⟨ps,hp,hs,hprod,hplen,rfl⟩
    refine ⟨?_,paddedOrder_append ps _ hp hs,?_⟩
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact Or.inr (hp a ha)
      · exact Or.inl (List.mem_replicate.mp ha).2
    · exact (unpadProduct_append ps _ (fun p hp' => (hp p hp').ne_zero)).trans hprod

lemma correctEncoding_unique {N n : ℕ} {xs ys : List ℕ}
    (hx : CorrectEncoding N n xs) (hy : CorrectEncoding N n ys) : xs=ys := by
  obtain ⟨ps,hp,hs,hprod,_,rfl⟩ := hx
  obtain ⟨qs,hq,ht,hqprod,_,rfl⟩ := hy
  have hperm := (Nat.primeFactorsList_unique hprod hp).trans
    (Nat.primeFactorsList_unique hqprod hq).symm
  have he : ps=qs := hperm.eq_of_pairwise' hs ht
  rw [he]

/-- The valid sorted padded encoding exists and is unique, with every entry in
its n-bit range; the mathematical factor list here is used for analysis only. -/
theorem correctEncoding_exists {N n : ℕ} (hN : 2≤N) (hb : N<2^n) :
    ∃ xs : List ℕ, CorrectEncoding N n xs ∧ xs.length=n ∧ ∀ a ∈ xs, a<2^n := by
  have hn : N.primeFactorsList.length<n := AuxiliaryTree.splitWeight_bound (by omega) hb
  let xs := N.primeFactorsList++List.replicate (n-N.primeFactorsList.length) 0
  refine ⟨xs,⟨N.primeFactorsList,(fun p hp => Nat.prime_of_mem_primeFactorsList hp),
    (Nat.primeFactorsList_sorted N).pairwise,Nat.prod_primeFactorsList (by omega),hn.le,rfl⟩,?_,?_⟩
  · simp only [xs,List.length_append,List.length_replicate]
    omega
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (Nat.le_of_mem_primeFactorsList ha).trans_lt hb
    · have he := (List.mem_replicate.mp ha).2
      rw [he]
      positivity

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FactorVerifier.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open scoped BigOperators

lemma rootWidth_ge (n : ℕ) : n≤rootWidth n := by
  dsimp [rootWidth]
  nlinarith

/-- The range check makes the AKS interface exact also for the invalid 0,1
entries occurring in arbitrary uniform guesses. -/
def primeWord (n : ℕ) : BooleanNetwork n 1 :=
  (wordLe (wordConstant (BitVec.ofNat n 2)) (select id)).band
    ((resizeWord n (rootWidth n)).comp (primalityNet n))

lemma primeWord_value {n : ℕ} (hn : 128≤n) (x : Basis n) :
    (primeWord n).eval x 0=true ↔ (bitsValue x).toNat.Prime := by
  have hfit : 2<2^n := by
    have := Nat.pow_le_pow_right (n:=2) (by decide) hn
    norm_num at this
    omega
  rw [primeWord,eval_band,Bool.and_eq_true,wordLe_eval,wordConstant_eval,
    eval_select,Function.comp_id,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hfit,decide_eq_true_eq,
    eval_comp]
  by_cases h : 2≤(bitsValue x).toNat
  · rw [and_iff_right h,primalityNet_correct hn _ (by
      rw [resizeWord_toNat (rootWidth_ge n)];exact h) (by
      rw [resizeWord_toNat (rootWidth_ge n)];exact (bitsValue x).isLt),
      resizeWord_toNat (rootWidth_ge n)]
  · constructor
    · exact fun hh => (h hh.1).elim
    · exact fun hh => (h hh.two_le).elim

lemma primeWord_count (n : ℕ) : (primeWord n).net.count≤
    49*n+10+rootWidth n+primalityBound n := by
  have h₁ := wordLe_count (wordConstant (n:=n) (BitVec.ofNat n 2)) (select id)
  have h₂ := resizeWord_count n (rootWidth n)
  have h₃ := primalityNet_count n
  rw [wordConstant_count,count_select] at h₁
  simp only [primeWord,count_band,count_comp]
  omega

def zeroWord {k n : ℕ} (a : BooleanNetwork k n) : BooleanNetwork k 1 :=
  equalOn a (wordConstant 0)

lemma zeroWord_value {k n : ℕ} (a : BooleanNetwork k n) (x : Basis k) :
    (zeroWord a).eval x 0=true ↔ (bitsValue (a.eval x)).toNat=0 := by
  rw [zeroWord,equalOn_value,wordConstant_eval]
  simp

def primeOrZero {k n : ℕ} (a : BooleanNetwork k n) : BooleanNetwork k 1 :=
  (zeroWord a).bor (a.comp (primeWord n))

lemma primeOrZero_value {k n : ℕ} (hn : 128≤n) (a : BooleanNetwork k n) (x : Basis k) :
    (primeOrZero a).eval x 0=true ↔
      (bitsValue (a.eval x)).toNat=0 ∨ (bitsValue (a.eval x)).toNat.Prime := by
  rw [primeOrZero,eval_bor,Bool.or_eq_true,zeroWord_value,eval_comp,primeWord_value hn]

def paddedPair {k n : ℕ} (a b : BooleanNetwork k n) : BooleanNetwork k 1 :=
  (zeroWord b).bor ((zeroWord a).bnot.band (wordLe a b))

lemma paddedPair_value {k n : ℕ} (a b : BooleanNetwork k n) (x : Basis k) :
    (paddedPair a b).eval x 0=true ↔
      PaddedOrder (bitsValue (a.eval x)).toNat (bitsValue (b.eval x)).toNat := by
  rw [paddedPair,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,bnot_value,
    zeroWord_value,zeroWord_value,wordLe_eval,decide_eq_true_eq]
  rfl

def unpadWord {k n : ℕ} (a : BooleanNetwork k n) : BooleanNetwork k n :=
  wordMux (zeroWord a) (wordConstant 1) a

lemma unpadWord_value {k n : ℕ} (hn : 0<n) (a : BooleanNetwork k n) (x : Basis k) :
    (bitsValue ((unpadWord a).eval x)).toNat=
      if (bitsValue (a.eval x)).toNat=0 then 1 else (bitsValue (a.eval x)).toNat := by
  have hp : 1<2^n := Nat.one_lt_pow (by omega) (by decide)
  rw [unpadWord,wordMux_eval]
  by_cases h : (bitsValue (a.eval x)).toNat=0
  · rw [ite_eq_left h,ite_eq_left ((zeroWord_value a x).mpr h),wordConstant_eval]
    simpa using (Nat.mod_eq_of_lt hp)
  · rw [ite_eq_right h,ite_eq_right (by simpa only [zeroWord_value] using h)]

/-- Multiplication is modulo the sufficiently wide product register; no
repetition of earlier expression DAGs occurs in this linear fold. -/
def productNet {k w : ℕ} : List (BooleanNetwork k w) → BooleanNetwork k w
  | [] => wordConstant 1
  | a::as => (a.pair (productNet as)).comp (mul w)

lemma productNet_value {k w : ℕ} (as : List (BooleanNetwork k w)) (x : Basis k) :
    bitsValue ((productNet as).eval x)=(as.map (fun a => bitsValue (a.eval x))).prod := by
  induction as with
  | nil => simp [productNet,wordConstant_eval]
  | cons a as ih => simp only [productNet,eval_comp,eval_pair,mul_word,ih,List.map_cons,List.prod_cons]

lemma productNet_nat {k w : ℕ} (as : List (BooleanNetwork k w)) (x : Basis k) :
    (bitsValue ((productNet as).eval x)).toNat=
      (as.map (fun a => (bitsValue (a.eval x)).toNat)).prod % 2^w := by
  induction as with
  | nil => simp [productNet,wordConstant_eval]
  | cons a as ih =>
    simp only [productNet,eval_comp,eval_pair,mul_word,BitVec.toNat_mul,ih,
      List.map_cons,List.prod_cons,Nat.mul_mod_mod]

def candidateWords {k n : ℕ} (as : Fin n→BooleanNetwork k n) (x : Basis k) : List ℕ :=
  List.ofFn (fun i => (bitsValue ((as i).eval x)).toNat)

def candidateProduct {k n : ℕ} (as : Fin n→BooleanNetwork k n) : BooleanNetwork k (rootWidth n) :=
  productNet (List.ofFn (fun i => (unpadWord (as i)).comp (resizeWord n (rootWidth n))))

lemma candidateProduct_value {k n : ℕ} (hn : 0<n) (as : Fin n→BooleanNetwork k n) (x : Basis k) :
    (bitsValue ((candidateProduct as).eval x)).toNat=unpadProduct (candidateWords as x) := by
  have he : ((List.ofFn (fun i => (unpadWord (as i)).comp (resizeWord n (rootWidth n)))).map
      (fun a => (bitsValue (a.eval x)).toNat)) =
      (candidateWords as x).map (fun a => if a=0 then 1 else a) := by
    simp only [List.map_ofFn,candidateWords]
    congr 1
    funext i
    simp only [Function.comp_apply,eval_comp,resizeWord_toNat (rootWidth_ge n),
      unpadWord_value hn]
  have hb : unpadProduct (candidateWords as x)≤(2^n)^n := by
    have hh := List.prod_le_pow_card ((candidateWords as x).map (fun a => if a=0 then 1 else a))
      (2^n) (by
        intro a ha
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
        split
        · exact Nat.one_le_pow _ _ (by decide)
        · exact (bitsValue ((as i).eval x)).isLt.le)
    simpa only [unpadProduct,List.length_map,candidateWords,List.length_ofFn] using hh
  have hpow : (2^n)^n<2^(rootWidth n) := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by decide) (by dsimp [rootWidth];nlinarith)
  rw [candidateProduct,productNet_nat,he]
  change unpadProduct (candidateWords as x) % 2^rootWidth n = _
  exact Nat.mod_eq_of_lt (hb.trans_lt hpow)

def factorVerifierOn {k n : ℕ} (N : BooleanNetwork k n) (as : Fin n→BooleanNetwork k n) :
    BooleanNetwork k 1 :=
  ((all (List.ofFn (fun i => primeOrZero (as i)))).band
    (all (List.ofFn (fun i : Fin (n*n) =>
      let p := finProdFinEquiv.symm i
      if p.1<p.2 then paddedPair (as p.1) (as p.2) else constant true)))).band
    (equalOn (candidateProduct as) (N.comp (resizeWord n (rootWidth n))))

lemma factorVerifierOn_correct {k n : ℕ} (hn : 128≤n) (N : BooleanNetwork k n)
    (as : Fin n→BooleanNetwork k n) (x : Basis k) :
    (factorVerifierOn N as).eval x 0=true ↔
      CorrectEncoding (bitsValue (N.eval x)).toNat n (candidateWords as x) := by
  rw [← factorListValid_iff (by simp [candidateWords]),FactorListValid]
  rw [factorVerifierOn,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,
    all_ofFn_eval,all_ofFn_eval,equalOn_value]
  rw [candidateProduct_value (by omega),eval_comp,resizeWord_toNat (rootWidth_ge n)]
  have hp : (∀ i : Fin n, (primeOrZero (as i)).eval x 0=true) ↔
      ∀ a ∈ candidateWords as x, a=0 ∨ a.Prime := by
    simp only [candidateWords,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,
      primeOrZero_value hn]
  have hs : (∀ i : Fin (n*n),
      (if (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2 then
        paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
        else constant true).eval x 0=true) ↔ (candidateWords as x).Pairwise PaddedOrder := by
    rw [candidateWords,List.pairwise_ofFn]
    constructor
    · intro h i j hij
      have hh := h (finProdFinEquiv (i,j))
      simp only [Equiv.symm_apply_apply,ite_eq_left hij] at hh
      exact (paddedPair_value _ _ _).mp hh
    · intro h i
      split_ifs with hij
      · exact (paddedPair_value _ _ _).mpr (h hij)
      · simp
  rw [hp,hs]
  tauto

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FactorVerifierBounds.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma zeroWord_count {k n : ℕ} (a : BooleanNetwork k n) :
    (zeroWord a).net.count ≤ a.net.count+97*n+21 := by
  have h := equalOn_count a (wordConstant (n:=k) (BitVec.ofNat n 0))
  rw [wordConstant_count] at h
  dsimp [zeroWord]
  omega

lemma primeOrZero_count {k n : ℕ} (a : BooleanNetwork k n) :
    (primeOrZero a).net.count ≤ 2*a.net.count+146*n+35+rootWidth n+primalityBound n := by
  have h₁ := zeroWord_count a
  have h₂ := primeWord_count n
  simp only [primeOrZero,count_bor,count_comp]
  omega

lemma paddedPair_count {k n : ℕ} (a b : BooleanNetwork k n) :
    (paddedPair a b).net.count ≤ 2*a.net.count+2*b.net.count+242*n+57 := by
  have h₁ := zeroWord_count a
  have h₂ := zeroWord_count b
  have h₃ := wordLe_count a b
  simp only [paddedPair,count_bor,count_band,count_bnot]
  omega

lemma unpadWord_count {k n : ℕ} (a : BooleanNetwork k n) :
    (unpadWord a).net.count ≤ 2*a.net.count+105*n+21 := by
  have h := zeroWord_count a
  simp only [unpadWord,wordMux_count,wordConstant_count]
  omega

lemma productNet_count {k w c : ℕ} (as : List (BooleanNetwork k w))
    (h : ∀ a∈as, a.net.count≤c) :
    (productNet as).net.count≤as.length*(c+90*w*w+14*w+6)+w := by
  induction as with
  | nil => simp [productNet,wordConstant_count]
  | cons a as ih =>
    have ha := h a (by simp)
    have hb := ih (fun b hb => h b (by simp [hb]))
    have hm := mul_count w
    simp only [productNet,count_comp,count_pair,List.length_cons]
    nlinarith

abbrev candidateProductBound (n c : ℕ) :=
  n*(2*c+105*n+21+rootWidth n+90*rootWidth n*rootWidth n+14*rootWidth n+6)+rootWidth n

lemma candidateProduct_count {k n c : ℕ} (as : Fin n→BooleanNetwork k n)
    (h : ∀ i, (as i).net.count≤c) :
    (candidateProduct as).net.count≤candidateProductBound n c := by
  have hh := productNet_count (c:=2*c+105*n+21+rootWidth n)
    (List.ofFn (fun i => (unpadWord (as i)).comp (resizeWord n (rootWidth n)))) (by
      intro a ha
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      have h₁ := unpadWord_count (as i)
      have h₂ := resizeWord_count n (rootWidth n)
      have h₃ := h i
      simp only [count_comp]
      omega)
  simpa only [candidateProduct,candidateProductBound,List.length_ofFn] using hh

abbrev factorVerifierBound (n c : ℕ) :=
  n*(2*c+146*n+35+rootWidth n+primalityBound n+1)+1+
  (n*n*(4*c+242*n+58)+1)+1+
  (candidateProductBound n c+c+rootWidth n+96*rootWidth n+21)+1

lemma factorVerifierOn_count {k n c : ℕ} (N : BooleanNetwork k n)
    (as : Fin n→BooleanNetwork k n) (hN : N.net.count≤c) (ha : ∀ i, (as i).net.count≤c) :
    (factorVerifierOn N as).net.count≤factorVerifierBound n c := by
  have h₁ := all_count (c:=2*c+146*n+35+rootWidth n+primalityBound n)
    (List.ofFn (fun i => primeOrZero (as i))) (by
      intro a hh
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
      have := primeOrZero_count (as i)
      have := ha i
      omega)
  have h₂ := all_count (c:=4*c+242*n+57)
    (List.ofFn (fun i : Fin (n*n) =>
      if (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2 then
        paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
      else constant true)) (by
      intro a hh
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
      by_cases hij : (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2
      · have he : (if (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2 then
              paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
            else constant true) =
              paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2) := ite_eq_left hij
        have hc := congrArg (fun d : BooleanNetwork k 1 => d.net.count) he
        have := paddedPair_count (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
        have := ha (finProdFinEquiv.symm i).1
        have := ha (finProdFinEquiv.symm i).2
        omega
      · have he : (if (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2 then
              paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
            else constant true) = (constant (n:=k) true) := ite_eq_right hij
        have hc := congrArg (fun d : BooleanNetwork k 1 => d.net.count) he
        have ht : (constant (n:=k) true).net.count=1 := rfl
        omega)
  have h₃ := equalOn_count (candidateProduct as) (N.comp (resizeWord n (rootWidth n)))
  have h₄ := candidateProduct_count as ha
  have h₅ := resizeWord_count n (rootWidth n)
  simp only [List.length_ofFn] at h₁ h₂
  rw [show 4*c+242*n+57+1 = 4*c+242*n+58 by omega] at h₂
  simp only [count_comp] at h₃
  simp only [factorVerifierOn,count_band]
  dsimp [factorVerifierBound]
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FactorGuess.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BitArithmetic BooleanNetwork Exactness

/-- The specified sorted, zero-padded n²-bit root encoding. -/
def guessWords (n : ℕ) (x : Basis (n*n)) : List ℕ :=
  List.ofFn (fun i : Fin n => (bitsValue (block x i)).toNat)

lemma guessWords_injective (n : ℕ) : Function.Injective (guessWords n) := by
  intro x y h
  have he : (fun i : Fin n => (bitsValue (block x i)).toNat)=
      (fun i : Fin n => (bitsValue (block y i)).toNat) := List.ofFn_injective h
  funext a
  obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective a
  have hi := congrFun he i
  have hb : bitsValue (block x i) = bitsValue (block y i) := BitVec.eq_of_toNat_eq hi
  have hj := congrArg (fun z : BitVec n => z.getLsbD j.val) hb
  simpa only [bitsValue_bit,block] using hj

lemma guessWords_surjective_bounded {n : ℕ} (xs : List ℕ) (hl : xs.length=n)
    (hb : ∀ a∈xs, a<2^n) : ∃ x : Basis (n*n), guessWords n x=xs := by
  let f : Fin n→ℕ := fun i => xs[i.val]'(by omega)
  let x : Basis (n*n) := fun a =>
    (BitVec.ofNat n (f (finProdFinEquiv.symm a).1)).getLsbD (finProdFinEquiv.symm a).2.val
  refine ⟨x,?_⟩
  have he : ∀ i : Fin n, (bitsValue (block x i)).toNat=f i := by
    intro i
    have hf : f i<2^n := hb _ (List.getElem_mem (by omega))
    have hg : block x i=fun j => (BitVec.ofNat n (f i)).getLsbD j.val := by
      funext j
      simp only [block,x,Equiv.symm_apply_apply]
    rw [hg,bitsValue_bits,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hf]
  simp only [guessWords,he]
  have h := List.ofFn_get xs
  subst n
  exact h

/-- Existence/uniqueness is a mathematical fact about the required output,
not a factoring oracle used in the circuit. -/
theorem unique_good_guess {N n : ℕ} (hN : 2≤N) (hb : N<2^n) :
    ∃! x : Basis (n*n), CorrectEncoding N n (guessWords n x) := by
  obtain ⟨xs,hx,hl,hb'⟩ := correctEncoding_exists hN hb
  obtain ⟨x,rfl⟩ := guessWords_surjective_bounded xs hl hb'
  refine ⟨x,hx,?_⟩
  intro y hy
  apply guessWords_injective n
  exact correctEncoding_unique hy hx

noncomputable def fairState (b : ℕ) : State b := fun _ => (Real.sqrt 2:ℂ)⁻¹^b

lemma fairState_mass (b : ℕ) (x : Basis b) :
    Complex.normSq (fairState b x)=(2:ℝ)⁻¹^b := by
  simp only [fairState,map_pow,Complex.normSq_inv,Complex.normSq_ofReal,
    Real.mul_self_sqrt (by norm_num : (0:ℝ)≤2)]

lemma fairState_normalized (b : ℕ) : ∑ x, Complex.normSq (fairState b x)=1 := by
  simp only [fairState_mass,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
    Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

/-- The actual fair-bit guess contributes exactly 2^(-n²), not an
input-dependent success probability. -/
theorem fair_guess_mass {N n : ℕ} (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (fun x => CorrectEncoding N n (guessWords n x)) (fairState (n*n))=
      (2:ℝ)⁻¹^(n*n) := by
  classical
  obtain ⟨x,hx,hu⟩ := unique_good_guess hN hb
  have he : ∀ y : Basis (n*n), CorrectEncoding N n (guessWords n y) ↔ y=x := by
    intro y
    exact ⟨fun hy => hu y hy,fun h => h ▸ hx⟩
  simp only [outcomeMass,he,Finset.sum_ite_eq',Finset.mem_univ,ite_true,fairState_mass]

/-- Concrete Boolean root-verification circuit with no run-time primality or
factorization oracle. The integer input is retained separately from the guess. -/
def guessVerifier (n : ℕ) : BooleanNetwork (n+n*n) 1 :=
  factorVerifierOn (select (Fin.castAdd (n*n)))
    (fun i => select (fun j => Fin.natAdd n (finProdFinEquiv (i,j))))

lemma guessVerifier_correct {n : ℕ} (hn : 128≤n) (a : Basis n) (x : Basis (n*n)) :
    (guessVerifier n).eval (Fin.append a x) 0=true ↔
      CorrectEncoding (bitsValue a).toNat n (guessWords n x) := by
  rw [guessVerifier,factorVerifierOn_correct hn]
  have hN : (select (Fin.castAdd (n*n))).eval (Fin.append a x)=a := by
    funext i
    exact Fin.append_left a x i
  rw [hN]
  apply iff_of_eq
  congr 1
  apply congrArg List.ofFn
  funext i
  congr 2
  funext j
  exact Fin.append_right a x (finProdFinEquiv (i,j))

lemma guessVerifier_count (n : ℕ) :
    (guessVerifier n).net.count≤factorVerifierBound n 0 := by
  apply factorVerifierOn_count <;> simp

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/FairOracle.lean =====
namespace OAI

section
open scoped BigOperators


/-! Actual fair-bit initialization followed by clean reversible Boolean
computation.  All random bits remain in the returned physical state. -/
namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

lemma outcomeMass_encode {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (he : Function.Injective e) (ψ : α → ℂ)
    (P : Basis q → Prop) :
    outcomeMass P (encodeState e ψ)=outcomeMass (P ∘ e) ψ := by
  classical
  unfold outcomeMass
  have hz : ∀ x ∈ (Finset.univ : Finset (Basis q)),
      x ∉ Finset.univ.image e →
      (if P x then Complex.normSq (encodeState e ψ x) else 0)=0 := by
    intro x _ hx
    have ho : x ∉ Set.range e := by
      rintro ⟨a,rfl⟩
      exact hx (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
    rw [encodeState_outside e ψ x ho]
    simp
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) hz,
    Finset.sum_image (fun _ _ _ _ h => he h)]
  simp only [encodeState_at e he,Function.comp_apply]

def fairOracle {n b m r : ℕ} (c : BooleanNetwork (n+b) m) (hr : c.net.count ≤ r) :
    List (Instruction (n+b+m+r)) :=
  firstProgram m r (rightProgram n (hadamardPrefix b b le_rfl)) ++ oracleOn c hr

lemma fairOracle_length {n b m r : ℕ} (c : BooleanNetwork (n+b) m) (hr : c.net.count ≤ r) :
    (fairOracle c hr).length ≤ b+4*c.net.count+2*m := by
  have h := oracleOn_length c hr
  simp only [fairOracle,List.length_append,firstProgram_length,rightProgram,List.length_map,
    hadamardPrefix_length]
  omega

lemma fairOracle_state {n b m r : ℕ} (c : BooleanNetwork (n+b) m)
    (hr : c.net.count ≤ r) (a : Basis n) :
    (programMatrix (fairOracle c hr)).mulVec
      (basisVector (packed r (Fin.append a (fun _ => false)) (fun _ => false))) =
      encodeState (fun x => packed r (Fin.append a x) (c.eval (Fin.append a x))) (fairState b) := by
  rw [fairOracle,programMatrix_append,← Matrix.mulVec_mulVec,firstProgram_basis,
    rightProgram_basis,hadamards_zero,encodeState_comp]
  change (programMatrix (oracleOn c hr)).mulVec
    (encodeState (fun x => packed r (Fin.append a x) (fun _ => false)) (fairState b)) = _
  rw [encodeState,Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul,oracleOn_basis,Bool.false_xor]
  rfl

lemma fairOracle_embedding {n b m r : ℕ} (c : BooleanNetwork (n+b) m) (a : Basis n) :
    Function.Injective (fun x : Basis b => packed r (Fin.append a x) (c.eval (Fin.append a x))) := by
  intro x y h
  have hh := (packed_eq_iff _ _ _ _).mp h
  exact append_right_injective a hh.1

lemma fairOracle_mass {n b m r : ℕ} (c : BooleanNetwork (n+b) m)
    (hr : c.net.count ≤ r) (a : Basis n) (P : Basis (n+b+m+r) → Prop) [DecidablePred P] :
    outcomeMass P ((programMatrix (fairOracle c hr)).mulVec
      (basisVector (packed r (Fin.append a (fun _ => false)) (fun _ => false)))) =
      (∑ x : Basis b, if P (packed r (Fin.append a x) (c.eval (Fin.append a x)))
        then (2:ℝ)⁻¹^b else 0) := by
  rw [fairOracle_state,outcomeMass_encode _ (fairOracle_embedding c a)]
  simp only [outcomeMass,Function.comp_apply,fairState_mass]

/-- A designated target bit of the packed clean oracle output. -/
def packedOutputBit {n m r : ℕ} (i : Fin m) (x : Basis (n+m+r)) : Bool :=
  x ((Fin.natAdd n i).castAdd r)

lemma packedOutputBit_eval {n m r : ℕ} (a : Basis n) (b : Basis m) (i : Fin m) :
    packedOutputBit (r:=r) i (packed r a b)=b i := by
  exact packed_target a b i

/-- The small, everywhere positive branch of Section 6, now with a physical
program and the concrete AKS verifier, not an abstract random-guess oracle. -/
lemma verified_guess_physical_mass {n r : ℕ} (hn : 128 ≤ n)
    (hr : (guessVerifier n).net.count ≤ r) (a : Basis n)
    (hN : 2 ≤ (bitsValue a).toNat) :
    outcomeMass (fun x => packedOutputBit (n:=n+n*n) (m:=1) (r:=r) 0 x=true)
      ((programMatrix (fairOracle (n:=n) (b:=n*n) (guessVerifier n) hr)).mulVec
        (basisVector (packed r (Fin.append a (fun _ => false)) (fun _ => false)))) =
      (2:ℝ)⁻¹^(n*n) := by
  rw [fairOracle_state,outcomeMass_encode _ (fairOracle_embedding (guessVerifier n) a)]
  change outcomeMass (fun x : Basis (n*n) =>
    packedOutputBit (r:=r) 0 (packed r (Fin.append a x) ((guessVerifier n).eval (Fin.append a x)))=true)
    (fairState (n*n)) = _
  simp_rw [packedOutputBit_eval,guessVerifier_correct hn]
  exact fair_guess_mass hN (bitsValue a).isLt

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/RecordedHistory.lean =====
namespace OAI

section
open scoped BigOperators


/-! The same-history deferred-filter argument of Section 6, at the level of
finite complex amplitudes with all old registers retained.  These are proved
lemmas for the main construction, not assumptions replacing that construction. -/
namespace ExactQuantumFactoring.RecordedHistory
open scoped BigOperators
open ExactQuantumFactoring.Exactness

/-- A fresh controlled computation appends a register, retaining the old one. -/
noncomputable def appendState {H Y : Type*} (ψ : H → ℂ) (fresh : H → Y → ℂ) : H × Y → ℂ :=
  fun hy => ψ hy.1 * fresh hy.1 hy.2

lemma append_mass {H Y : Type*} [Fintype H] [Fintype Y]
    (ψ : H → ℂ) (fresh : H → Y → ℂ) (passed : H → Prop) [DecidablePred passed]
    (pass : H → Y → Prop) :
    outcomeMass (fun hy : H × Y => passed hy.1 ∧ pass hy.1 hy.2) (appendState ψ fresh) =
      ∑ h, if passed h then Complex.normSq (ψ h) * outcomeMass (pass h) (fresh h) else 0 := by
  classical
  unfold outcomeMass appendState
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : passed h
  · simp only [hh, true_and, Complex.normSq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> simp
  · simp [hh]

/-- The normalized state of idle old work need not be known; exact local mass
on each passing passed suffices. No conditioning on future verification occurs. -/
lemma append_constant_mass {H Y : Type*} [Fintype H] [Fintype Y]
    (ψ : H → ℂ) (fresh : H → Y → ℂ) (passed : H → Prop) (pass : H → Y → Prop)
    (z : ℝ) (hlocal : ∀ h, passed h → outcomeMass (pass h) (fresh h) = z) :
    outcomeMass (fun hy : H × Y => passed hy.1 ∧ pass hy.1 hy.2) (appendState ψ fresh) =
      outcomeMass passed ψ * z := by
  classical
  rw [append_mass]
  unfold outcomeMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : passed h
  · have hl : (∑ y, if pass h y then Complex.normSq (fresh h y) else 0) = z :=
      hlocal h hh
    simp [hh, hl]
  · simp [hh]

lemma append_normalized {H Y : Type*} [Fintype H] [Fintype Y]
    (ψ : H → ℂ) (fresh : H → Y → ℂ)
    (hψ : ∑ h, Complex.normSq (ψ h) = 1)
    (hfresh : ∀ h, ∑ y, Complex.normSq (fresh h y) = 1) :
    ∑ hy, Complex.normSq (appendState ψ fresh hy) = 1 := by
  simp only [appendState, Complex.normSq_mul, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hfresh, mul_one]
  exact hψ

/-- An ordered history, stored with the most recent outcome first. -/
abbrev History (Y : Type*) (t : ℕ) := Fin t → Y

noncomputable def historyState {Y : Type*}
    (fresh : ∀ t, History Y t → Y → ℂ) : ∀ t, History Y t → ℂ
  | 0, _ => 1
  | t+1, h => historyState fresh t (Fin.tail h) * fresh t (Fin.tail h) (h 0)

def historyPass {Y : Type*} (pass : ∀ t, History Y t → Y → Prop) :
    ∀ t, History Y t → Prop
  | 0, _ => True
  | t+1, h => historyPass pass t (Fin.tail h) ∧ pass t (Fin.tail h) (h 0)

lemma outcomeMass_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (p : Y → Prop) (ψ : Y → ℂ) :
    outcomeMass (p ∘ e) (ψ ∘ e) = outcomeMass p ψ := by
  classical
  exact e.sum_comp (fun y => if p y then Complex.normSq (ψ y) else 0)

/-- Exactly z at every passing history gives exactly z^L, including all padded
slots. The hypotheses are local unconditioned fresh-register laws, not an
assumption about eventual successful completion. -/
lemma history_mass {Y : Type*} [Fintype Y]
    (fresh : ∀ t, History Y t → Y → ℂ)
    (pass : ∀ t, History Y t → Y → Prop) (z : ℝ)
    (hlocal : ∀ t h, historyPass pass t h → outcomeMass (pass t h) (fresh t h) = z) :
    ∀ L, outcomeMass (historyPass pass L) (historyState fresh L) = z^L := by
  intro L
  induction L with
  | zero => simp [outcomeMass, historyPass, historyState]
  | succ t ht =>
    let e : (History Y t × Y) ≃ History Y (t+1) :=
      (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ => Y))
    rw [← outcomeMass_equiv e]
    change outcomeMass
      (fun hy : History Y t × Y => historyPass pass t hy.1 ∧ pass t hy.1 hy.2)
      (appendState (historyState fresh t) (fresh t)) = z^(t+1)
    rw [append_constant_mass _ _ _ _ z (hlocal t), ht, pow_succ]

/-- The two filters are evaluated on the SAME recorded outcome and coins.
This proposition is independent of any stochastic representation of the runs. -/
lemma deferred_event_eq {Run Data : Type*} (trueData : Data)
    (produced : Run → Option Data) (verified : Run → Prop)
    (tests : Data → Run → Prop)
    (hallGood : ∀ r, tests trueData r → produced r = some trueData ∧ verified r)
    (hunique : ∀ r d, produced r = some d → verified r → d = trueData) :
    (fun r => ∃ d, produced r = some d ∧ verified r ∧ tests d r) =
      (fun r => tests trueData r) := by
  funext r
  apply propext
  constructor
  · rintro ⟨d, hd, hv, ht⟩
    rwa [hunique r d hd hv] at ht
  · intro ht
    exact ⟨trueData, (hallGood r ht).1, (hallGood r ht).2, ht⟩

lemma deferred_mass_eq {Run Data : Type*} [Fintype Run] (ψ : Run → ℂ)
    (trueData : Data) (produced : Run → Option Data) (verified : Run → Prop)
    (tests : Data → Run → Prop)
    (hallGood : ∀ r, tests trueData r → produced r = some trueData ∧ verified r)
    (hunique : ∀ r d, produced r = some d → verified r → d = trueData) :
    outcomeMass (fun r => ∃ d, produced r = some d ∧ verified r ∧ tests d r) ψ =
      outcomeMass (tests trueData) ψ := by
  rw [deferred_event_eq trueData produced verified tests hallGood hunique]

end ExactQuantumFactoring.RecordedHistory


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/ParallelPreparation.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

def leftRegister (p q : ℕ) : Register p (p+q) := ⟨Fin.castAdd q,Fin.castAdd_injective p q⟩
lemma append_leftRegister {p q : ℕ} (x : Basis p) (y : Basis q) :
    Fin.append x y ∘ leftRegister p q=x := by
  funext i
  exact Fin.append_left _ _ i
lemma append_replace_left {p q : ℕ} (x z : Basis p) (y : Basis q) :
    (leftRegister p q).replace (Fin.append x y) z=Fin.append z y := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · change (leftRegister p q).replace (Fin.append x y) z (leftRegister p q j)=_
    rw [Register.replace_inside,Fin.append_left]
  · have hj : ∀ k, leftRegister p q k≠Fin.natAdd p j := by
      intro k h
      have hh := congrArg Fin.val h
      change k.val=p+j.val at hh
      have := k.isLt
      omega
    rw [Register.replace_outside _ _ _ ⟨Fin.natAdd p j,hj⟩]
    simp only [Fin.append_right]

def leftProgram {p : ℕ} (q : ℕ) (ops : List (Instruction p)) : List (Instruction (p+q)) :=
  ops.map (Instruction.place (leftRegister p q))
lemma leftProgram_basis {p q : ℕ} (ops : List (Instruction p)) (x : Basis p) (y : Basis q) :
    (programMatrix (leftProgram q ops)).mulVec (basisVector (Fin.append x y))=
      encodeState (fun z => Fin.append z y) ((programMatrix ops).mulVec (basisVector x)) := by
  rw [leftProgram,Register.placed_basis_state,append_leftRegister]
  congr 1
  funext z
  exact append_replace_left x z y

def appendEquiv (p q : ℕ) : Basis p × Basis q ≃ Basis (p+q) :=
  Fin.appendEquiv p q
lemma appendEquiv_apply {p q : ℕ} (xy : Basis p × Basis q) :
    appendEquiv p q xy=Fin.append xy.1 xy.2 := rfl

noncomputable def independentState {α β : Type*} (ψ : α→ℂ) (χ : β→ℂ) : α×β→ℂ :=
  fun xy => ψ xy.1*χ xy.2

lemma encode_independent {α β : Type*} [Fintype α] [Fintype β] {p q : ℕ}
    (e : α→Basis p) (f : β→Basis q) (ψ : α→ℂ) (χ : β→ℂ) :
    encodeState (fun xy : α×β => Fin.append (e xy.1) (f xy.2)) (independentState ψ χ)=
      ∑ x, ψ x • encodeState (fun y => Fin.append (e x) (f y)) χ := by
  unfold encodeState independentState
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [smul_smul]

def parallelProgram {p q : ℕ} (A : List (Instruction p)) (B : List (Instruction q)) :
    List (Instruction (p+q)) := leftProgram q A ++ rightProgram p B
lemma parallelProgram_length {p q : ℕ} (A : List (Instruction p)) (B : List (Instruction q)) :
    (parallelProgram A B).length=A.length+B.length := by
  simp [parallelProgram,leftProgram,rightProgram]

lemma parallelProgram_basis {p q : ℕ} (A : List (Instruction p)) (B : List (Instruction q))
    (x : Basis p) (y : Basis q) :
    (programMatrix (parallelProgram A B)).mulVec (basisVector (Fin.append x y))=
      encodeState (appendEquiv p q) (independentState
        ((programMatrix A).mulVec (basisVector x)) ((programMatrix B).mulVec (basisVector y))) := by
  rw [parallelProgram,programMatrix_append,← Matrix.mulVec_mulVec,leftProgram_basis]
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,rightProgram_basis]
  exact (encode_independent id id _ _).symm

lemma independent_mass {α β : Type*} [Fintype α] [Fintype β]
    (ψ : α→ℂ) (χ : β→ℂ) (P : α→Prop) (R : β→Prop) :
    outcomeMass (fun xy : α×β => P xy.1 ∧ R xy.2) (independentState ψ χ)=
      outcomeMass P ψ*outcomeMass R χ := by
  exact RecordedHistory.append_constant_mass ψ (fun _ => χ) P (fun _ => R) _ (fun _ _ => rfl)

lemma independent_mass_left {α β : Type*} [Fintype α] [Fintype β]
    (ψ : α→ℂ) (χ : β→ℂ) (P : α→Prop) (hχ : ∑ y, Complex.normSq (χ y)=1) :
    outcomeMass (fun xy : α×β => P xy.1) (independentState ψ χ)=outcomeMass P ψ := by
  have hh := independent_mass ψ χ P (fun _ => True)
  have he : (fun xy : α×β => P xy.1 ∧ True)=(fun xy => P xy.1) := by funext xy; simp
  have hn : outcomeMass (fun _ : β => True) χ=1 := by
    unfold outcomeMass
    simpa only [↓reduceIte] using hχ
  rw [he,hn,mul_one] at hh
  exact hh

lemma independent_mass_right {α β : Type*} [Fintype α] [Fintype β]
    (ψ : α→ℂ) (χ : β→ℂ) (R : β→Prop) (hψ : ∑ x, Complex.normSq (ψ x)=1) :
    outcomeMass (fun xy : α×β => R xy.2) (independentState ψ χ)=outcomeMass R χ := by
  have hh := independent_mass ψ χ (fun _ => True) R
  have he : (fun xy : α×β => True ∧ R xy.2)=(fun xy => R xy.2) := by funext xy; simp
  have hn : outcomeMass (fun _ : α => True) ψ=1 := by
    unfold outcomeMass
    simpa only [↓reduceIte] using hψ
  rw [he,hn,one_mul] at hh
  exact hh

lemma fair_normalized (b : ℕ) : ∑ x : Basis b, Complex.normSq (fairState b x)=1 := by
  exact fairState_normalized b

lemma basis_preparation_normalized {q : ℕ} (A : List (Instruction q)) (x : Basis q) :
    ∑ y, Complex.normSq ((programMatrix A).mulVec (basisVector x) y)=1 := by
  rw [unitary_mass _ (programMatrix_unitary _)]
  simp [basisVector]

end ExactQuantumFactoring


end

end OAI


