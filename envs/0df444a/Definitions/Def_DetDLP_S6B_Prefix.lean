-- Prove2me | Definitions.Def_DetDLP_S6B_Prefix
-- name    : DetDLP_S6B_Prefix
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:11:19.351825+00:00
-- url     : https://prove2.me/theorems/064b1cdf-fd08-4e1f-a7f6-0b03c2459255
-- title:
--   Proper divisors from little-endian prefix queries
-- statement:
--   Let $N$ be a composite integer with $2\le N<2^d$. Starting with the empty prefix, append zero if the zero extension has a completion to a nontrivial factor pair of $N$, and append one otherwise. The test subtracts the contributions of the two trivial pairs from the pinned count. After $4d$ steps the first $d$ bits encode a factor $a$ satisfying $$2\le a<N,\qquad a\mid N.$$ The prefix is stored as a list in external-edge order, so the update and witness invariant apply directly to a count-query driver.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Proposition 2.6 (pp. 10–11)

import Definitions.Def_DetDLP_W5_M6DivisorConstraints

set_option autoImplicit false
namespace DetDLP.S6BPrefix
open w5_M6DivisorConstraints

/-- A prefix lists the assigned coordinates in increasing external-edge order. -/
def pins {k : ℕ} (p : List Bool) (i : Fin k) := p[i.val]?

def advance (ok : List Bool → Bool) (p : List Bool) := p ++ [!ok (p ++ [false])]

def grow (ok : List Bool → Bool) : ℕ → List Bool → List Bool
  | 0, p => p
  | n+1, p => grow ok n (advance ok p)

@[simp] theorem grow_length (ok : List Bool → Bool) (n : ℕ) (p : List Bool) :
    (grow ok n p).length = p.length + n := by
  induction n generalizing p with
  | zero => simp [grow]
  | succ n ih => simp [grow,ih,advance]; omega

private theorem extend {k : ℕ} (x : Fin k → Bool) (p : List Bool) (hp : p.length < k)
    (h : MatchesPins (pins p) x) : MatchesPins (pins (p ++ [x ⟨p.length,hp⟩])) x := by
  intro i b hi
  by_cases hl : i.val < p.length
  · apply h i b; simpa [pins,List.getElem?_append_left hl] using hi
  · have hi' := i.isLt
    simp only [pins,List.getElem?_append_right (Nat.le_of_not_gt hl)] at hi
    by_cases he : i.val = p.length
    · have hf : i = ⟨p.length,hp⟩ := Fin.ext he
      simpa [hf] using hi
    · have ht : 1 ≤ i.val - p.length := by omega
      rw [List.getElem?_eq_none (by simpa only [List.length_cons,List.length_nil] using ht)] at hi
      cases hi

private theorem advance_preserves {k : ℕ} (R : (Fin k → Bool) → Prop) (ok : List Bool → Bool)
    (spec : ∀ p, ok p = true ↔ ∃ x, R x ∧ MatchesPins (pins p) x)
    (p : List Bool) (hp : p.length < k) (hex : ∃ x, R x ∧ MatchesPins (pins p) x) :
    ∃ x, R x ∧ MatchesPins (pins (advance ok p)) x := by
  cases he : ok (p ++ [false]) with
  | true => simpa only [advance,he,Bool.not_true] using (spec _).mp he
  | false =>
    obtain ⟨x,hx,hp'⟩ := hex
    have hExt := extend x p hp hp'
    cases hb : x ⟨p.length,hp⟩ with
    | true => exact ⟨x,hx,by simpa [advance,he,hb] using hExt⟩
    | false =>
      rw [hb] at hExt
      have hyes := (spec _).mpr ⟨x,hx,hExt⟩
      simp [he] at hyes

theorem grow_preserves {k : ℕ} (R : (Fin k → Bool) → Prop) (ok : List Bool → Bool)
    (spec : ∀ p, ok p = true ↔ ∃ x, R x ∧ MatchesPins (pins p) x)
    (n : ℕ) (p : List Bool) (hn : p.length+n ≤ k) (hex : ∃ x, R x ∧ MatchesPins (pins p) x) :
    ∃ x, R x ∧ MatchesPins (pins (grow ok n p)) x := by
  induction n generalizing p with
  | zero => exact hex
  | succ n ih =>
    apply ih (advance ok p) (by simp [advance]; omega)
    exact advance_preserves R ok spec p (by omega) hex

noncomputable def query (d N : ℕ) (p : List Bool) : Bool := correctedOracle
    (completionCount (ProductIs (d:=d) N)) (factorWord d 1 N N) (factorWord d N 1 N) (pins p)

noncomputable def answer (d N : ℕ) := bitsToNat (fun i : Fin d => (grow (query d N) (4*d) [])[i.val]?.getD false)

theorem answer_spec {d N : ℕ} (hN2 : 2 ≤ N) (hN : N < 2^d) (hc : ¬ N.Prime) :
    2 ≤ answer d N ∧ answer d N < N ∧ answer d N ∣ N := by
  let R := fun x : Fin (4*d) → Bool => ProductIs N x ∧ x ≠ factorWord d 1 N N ∧ x ≠ factorWord d N 1 N
  obtain ⟨ha,hb,hab⟩ := trivial_words_spec hN2 hN
  have hs : ∀ p, query d N p = true ↔ ∃ x, R x ∧ MatchesPins (pins p) x := fun p =>
    correctedOracle_spec (ProductIs N) _ (fun _ => rfl) _ _ ha hb hab (pins p)
  obtain ⟨x,hx⟩ := exists_nontrivial_product hN2 hN hc
  obtain ⟨y,hy,hm⟩ := grow_preserves R (query d N) hs (4*d) [] (by simp)
    ⟨x,hx,by simp [MatchesPins,pins]⟩
  have hv (i : Fin d) : (grow (query d N) (4*d) [])[i.val]?.getD false = inputA y i := by
    have hi : i.val < (grow (query d N) (4*d) []).length := by simp; omega
    rw [List.getElem?_eq_getElem hi,Option.getD_some]
    exact (hm ⟨i.val,by omega⟩ _ (List.getElem?_eq_getElem hi)).symm
  have he : answer d N = bitsToNat (inputA y) := congrArg bitsToNat (funext hv)
  rw [he]
  exact proper_divisor_of_nontrivial_product hN2 hN y hy
end DetDLP.S6BPrefix


