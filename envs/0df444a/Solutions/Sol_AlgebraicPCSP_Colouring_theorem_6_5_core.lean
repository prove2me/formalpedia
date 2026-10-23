-- Prove2me | solution 1 for AlgebraicPCSP.Colouring.theorem_6_5_core
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T23:40:11.711471+00:00
-- url     : https://prove2.me/submissions/c9f67a79-56b8-4a3e-8f76-731dbb0541aa

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Colouring_Minion
import Definitions.Def_AlgebraicPCSP_Colouring_Structures

set_option autoImplicit false

namespace B999C604

open PCSPBLPAff.Symmetric AlgebraicPCSP.Colouring

/-- A polymorphism of `(K_k, K_c)` separates tuples that differ in every coordinate. -/
theorem pol_ne {k c L : ℕ} {o : (Fin L → Fin k) → Fin c}
    (hpol : IsPolymorphism (Kgraph k) (Kgraph c) o) (u v : Fin L → Fin k)
    (huv : ∀ l, u l ≠ v l) : o u ≠ o v := by
  have h := hpol () (fun l => ![u l, v l]) (fun l => by
    simp only [Kgraph, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact huv l)
  simpa [Kgraph] using h

/-- Lemma 6.4 of BBKO: for `k ≥ 3`, `Pol(K_k, K_{2k-1})` has no Olšák function. The `2k`
values `o(a,a,a+1,a+1,a+1,a)` (`a ∈ ℤ_k`) and `o(d+2,d+1,d,d,d+2,d+1)` (`d ∈ ℤ_k`) are pairwise
distinct. -/
theorem no_olsak (m : ℕ) (o : (Fin 6 → Fin (m + 3)) → Fin (2 * (m + 3) - 1))
    (hpol : IsPolymorphism (Kgraph (m + 3)) (Kgraph (2 * (m + 3) - 1)) o)
    (hol : IsOlsak o) : False := by
  have h10 : (1 : Fin (m + 3)) ≠ 0 := by simp [Fin.ext_iff]
  have h20 : (2 : Fin (m + 3)) ≠ 0 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < m + 3 by omega)]
  have h21 : (2 : Fin (m + 3)) ≠ 1 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < m + 3 by omega)]
  have h112 : (1 : Fin (m + 3)) + 1 = 2 := Fin.ext (by
    simp [Fin.val_add, Nat.mod_eq_of_lt (show 2 < m + 3 by omega),
      Nat.mod_eq_of_lt (show 1 < m + 3 by omega)])
  have h11 : (1 : Fin (m + 3)) + 1 ≠ 0 := by rw [h112]; exact h20
  have h01 : (0 : Fin (m + 3)) ≠ 1 := fun h => h10 h.symm
  have h02 : (0 : Fin (m + 3)) ≠ 2 := fun h => h20 h.symm
  have h12 : (1 : Fin (m + 3)) ≠ 2 := fun h => h21 h.symm
  have hcross : ∀ a d : Fin (m + 3),
      o ![a, a, a + 1, a + 1, a + 1, a] ≠ o ![d + 2, d + 1, d, d, d + 2, d + 1] := by
    intro a d
    by_cases e0 : a = d
    · subst e0
      apply pol_ne hpol
      intro l
      fin_cases l <;> simp [h10, h20, h21, h12, h01, h02]
    by_cases e1 : a = d + 1
    · subst e1
      rw [(hol _ _).1]
      apply pol_ne hpol
      intro l
      fin_cases l <;> simp [add_assoc, h112, h10, h20, h21, h12, h01, h02, h11]
    · rw [(hol _ _).1, (hol _ _).2]
      have e1' : a + 1 ≠ d + 2 := by
        intro h
        apply e1
        have h' : a + 1 = d + 1 + 1 := by rw [h, add_assoc, h112]
        exact add_right_cancel h'
      apply pol_ne hpol
      intro l
      fin_cases l <;> simp [e0, e1, e1']
  let Φ : Fin (m + 3) ⊕ Fin (m + 3) → Fin (2 * (m + 3) - 1) :=
    Sum.elim (fun a => o ![a, a, a + 1, a + 1, a + 1, a])
      (fun d => o ![d + 2, d + 1, d, d, d + 2, d + 1])
  have hinj : Function.Injective Φ := by
    intro p q hpq
    rcases p with a | a <;> rcases q with b | b
    · by_contra hab
      have hab' : a ≠ b := fun h => hab (by rw [h])
      refine pol_ne hpol _ _ ?_ hpq
      intro l
      fin_cases l <;> simp [hab']
    · exact absurd hpq (hcross a b)
    · exact absurd hpq.symm (hcross b a)
    · by_contra hab
      have hab' : a ≠ b := fun h => hab (by rw [h])
      refine pol_ne hpol _ _ ?_ hpq
      intro l
      fin_cases l <;> simp [hab']
  have := Fintype.card_le_of_injective Φ hinj
  simp only [Fintype.card_sum, Fintype.card_fin] at this
  omega

/-- The Olšák coordinate of a not-all-equal column `(p, q, r) ∈ {0,1}³`: the position whose
entries in the three Olšák rows are `x` exactly in the rows `i` with column entry `0`. -/
def pat : Fin 2 → Fin 2 → Fin 2 → Fin 6 := ![![![0, 0], ![1, 5]], ![![2, 4], ![3, 0]]]

theorem pat_spec {k : ℕ} (p q r : Fin 2) (hpqr : ¬ (p = q ∧ q = r)) (a b : Fin k) :
    (![a, a, b, b, b, a] : Fin 6 → Fin k) (pat p q r) = (if p = 0 then a else b) ∧
    (![a, b, a, b, a, b] : Fin 6 → Fin k) (pat p q r) = (if q = 0 then a else b) ∧
    (![b, a, a, a, b, b] : Fin 6 → Fin k) (pat p q r) = (if r = 0 then a else b) := by
  fin_cases p <;> fin_cases q <;> fin_cases r <;> simp_all [pat]

end B999C604

open AlgebraicPCSP.Colouring PCSPBLPAff.Symmetric in
theorem solution (k : ℕ) (hk : 3 ≤ k) :
    ∃ (K : ℕ) (hK : 2 ≤ K)
      (ξ : (n : ℕ) → ((Fin n → Fin k) → Fin (2 * k - 1)) → ((Fin n → Fin 2) → Fin K)),
      IsMinionHom (Pol (Kgraph k) (Kgraph (2 * k - 1)) (Kgraph_template (by omega)))
        (HMinion K hK) ξ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have hK : 2 ≤ Fintype.card (Fin (m + 3) → Fin (m + 3) → Fin (2 * (m + 3) - 1)) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    have h2 := Nat.le_self_pow (n := m + 3) (by omega) (2 * (m + 3) - 1)
    have h3 := Nat.le_self_pow (n := m + 3) (by omega) ((2 * (m + 3) - 1) ^ (m + 3))
    omega
  let e := Fintype.equivFin (Fin (m + 3) → Fin (m + 3) → Fin (2 * (m + 3) - 1))
  refine ⟨_, hK, fun n f x => e (fun a b => f (fun l => if x l = 0 then a else b)), ?_, ?_⟩
  · rintro n f ⟨hn, hf⟩
    refine ⟨hn, ?_⟩
    intro R M hM
    have hNAE : ∀ l, ¬ (M l 0 = M l 1 ∧ M l 1 = M l 2) := fun l => hM l
    change ¬ (_ ∧ _)
    rintro ⟨h01, h12⟩
    have h01' : (fun a b => f (fun l => if M l 0 = 0 then a else b)) =
        (fun a b => f (fun l => if M l 1 = 0 then a else b)) := e.injective h01
    have h12' : (fun a b => f (fun l => if M l 1 = 0 then a else b)) =
        (fun a b => f (fun l => if M l 2 = 0 then a else b)) := e.injective h12
    let o : (Fin 6 → Fin (m + 3)) → Fin (2 * (m + 3) - 1) :=
      fun y => f (fun l => y (B999C604.pat (M l 0) (M l 1) (M l 2)))
    apply B999C604.no_olsak m o
    · intro R' M' hM'
      exact hf R' (fun l => M' (B999C604.pat (M l 0) (M l 1) (M l 2))) (fun l => hM' _)
    · intro x y
      have r0 : o ![x, x, y, y, y, x] = f (fun l => if M l 0 = 0 then x else y) := by
        simp only [o]
        congr 1
        funext l
        exact (B999C604.pat_spec _ _ _ (hNAE l) x y).1
      have r1 : o ![x, y, x, y, x, y] = f (fun l => if M l 1 = 0 then x else y) := by
        simp only [o]
        congr 1
        funext l
        exact (B999C604.pat_spec _ _ _ (hNAE l) x y).2.1
      have r2 : o ![y, x, x, x, y, y] = f (fun l => if M l 2 = 0 then x else y) := by
        simp only [o]
        congr 1
        funext l
        exact (B999C604.pat_spec _ _ _ (hNAE l) x y).2.2
      refine ⟨?_, ?_⟩
      · rw [r0, r1]
        exact congrFun (congrFun h01' x) y
      · rw [r1, r2]
        exact congrFun (congrFun h12' x) y
  · intro m' n π g _
    rfl
