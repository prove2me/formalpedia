-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:21:11.18129+00:00
-- url     : https://prove2.me/theorems/b58f6572-6632-42a1-a584-e09aa0878084
-- title:
--   Count Left Inv Seq Alternating Word Even
-- statement:
--   Definitions and structural lemmas for Count Left Inv Seq Alternating Word Even, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/CountLeftInvSeqAlternatingWordEven.lean

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_StatementW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace Formalism.CohomologicalDescent
open CoxeterSystem List
namespace ReflectionWords
variable {B : Type*} {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
def reflStep (g : W) (p : W × ZMod 2) : W × ZMod 2 :=
  (g * p.1 * g, p.2 + if p.1 = g then 1 else 0)
lemma zmod_two_add_self (a : ZMod 2) : a + a = 0 := by fin_cases a <;> decide
lemma reflStep_involutive {g : W} (hg : g * g = 1) : Function.Involutive (reflStep g) := by
  rintro ⟨w, e⟩
  have h1 : g * (g * w * g) * g = w := by
    calc g * (g * w * g) * g = (g * g) * w * (g * g) := by group
    _ = w := by simp [hg]
  have h2 : (g * w * g = g) ↔ (w = g) := by
    constructor
    · intro h
      calc w = g * (g * w * g) * g := h1.symm
      _ = g := by rw [h, hg, one_mul]
    · rintro rfl; rw [hg, one_mul]
  simp only [reflStep, h1, h2, Prod.mk.injEq, true_and]
  rw [add_assoc, zmod_two_add_self, add_zero]
def reflPerm (i : B) : Equiv.Perm (W × ZMod 2) :=
  Function.Involutive.toPerm _ (reflStep_involutive (cs.simple_mul_simple_self i))
lemma prod_map_reflPerm (ω : List B) (w : W) (e : ZMod 2) :
    (ω.map (reflPerm cs)).prod (w, e) =
      (cs.wordProd ω * w * (cs.wordProd ω)⁻¹, e + ((cs.rightInvSeq ω).count w : ZMod 2)) := by
  induction ω with
  | nil => simp [rightInvSeq]
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih]
    simp only [reflPerm, Function.Involutive.coe_toPerm, reflStep, rightInvSeq, List.count_cons,
      wordProd_cons, mul_inv_rev, inv_simple]
    have key : (cs.wordProd ω)⁻¹ * cs.simple i * cs.wordProd ω = w ↔
        cs.wordProd ω * w * (cs.wordProd ω)⁻¹ = cs.simple i := by
      constructor
      · rintro rfl; group
      · intro h; rw [← h]; group
    refine Prod.ext ?_ ?_
    · simp only; group
    · by_cases h : cs.wordProd ω * w * (cs.wordProd ω)⁻¹ = cs.simple i
      · have h' := key.mpr h
        simp [h, h', add_assoc]
      · have h' : ¬ (cs.wordProd ω)⁻¹ * cs.simple i * cs.wordProd ω = w := fun hh => h (key.mp hh)
        simp [h, h']
lemma prod_map_alternatingWord {G : Type*} [Monoid G] (f : B → G) (i i' : B) (p : ℕ) :
    ((alternatingWord i i' (2 * p)).map f).prod = (f i * f i') ^ p := by
  induction p with
  | zero => simp [alternatingWord]
  | succ p ih =>
    have h : alternatingWord i i' (2 * (p + 1)) = i :: i' :: alternatingWord i i' (2 * p) := by
      rw [show 2 * (p + 1) = 2 * p + 1 + 1 by ring, alternatingWord_succ', alternatingWord_succ']
      simp
    rw [h]
    simp [ih, pow_succ', mul_assoc]
lemma reverse_alternatingWord (i i' : B) (p : ℕ) :
    (alternatingWord i i' (2 * p)).reverse = alternatingWord i' i (2 * p) := by
  induction p with
  | zero => simp [alternatingWord]
  | succ p ih =>
    have h : alternatingWord i i' (2 * (p + 1)) = i :: i' :: alternatingWord i i' (2 * p) := by
      rw [show 2 * (p + 1) = 2 * p + 1 + 1 by ring, alternatingWord_succ', alternatingWord_succ']
      simp
    rw [h, show 2 * (p + 1) = 2 * p + 1 + 1 by ring, alternatingWord_succ, alternatingWord_succ]
    simp [ih]
lemma count_leftInvSeq_alternatingWord_even (i i' : B) (w : W) :
    Even ((cs.leftInvSeq (alternatingWord i' i (2 * M i i'))).count w) := by
  set m := M i i' with hm
  set L := cs.leftInvSeq (alternatingWord i' i (2 * m)) with hL
  have hlen : L.length = 2 * m := by simp [L]
  have hper : ∀ k (hk : k < m), L[m + k]'(by omega) = L[k]'(by omega) := by
    intro k hk
    simp only [L]
    rw [cs.getElem_leftInvSeq_alternatingWord i' i m (m + k) (by omega),
      cs.getElem_leftInvSeq_alternatingWord i' i m k (by omega),
      cs.prod_alternatingWord_eq_mul_pow, cs.prod_alternatingWord_eq_mul_pow]
    have e1 : ¬ Even (2 * (m + k) + 1) := by simp
    have e2 : ¬ Even (2 * k + 1) := by simp
    simp only [e1, e2, if_false]
    rw [show (2 * (m + k) + 1) / 2 = m + k by omega, show (2 * k + 1) / 2 = k by omega, pow_add,
      hm, cs.simple_mul_simple_pow, one_mul]
  have hsplit : L = L.take m ++ L.take m := by
    conv_lhs => rw [← List.take_append_drop m L]
    congr 1
    apply List.ext_getElem
    · simp [hlen]; omega
    · intro k h1 h2
      simp only [List.getElem_drop, List.getElem_take]
      exact hper k (by simp [hlen] at h2; omega)
  rw [hsplit, List.count_append]
  exact ⟨_, rfl⟩
lemma isLiftable_reflPerm : M.IsLiftable (reflPerm cs) := by
  intro i i'
  rw [← prod_map_alternatingWord]
  refine Equiv.ext fun p => ?_
  obtain ⟨w, e⟩ := p
  rw [prod_map_reflPerm]
  have h1 : cs.wordProd (alternatingWord i i' (2 * M i i')) = 1 := by
    rw [wordProd, prod_map_alternatingWord, cs.simple_mul_simple_pow]
  have h2 : ((cs.rightInvSeq (alternatingWord i i' (2 * M i i'))).count w : ZMod 2) = 0 := by
    rw [← List.count_reverse, ← leftInvSeq_reverse, reverse_alternatingWord]
    obtain ⟨r, hr⟩ := count_leftInvSeq_alternatingWord_even cs i i' w
    rw [hr]; push_cast; exact zmod_two_add_self _
  simp [h1, h2]
def act : W →* Equiv.Perm (W × ZMod 2) := cs.lift ⟨reflPerm cs, isLiftable_reflPerm cs⟩
end ReflectionWords
universe u v
namespace ReflectionWords
def transp (n : ℕ) : Finset (Equiv.Perm (Fin (n + 1))) :=
  ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2)).image
    (fun p => Equiv.swap p.1 p.2)
end ReflectionWords
end Formalism.CohomologicalDescent


