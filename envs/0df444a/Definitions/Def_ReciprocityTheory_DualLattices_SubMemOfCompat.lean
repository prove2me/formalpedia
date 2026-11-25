-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
-- name    : ReciprocityTheory_DualLattices_SubMemOfCompat
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T16:28:33.174532+00:00
-- url     : https://prove2.me/theorems/59e787c7-361b-4035-a515-2f478a42dc33
-- title:
--   Sub Mem Of Compat
-- statement:
--   Definitions and structural lemmas for Sub Mem Of Compat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemOfCompat.lean

import Definitions.Def_ReciprocityTheory_DualLattices_AinfTower
import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
namespace ReciprocityTheory.PGsh
namespace Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
def r'Alg (n : ℕ) : R'n p O ε (n + 1) →ₐ[R0 p O ε] R'n p O ε n :=
  Ideal.Quotient.liftₐ _ (Ideal.Quotient.mkₐ (R0 p O ε) _) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton'.2 ⟨b * p, by ring⟩)
def rRing (n : ℕ) : Rn p O (n + 1) →+* Rn p O n :=
  Ideal.Quotient.lift (span {(p : O) ^ (n + 1 + 1)})
    (Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton'.2 ⟨b * p, by ring⟩)
def rAlg (n : ℕ) : (LR p O hv ε hε (n + 1) : Type) →ₐ[R0 p O ε] (LR p O hv ε hε n : Type) :=
  { toRingHom := rRing p O n
    commutes' := fun _ => rfl }
lemma r'Alg_surj (n : ℕ) : Function.Surjective (r'Alg p O ε n) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩
lemma rAlg_surj (n : ℕ) : Function.Surjective (rAlg p O hv ε hε n) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩
lemma sub_mem_of_compat (f : ℕ → O)
    (hf : ∀ n, f (n + 1) - f n ∈ span {(p : O) ^ (n + 1)}) :
    ∀ m k, f (m + k) - f m ∈ span {(p : O) ^ m} := by
  intro m k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : f (m + k + 1) - f (m + k) ∈ span {(p : O) ^ m} := by
      have h := hf (m + k)
      rw [Ideal.mem_span_singleton'] at h ⊢
      obtain ⟨a, ha⟩ := h
      exact ⟨a * p ^ (k + 1), by rw [← ha, mul_assoc, ← pow_add]; ring_nf⟩
    have : f (m + (k + 1)) - f m = (f (m + k + 1) - f (m + k)) + (f (m + k) - f m) := by
      rw [← add_assoc]; ring
    rw [this]
    exact Ideal.add_mem _ h1 ih
lemma complete_O (x : ∀ n, (Rn p O n)) (hx : ∀ n, rRing p O n (x (n + 1)) = x n) :
    ∃ a : O, ∀ n, Ideal.Quotient.mk (span {(p : O) ^ (n + 1)}) a = x n := by
  choose f hf using fun n => Ideal.Quotient.mk_surjective (x n)
  have hc : ∀ n, f (n + 1) - f n ∈ span {(p : O) ^ (n + 1)} := by
    intro n
    have h := hx n
    rw [← hf (n + 1), ← hf n, rRing, Ideal.Quotient.lift_mk, Ideal.Quotient.eq] at h
    exact h
  have hsm : ∀ m, (span {(p : O)} ^ m • ⊤ : Submodule O O) = span {(p : O) ^ m} := by
    intro m
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := span {(p : O)}) (M := O) inferInstance
    (f := f) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have := sub_mem_of_compat p O f hc m k
      rw [← neg_sub]
      exact (Ideal.neg_mem_iff _).2 this)
  refine ⟨L, fun n => ?_⟩
  rw [← hf n, Ideal.Quotient.eq]
  have h1 := hL (n + 1)
  rw [SModEq.sub_mem, hsm] at h1
  have h2 := hc n
  have : L - f n = (f (n + 1) - f n) - (f (n + 1) - L) := by ring
  rw [this]
  exact Ideal.sub_mem _ h2 h1
def ainfTowerL : ATowerL (R0 p O ε) p where
  toATower := ainfTower p O hv ε hε
  r' n := ⟨r'Alg p O ε n, TowerExample.isLocalHom_of_surj _ (r'Alg_surj p O ε n)⟩
  r n := ⟨rAlg p O hv ε hε n, TowerExample.isLocalHom_of_surj _ (rAlg_surj p O hv ε hε n)⟩
  r_π n x := by
    obtain ⟨x0, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x0
    rfl
  r_q n x := rfl
  r'_ξ n := rfl
  complete x hx := complete_O p O x hx
end Ainf
end ReciprocityTheory.PGsh


