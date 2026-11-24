-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CommutatorAdjointHolds
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CommutatorAdjointHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:14.399428+00:00
-- url     : https://prove2.me/theorems/4d41e88d-66d3-48e8-a2a8-89fdb57bbe79
-- title:
--   Commutator Adjoint Holds
-- statement:
--   Definitions and structural lemmas for Commutator Adjoint Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS Polynomial
namespace PositivityTheory.CW
namespace GradedNormalNilpotent
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
structure Hyp (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) : Prop where
  mono : ∀ j k, j ≤ k → U E j ≤ U E k
  one : (1 : Module.End ℂ V) ∈ U E 0
  e1 : ∀ a b, E a b ∈ U E 1
  mul : ∀ j k, ∀ x ∈ U E j, ∀ y ∈ U E k, x * y ∈ U E (j + k)
  comm : ∀ j k, ∀ x ∈ U E j, ∀ y ∈ U E k, x * y - y * x ∈ U E (j + k - 1)
  zmem : ∀ a b, Z ε E a b ∈ U E 2
variable (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
def Jk : ℕ → Submodule ℂ (Module.End ℂ V)
  | 0 => ⊥
  | 1 => U E 0
  | k + 2 => {
      carrier := {x | ∃ u ∈ U E (k + 1), ∃ w : Fin n → Fin n → Module.End ℂ V,
        (∀ c d, w c d ∈ U E k) ∧ x = u + ∑ c, ∑ d, w c d * Z ε E c d}
      add_mem' := by
        rintro _ _ ⟨u, hu, w, hw, rfl⟩ ⟨u', hu', w', hw', rfl⟩
        refine ⟨u + u', add_mem hu hu', w + w', fun c d => add_mem (hw c d) (hw' c d), ?_⟩
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]; abel
      zero_mem' := ⟨0, zero_mem _, 0, fun _ _ => zero_mem _, by simp⟩
      smul_mem' := by
        rintro r _ ⟨u, hu, w, hw, rfl⟩
        refine ⟨r • u, Submodule.smul_mem _ r hu, r • w, fun c d => Submodule.smul_mem _ r (hw c d), ?_⟩
        simp [smul_add, Finset.smul_sum] }
lemma mem_Jk_succ_succ (k : ℕ) (x : Module.End ℂ V) : x ∈ Jk ε E (k + 2) ↔ ∃ u ∈ U E (k + 1),
    ∃ w : Fin n → Fin n → Module.End ℂ V, (∀ c d, w c d ∈ U E k) ∧ x = u + ∑ c, ∑ d, w c d * Z ε E c d :=
  Iff.rfl
lemma U_le_Jk (k : ℕ) : U E k ≤ Jk ε E (k + 1) := by
  rcases k with _ | k
  · exact le_rfl
  · intro x hx
    exact (mem_Jk_succ_succ ε E k x).2 ⟨x, hx, 0, fun _ _ => zero_mem _, by simp⟩
lemma U0 {x : Module.End ℂ V} (hx : x ∈ U E 0) : ∃ c : ℂ, x = c • (1 : Module.End ℂ V) := by
  have : U E 0 ≤ Submodule.span ℂ {(1 : Module.End ℂ V)} := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact Submodule.subset_span rfl
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (this hx)
  exact ⟨c, hc.symm⟩
variable {ε E}
lemma memJ_left (h : Hyp ε E) (i j : ℕ) {x y : Module.End ℂ V} (hx : x ∈ U E i) (hy : y ∈ Jk ε E j) :
    x * y ∈ Jk ε E (i + j) := by
  rcases j with _ | _ | j
  · have : y = 0 := (Submodule.mem_bot ℂ).mp hy
    simp [this]
  · exact U_le_Jk ε E i (by simpa using h.mul i 0 x hx y hy)
  · obtain ⟨u, hu, w, hw, rfl⟩ := (mem_Jk_succ_succ ε E j y).1 hy
    rw [show i + (j + 2) = (i + j) + 2 by omega, mem_Jk_succ_succ]
    refine ⟨x * u, ?_, fun c d => x * w c d, fun c d => h.mul i j x hx _ (hw c d), ?_⟩
    · have := h.mul i (j + 1) x hx u hu; rwa [← add_assoc] at this
    · simp [mul_add, Finset.mul_sum, mul_assoc]
lemma memJ_right (h : Hyp ε E) (i j : ℕ) {x y : Module.End ℂ V} (hy : y ∈ Jk ε E j) (hx : x ∈ U E i) :
    y * x ∈ Jk ε E (j + i) := by
  rcases j with _ | _ | j
  · have : y = 0 := (Submodule.mem_bot ℂ).mp hy
    simp [this]
  · rw [add_comm]; exact U_le_Jk ε E i (by simpa using h.mul 0 i y hy x hx)
  · obtain ⟨u, hu, w, hw, rfl⟩ := (mem_Jk_succ_succ ε E j y).1 hy
    rw [show j + 2 + i = (j + i) + 2 by omega, mem_Jk_succ_succ]
    refine ⟨u * x + ∑ c, ∑ d, w c d * (Z ε E c d * x - x * Z ε E c d), ?_, fun c d => w c d * x,
      fun c d => h.mul j i _ (hw c d) x hx, ?_⟩
    · refine add_mem ?_ (Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun d _ => ?_)
      · have := h.mul (j + 1) i u hu x hx; rwa [show j + 1 + i = j + i + 1 by omega] at this
      · have := h.mul j (2 + i - 1) _ (hw c d) _ (h.comm 2 i _ (h.zmem c d) x hx)
        rwa [show j + (2 + i - 1) = j + i + 1 by omega] at this
    · simp only [add_mul, Finset.sum_mul, mul_sub, mul_assoc, Finset.sum_sub_distrib]; abel
variable (ε E) in

def Rr (h : Hyp ε E) : Subalgebra ℂ (Module.End ℂ V)[X] where
  carrier := {f | ∀ k, f.coeff k ∈ U E k}
  mul_mem' {f g} hf hg k := by
    rw [coeff_mul]
    exact Submodule.sum_mem _ fun x hx => by
      have := h.mul _ _ _ (hf x.1) _ (hg x.2); rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hx] at this
  add_mem' {f g} hf hg k := by rw [coeff_add]; exact add_mem (hf k) (hg k)
  algebraMap_mem' r k := by
    rw [Polynomial.algebraMap_apply, coeff_C]
    split_ifs with hk
    · subst hk; rw [Algebra.algebraMap_eq_smul_one]; exact Submodule.smul_mem _ r h.one
    · exact zero_mem _
variable (ε E) in

def inJ (f : (Module.End ℂ V)[X]) : Prop := ∀ k, f.coeff k ∈ Jk ε E k
lemma inJ_mul_right (h : Hyp ε E) {x g : (Module.End ℂ V)[X]} (hx : inJ ε E x) (hg : g ∈ Rr ε E h) :
    inJ ε E (x * g) := fun k => by
  rw [coeff_mul]
  exact Submodule.sum_mem _ fun p hp => by
    have := memJ_right h _ _ (hx p.1) (hg p.2); rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hp] at this
lemma inJ_mul_left (h : Hyp ε E) {x g : (Module.End ℂ V)[X]} (hx : inJ ε E x) (hg : g ∈ Rr ε E h) :
    inJ ε E (g * x) := fun k => by
  rw [coeff_mul]
  exact Submodule.sum_mem _ fun p hp => by
    have := memJ_left h _ _ (hg p.1) (hx p.2); rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hp] at this
lemma inJ_comm (h : Hyp ε E) {f g : (Module.End ℂ V)[X]} (hf : f ∈ Rr ε E h) (hg : g ∈ Rr ε E h) :
    inJ ε E (f * g - g * f) := fun k => by
  have e : (g * f).coeff k = ∑ x ∈ antidiagonal k, g.coeff x.2 * f.coeff x.1 := by
    rw [coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]; rfl
  rw [coeff_sub, e, coeff_mul, ← Finset.sum_sub_distrib]
  rcases k with _ | k
  · obtain ⟨a, ha⟩ := U0 E (hf 0)
    obtain ⟨b, hb⟩ := U0 E (hg 0)
    simp [ha, hb, smul_smul, mul_comm]
  · refine U_le_Jk ε E k (Submodule.sum_mem _ fun x hx => ?_)
    have := h.comm _ _ _ (hf x.1) _ (hg x.2)
    rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hx, Nat.add_sub_cancel] at this
variable (ε E) in

def con (h : Hyp ε E) : RingCon (Rr ε E h) where
  r f g := inJ ε E ((f : (Module.End ℂ V)[X]) - g)
  iseqv := ⟨fun f k => by simp,
    fun {f g} hfg k => by rw [← neg_sub, coeff_neg]; exact neg_mem (hfg k),
    fun {f g l} h1 h2 k => by
      have := add_mem (h1 k) (h2 k); rwa [← coeff_add, sub_add_sub_cancel] at this⟩
  add' {a b c d} h1 h2 k := by
    have := add_mem (h1 k) (h2 k)
    simp only [Subalgebra.coe_add, coeff_sub, coeff_add] at *
    convert this using 1; abel
  mul' {a b c d} h1 h2 k := by
    have e : ((a * c : Rr ε E h) : (Module.End ℂ V)[X]) - (b * d : Rr ε E h) =
        ((a : (Module.End ℂ V)[X]) - b) * c + (b : (Module.End ℂ V)[X]) * ((c : (Module.End ℂ V)[X]) - d) := by
      simp only [Subalgebra.coe_mul, sub_mul, mul_sub]; abel
    rw [e, coeff_add]
    exact add_mem (inJ_mul_right h h1 c.2 k) (inJ_mul_left h h2 b.2 k)
variable (ε E) in

abbrev Q (h : Hyp ε E) := (con ε E h).Quotient
instance instCR (h : Hyp ε E) : CommRing (Q ε E h) :=
  { (inferInstance : Ring (Q ε E h)) with
    mul_comm := by
      intro x y
      refine Quotient.inductionOn₂' x y fun f g => ?_
      change ((f : Q ε E h) * g) = g * f
      rw [← RingCon.coe_mul, ← RingCon.coe_mul, RingCon.eq]
      show inJ ε E (((f * g : Rr ε E h) : (Module.End ℂ V)[X]) - (g * f : Rr ε E h))
      simp only [Subalgebra.coe_mul]
      exact inJ_comm h f.2 g.2 }
instance instQA (h : Hyp ε E) : Algebra ℚ (Q ε E h) := Algebra.compHom _ (algebraMap ℚ ℂ)
example (h : Hyp ε E) (A4' : A4) (N : Matrix (Fin n) (Fin n) (Q ε E h)) (hN : ∀ k, (N ^ (k + 1)).trace = 0) :
    N ^ n = 0 := A4' (Q ε E h) n N hN
variable (h : Hyp ε E)
def L (j : ℕ) (x : Module.End ℂ V) (hx : x ∈ U E j) : Rr ε E h :=
  ⟨C x * X ^ j, fun k => by
    rw [coeff_C_mul_X_pow]; split_ifs with hk
    · subst hk; exact hx
    · exact zero_mem _⟩
def MR (M : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (j : ℕ) (hM : ∀ a b, M a b ∈ U E j) :
    Matrix (Fin n) (Fin n) (Rr ε E h) := fun a b => L h j (M a b) (hM a b)
abbrev psi : Rr ε E h →+* Q ε E h := RingCon.mk' (con ε E h)
end GradedNormalNilpotent
end PositivityTheory.CW
end


