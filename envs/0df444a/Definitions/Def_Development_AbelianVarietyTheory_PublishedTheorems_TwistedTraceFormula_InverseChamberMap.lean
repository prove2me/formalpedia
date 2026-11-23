-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_InverseChamberMap
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_InverseChamberMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:17.938617+00:00
-- url     : https://prove2.me/theorems/d04dc217-2af3-4597-b182-a0e93806eb08
-- title:
--   Inverse Chamber Map
-- statement:
--   Definitions and structural lemmas for Inverse Chamber Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/InverseChamberMap.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace ContDiff Classical
namespace GlobalTheory.Chamber
variable {k : ℕ}
abbrev A0 (k : ℕ) : Type := EuclideanSpace ℝ (Fin k)
abbrev SV (k : ℕ) : Type := Fin k → SignType
def vec (u : SV k) : A0 k := WithLp.toLp 2 fun i => (u i : ℝ)
def Below (u u' : SV k) : Prop := ∀ i, u i ≠ 0 → u' i = u i
def IsPar (P : Finset (SV k)) : Prop := 0 ∉ P ∧ ∀ u ∈ P, ∀ u' ∈ P, Below u u' ∨ Below u' u
def aP (P : Finset (SV k)) : Submodule ℝ (A0 k) := Submodule.span ℝ (vec '' (P : Set (SV k)))
def pr (P : Finset (SV k)) : A0 k →L[ℝ] A0 k := (aP P).starProjection
def IsLevi (𝔞 : Submodule ℝ (A0 k)) : Prop := ∃ P, IsPar P ∧ aP P = 𝔞
def aMQ (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) : Submodule ℝ (A0 k) := 𝔞 ⊓ (aP Q)ᗮ
def parF (𝔞 : Submodule ℝ (A0 k)) (R : Finset (SV k)) : Finset (Finset (SV k)) :=
  univ.filter fun Q => IsPar Q ∧ aP Q ≤ 𝔞 ∧ R ⊆ Q
def parP (𝔞 : Submodule ℝ (A0 k)) (R : Finset (SV k)) : Finset (Finset (SV k)) :=
  univ.filter fun P => IsPar P ∧ aP P = 𝔞 ∧ R ⊆ P
def between (P R : Finset (SV k)) : Finset (Finset (SV k)) := P.powerset.filter (R ⊆ ·)
def wt (Q : Finset (SV k)) (u : SV k) : A0 k := vec u - pr Q (vec u)
def rt (P : Finset (SV k)) (u : SV k) : A0 k := wt (P.erase u) u
def tau (P Q : Finset (SV k)) (H : A0 k) : ℝ := if ∀ u ∈ P \ Q, 0 < ⟪rt P u, H⟫_ℝ then 1 else 0
def tauHat (P Q : Finset (SV k)) (H : A0 k) : ℝ := if ∀ u ∈ P \ Q, 0 < ⟪wt Q u, H⟫_ℝ then 1 else 0
def gamP (P R : Finset (SV k)) (X H : A0 k) : ℝ :=
  ∑ S ∈ between P R, (-1) ^ (S \ R).card * tau P S H * tauHat S R (H - X)
def gamM (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) (X : Finset (SV k) → A0 k) (H : A0 k) : ℝ :=
  ∑ P ∈ parF 𝔞 Q, (-1) ^ (P \ Q).card * tauHat P Q (H - X P)
def IsOrth (𝔞 : Submodule ℝ (A0 k)) (X : Finset (SV k) → A0 k) : Prop :=
  ∀ P ∈ parF 𝔞 ∅, ∀ Q ⊆ P, X Q = pr Q (X P)
def IsGMFam (𝔞 : Submodule ℝ (A0 k)) (c : Finset (SV k) → A0 k → ℂ) : Prop :=
  ∀ P ∈ parF 𝔞 ∅, ContDiff ℝ ∞ (c P) ∧ ∀ Q ⊆ P, ∀ l, c Q l = c P (pr Q l)
def eL (l H : A0 k) : ℂ := Complex.exp (Complex.I * (⟪l, H⟫_ℝ : ℝ))
def expFam (X : Finset (SV k) → A0 k) : Finset (SV k) → A0 k → ℂ := fun P l => eL l (X P)
def epsOf (s : Finset (SV k)) (b : SV k → A0 k) (l : A0 k) : ℂ :=
  (√(Matrix.gram ℝ fun u : s => b u).det : ℝ) * ∏ u ∈ s, (Complex.I * (⟪l, b u⟫_ℝ : ℝ))⁻¹
def eps (P Q : Finset (SV k)) : A0 k → ℂ := epsOf (P \ Q) (rt P)
def epsHat (P Q : Finset (SV k)) : A0 k → ℂ := epsOf (P \ Q) (wt Q)
def generic (k : ℕ) : Set (A0 k) := {l | ∀ P, IsPar P → ∀ Q ⊆ P, ∀ u ∈ P \ Q, ⟪l, wt Q u⟫_ℝ ≠ 0}
def sumM (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) (c : Finset (SV k) → A0 k → ℂ) (l : A0 k) : ℂ :=
  ∑ P ∈ parP 𝔞 Q, eps P Q l * c P l
def sumP (P R : Finset (SV k)) (c : Finset (SV k) → A0 k → ℂ) (l : A0 k) : ℂ :=
  ∑ S ∈ between P R, (-1) ^ (P \ S).card * epsHat P S l * eps S R l * c S l
def cM (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) (c : Finset (SV k) → A0 k → ℂ) : A0 k → ℂ :=
  extendFrom (generic k) (sumM 𝔞 Q c)
def cP (P R : Finset (SV k)) (c : Finset (SV k) → A0 k → ℂ) : A0 k → ℂ := extendFrom (generic k) (sumP P R c)
def stdVec (j : Fin k) : SV k := fun i => if i ≤ j then 1 else 0
def stdPar (J : Finset (Fin k)) : Finset (SV k) := J.image stdVec
def invSV (π : Equiv.Perm (Fin k)) (ε : Fin k → SignTypeˣ) (u : SV k) : SV k := fun i => ε i * u (π i)
def inverseChamberMap (π : Equiv.Perm (Fin k)) (ε : Fin k → SignTypeˣ) (H : A0 k) : A0 k :=
  WithLp.toLp 2 fun i => ((ε i : SignType) : ℝ) * H (π i)
def weylPar (π : Equiv.Perm (Fin k)) (ε : Fin k → SignTypeˣ) : Finset (SV k) := (stdPar univ).image (invSV π ε)
def Regular (c : ℝ) (T : A0 k) : Prop := (∀ i j, i < j → c ≤ T i - T j) ∧ ∀ i, c ≤ T i
theorem mem_parF {𝔞 : Submodule ℝ (A0 k)} {R Q : Finset (SV k)} : Q ∈ parF 𝔞 R ↔ IsPar Q ∧ aP Q ≤ 𝔞 ∧ R ⊆ Q := by
  simp [parF]
theorem exists_top {α : Type} {r : α → α → Prop} (ht : ∀ a b c, r a b → r b c → r a c) (A : Finset α) (hA : A.Nonempty)
    (h : ∀ a ∈ A, ∀ b ∈ A, r a b ∨ r b a) : ∃ a ∈ A, ∀ b ∈ A, r b a := by
  induction hA using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, mem_singleton_self a, fun b hb => (mem_singleton.1 hb).symm ▸ or_self_iff.1 (h a (by simp) a (by simp))⟩
  | cons a s ha hs ih =>
    obtain ⟨b, hb, hb'⟩ := ih fun x hx y hy => h x (mem_cons_of_mem hx) y (mem_cons_of_mem hy)
    rcases h a (mem_cons_self _ _) b (mem_cons_of_mem hb) with e | e
    · exact ⟨b, mem_cons_of_mem hb, fun c hc => (mem_cons.1 hc).elim (· ▸ e) (hb' c)⟩
    · exact ⟨a, mem_cons_self _ _, fun c hc => (mem_cons.1 hc).elim
        (·.symm ▸ or_self_iff.1 (h a (mem_cons_self _ _) a (mem_cons_self _ _))) fun hc => ht _ _ _ (hb' c hc) e⟩
theorem IsPar.vec_notMem {P : Finset (SV k)} (h : IsPar P) {u : SV k} (hu : u ∈ P) : vec u ∉ aP (P.erase u) := by
  obtain ⟨a, ha, hA⟩ := exists_top (r := Below) (fun a b c h h' i hi => (h' i (h i hi ▸ hi)).trans (h i hi))
    (insert 0 ((P.erase u).filter (Below · u))) (insert_nonempty _ _) fun a ha b hb => by
      rcases mem_insert.1 ha with rfl | ha
      · exact .inl fun i hi => (hi rfl).elim
      rcases mem_insert.1 hb with rfl | hb
      · exact .inr fun i hi => (hi rfl).elim
      exact h.2 a (mem_of_mem_erase (mem_filter.1 ha).1) b (mem_of_mem_erase (mem_filter.1 hb).1)
  have key : ∀ a b : SV k, Below a b → a ≠ b → ∃ i, b i ≠ 0 ∧ a i = 0 := fun a b hab hne => by
    by_contra! hn
    exact hne (funext fun i => by
      by_cases e : b i = 0
      · by_contra e'; exact e' ((hab i (e ▸ e')).symm)
      · exact (hab i (hn i e)).symm)
  obtain ⟨i, hi, hai⟩ := key a u (by
      rcases mem_insert.1 ha with rfl | ha
      · exact fun i hi => (hi rfl).elim
      · exact (mem_filter.1 ha).2) (by
      rcases mem_insert.1 ha with rfl | ha
      · exact fun e => h.1 (e ▸ hu)
      · exact ne_of_mem_erase (mem_filter.1 ha).1)
  have h1 : ∀ b ∈ P.erase u, Below b u → b i = 0 := fun b hb hbu => by
    by_contra e; exact e ((hA b (mem_insert_of_mem (mem_filter.2 ⟨hb, hbu⟩)) i e).symm.trans hai)
  have fin : ∀ φ : A0 k →ₗ[ℝ] ℝ, φ (vec u) ≠ 0 → (∀ b ∈ P.erase u, φ (vec b) = 0) → vec u ∉ aP (P.erase u) :=
    fun φ h0 hb hm => h0 ((Submodule.span_le (p := LinearMap.ker φ)).2 (by rintro _ ⟨b, hb', rfl⟩; exact hb b hb') hm)
  have sq : ∀ s : SignType, s ≠ 0 → (s : ℝ) * s = 1 := fun s hs => by cases s <;> simp_all
  by_cases hB : ((P.erase u).filter (Below u ·)).Nonempty
  · obtain ⟨b, hb, hB⟩ := exists_top (r := fun a b => Below b a)
      (fun a b c h h' i hi => (h i (h' i hi ▸ hi)).trans (h' i hi)) _ hB fun a ha b hb =>
        h.2 b (mem_of_mem_erase (mem_filter.1 hb).1) a (mem_of_mem_erase (mem_filter.1 ha).1)
    obtain ⟨j, hj, huj⟩ := key u b (mem_filter.1 hb).2 (ne_of_mem_erase (mem_filter.1 hb).1).symm
    refine fin ((u i : ℝ) • EuclideanSpace.projₗ i - (b j : ℝ) • EuclideanSpace.projₗ j) (by simp [vec, huj, sq _ hi])
      fun c hc => ?_
    rcases h.2 c (mem_of_mem_erase hc) u hu with e | e
    · have : c j = 0 := by by_contra e'; exact e' ((e j e').symm.trans huj)
      simp [vec, h1 c hc e, this]
    · simp [vec, e i hi, hB c (mem_filter.2 ⟨hc, e⟩) j hj, sq _ hi, sq _ hj]
  · refine fin (EuclideanSpace.projₗ i) (left_ne_zero_of_mul ((sq _ hi).trans_ne one_ne_zero)) fun c hc => ?_
    rcases h.2 c (mem_of_mem_erase hc) u hu with e | e
    · simp [vec, h1 c hc e]
    · exact (hB ⟨c, mem_filter.2 ⟨hc, e⟩⟩).elim
example (c : Finset (SV k) → A0 k → ℂ) (l : A0 k) : sumP ∅ ∅ c l = c ∅ l := by
  have h : ∀ b : SV k → A0 k, epsOf (∅ \ ∅) b l = 1 := fun b => by
    have : IsEmpty ↥((∅ : Finset (SV k)) \ ∅) := ⟨fun x => by simpa using x.2⟩
    rw [epsOf, Matrix.det_isEmpty]; simp
  simp only [sumP, between, powerset_empty, filter_singleton, Subset.refl, if_true, sum_singleton, eps, epsHat, h]
  simp
example (X : Finset (SV k) → A0 k) (H : A0 k) : gamM ⊥ ∅ X H = 1 := by
  have : parF (⊥ : Submodule ℝ (A0 k)) ∅ = {∅} := by
    ext Q
    rw [mem_parF, mem_singleton]
    refine ⟨fun h => eq_empty_of_forall_notMem fun u hu => h.1.vec_notMem hu ?_, fun e => ?_⟩
    · rw [(Submodule.mem_bot ℝ).1 (h.2.1 (Submodule.subset_span ⟨u, hu, rfl⟩))]; exact zero_mem _
    · subst e; simp [IsPar, aP]
  simp [gamM, this, tauHat]
end GlobalTheory.Chamber
end


