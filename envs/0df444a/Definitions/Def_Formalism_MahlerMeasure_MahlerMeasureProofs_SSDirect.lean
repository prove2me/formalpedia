-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:20.132779+00:00
-- url     : https://prove2.me/theorems/94a8212c-57a7-44ab-a63f-64e3970ecfa2
-- title:
--   SSDirect
-- statement:
--   Definitions and structural lemmas for SSDirect, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.M.SSD
open MvPolynomial Finset
section Gen
variable {σ ι K : Type} [CommRing K] [Nontrivial K] [DecidableEq σ] (sv : ι → σ)
def sd (m : σ →₀ ℕ) : ι → ℕ := fun k => m (sv k)
omit [Nontrivial K] in
lemma sd_add (m m' : σ →₀ ℕ) : sd sv (m + m') = sd sv m + sd sv m' := by
  funext k; simp [sd]
def SFree (f : MvPolynomial σ K) : Prop := ∀ m ∈ f.support, sd sv m = 0
def Good (f : MvPolynomial σ K) (a : ι → ℕ) (s : σ →₀ ℕ) : Prop :=
  sd sv s = a ∧ ∀ m ∈ (f - monomial s 1).support, sd sv m ≤ a ∧ sd sv m ≠ a
lemma le_add_eq {x y a b : ι → ℕ} (hx : x ≤ a) (hy : y ≤ b) (h : x + y = a + b) : x = a := by
  funext k
  have h1 : x k ≤ a k := hx k
  have h2 : y k ≤ b k := hy k
  have h3 := congrFun h k
  simp only [Pi.add_apply] at h3
  omega
omit [Nontrivial K] in
lemma mem_support_mul {f g : MvPolynomial σ K} {m : σ →₀ ℕ} (hm : m ∈ (f * g).support) :
    ∃ u ∈ f.support, ∃ w ∈ g.support, m = u + w := by
  have := support_mul f g hm
  rw [Finset.mem_add] at this
  obtain ⟨u, hu, w, hw, rfl⟩ := this
  exact ⟨u, hu, w, hw, rfl⟩
omit [Nontrivial K] in
lemma mem_support_add {f g : MvPolynomial σ K} {m : σ →₀ ℕ} (hm : m ∈ (f + g).support) :
    m ∈ f.support ∨ m ∈ g.support := by
  have := support_add hm
  simpa [Finset.mem_union] using this
lemma mem_support_monomial_one {s m : σ →₀ ℕ} (hm : m ∈ (monomial s (1 : K)).support) : m = s := by
  have := support_monomial_subset hm
  simpa using this
lemma Good.mul {f g : MvPolynomial σ K} {a b : ι → ℕ} {s s' : σ →₀ ℕ}
    (hf : Good sv f a s) (hg : Good sv g b s') : Good sv (f * g) (a + b) (s + s') := by
  refine ⟨by rw [sd_add, hf.1, hg.1], ?_⟩
  intro m hm
  have hid : f * g - monomial (s + s') 1 =
      monomial s 1 * (g - monomial s' 1) + (f - monomial s 1) * monomial s' 1 +
        (f - monomial s 1) * (g - monomial s' 1) := by
    have : (monomial (s + s') (1 : K)) = monomial s 1 * monomial s' 1 := by
      rw [monomial_mul, mul_one]
    rw [this]; ring
  rw [hid] at hm
  rcases mem_support_add hm with hm | hm
  · rcases mem_support_add hm with hm | hm
    · obtain ⟨u, hu, w, hw, rfl⟩ := mem_support_mul hm
      rw [mem_support_monomial_one hu] at *
      obtain ⟨h1, h2⟩ := hg.2 w hw
      rw [sd_add, hf.1]
      refine ⟨add_le_add le_rfl h1, fun h => h2 (add_left_cancel h)⟩
    · obtain ⟨u, hu, w, hw, rfl⟩ := mem_support_mul hm
      rw [mem_support_monomial_one hw] at *
      obtain ⟨h1, h2⟩ := hf.2 u hu
      rw [sd_add, hg.1]
      refine ⟨add_le_add h1 le_rfl, fun h => h2 (add_right_cancel h)⟩
  · obtain ⟨u, hu, w, hw, rfl⟩ := mem_support_mul hm
    obtain ⟨h1, h2⟩ := hf.2 u hu
    obtain ⟨h3, _⟩ := hg.2 w hw
    rw [sd_add]
    exact ⟨add_le_add h1 h3, fun h => h2 (le_add_eq h1 h3 h)⟩
omit [Nontrivial K] in
lemma SFree.mul {f g : MvPolynomial σ K} (hf : SFree sv f) (hg : SFree sv g) : SFree sv (f * g) := by
  intro m hm
  obtain ⟨u, hu, w, hw, rfl⟩ := mem_support_mul hm
  rw [sd_add, hf u hu, hg w hw, add_zero]
omit [Nontrivial K] in
lemma SFree.add {f g : MvPolynomial σ K} (hf : SFree sv f) (hg : SFree sv g) : SFree sv (f + g) := by
  intro m hm
  rcases mem_support_add hm with h | h
  · exact hf m h
  · exact hg m h
omit [Nontrivial K] in
lemma SFree.C (c : K) : SFree sv (C c : MvPolynomial σ K) := by
  classical
  intro m hm
  rw [support_C] at hm
  split_ifs at hm
  · simp at hm
  · rw [Finset.mem_singleton] at hm; subst hm; funext k; simp [sd]
lemma SFree.X {v : σ} (hv : ∀ k, v ≠ sv k) : SFree sv (X v : MvPolynomial σ K) := by
  intro m hm
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  funext k; simp [sd, hv k]
lemma SFree.rename {τ : Type} (e : τ → σ) (he : ∀ x k, e x ≠ sv k) (y : MvPolynomial τ K) :
    SFree sv (rename e y) := by
  induction y using MvPolynomial.induction_on with
  | C a => rw [rename_C]; exact SFree.C sv a
  | add f g hf hg => rw [map_add]; exact hf.add sv hg
  | mul_X f x hf => rw [map_mul, rename_X]; exact hf.mul sv (SFree.X sv (he x))
end Gen
end Formalism.GM.M.SSD
namespace Formalism.GM.M.SSD
open MvPolynomial Finset
section Abs
variable {σ ι K ι' : Type} [Field K] [DecidableEq σ] [Fintype ι] (sv : ι → σ)
end Abs
end Formalism.GM.M.SSD
namespace Formalism.GM.M.SSD
open MvPolynomial Finset
section Kap
variable {σ τ K : Type} [Field K] [DecidableEq σ]
noncomputable def kap (F : (τ →₀ ℕ) → (σ →₀ ℕ)) (hF : Function.Injective F) (Q : MvPolynomial σ K) :
    MvPolynomial τ K :=
  ∑ n ∈ Q.support.preimage F hF.injOn, monomial n (coeff (F n) Q)
variable (e : τ → σ)
lemma F_inj (he : Function.Injective e) (zm μ : σ →₀ ℕ) : Function.Injective (fun n : τ →₀ ℕ => zm + Finsupp.mapDomain e n + μ) := by
  intro n n' h
  simp only at h
  exact Finsupp.mapDomain_injective he (add_left_cancel (add_right_cancel h))
end Kap
section TSat
variable {p : ℕ} [Fact p.Prime] {σ τ : Type} [DecidableEq σ] (e : τ → σ)
def IsInt {υ : Type} (f : MvPolynomial υ ℚ_[p]) : Prop := ∀ m, coeff m f ∈ (algebraMap ℤ_[p] ℚ_[p]).range
end TSat
end Formalism.GM.M.SSD
namespace Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
section Vars
variable {t : ℕ}
def lv (j : Fin t → ℕ) (jp : ℕ) : Fin (t + 1) → ℕ :=
  ∑ i, j i • Pi.single (Fin.castSucc i) 1 + jp • Pi.single (Fin.last t) 1
end Vars
section Int
variable {σ : Type}
end Int
section Block
variable [NeZero r] (D : BlockData N)
noncomputable def zmS : BVar N r D.T.t →₀ ℕ :=
  ∑ i, Finsupp.single (scalZ N r D.T.t (Fin.castSucc i)) (D.T.z i) +
    Finsupp.single (scalZ N r D.T.t (Fin.last D.T.t)) D.zPlus
noncomputable def pre (j : Fin D.T.t → ℕ) (jp : ℕ) : MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp
def Bset (j : Fin D.T.t → ℕ) (jp : ℕ) : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr, ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp),
    x = monomial (zmS D) 1 * rename (chainEmb N r D.T.t) y * g}
end Block
end Formalism.GM.M
namespace Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
section Main
variable [NeZero r] (D : BlockData N)
end Main
end Formalism.GM.M
namespace Formalism.GM
end Formalism.GM


