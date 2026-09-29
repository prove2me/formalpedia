-- Prove2me | solution 1 for Algebra.le_of_etale_of_forall_exists_pow_expChar_pow_sub_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5a5b4801-28ed-5bb5-ae99-61e71d4b3fa5

import Mathlib
import Theorems.Thm_Algebra_exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_le_of_etale_of_forall_exists_pow_expChar_pow_sub_isNilpotent

set_option autoImplicit false

universe u v w

namespace PI0C2

open Algebra

section EtaleTransfer
variable (K : Type u) [Field K]

theorem etale_of_equiv {X : Type v} {Y : Type w} [CommRing X] [Algebra K X] [CommRing Y] [Algebra K Y]
    [Algebra.Etale K X] (e : X ≃ₐ[K] Y) : Algebra.Etale K Y := by
  haveI : Algebra.FormallyEtale K Y := Algebra.FormallyEtale.of_equiv e
  exact ⟨inferInstance, Algebra.FinitePresentation.equiv e⟩

theorem finite_of_etale (X : Type v) [CommRing X] [Algebra K X] [Algebra.Etale K X] : Module.Finite K X :=
  Algebra.FormallyUnramified.finite_of_free K X

theorem isReduced_of_etale (X : Type v) [CommRing X] [Algebra K X] [Algebra.Etale K X] : IsReduced X :=
  Algebra.FormallyUnramified.isReduced_of_field K X

end EtaleTransfer

section Reduced

variable (K : Type u) [Field K]

theorem single_one_pow {ι : Type v} [DecidableEq ι] {L : ι → Type v} [∀ i, Field (L i)] (i : ι) {m : ℕ} (hm : m ≠ 0) :
    (Pi.single i 1 : ∀ i, L i) ^ m = Pi.single i 1 := by
  ext j
  rw [Pi.pow_apply]
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj, zero_pow hm]

theorem eq_top_of_forall_pow_mem_pi {ι : Type v} [Fintype ι] [DecidableEq ι]
    (L : ι → Type v) [∀ i, Field (L i)] [∀ i, Algebra K (L i)] [∀ i, Algebra.IsSeparable K (L i)]
    (D : Subalgebra K (∀ i, L i))
    (h : ∀ x : ∀ i, L i, ∃ n : ℕ, x ^ ringExpChar K ^ n ∈ D) : D = ⊤ := by
  classical
  haveI := ringExpChar.expChar K
  have hq : ∀ n : ℕ, ringExpChar K ^ n ≠ 0 := fun n => pow_ne_zero _ (expChar_pos K _).ne'
  rw [_root_.eq_top_iff]
  intro x _

  have hidem : ∀ i, (Pi.single i 1 : ∀ i, L i) ∈ D := fun i => by
    obtain ⟨n, hn⟩ := h (Pi.single i 1)
    rwa [single_one_pow i (hq n)] at hn

  have hcomp : ∀ i, ∃ d ∈ D, (d : ∀ i, L i) i = x i := fun i => by
    obtain ⟨n, hn⟩ := h x
    let Di : Subalgebra K (L i) := D.map (Pi.evalAlgHom K L i)
    have hpow : (x i) ^ ringExpChar K ^ n ∈ Di := ⟨x ^ ringExpChar K ^ n, hn, by simp⟩
    have hsep : IsSeparable K (x i) := Algebra.IsSeparable.isSeparable K (x i)
    have hxi : x i ∈ Di := by
      have h1 : x i ∈ IntermediateField.adjoin K {(x i) ^ ringExpChar K ^ n} := by
        rw [← IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable K (L i) hsep (ringExpChar K) n]
        exact IntermediateField.mem_adjoin_simple_self K (x i)
      have h2 : (IntermediateField.adjoin K {(x i) ^ ringExpChar K ^ n}).toSubalgebra =
          Algebra.adjoin K {(x i) ^ ringExpChar K ^ n} :=
        IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsIntegral.isIntegral _).isAlgebraic
      have h3 : x i ∈ Algebra.adjoin K {(x i) ^ ringExpChar K ^ n} := by
        rw [← h2]; exact h1
      exact (Algebra.adjoin_le (Set.singleton_subset_iff.mpr hpow) : _ ≤ Di) h3
    obtain ⟨d, hd, hdi⟩ := hxi
    exact ⟨d, hd, by simpa using hdi⟩
  rw [← Finset.univ_sum_single x]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  obtain ⟨d, hd, hdi⟩ := hcomp i
  have : (Pi.single i (x i) : ∀ i, L i) = d * Pi.single i 1 := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [hdi]
    · simp [Pi.single_eq_of_ne hj]
  rw [this]
  exact D.mul_mem hd (hidem i)

theorem eq_top_of_forall_pow_mem (P : Type v) [CommRing P] [Algebra K P] [Algebra.Etale K P]
    (D : Subalgebra K P) (h : ∀ x : P, ∃ n : ℕ, x ^ ringExpChar K ^ n ∈ D) : D = ⊤ := by
  classical
  obtain ⟨I, hI, L, hL, hLa, e, hsep⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K P).mp inferInstance
  haveI := hI
  haveI := Fintype.ofFinite I
  haveI : ∀ i, Algebra.IsSeparable K (L i) := fun i => (hsep i).2
  have hD : D.map (e : P →ₐ[K] ∀ i, L i) = ⊤ := by
    refine eq_top_of_forall_pow_mem_pi K L _ fun y => ?_
    obtain ⟨n, hn⟩ := h (e.symm y)
    exact ⟨n, ⟨_, hn, by simp [map_pow]⟩⟩
  rw [_root_.eq_top_iff]
  intro x _
  have : e x ∈ D.map (e : P →ₐ[K] ∀ i, L i) := by rw [hD]; trivial
  obtain ⟨y, hy, hyx⟩ := this
  have : y = x := e.injective hyx
  exact this ▸ hy

end Reduced

section Main

variable (K : Type u) [Field K] (C : Type v) [CommRing C] [Algebra K C]

noncomputable def restrictEquiv (C₀ S : Subalgebra K C) (hle : S ≤ C₀) : S.comap C₀.val ≃ₐ[K] S where
  toFun := fun x => ⟨(x : C₀), x.2⟩
  invFun := fun s => ⟨⟨s, hle s.2⟩, s.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl
  map_add' := fun _ _ => rfl
  commutes' := fun _ => rfl

theorem le_of_etale (D : Subalgebra K C) (hD : Algebra.Etale K D)
    (hrad : ∀ x : C, ∃ (n : ℕ) (y : C), y ∈ D ∧ IsNilpotent (x ^ ringExpChar K ^ n - y))
    (S : Subalgebra K C) (hS : Algebra.Etale K S) : S ≤ D := by
  classical
  haveI := hD; haveI := hS
  haveI : Module.Finite K S := finite_of_etale K S
  haveI : Module.Finite K D := finite_of_etale K D

  let bS := Module.finBasis K S
  let bD := Module.finBasis K D
  let gens : Set C := Set.range (fun i => (bS i : C)) ∪ Set.range (fun i => (bD i : C))
  have hgens_fin : gens.Finite := (Set.finite_range _).union (Set.finite_range _)
  have hgens_int : ∀ x ∈ gens, IsIntegral K x := by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact (Algebra.IsIntegral.isIntegral (R := K) (bS i)).map S.val
    · exact (Algebra.IsIntegral.isIntegral (R := K) (bD i)).map D.val
  let C₀ : Subalgebra K C := Algebra.adjoin K gens
  haveI : Module.Finite K C₀ := by
    have h := fg_adjoin_of_finite (R := K) hgens_fin hgens_int
    exact Module.Finite.iff_fg.mpr h
  have hSle : S ≤ C₀ := fun s hs => by
    have h1 : (s : C) = ∑ i, (bS.repr ⟨s, hs⟩ i) • (bS i : C) := by
      conv_lhs => rw [show (s : C) = ((⟨s, hs⟩ : S) : C) from rfl, ← bS.sum_repr ⟨s, hs⟩]
      rw [AddSubmonoidClass.coe_finset_sum]
      simp only [Subalgebra.coe_smul]
    rw [h1]
    refine sum_mem fun i _ => C₀.smul_mem ?_ _
    exact Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)
  have hDle : D ≤ C₀ := fun d hd => by
    have h1 : (d : C) = ∑ i, (bD.repr ⟨d, hd⟩ i) • (bD i : C) := by
      conv_lhs => rw [show (d : C) = ((⟨d, hd⟩ : D) : C) from rfl, ← bD.sum_repr ⟨d, hd⟩]
      rw [AddSubmonoidClass.coe_finset_sum]
      simp only [Subalgebra.coe_smul]
    rw [h1]
    refine sum_mem fun i _ => C₀.smul_mem ?_ _
    exact Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)

  let S₀ : Subalgebra K C₀ := S.comap C₀.val
  let D₀ : Subalgebra K C₀ := D.comap C₀.val
  haveI hS₀ : Algebra.Etale K S₀ := etale_of_equiv K (restrictEquiv K C C₀ S hSle).symm
  haveI hD₀ : Algebra.Etale K D₀ := etale_of_equiv K (restrictEquiv K C C₀ D hDle).symm

  obtain ⟨P₀, hP₀, hmax, -⟩ :=
    Algebra.exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent K C₀
  haveI := hP₀
  have hSP : S₀ ≤ P₀ := hmax S₀ hS₀
  have hDP : D₀ ≤ P₀ := hmax D₀ hD₀

  haveI : IsReduced P₀ := isReduced_of_etale K P₀
  have hDtop : D₀.comap P₀.val = ⊤ := by
    refine eq_top_of_forall_pow_mem K P₀ _ fun x => ?_
    obtain ⟨n, y, hy, hnil⟩ := hrad ((x : C₀) : C)
    refine ⟨n, ?_⟩

    have hyC₀ : y ∈ C₀ := hDle hy
    have hyP₀ : (⟨y, hyC₀⟩ : C₀) ∈ P₀ := hDP (show (⟨y, hyC₀⟩ : C₀) ∈ D₀ from hy)
    have hdiff : IsNilpotent (x ^ ringExpChar K ^ n - ⟨⟨y, hyC₀⟩, hyP₀⟩ : P₀) := by
      obtain ⟨m, hm⟩ := hnil
      refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
      simpa using hm
    have h0 : x ^ ringExpChar K ^ n - ⟨⟨y, hyC₀⟩, hyP₀⟩ = (0 : P₀) := hdiff.eq_zero
    rw [sub_eq_zero] at h0
    show ((x ^ ringExpChar K ^ n : P₀) : C₀) ∈ D₀
    rw [h0]
    exact hy

  intro s hs
  have hs₀ : (⟨s, hSle hs⟩ : C₀) ∈ S₀ := hs
  have hsP : (⟨s, hSle hs⟩ : C₀) ∈ P₀ := hSP hs₀
  have : (⟨⟨s, hSle hs⟩, hsP⟩ : P₀) ∈ D₀.comap P₀.val := by rw [hDtop]; trivial
  exact this

end Main

end PI0C2

theorem solution
    (K : Type u) [Field K] (C : Type v) [CommRing C] [Algebra K C]
    (D : Subalgebra K C) (hD : Algebra.Etale K D)
    (hrad : ∀ x : C, ∃ (n : ℕ) (y : C), y ∈ D ∧ IsNilpotent (x ^ ringExpChar K ^ n - y))
    (S : Subalgebra K C) (hS : Algebra.Etale K S) : S ≤ D:=
  PI0C2.le_of_etale K C D hD hrad S hS

end S_Algebra_le_of_etale_of_forall_exists_pow_expChar_pow_sub_isNilpotent
end P2MW
export P2MW.S_Algebra_le_of_etale_of_forall_exists_pow_expChar_pow_sub_isNilpotent (solution)
