-- Prove2me | solution 1 for AffineOfTotalDegreeLeOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:35:23.61091+00:00
-- url     : https://prove2.me/submissions/1b01def4-f264-40a5-a316-d3b14272be02

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_AffineOfTotalDegreeLeOne

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n : ℕ} {P : MvPolynomial (Fin n) ℝ}
    (hdeg : P.totalDegree ≤ 1) :
    ∃ (w : EuclideanSpace ℝ (Fin n)) (c : ℝ), ∀ x : EuclideanSpace ℝ (Fin n),
      MvPolynomial.eval (fun i => x i) P = inner ℝ w x + c := by
  classical
  refine ⟨WithLp.toLp 2 (fun a : Fin n => P.coeff (Finsupp.single a 1)),
    P.coeff 0, ?_⟩
  intro x
  have hinj : Function.Injective (fun a : Fin n => Finsupp.single a 1) := by
    intro a b hab
    have := congrArg (fun f : Fin n →₀ ℕ => f a) hab
    simp only [Finsupp.single_eq_same, Finsupp.single_apply] at this
    by_contra hne
    rw [if_neg (Ne.symm hne)] at this
    exact one_ne_zero this
  set S : Finset (Fin n →₀ ℕ) :=
    insert 0 (Finset.univ.image (fun a : Fin n => Finsupp.single a 1)) with hSdef
  -- Step 1: support ⊆ S
  have hsub : P.support ⊆ S := by
    intro d hd
    have hsum : d.sum (fun _ e => e) = ∑ a, d a := Finsupp.sum_fintype _ _ (fun _ => rfl)
    have hle : ∑ a, d a ≤ 1 := by
      rw [← hsum]; exact le_trans (MvPolynomial.le_totalDegree hd) hdeg
    rw [hSdef, Finset.mem_insert, Finset.mem_image]
    by_cases hall : ∀ a, d a = 0
    · left; ext a; exact hall a
    · right
      obtain ⟨a, ha⟩ := not_forall.mp hall
      have hda : d a ≤ 1 :=
        le_trans (Finset.single_le_sum (f := fun i => d i) (fun i _ => Nat.zero_le _)
          (Finset.mem_univ a)) hle
      have hda1 : d a = 1 := by omega
      refine ⟨a, Finset.mem_univ a, ?_⟩
      refine (Finsupp.eq_single_iff.mpr ⟨?_, hda1⟩).symm
      intro b hb
      rw [Finsupp.mem_support_iff] at hb
      simp only [Finset.mem_singleton]
      by_contra hab
      have hpair : d a + d b ≤ ∑ i, d i := by
        have h1 : ∑ i ∈ ({a, b} : Finset (Fin n)), d i = d a + d b :=
          Finset.sum_pair (Ne.symm hab)
        rw [← h1]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      have hb1 : 1 ≤ d b := Nat.one_le_iff_ne_zero.mpr hb
      omega
  -- Step 3: evaluate
  rw [MvPolynomial.eval_eq' (fun i => x i) P]
  rw [Finset.sum_subset hsub (fun d _ hdnot => by
    rw [MvPolynomial.notMem_support_iff.mp hdnot, zero_mul])]
  have h0notmem : (0 : Fin n →₀ ℕ) ∉ Finset.univ.image (fun a : Fin n => Finsupp.single a 1) := by
    rw [Finset.mem_image]
    rintro ⟨a, -, hcontra⟩
    have := congrArg (fun f : Fin n →₀ ℕ => f a) hcontra
    simp at this
  rw [hSdef, Finset.sum_insert h0notmem, Finset.sum_image (fun a _ b _ h => hinj h)]
  -- the two monomial values (tex Step 2)
  have hzero : ∏ a : Fin n, (x a) ^ ((0 : Fin n →₀ ℕ) a) = 1 := by simp
  have hsingle : ∀ a : Fin n, ∏ b : Fin n, (x b) ^ ((Finsupp.single a 1 : Fin n →₀ ℕ) b) = x a := by
    intro a
    rw [Finset.prod_eq_single a (fun b _ hb => by
      simp [Ne.symm hb]) (fun h => absurd (Finset.mem_univ a) h)]
    simp
  rw [hzero]
  simp only [hsingle]
  -- Step 4: the inner product
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [mul_one]
  rw [add_comm]
  exact congrArg (fun z => z + P.coeff 0)
    (Finset.sum_congr rfl (fun a _ => by ring))
