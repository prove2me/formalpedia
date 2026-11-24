-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_HasseDerivatives
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_HasseDerivatives
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:15:14.660692+00:00
-- url     : https://prove2.me/theorems/c37c2262-e746-414d-b59c-8197e011dd47
-- title:
--   Hasse derivatives, finite product rules, and power divisibility
-- statement:
--   Define the k-th Hasse derivative of a polynomial using the standard polynomial Hasse derivative operator. The bundle supplies its finite product rule: distribute total derivative order k among the factors and sum the products of their assigned Hasse derivatives. It also proves that g^(r−k) divides the k-th Hasse derivative of g^r and of f g^r, with subtraction in the natural numbers. These divisibility statements provide the exact polynomial quotients used in the Stepanov linear system and remain valid in positive characteristic.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/HasseDerivatives.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/HasseDerivatives.lean lines 3–419; SHA256 52716d7f8f075321c272319ddf388e0d1218878519fbf0e51588773d3636d49b.

import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring



noncomputable def hasseDerivOp (F : Type*) [Field F] (k : ℕ) : Polynomial F → Polynomial F :=
  fun p => (Polynomial.hasseDeriv k) p

lemma sum_hasseDeriv_piAntidiag_eq_sum_fin
    (F : Type*) [Field F] (k r : ℕ) (f : Fin r → Polynomial F) :
    (∑ j ∈ ((Finset.univ : Finset (Fin r)).piAntidiag k),
        (Finset.univ : Finset (Fin r)).prod
          (fun i => hasseDerivOp F (j i) (f i)))
      =
      (∑ j ∈ (((Finset.univ : Finset (Fin r → Fin (k + 1)))).filter
                  (fun j =>
                    ((Finset.univ : Finset (Fin r)).sum (fun i => (j i).val)) = k)),
          (Finset.univ : Finset (Fin r)).prod
            (fun i => hasseDerivOp F ((j i).val) (f i))) :=
by
  let phi :
      (j : Fin r → ℕ) →
      j ∈ ((Finset.univ : Finset (Fin r)).piAntidiag k) →
      (Fin r → Fin (k + 1)) :=
    fun j hj i =>
      ⟨j i,
        Nat.lt_succ_of_le <|
          by
            have hj_sum :
                (Finset.univ : Finset (Fin r)).sum j = k :=
              (Finset.mem_piAntidiag.mp hj).1
            simpa [hj_sum] using
              (Finset.single_le_sum_of_canonicallyOrdered
                (f := j) (s := (Finset.univ : Finset (Fin r))) (i := i) (by simp))⟩
  refine
    Finset.sum_bij (fun j hj => phi j hj) ?_ ?_ ?_ ?_
  · intro j hj
    rcases Finset.mem_piAntidiag.mp hj with ⟨hj_sum, -⟩
    simp [phi, hj_sum]
  · intro j₁ _ j₂ _ h_eq
    funext i
    simpa [phi] using congrArg (fun g => (g i).val) h_eq
  · intro j' hj'
    refine ⟨fun i => (j' i).val, ?_, ?_⟩
    · rcases Finset.mem_filter.mp hj' with ⟨_, hP⟩
      refine Finset.mem_piAntidiag.mpr ?_
      refine ⟨hP, ?_⟩
      intro i _
      simp
    · ext i
      simp [phi]
  · intro j _
    simp [phi]

lemma hasseLeibniz_general (F : Type*) [Field F] (k r : ℕ) (f : Fin r → Polynomial F) :
  hasseDerivOp F k ((Finset.univ : Finset (Fin r)).prod (fun i => f i)) =
    Finset.sum
      (((Finset.univ : Finset (Fin r → Fin (k + 1)))).filter
        (fun j => ((Finset.univ : Finset (Fin r)).sum (fun i => (j i).val)) = k))
      (fun j => (Finset.univ : Finset (Fin r)).prod
        (fun i => hasseDerivOp F ((j i).val) (f i))) :=
by
  have hasseLeibniz_piAntidiag_finset :
      ∀ (s : Finset (Fin r)) (k : ℕ),
        hasseDerivOp F k (s.prod f) =
          ∑ j ∈ s.piAntidiag k,
            s.prod fun i => hasseDerivOp F (j i) (f i) := by
    intro s
    refine Finset.cons_induction ?h_empty ?h_cons s
    · intro k
      cases k with
      | zero =>
          simp [hasseDerivOp]
      | succ k =>
          simpa [hasseDerivOp,
            Finset.piAntidiag_empty_of_ne_zero (Nat.succ_ne_zero _)] using
            (Polynomial.hasseDeriv_C (R := F) (k := Nat.succ k) (r := (1 : F))
              (Nat.succ_pos _))
    · intro a s ha ih k
      let u : Finset (Fin r) := Finset.cons a s ha
      have hmul :
          hasseDerivOp F k (u.prod f) =
            ∑ p ∈ Finset.antidiagonal k,
              hasseDerivOp F p.1 (f a) *
                hasseDerivOp F p.2 (s.prod f) := by
        have hprod : u.prod f = f a * s.prod f := by
          simpa [u] using
            (Finset.prod_cons (s := s) (a := a) (f := f) ha)
        simpa [hasseDerivOp, hprod] using
          (Polynomial.hasseDeriv_mul (R := F) (k := k)
            (f := f a) (g := s.prod f))
      have hL :
          hasseDerivOp F k (u.prod f) =
            ∑ p ∈ Finset.antidiagonal k,
              hasseDerivOp F p.1 (f a) *
                ∑ g ∈ s.piAntidiag p.2,
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
        refine (hmul.trans ?_)
        refine Finset.sum_congr rfl ?_
        intro p hp
        simp [ih p.2]
      let w : (Fin r → ℕ) → Polynomial F :=
        fun j => u.prod fun i => hasseDerivOp F (j i) (f i)
      have hR1 :
          ∑ j ∈ u.piAntidiag k, w j =
            ∑ p ∈ Finset.antidiagonal k,
              ∑ j ∈ (s.piAntidiag p.2).map
                      (addRightEmbedding (fun t => if t = a then p.1 else 0)),
                w j := by
        let t : (ℕ × ℕ) → Finset (Fin r → ℕ) :=
          fun p =>
            (s.piAntidiag p.2).map
              (addRightEmbedding (fun t => if t = a then p.1 else 0))
        have hpw :
            (↑(Finset.antidiagonal k) : Set (ℕ × ℕ)).PairwiseDisjoint t := by
          simpa [t] using
            (Finset.pairwiseDisjoint_piAntidiag_map_addRightEmbedding
              (i := a) (s := s) (hi := ha) (n := k))
        have hsd :
            ∑ j ∈ (Finset.antidiagonal k).biUnion t, w j =
              ∑ p ∈ Finset.antidiagonal k,
                ∑ j ∈ t p, w j := by
          simpa [t] using
            (Finset.sum_biUnion
              (s := Finset.antidiagonal k)
              (t := t)
              (hs := hpw)
              (f := w))
        have hpi :
            u.piAntidiag k = (Finset.antidiagonal k).biUnion t := by
          simpa [u, t, Finset.disjiUnion_eq_biUnion] using
            (Finset.piAntidiag_cons (i := a) (s := s) (hi := ha) (n := k))
        simpa [hpi, t] using hsd
      have h_inner :
          ∀ p ∈ Finset.antidiagonal k,
            (∑ j ∈ (s.piAntidiag p.2).map
                      (addRightEmbedding (fun t => if t = a then p.1 else 0)),
                w j) =
              hasseDerivOp F p.1 (f a) *
                ∑ g ∈ s.piAntidiag p.2,
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
        intro p hp
        let e : (Fin r → ℕ) ↪ (Fin r → ℕ) :=
          addRightEmbedding (fun t => if t = a then p.1 else 0)
        have h_pointwise :
            ∀ g ∈ s.piAntidiag p.2,
              w (e g) =
                hasseDerivOp F p.1 (f a) *
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
          intro g hg
          obtain ⟨-, hmem⟩ : s.sum g = p.2 ∧ ∀ i, g i ≠ 0 → i ∈ s := by
            simpa [Finset.mem_piAntidiag] using hg
          have hga : g a = 0 := by
            by_contra hne
            exact ha (hmem a hne)
          have hsplit :
              u.prod (fun i => hasseDerivOp F (e g i) (f i)) =
                hasseDerivOp F (e g a) (f a) *
                  s.prod fun i => hasseDerivOp F (e g i) (f i) := by
            simpa [u] using
              (Finset.prod_cons
                (s := s) (a := a)
                (f := fun i => hasseDerivOp F (e g i) (f i))
                ha)
          have h_on_s :
              ∀ i ∈ s, e g i = g i := by
            intro i hi
            have hne : i ≠ a := by
              intro h
              subst h
              exact ha hi
            simp [e, hne]
          have hprod_s :
              s.prod (fun i => hasseDerivOp F (e g i) (f i)) =
                s.prod fun i => hasseDerivOp F (g i) (f i) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            simp [h_on_s i hi]
          have h_at_a : e g a = p.1 := by
            simp [e, hga]
          simp [w, hsplit, h_at_a, hprod_s]
        calc
          ∑ j ∈ (s.piAntidiag p.2).map
                    (addRightEmbedding (fun t => if t = a then p.1 else 0)),
                w j =
              ∑ g ∈ s.piAntidiag p.2, w (e g) := by simp [w, e]
          _ =
              ∑ g ∈ s.piAntidiag p.2,
                hasseDerivOp F p.1 (f a) *
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
                refine Finset.sum_congr rfl ?_
                intro g hg
                simpa using h_pointwise g hg
          _ = hasseDerivOp F p.1 (f a) *
                ∑ g ∈ s.piAntidiag p.2,
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
                simp [Finset.mul_sum]
      have hR :
          ∑ j ∈ u.piAntidiag k, w j =
            ∑ p ∈ Finset.antidiagonal k,
              hasseDerivOp F p.1 (f a) *
                ∑ g ∈ s.piAntidiag p.2,
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
        refine (hR1.trans ?_)
        refine Finset.sum_congr rfl ?_
        intro p hp
        simpa using h_inner p hp
      simpa [u, w] using hL.trans hR.symm
  simpa using
    (hasseLeibniz_piAntidiag_finset (Finset.univ : Finset (Fin r)) k).trans
      (sum_hasseDeriv_piAntidiag_eq_sum_fin F k r f)



lemma hasseDerivOp_prod_single_polynomial_dvd
    (F : Type*) [Field F] (k r : ℕ)
    (g : Polynomial F)
    (j : Fin r → Fin (k + 1))
    (h_sum : (Finset.univ : Finset (Fin r)).sum (fun i => (j i).val) = k) :
    g^(r - k) ∣
      (Finset.univ : Finset (Fin r)).prod
        (fun i => hasseDerivOp F (j i).val g) :=
by
  let s : Finset (Fin r) := Finset.univ
  let Z : Finset (Fin r) := s.filter fun i => (j i).val = 0
  let NZ : Finset (Fin r) := s.filter fun i => (j i).val ≠ 0
  have hprod_split :
      Z.prod (fun i => hasseDerivOp F (j i).val g) *
        NZ.prod (fun i => hasseDerivOp F (j i).val g) =
      s.prod (fun i => hasseDerivOp F (j i).val g) :=
    Finset.prod_filter_mul_prod_filter_not
      (s := s)
      (p := fun i : Fin r => (j i).val = 0)
      (f := fun i => hasseDerivOp F (j i).val g)
  have hsum_decomp :
      Z.sum (fun i => (j i).val) + NZ.sum (fun i => (j i).val) =
        s.sum (fun i => (j i).val) :=
    Finset.sum_filter_add_sum_filter_not
      (s := s)
      (p := fun i : Fin r => (j i).val = 0)
      (f := fun i => (j i).val)
  have hZsum_zero :
      Z.sum (fun i => (j i).val) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    simpa using (Finset.mem_filter.1 hi).2
  have hsum_NZ :
      NZ.sum (fun i => (j i).val) = k := by
    simpa [hZsum_zero] using hsum_decomp.trans h_sum
  have h_le_Zcard : r - k ≤ Z.card := by
    have hNZ_card_le_sum :
        NZ.card ≤ NZ.sum (fun i => (j i).val) := by
      have hones :
          NZ.card = NZ.sum (fun _ : Fin r => (1 : ℕ)) :=
        Finset.card_eq_sum_ones (s := NZ)
      have hterm :
          NZ.sum (fun _ : Fin r => (1 : ℕ)) ≤
            NZ.sum (fun i => (j i).val) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        obtain ⟨_, hne⟩ := Finset.mem_filter.1 hi
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
      rwa [hones.symm] at hterm
    have hNZ_card_le_k : NZ.card ≤ k := by
      simpa [hsum_NZ] using hNZ_card_le_sum
    have h_r_eq : r = Z.card + NZ.card := by
      have hcard_Z_NZ :
          Z.card + NZ.card = s.card :=
        Finset.card_filter_add_card_filter_not
          (s := s)
          (p := fun i : Fin r => (j i).val = 0)
      simpa [s] using hcard_Z_NZ.symm
    simpa [h_r_eq, Nat.add_comm] using
      Nat.sub_le_sub_left hNZ_card_le_k r
  have hZprod :
      Z.prod (fun i => hasseDerivOp F (j i).val g) = g ^ Z.card := by
    calc
      Z.prod (fun i => hasseDerivOp F (j i).val g)
          = Z.prod (fun _ : Fin r => g) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              obtain ⟨_, hzero⟩ := Finset.mem_filter.1 hi
              simp [hasseDerivOp, hzero]
      _ = g ^ Z.card :=
        Finset.prod_const (s := Z) (b := g)
  have hdiv_Z :
      g ^ (r - k) ∣ Z.prod (fun i => hasseDerivOp F (j i).val g) := by
    simpa [hZprod] using pow_dvd_pow g h_le_Zcard
  have :=
    dvd_mul_of_dvd_left hdiv_Z
      (NZ.prod fun i => hasseDerivOp F (j i).val g)
  simpa [s, hprod_split] using this

lemma hasseDerivOp_pow_dvd
    (F : Type*) [Field F] (k r : ℕ) :
    ∀ g : Polynomial F,
      g^(r - k) ∣ hasseDerivOp F k (g^r) :=
by
  intro g
  have hLeib' := hasseLeibniz_general F k r (fun _ : Fin r => g)
  simp [Finset.card_univ, Fintype.card_fin] at hLeib'
  rw [hLeib']
  refine Finset.dvd_sum ?_
  intro j hj
  simpa using hasseDerivOp_prod_single_polynomial_dvd F k r g j (Finset.mem_filter.1 hj).2

lemma hasseDerivOp_mul_pow_dvd (F : Type*) [Field F]
    (k r : ℕ) :
    ∀ f g : Polynomial F,
      g^(r - k) ∣ hasseDerivOp F k (f * g^r) :=
by
  intro f g
  have :
      g ^ (r - k) ∣
        ∑ p ∈ Finset.antidiagonal k,
          hasseDerivOp F p.1 f * hasseDerivOp F p.2 (g ^ r) := by
    refine Finset.dvd_sum ?_
    intro p hp
    have : p.2 ≤ k := by
      have : p.2 ≤ p.1 + p.2 := Nat.le_add_left _ _
      simpa [Finset.mem_antidiagonal.1 hp] using this
    refine dvd_mul_of_dvd_right
      (dvd_trans (pow_dvd_pow _ (Nat.sub_le_sub_left this _))
        (hasseDerivOp_pow_dvd (F := F) (k := p.2) (r := r) g)) _
  simpa [hasseDerivOp,
    ← Polynomial.hasseDeriv_mul (R := F) (k := k) (f := f) (g := g ^ r)] using this


