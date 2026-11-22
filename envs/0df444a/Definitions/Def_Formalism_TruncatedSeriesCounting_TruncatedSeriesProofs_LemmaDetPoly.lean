-- Prove2me | Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly
-- name    : Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:33:23.675146+00:00
-- url     : https://prove2.me/theorems/263af829-cb7e-482f-a3a5-3dbb28483b26
-- title:
--   Lemma Det Poly
-- statement:
--   Definitions and structural lemmas for Lemma Det Poly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/LemmaDetPoly.lean

import Definitions.Def_Formalism_TruncatedSeriesCounting_LemmaDetPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical Polynomial
noncomputable section
namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
variable {R : Type*} [CommRing R] {G : Type*} [Monoid G] {n : Type} [Fintype n] [DecidableEq n]
def polyS (S : Subring R) : Subring R[X] where
  carrier := {p | ∀ k, p.coeff k ∈ S}
  mul_mem' := by
    intro p q hp hq k
    show (p * q).coeff k ∈ S
    rw [Polynomial.coeff_mul]
    exact Subring.sum_mem _ (fun x _ => S.mul_mem (hp _) (hq _))
  one_mem' := by
    intro k
    show (1 : R[X]).coeff k ∈ S
    rw [Polynomial.coeff_one]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  add_mem' := by
    intro p q hp hq k
    show (p + q).coeff k ∈ S
    rw [Polynomial.coeff_add]; exact S.add_mem (hp k) (hq k)
  zero_mem' := by intro k; show (0 : R[X]).coeff k ∈ S; simp [S.zero_mem]
  neg_mem' := by
    intro p hp k
    show (-p).coeff k ∈ S
    rw [Polynomial.coeff_neg]; exact S.neg_mem (hp k)
def term (ρ : G →* Matrix n n R) (L : R × ℕ × G) : Matrix n n R[X] :=
  (C L.1 * X ^ L.2.1) • (C : R →+* R[X]).mapMatrix (ρ L.2.2)
def F (ρ : G →* Matrix n n R) (l : List (R × ℕ × G)) : R[X] :=
  Matrix.det (1 - (l.map (term ρ)).sum)
def newL (L0 L : R × ℕ × G) (k : ℕ) : R × ℕ × G :=
  (L0.1 ^ k * L.1, k * L0.2.1 + L.2.1, L0.2.2 ^ k * L.2.2)
lemma term_newL (ρ : G →* Matrix n n R) (L0 L : R × ℕ × G) (k : ℕ) :
    term ρ (newL L0 L k) = term ρ L0 ^ k * term ρ L := by
  simp only [term, newL, map_mul, map_pow, _root_.smul_pow, smul_mul_smul_comm]
  congr 1
  ring
section Trunc
variable (N : ℕ)
abbrev piN : R[X] →+* R[X] ⧸ Ideal.span {(X : R[X]) ^ (N + 1)} := Ideal.Quotient.mk _
lemma piN_eq_zero {c : R} {d : ℕ} (hd : N + 1 ≤ d) : piN N (C c * X ^ d) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact Dvd.dvd.mul_left (pow_dvd_pow X hd) _
lemma mapMatrix_smul_zero {a : R[X]} (ha : piN N a = 0) (M : Matrix n n R[X]) :
    (piN N).mapMatrix (a • M) = 0 := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, ha]
lemma geom_list {A : Type*} [Ring A] (x : A) (N : ℕ) :
    (1 - x) * (1 + ((List.range N).map (fun k => x ^ (k + 1))).sum) = 1 - x ^ (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ← add_assoc, mul_add, ih, sub_mul, one_mul, ← pow_succ']
    abel
lemma alg_identity {A : Type*} [Ring A] (x : A) (N : ℕ) (hx : x ^ (N + 1) = 0) (ys : List A) :
    (1 - x) * (1 - (ys.sum + (ys.map (fun y => ((List.range N).map (fun k => x ^ (k + 1) * y)).sum)).sum)) =
      1 - (x + ys.sum) := by
  have h1 : (ys.map (fun y => ((List.range N).map (fun k => x ^ (k + 1) * y)).sum)).sum =
      ((List.range N).map (fun k => x ^ (k + 1))).sum * ys.sum := by
    simp only [List.sum_map_mul_right]
    rw [List.sum_map_mul_left, List.map_id']
  rw [h1]
  have hg := geom_list x N
  rw [hx, sub_zero] at hg
  calc (1 - x) * (1 - (ys.sum + ((List.range N).map (fun k => x ^ (k + 1))).sum * ys.sum))
      = (1 - x) - ((1 - x) * (1 + ((List.range N).map (fun k => x ^ (k + 1))).sum)) * ys.sum := by
        noncomm_ring
    _ = 1 - (x + ys.sum) := by
        rw [hg]
        noncomm_ring
lemma sum_flat {α A : Type*} [AddCommMonoid A] (f : α → A) (h : α → List α) (l : List α) :
    ((l.flatMap h).map f).sum = (l.map (fun a => ((h a).map f).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]
def elim (L0 : R × ℕ × G) (rest : List (R × ℕ × G)) : List (R × ℕ × G) :=
  rest ++ rest.flatMap (fun L => (List.range N).map (fun k => newL L0 L (k + 1)))
lemma key (ρ : G →* Matrix n n R) (L0 : R × ℕ × G) (h0 : 1 ≤ L0.2.1) (rest : List (R × ℕ × G)) :
    piN N (F ρ (L0 :: rest)) = piN N (Matrix.det (1 - term ρ L0)) * piN N (F ρ (elim N L0 rest)) := by
  simp only [F, RingHom.map_det, ← Matrix.det_mul]
  congr 1
  set φ := (piN (R := R) N).mapMatrix (m := n)
  have hx : (φ (term ρ L0)) ^ (N + 1) = 0 := by
    rw [← map_pow, term, _root_.smul_pow, mul_pow, ← pow_mul, ← map_pow]
    exact mapMatrix_smul_zero N (piN_eq_zero N (by nlinarith)) _
  have hnew : ∀ L k, φ (term ρ (newL L0 L (k + 1))) = φ (term ρ L0) ^ (k + 1) * φ (term ρ L) := by
    intro L k
    rw [term_newL, map_mul, map_pow]
  simp only [map_sub, map_one, map_add, map_list_sum, List.map_cons, List.sum_cons, elim,
    List.map_append, List.sum_append, sum_flat, List.map_map]
  rw [← alg_identity (φ (term ρ L0)) N hx]
  congr 3
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro L _
  simp only [Function.comp_apply]
  rw [map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  exact (hnew L k).symm
variable {S : Subring R}
abbrev SQ (S : Subring R) : Subring (R[X] ⧸ Ideal.span {(X : R[X]) ^ (N + 1)}) :=
  (polyS S).map (piN N)
def Valid (S : Subring R) (D : ℕ) (l : List (R × ℕ × G)) : Prop := ∀ L ∈ l, L.1 ∈ S ∧ D ≤ L.2.1
end Trunc
end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp
open DetPolyCore
section
variable {O K Xs : Type*} [CommRing O] [CommRing K] [Algebra O K]
def MainNotions (T : Subalgebra O (Xs → O)) : Subring (Xs → K) where
  carrier := {f | FromT T f}
  mul_mem' := by
    rintro f g ⟨t, ht, hf⟩ ⟨u, hu, hg⟩
    exact ⟨t * u, T.mul_mem ht hu, fun x => by simp [hf, hg]⟩
  one_mem' := ⟨1, T.one_mem, fun x => by simp⟩
  add_mem' := by
    rintro f g ⟨t, ht, hf⟩ ⟨u, hu, hg⟩
    exact ⟨t + u, T.add_mem ht hu, fun x => by simp [hf, hg]⟩
  zero_mem' := ⟨0, T.zero_mem, fun x => by simp⟩
  neg_mem' := by
    rintro f ⟨t, ht, hf⟩
    exact ⟨-t, T.neg_mem ht, fun x => by simp [hf]⟩
def S1 (T : Subalgebra O (Xs → O)) (m : ℕ) : Subring (Xs → MvPolynomial (Fin m) K) where
  carrier := {f | ∀ α, (fun x => (f x).coeff α) ∈ MainNotions (K := K) T}
  mul_mem' := by
    intro f g hf hg α
    show (fun x => ((f * g) x).coeff α) ∈ MainNotions T
    simp only [Pi.mul_apply, MvPolynomial.coeff_mul]
    have key : ∀ s : Finset ((Fin m →₀ ℕ) × (Fin m →₀ ℕ)),
        (fun x => ∑ p ∈ s, (f x).coeff p.1 * (g x).coeff p.2) ∈ MainNotions T := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        have e : (fun x => ∑ p ∈ (∅ : Finset ((Fin m →₀ ℕ) × (Fin m →₀ ℕ))),
            (f x).coeff p.1 * (g x).coeff p.2) = 0 := by funext x; simp
        rw [e]; exact (MainNotions T).zero_mem
      | insert a s ha ih =>
        have e : (fun x => ∑ p ∈ insert a s, (f x).coeff p.1 * (g x).coeff p.2) =
            (fun x => (f x).coeff a.1) * (fun x => (g x).coeff a.2) +
              (fun x => ∑ p ∈ s, (f x).coeff p.1 * (g x).coeff p.2) := by
          funext x; simp [Finset.sum_insert ha]
        rw [e]; exact (MainNotions T).add_mem ((MainNotions T).mul_mem (hf _) (hg _)) ih
    exact key _
  one_mem' := by
    intro α
    show (fun x => ((1 : Xs → MvPolynomial (Fin m) K) x).coeff α) ∈ MainNotions T
    by_cases h : (0 : Fin m →₀ ℕ) = α
    · have e : (fun x => ((1 : Xs → MvPolynomial (Fin m) K) x).coeff α) = 1 := by
        funext x; simp [MvPolynomial.coeff_one, h]
      rw [e]; exact (MainNotions T).one_mem
    · have e : (fun x => ((1 : Xs → MvPolynomial (Fin m) K) x).coeff α) = 0 := by
        funext x; simp [MvPolynomial.coeff_one, h]
      rw [e]; exact (MainNotions T).zero_mem
  add_mem' := by
    intro f g hf hg α
    have e : (fun x => ((f + g) x).coeff α) = (fun x => (f x).coeff α) + (fun x => (g x).coeff α) := by
      funext x; simp
    show (fun x => ((f + g) x).coeff α) ∈ MainNotions T
    rw [e]; exact (MainNotions T).add_mem (hf α) (hg α)
  zero_mem' := by
    intro α
    have e : (fun x => ((0 : Xs → MvPolynomial (Fin m) K) x).coeff α) = 0 := by funext x; simp
    show (fun x => ((0 : Xs → MvPolynomial (Fin m) K) x).coeff α) ∈ MainNotions T
    rw [e]; exact (MainNotions T).zero_mem
  neg_mem' := by
    intro f hf α
    have e : (fun x => ((-f) x).coeff α) = -(fun x => (f x).coeff α) := by funext x; simp
    show (fun x => ((-f) x).coeff α) ∈ MainNotions T
    rw [e]; exact (MainNotions T).neg_mem (hf α)
end
section
variable {K Xs G : Type*} [CommRing K] [Monoid G] {n : Type} [Fintype n] [DecidableEq n]
def rho (r : G →* (Xs → Matrix n n K)) (m : ℕ) : G →* Matrix n n (Xs → MvPolynomial (Fin m) K) where
  toFun g := Matrix.of fun i j x => MvPolynomial.C (r g x i j)
  map_one' := by
    refine Matrix.ext fun i j => funext fun x => ?_
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  map_mul' := by
    intro g h
    refine Matrix.ext fun i j => funext fun x => ?_
    simp [Matrix.mul_apply, Finset.sum_apply]
end
end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp
namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
open DetPolyCore DetPolyApp
end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities


