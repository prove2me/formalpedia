-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ExactBivariatePolynomial
-- name    : CK_GeneralCK_Certificates_E8ExactBivariatePolynomial
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T21:26:10.183231+00:00
-- url     : https://prove2.me/theorems/ddf1f37b-f30d-4b85-9f3a-7775a5af44d4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ExactBivariatePolynomial` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ExactBivariatePolynomial` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ExactBivariatePolynomial` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ExactBivariatePolynomial (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ExactBivariatePolynomial.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginPolynomialLower

-- ===== source module GeneralCK.Certificates.E8ExactBivariatePolynomial =====
section

/-! A small, kernel-reducible polynomial normalizer used by the E8 origin replay. -/

namespace GeneralCK.Certificates.E8ExactBivariatePolynomial

open E8OriginPolynomialLower

def insertTerm (p : Term) : List Term -> List Term
  | [] => if p.c = 0 then [] else [p]
  | q :: qs =>
      if p.c = 0 then q :: qs
      else if p.i = q.i ∧ p.j = q.j then
        if p.c + q.c = 0 then qs
        else { i := q.i, j := q.j, c := p.c + q.c } :: qs
      else q :: insertTerm p qs

def normalize : List Term -> List Term
  | [] => []
  | p :: ps => insertTerm p (normalize ps)

def add (p q : List Term) : List Term := normalize (p ++ q)

def scaleTerm (a : Rat) (p : Term) : Term :=
  { i := p.i, j := p.j, c := a * p.c }

def mulTerm (p q : Term) : Term :=
  { i := p.i + q.i, j := p.j + q.j, c := p.c * q.c }

def rawMul : List Term -> List Term -> List Term
  | [], _ => []
  | p :: ps, q => q.map (mulTerm p) ++ rawMul ps q

def mul (p q : List Term) : List Term := normalize (rawMul p q)

def scale (a : Rat) : List Term -> List Term
  | [] => []
  | p :: ps => scaleTerm a p :: scale a ps

def const (a : Rat) : List Term := [{ i := 0, j := 0, c := a }]
def affine (a b : Rat) : List Term :=
  [{ i := 1, j := 0, c := a }, { i := 0, j := 1, c := b }]

/-- Horner evaluation of ascending univariate coefficients at `a*s+b*t`. -/
def ofUnivariateAffine (a b : Rat) : List Rat -> List Term
  | [] => []
  | c :: cs => add (const c) (mul (affine a b) (ofUnivariateAffine a b cs))

theorem evalTerms_append (p q : List Term) (s t : Real) :
    evalTerms (p ++ q) s t = evalTerms p s t + evalTerms q s t := by
  induction p with
  | nil => simp [evalTerms]
  | cons x xs ih => simp [evalTerms, ih, add_assoc]

theorem evalTerms_insertTerm (p : Term) (q : List Term) (s t : Real) :
    evalTerms (insertTerm p q) s t = evalTerm p s t + evalTerms q s t := by
  induction q with
  | nil =>
      by_cases hz : p.c = 0
      · simp [insertTerm, hz, evalTerms, evalTerm]
      · simp [insertTerm, hz, evalTerms]
  | cons x xs ih =>
      by_cases hz : p.c = 0
      · simp [insertTerm, hz, evalTerms, evalTerm]
      · by_cases h : p.i = x.i ∧ p.j = x.j
        · rcases h with ⟨hi, hj⟩
          by_cases hs : p.c + x.c = 0
          · have hc : (p.c : Real) + (x.c : Real) = 0 := by exact_mod_cast hs
            simp [insertTerm, hz, hi, hj, hs, evalTerms, evalTerm]
            have hc' : (p.c : Real) = -(x.c : Real) := by linarith
            rw [hc']
            ring
          · simp [insertTerm, hz, hi, hj, hs, evalTerms, evalTerm]
            push_cast
            ring
        · simp [insertTerm, hz, h, evalTerms, ih, add_left_comm]

theorem evalTerms_normalize (p : List Term) (s t : Real) :
    evalTerms (normalize p) s t = evalTerms p s t := by
  induction p with
  | nil => rfl
  | cons x xs ih => simp [normalize, evalTerms_insertTerm, evalTerms, ih]

theorem evalTerms_add (p q : List Term) (s t : Real) :
    evalTerms (add p q) s t = evalTerms p s t + evalTerms q s t := by
  simp [add, evalTerms_normalize, evalTerms_append]

theorem evalTerm_mulTerm (p q : Term) (s t : Real) :
    evalTerm (mulTerm p q) s t = evalTerm p s t * evalTerm q s t := by
  simp [mulTerm, evalTerm, pow_add]
  push_cast
  ring

theorem evalTerms_map_mulTerm (p : Term) (q : List Term) (s t : Real) :
    evalTerms (q.map (mulTerm p)) s t = evalTerm p s t * evalTerms q s t := by
  induction q with
  | nil => simp [evalTerms]
  | cons x xs ih => simp [evalTerms, evalTerm_mulTerm, ih, mul_add]

theorem evalTerms_rawMul (p q : List Term) (s t : Real) :
    evalTerms (rawMul p q) s t = evalTerms p s t * evalTerms q s t := by
  induction p with
  | nil => simp [rawMul, evalTerms]
  | cons x xs ih =>
      simp [rawMul, evalTerms_append, evalTerms_map_mulTerm, evalTerms, ih, add_mul]

theorem evalTerms_mul (p q : List Term) (s t : Real) :
    evalTerms (mul p q) s t = evalTerms p s t * evalTerms q s t := by
  simp [mul, evalTerms_normalize, evalTerms_rawMul]

theorem evalTerms_scale (a : Rat) (p : List Term) (s t : Real) :
    evalTerms (scale a p) s t = (a : Real) * evalTerms p s t := by
  induction p with
  | nil => simp [scale, evalTerms]
  | cons x xs ih =>
      simp [scale, scaleTerm, evalTerms, evalTerm, ih]
      push_cast
      ring

def nonnegativePart (p : List Term) : List Term :=
  p.filter fun x => decide (0 <= x.c)

def negativePart (p : List Term) : List Term :=
  p.filter fun x => decide (x.c < 0)

theorem evalTerms_parts (p : List Term) (s t : Real) :
    evalTerms p s t =
      evalTerms (nonnegativePart p) s t + evalTerms (negativePart p) s t := by
  induction p with
  | nil => simp [nonnegativePart, negativePart, evalTerms]
  | cons x xs ih =>
      by_cases h : 0 <= x.c
      · have hn : ¬x.c < 0 := not_lt.mpr h
        simp [nonnegativePart, negativePart, h, hn, evalTerms, ih, add_assoc]
      · have hn : x.c < 0 := lt_of_not_ge h
        simp [nonnegativePart, negativePart, h, hn, evalTerms, ih]
        ring

theorem evalTerms_const (a : Rat) (s t : Real) :
    evalTerms (const a) s t = (a : Real) := by
  simp [const, evalTerms, evalTerm]

theorem evalTerms_affine (a b : Rat) (s t : Real) :
    evalTerms (affine a b) s t = (a : Real) * s + (b : Real) * t := by
  simp [affine, evalTerms, evalTerm]

theorem evalTerms_ofUnivariateAffine (a b : Rat) (cs : List Rat) (s t : Real) :
    evalTerms (ofUnivariateAffine a b cs) s t =
      cs.foldr (fun c z => (c : Real) + ((a : Real) * s + (b : Real) * t) * z) 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp [ofUnivariateAffine, evalTerms_add, evalTerms_const, evalTerms_mul,
        evalTerms_affine, ih]

/-- The sum of all coefficients carried by a given monomial. -/
def coeffAt : List Term -> Nat -> Nat -> Rat
  | [], _, _ => 0
  | p :: ps, i, j =>
      (if p.i = i ∧ p.j = j then p.c else 0) + coeffAt ps i j

theorem coeffAt_append (p q : List Term) (i j : Nat) :
    coeffAt (p ++ q) i j = coeffAt p i j + coeffAt q i j := by
  induction p with
  | nil => simp [coeffAt]
  | cons x xs ih => simp [coeffAt, ih, add_assoc]

theorem coeffAt_scale (a : Rat) (p : List Term) (i j : Nat) :
    coeffAt (scale a p) i j = a * coeffAt p i j := by
  induction p with
  | nil => simp [scale, coeffAt]
  | cons x xs ih =>
      simp only [scale, coeffAt, scaleTerm]
      by_cases h : x.i = i ∧ x.j = j
      · simp [h, ih]
        ring
      · simp [h, ih]

noncomputable def gridEval (N : Nat) (p : List Term) (s t : Real) : Real :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    (coeffAt p i j : Real) * s ^ i * t ^ j

private theorem gridEval_single (N : Nat) (p : Term) (s t : Real)
    (hi : p.i < N) (hj : p.j < N) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      ((if p.i = i ∧ p.j = j then p.c else 0 : Rat) : Real) * s ^ i * t ^ j) =
      evalTerm p s t := by
  simp_rw [apply_ite]
  rw [Finset.sum_eq_single p.i]
  · rw [Finset.sum_eq_single p.j]
    · simp [evalTerm]
    · intro j hj' hne
      simp [hne.symm]
    · simp [hj]
  · intro i hi' hne
    simp [hne.symm]
  · simp [hi]

theorem gridEval_cons (N : Nat) (p : Term) (ps : List Term) (s t : Real)
    (hi : p.i < N) (hj : p.j < N) :
    gridEval N (p :: ps) s t = evalTerm p s t + gridEval N ps s t := by
  unfold gridEval
  simp only [coeffAt]
  push_cast
  simp_rw [add_mul]
  simp_rw [Finset.sum_add_distrib]
  rw [gridEval_single N p s t hi hj]

theorem evalTerms_eq_gridEval (N : Nat) (p : List Term) (s t : Real)
    (hdeg : ∀ q ∈ p, q.i < N ∧ q.j < N) :
    evalTerms p s t = gridEval N p s t := by
  induction p with
  | nil => simp [evalTerms, gridEval, coeffAt]
  | cons q qs ih =>
      have hq := hdeg q (by simp)
      rw [evalTerms, gridEval_cons N q qs s t hq.1 hq.2]
      rw [ih (fun r hr => hdeg r (by simp [hr]))]

theorem evalTerms_eq_of_coeffAt (N : Nat) (p q : List Term) (s t : Real)
    (hp : ∀ r ∈ p, r.i < N ∧ r.j < N)
    (hq : ∀ r ∈ q, r.i < N ∧ r.j < N)
    (hc : ∀ i < N, ∀ j < N, coeffAt p i j = coeffAt q i j) :
    evalTerms p s t = evalTerms q s t := by
  rw [evalTerms_eq_gridEval N p s t hp, evalTerms_eq_gridEval N q s t hq]
  unfold gridEval
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hc i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)]

noncomputable def supportEval (S : Finset (Nat × Nat)) (p : List Term)
    (s t : Real) : Real :=
  ∑ e ∈ S, (coeffAt p e.1 e.2 : Real) * s ^ e.1 * t ^ e.2

private theorem supportEval_single (S : Finset (Nat × Nat)) (p : Term)
    (s t : Real) (hp : (p.i, p.j) ∈ S) :
    (∑ e ∈ S,
      ((if p.i = e.1 ∧ p.j = e.2 then p.c else 0 : Rat) : Real) *
        s ^ e.1 * t ^ e.2) = evalTerm p s t := by
  simp_rw [apply_ite]
  rw [Finset.sum_eq_single (p.i, p.j)]
  · simp [evalTerm]
  · intro e he hne
    have hnot : ¬(p.i = e.1 ∧ p.j = e.2) := by
      intro h
      apply hne
      exact Prod.ext h.1.symm h.2.symm
    simp [hnot]
  · intro hn
    exact (hn hp).elim

theorem evalTerms_eq_supportEval (S : Finset (Nat × Nat)) (p : List Term)
    (s t : Real) (hp : ∀ q ∈ p, (q.i, q.j) ∈ S) :
    evalTerms p s t = supportEval S p s t := by
  induction p with
  | nil => simp [evalTerms, supportEval, coeffAt]
  | cons q qs ih =>
      rw [evalTerms]
      unfold supportEval
      simp only [coeffAt]
      push_cast
      simp_rw [add_mul, Finset.sum_add_distrib]
      rw [supportEval_single S q s t (hp q (by simp))]
      have htail := ih (fun r hr => hp r (by simp [hr]))
      unfold supportEval at htail
      rw [← htail]

theorem evalTerms_eq_of_coeffAtOn (S : Finset (Nat × Nat))
    (p q : List Term) (s t : Real)
    (hp : ∀ r ∈ p, (r.i, r.j) ∈ S)
    (hq : ∀ r ∈ q, (r.i, r.j) ∈ S)
    (hc : ∀ e ∈ S, coeffAt p e.1 e.2 = coeffAt q e.1 e.2) :
    evalTerms p s t = evalTerms q s t := by
  rw [evalTerms_eq_supportEval S p s t hp,
    evalTerms_eq_supportEval S q s t hq]
  unfold supportEval
  apply Finset.sum_congr rfl
  intro e he
  rw [hc e he]

end GeneralCK.Certificates.E8ExactBivariatePolynomial

end


