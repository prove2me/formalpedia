-- Prove2me | Definitions.Def_DualCoppersmith_Recovery_Instance
-- name    : DualCoppersmith_Recovery_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T02:53:55.505646+00:00
-- url     : https://prove2.me/theorems/d5f89403-dd7a-4fb2-8cd4-a4c70d4d3fc9
-- title:
--   Bounded modular root instance and total-degree shifts
-- statement:
--   A bounded modular root input consists of a known prime $p$, integer polynomials $F=(f_1,\ldots,f_s)$ in $\ell\ge1$ variables, and positive integer bounds $X_i$. A target integer vector is a bounded root precisely when
--
--   $$|r_i|<X_i\quad\text{for every }i,\qquad p\mid f_a(r)\quad\text{for every }a.$$
--
--   The shift parameters are arbitrary integers $m,t\ge1$ with $\deg(f_a)\le t$. The ordered monomial coordinates are all $\alpha\in\mathbb N^\ell$ with $|\alpha|\le t$. For $1\le|u|\le m$ and $\deg(x^\beta F^u)\le t$, the coefficient rows are those of $p^{m-|u|}x^\beta F^u$, padded by zero in missing coordinates. This module defines the complete input and the exact finite coefficient matrix used throughout the mission.
--
--   **Formalization Note** Indices are zero-based. A finite equivalence fixes the monomial order. Zero input polynomials are permitted; identically zero shifts are omitted because their rows impose no constraints. For a nonzero shift, its degree condition implies $|\beta|\le t$, making the index type finite. Multiplicity coordinates lie between zero and $m$; their sum is tested separately. No coefficient bound, relation nonvanishing modulo $p$, Jacobian assumption, or relation between $m$ and $t$ is imposed. The target root is absent from the input structure.
-- source:
--   Taehun Kang, Jebin Kim, Changmin Lee, JeongHwan Lee, STOC 2027 submission #1253 (October 2026), p. 4, Definitions 2.4–2.5 (PDF p. 5); p. 5, coefficient matrix (PDF p. 6); p. 3, §2.1 (PDF p. 4)

import Mathlib

set_option autoImplicit false

namespace DualCoppersmith.Recovery

/-- Definition 2.4. The root is not part of the input. -/
structure Instance where
  ell : ℕ
  ell_pos : 0 < ell
  s : ℕ
  p : ℕ
  prime : Nat.Prime p
  F : Fin s → MvPolynomial (Fin ell) ℤ
  X : Fin ell → ℕ
  X_pos : ∀ i, 0 < X i

/-- All and only the strict integer box and original congruence checks. -/
def IsBoundedRoot (I : Instance) (r : Fin I.ell → ℤ) : Prop :=
  (∀ i, |r i| < (I.X i : ℤ)) ∧
    ∀ a, (I.p : ℤ) ∣ MvPolynomial.eval r (I.F a)

structure Parameters (I : Instance) where
  m : ℕ
  t : ℕ
  m_pos : 0 < m
  t_pos : 0 < t
  degree_le : ∀ a, (I.F a).totalDegree ≤ t

/-- A finite presentation of all multi-indices of total degree at most t. -/
abbrev Monomial (ell t : ℕ) :=
  {a : Fin ell → Fin (t + 1) // ∑ i, (a i).val ≤ t}

noncomputable def monomialOrder (ell t : ℕ) :
    Monomial ell t ≃ Fin (Fintype.card (Monomial ell t)) :=
  Fintype.equivFin _

abbrev dimension (I : Instance) (P : Parameters I) :=
  Fintype.card (Monomial I.ell P.t)

noncomputable def multiIndex {ell t : ℕ} (a : Monomial ell t) : Fin ell →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a.val i).val)

noncomputable def exponent (I : Instance) (P : Parameters I)
    (j : Fin (dimension I P)) : Fin I.ell →₀ ℕ :=
  multiIndex ((monomialOrder I.ell P.t).symm j)

noncomputable def constantIndex (I : Instance) (P : Parameters I) :
    Fin (dimension I P) :=
  monomialOrder I.ell P.t ⟨fun _ => ⟨0, by omega⟩, by simp⟩

noncomputable def linearIndex (I : Instance) (P : Parameters I) (i : Fin I.ell) :
    Fin (dimension I P) :=
  monomialOrder I.ell P.t
    ⟨fun j => ⟨if j = i then 1 else 0, by split <;> have := P.t_pos <;> omega⟩,
      by simpa using (Nat.succ_le_of_lt P.t_pos)⟩

abbrev Multiplicity (I : Instance) (P : Parameters I) := Fin I.s → Fin (P.m + 1)

def multiplicityDegree (I : Instance) (P : Parameters I) (i : Multiplicity I P) : ℕ :=
  ∑ a, (i a).val

noncomputable def shiftCore (I : Instance) (P : Parameters I)
    (i : Multiplicity I P) (beta : Monomial I.ell P.t) : MvPolynomial (Fin I.ell) ℤ :=
  MvPolynomial.monomial (multiIndex beta) 1 * ∏ a, I.F a ^ (i a).val

/-- Omit exactly the identically zero rows; these impose only 0 = 0. -/
noncomputable def shiftIndices (I : Instance) (P : Parameters I) :
    Finset (Multiplicity I P × Monomial I.ell P.t) := by
  classical
  exact Finset.univ.filter fun q =>
    1 ≤ multiplicityDegree I P q.1 ∧ multiplicityDegree I P q.1 ≤ P.m ∧
      shiftCore I P q.1 q.2 ≠ 0 ∧ (shiftCore I P q.1 q.2).totalDegree ≤ P.t

noncomputable def shift (I : Instance) (P : Parameters I)
    (q : Multiplicity I P × Monomial I.ell P.t) : MvPolynomial (Fin I.ell) ℤ :=
  MvPolynomial.C ((I.p : ℤ) ^ (P.m - multiplicityDegree I P q.1)) *
    shiftCore I P q.1 q.2

noncomputable def coefficientMatrix (I : Instance) (P : Parameters I) :
    Matrix (shiftIndices I P) (Fin (dimension I P)) ℤ :=
  fun q j => MvPolynomial.coeff (exponent I P j) (shift I P q.val)

end DualCoppersmith.Recovery


