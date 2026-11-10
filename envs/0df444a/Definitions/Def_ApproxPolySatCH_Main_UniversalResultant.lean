-- Prove2me | Definitions.Def_ApproxPolySatCH_Main_UniversalResultant
-- name    : ApproxPolySatCH_Main_UniversalResultant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:08:13.529126+00:00
-- url     : https://prove2.me/theorems/88c7ace8-5f15-4a87-9d43-25867078ee91
-- title:
--   Universal integer homogeneous resultant by Macaulay minors
-- statement:
--   For $r$ forms of specified positive degrees $d_1,\ldots,d_r$ in $r$ variables, use the published coefficient variables $u_{i,\alpha}$ with $|\alpha|=d_i$. At degree $t=1+\sum_i(d_i-1)$, form the full Macaulay multiplication matrix
--   $$\bigoplus_i\mathbb Z[\mathbf u][X]_{t-d_i}\longrightarrow\mathbb Z[\mathbf u][X]_t,\qquad (A_i)_i\longmapsto\sum_i A_iF_i.$$
--   Take the gcd of its square maximal minors over the universal integer coefficient ring, then choose its sign so its value on the ordered pure powers is positive. Repeated-column minors are harmless zero minors. This is a construction of the normalized universal resultant, independently of the product formula to be proved. Specialization evaluates this one integer polynomial in any commutative ring.
--
--   The degree vector is retained for zero input forms. No nonzero-resultant promise, complex coefficient-field restriction, resultant oracle, or supplied resultant system is assumed. The matrix and gcd are mathematical semantics, not a claim of efficient expansion.
--
--   The construction is the classical Macaulay construction; see also Cattani–Dickenstein, Introduction to residues and resultants, §1.6, equation (1.56), https://mate.dm.uba.ar/~alidick/papers/chapter1cd.pdf, and the EliminationMatrices documentation, https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/EliminationMatrices/html/_elimination__Matrix_lp__List_cm__Matrix_rp.html.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), §§2,4–5, pp.7,11–13,21,25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf

import Mathlib
import Definitions.Def_ResultantVNP_CoeffVar

set_option autoImplicit false

namespace ApproxPolySatCH.Main

/-- Exponents of exactly the indicated total degree. -/
abbrev HomExp (n t : ℕ) := {a : Fin n →₀ ℕ // ∑ j, a j = t}

/-- The critical degree plus one; used only for positive degree vectors. -/
def macaulayDegree {n : ℕ} (d : Fin n → ℕ) : ℕ := 1 + ∑ i, (d i - 1)

/-- Columns of the full Macaulay multiplication map at the critical degree plus one. -/
abbrev MacaulayColumn {n : ℕ} (d : Fin n → ℕ) :=
  Σ i : Fin n, HomExp n (macaulayDegree d - d i)

/-- The full universal multiplication matrix, with integer coefficient indeterminates.
Its rows represent degree-t monomials and its columns represent X^a F_i. -/
noncomputable def macaulayMatrix {n : ℕ} (d : Fin n → ℕ) :
    Matrix (HomExp n (macaulayDegree d)) (MacaulayColumn d)
      (MvPolynomial (ResultantVNP.CoeffVar d) ℤ) := by
  classical
  exact fun r c => if h : ∑ j, (r.val - c.2.val) j = d c.1 then
    if c.2.val ≤ r.val then MvPolynomial.X ⟨c.1, r.val - c.2.val, h⟩ else 0
  else 0

/-- All square maximal minors, including repeated-column zero minors. -/
noncomputable def macaulayMinor {n : ℕ} (d : Fin n → ℕ)
    (cols : HomExp n (macaulayDegree d) → MacaulayColumn d) :
    MvPolynomial (ResultantVNP.CoeffVar d) ℤ := by
  classical
  exact Matrix.det (fun r s => macaulayMatrix d r (cols s))

/-- Gcd over the universal integer coefficient ring, before any specialization. -/
noncomputable def resultantGCD {n : ℕ} (d : Fin n → ℕ) :
    MvPolynomial (ResultantVNP.CoeffVar d) ℤ := by
  classical
  letI := UniqueFactorizationMonoid.toGCDMonoid
    (MvPolynomial (ResultantVNP.CoeffVar d) ℤ)
  exact (Finset.univ : Finset (HomExp n (macaulayDegree d) → MacaulayColumn d)).toList.foldl
    (fun g cols => gcd g (macaulayMinor d cols)) 0

/-- Normalize the gcd by its sign at the ordered system of pure powers.
The construction uses actual matrices and gcds, with no assumed resultant specification. -/
noncomputable def universalResultant {n : ℕ} (d : Fin n → ℕ) :
    MvPolynomial (ResultantVNP.CoeffVar d) ℤ := by
  classical
  let g := resultantGCD d
  let s := MvPolynomial.eval
    (fun v : ResultantVNP.CoeffVar d =>
      if v.2.val = Finsupp.single v.1 (d v.1) then (1 : ℤ) else 0) g
  exact if s < 0 then -g else g

/-- Specialize the one universal integer polynomial in any commutative coefficient ring.
Specified degrees allow zero forms without changing the ambient coefficient blocks. -/
noncomputable def homogeneousResultant {A : Type} [CommRing A] {n : ℕ}
    (d : Fin n → ℕ) (F : Fin n → MvPolynomial (Fin n) A) : A :=
  MvPolynomial.eval₂ (Int.castRingHom A)
    (fun v : ResultantVNP.CoeffVar d => (F v.1).coeff v.2.val) (universalResultant d)

end ApproxPolySatCH.Main


