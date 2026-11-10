-- Prove2me | Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages
-- name    : ApproxPolySatCH_Main_ResultantLanguages
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:11:50.845667+00:00
-- url     : https://prove2.me/theorems/ae0a2dca-9113-4b92-b5f5-232f40f19b15
-- title:
--   Sparse resultant coefficient and MRV languages; finite extension bounds
-- statement:
--   A forms input consists of sparse homogeneous forms of specified positive X-degrees, arbitrary binary parameter exponents and coefficient codes. Its resultant is the specialization of the universal integer resultant. The coefficient-zero language tests exact vanishing at a supplied binary exponent tuple. In the finite-field language the prime and defining polynomial are part of the word.
--
--   For MRV the first parameter is epsilon. Writing $R=\sum_{\beta,j}c_{\beta,j}\varepsilon^jY^\beta$, accept exactly when
--   $$\min_{\beta,j:c_{\beta,j}\ne0}j<\min_{j:c_{\beta_0,j}\ne0}j.$$
--   The minimum of an empty support is infinity, so a zero resultant is rejected. The finite version includes the coefficient field description. Query-extension bounds require an actual field embedding, finite-dimensionality, and an extension degree bounded by a single polynomial in the input length.
--
--   The minimally dependent reduction is expressed by one finite machine, one clock and one seed-length polynomial, before every encoded field and system. With probability at least $2/3$, its written output is a valid minimally dependent tuple in positive dimension, has the same APS status, and uses a polynomial-degree extension in finite characteristic or rational coefficients in characteristic zero. Finite seed sets are counted exactly. No operation on an expanded resultant is assigned free cost.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), §§2–5, pp.7,14,16–18,23–26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf

import Definitions.Def_ApproxPolySatCH_Main_TrailingResultant

set_option autoImplicit false

namespace ApproxPolySatCH.Main

structure FormTerm (v n : ℕ) where
  coefficient : ScalarCode
  parameters : Fin v → ℕ
  xExponent : Fin (n + 1) → ℕ

structure FormsInput where
  n : ℕ
  v : ℕ
  degrees : Fin (n + 1) → ℕ
  forms : Fin (n + 1) → List (FormTerm v n)

noncomputable def inputForm (k : CoefficientField) (I : FormsInput) (i : Fin (I.n + 1)) :
    Poly (Poly k.Carrier I.v) (I.n + 1) :=
  (I.forms i).foldl (fun p t => p +
    MvPolynomial.C (MvPolynomial.C (scalar k t.coefficient) *
      ∏ j : Fin I.v, MvPolynomial.X j ^ t.parameters j) *
    ∏ j : Fin (I.n + 1), MvPolynomial.X j ^ t.xExponent j) 0

def ValidForms (k : CoefficientField) (I : FormsInput) : Prop :=
  (∀ i, 0 < I.degrees i) ∧
  (∀ i, ∀ t ∈ I.forms i, ValidScalar k t.coefficient) ∧
  (∀ i, ∀ e ∈ (inputForm k I i).support, ∑ j, e j = I.degrees i)

noncomputable def inputResultant (k : CoefficientField) (I : FormsInput) : Poly k.Carrier I.v :=
  homogeneousResultant I.degrees (inputForm k I)

def encodeForms (I : FormsInput) : Word :=
  encodeNat I.n ++ encodeNat I.v ++ encodeList encodeNat (List.ofFn I.degrees) ++
    encodeList (encodeList (fun t => encodeScalar t.coefficient ++
      encodeList encodeNat (List.ofFn t.parameters) ++ encodeList encodeNat (List.ofFn t.xExponent)))
      (List.ofFn I.forms)

noncomputable def exponentVector {v : ℕ} (b : Fin v → ℕ) : Fin v →₀ ℕ := Finsupp.equivFunOnFinite.symm b

noncomputable def CoefficientZero (k : CoefficientField) : Language :=
  {x | ∃ (I : FormsInput) (b : Fin I.v → ℕ),
    x = encodeForms I ++ encodeList encodeNat (List.ofFn b) ∧
    ValidForms k I ∧ (inputResultant k I).coeff (exponentVector b) = 0}

noncomputable def CoefficientZeroFinite : Language :=
  {x | ∃ k : CoefficientField, k ≠ .rational ∧ ∃ w ∈ CoefficientZero k, x = k.encode ++ w}

/-- The first parameter is epsilon. Exponents of all other parameters are the distinguished tuple. -/
noncomputable def gaussOrder {k : Type} [Field k] {v : ℕ} (p : Poly k (v + 1)) : WithTop ℕ :=
  p.support.inf (fun e => (e 0 : WithTop ℕ))

open Classical in
noncomputable def selectedOrder {k : Type} [Field k] {v : ℕ}
    (b : Fin v → ℕ) (p : Poly k (v + 1)) : WithTop ℕ :=
  (p.support.filter (fun e => ∀ j : Fin v, e j.succ = b j)).inf (fun e => (e 0 : WithTop ℕ))

/-- No promise of a nonzero resultant: empty supports have infimum infinity. -/
noncomputable def MRV (k : CoefficientField) : Language :=
  {x | ∃ (n v : ℕ) (d : Fin (n + 1) → ℕ)
    (F : Fin (n + 1) → List (FormTerm (v + 1) n)) (b : Fin v → ℕ),
    let I : FormsInput := ⟨n, v + 1, d, F⟩
    x = encodeForms I ++ encodeList encodeNat (List.ofFn b) ∧ ValidForms k I ∧
    gaussOrder (inputResultant k I) < selectedOrder b (inputResultant k I)}

noncomputable def MRVFinite : Language :=
  {x | ∃ k : CoefficientField, k ≠ .rational ∧ ∃ w ∈ MRV k, x = k.encode ++ w}

noncomputable def SparseFinite : Language :=
  {x | ∃ k : CoefficientField, k ≠ .rational ∧ ∃ w ∈ SparseLanguage k, x = k.encode ++ w}

/-- An embedding and its actual finite extension degree, charged in the input length. -/
def ExtensionBound (k ell : CoefficientField) (B : ℕ) : Prop :=
  match k with
  | .rational => ell = .rational
  | .finite _ _ _ _ _ _ => ell ≠ .rational ∧ ∃ e : k.Carrier →+* ell.Carrier,
      letI : Algebra k.Carrier ell.Carrier := e.toAlgebra
      Module.Finite k.Carrier ell.Carrier ∧ Module.finrank k.Carrier ell.Carrier ≤ B

/-- Every actual oracle query has a polynomial-degree coefficient extension of the input field.
No coefficient oracle or expanded resultant is supplied to the machine. -/
def QueryExtensions (k : CoefficientField) (M : NKtLB.Machine) (c d a b e h : ℕ) : Prop :=
  ∀ (n : ℕ) (S : SparseSystem n), ValidSparse k S →
    let x := encodeSparse S
    ∀ r : Fin (clock a b x.length) → Bool, ∀ t < clock c d x.length,
      let cfg := Run M MRVFinite x (List.ofFn r) t
      cfg.state = M.query → cfg.state ≠ M.halt →
      ∃ (ell : CoefficientField) (I : FormsInput) (v : ℕ) (beta : Fin v → ℕ),
        I.v = v + 1 ∧ ValidForms ell I ∧
        cfg.queryString = ell.encode ++ encodeForms I ++ encodeList encodeNat (List.ofFn beta) ∧
        ExtensionBound k ell (clock e h x.length)

/-- Uniform randomized many-one transformation to minimally dependent systems.
Field construction, the written output and all random branches use the same bit clock. -/
def MinimalReduction : Prop :=
  ∃ (M : NKtLB.Machine) (c d a b e h : ℕ),
    (∀ x : Word, ∀ r : Fin (clock a b x.length) → Bool,
      (Run M ∅ x (List.ofFn r) (clock c d x.length)).state = M.halt) ∧
    ∀ (k : CoefficientField) (n : ℕ) (S : SparseSystem n), ValidSparse k S →
      let x := k.encode ++ encodeSparse S
      2 * 2 ^ clock a b x.length ≤ 3 * Set.ncard
        {r : Fin (clock a b x.length) → Bool |
          ∃ (ell : CoefficientField) (m : ℕ) (T : SparseSystem m),
            ValidSparse ell T ∧
            (Run M ∅ x (List.ofFn r) (clock c d x.length)).output =
              NKtLB.bitsSym (ell.encode ++ encodeSparse T) ∧
            ExtensionBound k ell (clock e h x.length) ∧
            ∃ hlength : T.length = m + 1, ∃ f : Fin (m + 1) → Poly ell.Carrier m,
              (∀ i, f i = sparsePolynomials ell T (Fin.cast hlength.symm i)) ∧
              1 ≤ m ∧ MinimallyDependent f ∧ (APS f ↔ APS (sparsePolynomials k S))}
end ApproxPolySatCH.Main


