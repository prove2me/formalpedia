-- Prove2me | Definitions.Def_HararySachs_Hyper_CharPoly
-- name    : HararySachs_Hyper_CharPoly
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T12:35:46.656991+00:00
-- url     : https://prove2.me/theorems/3a49e97b-ed7b-4a13-b13b-3a7a01433514
-- title:
--   Theorem 3 and Definition 1 — the resultant characteristic polynomial
-- statement:
--   Let $\mathcal H=([n],E)$ be a simple $k$-uniform hypergraph. Its adjacency hypermatrix has entry $1/(k-1)!$ on an ordered $k$-tuple whose underlying set is an edge, and entry zero otherwise. The $j$th coordinate of $(\lambda\mathcal I-\mathcal A_{\mathcal H})x^{k-1}$ is formed by summing over every ordered $(k-1)$-tuple. The characteristic polynomial is the multivariate resultant of these coordinates:
--
--   $$\phi(\mathcal H)=\operatorname{Res}((\lambda\mathcal I-\mathcal A_{\mathcal H})x^{k-1}),\qquad \phi_d(\mathcal H)=[\lambda^{n(k-1)^{n-1}-d}]\phi(\mathcal H).$$
--
--   The resultant is characterized by its common-root criterion, normalization on coordinate monomials, and irreducibility over $\mathbb C$. These definitions connect the spectral invariant to the later combinatorial formula.
--
--   **Formalization Note** A resultant polynomial is supplied together with these three properties. The polynomial $\phi$ is evaluated from that resultant; it is not defined through traces. Rational coefficients represent the normalized adjacency entries.
-- source:
--   Clark and Cooper, A Harary-Sachs theorem for hypergraphs, arXiv:1812.00468v2, p. 3, Theorem 3, Definition 1, and adjacency hypermatrix display

import Mathlib

namespace HararySachs.Hyper

abbrev ResVar (n : ℕ) (D : Fin n → ℕ) :=
  Σ i : Fin n, {a : Fin n →₀ ℕ // a.degree = D i}

def IsResultant (n : ℕ) (D : Fin n → ℕ)
    (res : MvPolynomial (ResVar n D) ℤ) : Prop :=
  (∀ F : Fin n → MvPolynomial (Fin n) ℂ,
    (∀ i, (F i).IsHomogeneous (D i)) →
      ((∃ x : Fin n → ℂ, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (F i) = 0) ↔
        MvPolynomial.aeval (fun v : ResVar n D =>
          MvPolynomial.coeff v.2.1 (F v.1))
          (MvPolynomial.map (Int.castRingHom ℂ) res) = 0)) ∧
  (MvPolynomial.aeval (fun v : ResVar n D =>
      if v.2.1 = Finsupp.single v.1 (D v.1) then (1 : ℤ) else 0) res = 1) ∧
  Irreducible (MvPolynomial.map (Int.castRingHom ℂ) res)

def adjEntry {n k : ℕ} (E : Finset (Finset (Fin n)))
    (i : Fin k → Fin n) : ℚ :=
  if Finset.univ.image i ∈ E then 1 / ((Nat.factorial (k - 1) : ℚ)) else 0

noncomputable def coord {n k : ℕ} (E : Finset (Finset (Fin n))) (j : Fin n) :
    MvPolynomial (Fin n) (Polynomial ℚ) :=
  MvPolynomial.monomial (Finsupp.single j (k - 1)) (Polynomial.X) -
    ∑ t : Fin (k - 1) → Fin n,
      MvPolynomial.monomial
        ((Finset.univ : Finset (Fin (k - 1))).sum (fun a => Finsupp.single (t a) 1))
        (Polynomial.C (adjEntry E (Fin.cons j t)))

noncomputable def charPoly {n k : ℕ} (E : Finset (Finset (Fin n)))
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) : Polynomial ℚ :=
  MvPolynomial.aeval (fun v : ResVar n (fun _ => k - 1) =>
    MvPolynomial.coeff v.2.1 (coord (k := k) E v.1))
      (MvPolynomial.map (Int.castRingHom (Polynomial ℚ)) res)

noncomputable def codegCoeff {n k : ℕ} (E : Finset (Finset (Fin n)))
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) (d : ℕ) : ℚ :=
  (charPoly (k := k) E res).coeff (n * (k - 1) ^ (n - 1) - d)

end HararySachs.Hyper


