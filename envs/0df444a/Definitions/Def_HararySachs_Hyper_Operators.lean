-- Prove2me | Definitions.Def_HararySachs_Hyper_Operators
-- name    : HararySachs_Hyper_Operators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T12:39:45.694322+00:00
-- url     : https://prove2.me/theorems/cbe40935-28d5-461f-b769-2c52d978e7e2
-- title:
--   Equation (1) and Definition 2 — differential traces and Schur polynomials
-- statement:
--   Introduce independent variables $A_{ij}$, the matrix trace $\operatorname{tr}(A^L)$, and the differential operator $\hat f_i$ obtained by replacing each variable in the $i$th adjacency coordinate by the corresponding partial derivative. The paper's trace is
--
--   $$\operatorname{Tr}_d(\mathcal H)=(k-1)^{n-1}\sum_{a_1+\cdots+a_n=d}\frac{[A^0]\left(\prod_i\hat f_i^{a_i}\right)\operatorname{tr}(A^{d(k-1)})}{\prod_i(a_i(k-1))!}.$$
--
--   The Schur expression $P_d$ sums products of inputs over positive compositions of $d$, divided by the factorial of the number of parts. These are the quantities in the trace identity used to recover characteristic-polynomial coefficients.
--
--   **Formalization Note** The $\hat f_i$ retain the factor $1/(k-1)!$ from the adjacency hypermatrix. The operators are applied in a fixed vertex order, and the constant coefficient is taken after every derivative has acted.
-- source:
--   Clark and Cooper, A Harary-Sachs theorem for hypergraphs, arXiv:1812.00468v2, p. 4, Equation (1) and Definition 2; p. 5, Definition 3

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Digraph

namespace HararySachs.Hyper

abbrev AuxPoly (n : ℕ) := MvPolynomial (Fin n × Fin n) ℚ

noncomputable def trPow (n L : ℕ) : AuxPoly n :=
  Matrix.trace ((Matrix.of (fun i j : Fin n =>
    MvPolynomial.X (i, j))) ^ L)

noncomputable def fhat {n k : ℕ} (E : Finset (Finset (Fin n)))
    (i : Fin n) (p : AuxPoly n) : AuxPoly n :=
  ∑ t : Fin (k - 1) → Fin n,
    adjEntry E (Fin.cons i t) •
      (List.ofFn t).foldr (fun j q => MvPolynomial.pderiv (i, j) q) p

noncomputable def fhatPow {n k : ℕ} (E : Finset (Finset (Fin n)))
    (i : Fin n) (a : ℕ) (p : AuxPoly n) : AuxPoly n :=
  ((fhat (k := k) E i)^[a]) p

noncomputable def applyAll {n k d : ℕ} (E : Finset (Finset (Fin n)))
    (a : Fin n → Fin (d + 1)) (p : AuxPoly n) : AuxPoly n :=
  (List.ofFn (fun i : Fin n => i)).foldl
    (fun q i => fhatPow (k := k) E i (a i).val q) p

noncomputable def Tr {n k : ℕ} (E : Finset (Finset (Fin n))) (d : ℕ) : ℚ := by
  classical
  exact ((k - 1 : ℕ) : ℚ) ^ (n - 1) *
    ∑ a : Fin n → Fin (d + 1),
      if (∑ i, (a i).val) = d then
        MvPolynomial.coeff 0 (applyAll (k := k) E a (trPow n (d * (k - 1)))) /
          ∏ i, (Nat.factorial ((a i).val * (k - 1)) : ℚ)
      else 0

noncomputable def schurP (d : ℕ) (t : ℕ → ℚ) : ℚ := by
  classical
  exact if d = 0 then 1 else
    ∑ m ∈ Finset.Icc 1 d,
      (∑ a : Fin m → Fin (d + 1),
        if (∀ i, 0 < (a i).val) ∧ (∑ i, (a i).val) = d then
          (∏ i, t (a i).val) / (Nat.factorial m : ℚ)
        else 0)

noncomputable def diffMonomial {n : ℕ} (m : ArcMult n) (p : AuxPoly n) :
    AuxPoly n :=
  (Finset.univ : Finset (Fin n × Fin n)).toList.foldl
    (fun q a => ((MvPolynomial.pderiv a)^[m a.1 a.2]) q) p

abbrev Arcs {n : ℕ} (m : ArcMult n) :=
  Σ u : Fin n, Σ v : Fin n, Fin (m u v)

def IsTour {n L : ℕ} (m : ArcMult n) (hL : 0 < L)
    (σ : Fin L ≃ Arcs m) : Prop :=
  ∀ t : Fin L,
    (σ t).2.1 = (σ ⟨(t.val + 1) % L, Nat.mod_lt _ hL⟩).1

noncomputable def numTours {n L : ℕ} (m : ArcMult n) (hL : 0 < L) : ℕ := by
  classical
  exact (Finset.univ.filter (fun σ : Fin L ≃ Arcs m => IsTour m hL σ)).card

end HararySachs.Hyper


