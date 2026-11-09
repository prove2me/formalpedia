-- Prove2me | Definitions.Def_DenseProdQSAT_Testing_Algebra
-- name    : DenseProdQSAT_Testing_Algebra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:16.019069+00:00
-- url     : https://prove2.me/theorems/4f6a149d-7841-4611-9ccd-6d45b81d992b
-- title:
--   Real amplitude and coefficient coordinates, ternary signs and Gram minors
-- statement:
--   A local amplitude is split into its real and imaginary coordinates, indexed by its qudit, basis index, and a two-element component label. Polynomial systems use the same split for every coefficient of every monomial of total degree at most $N$.
--
--   For a complex matrix $M$ with $q$ columns, define
--
--   $$G=M^*M,\qquad E_r(M)=\sum_{\substack{I\subseteq\{0,\ldots,q-1\}\\|I|=r}}\det G_{I,I}.$$
--
--   The empty principal minor has determinant one, and no $(q+1)$-element column subset exists. Ternary signs distinguish negative, zero, and positive real values; they are encoded by three finite labels. These coordinates and sums provide the interfaces for kernel matrices, the common-root test, polynomial sign counts, and the rank criterion. They assert no algebraic or quantum conclusion.
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), Theorem 4.5, Fact 4.8; Lemmas 4.9–4.10 p. 14, p. 13

import Definitions.Def_DenseProdQSAT_Testing_Coordinates
set_option autoImplicit false

namespace DenseProdQSAT.Testing

abbrev AmplitudeIndex {n : ℕ} (d : ℕ) (F : Finset (Fin n)) := F × Fin d × Bool

def RealAmplitudes {n d : ℕ} (F : Finset (Fin n)) (ψ : States n d) :
    AmplitudeIndex d F → ℝ :=
  fun a => if a.2.2 then (ψ a.1 a.2.1).im else (ψ a.1 a.2.1).re

abbrev BoundedMonomial (d N : ℕ) :=
  {a : Fin d →₀ ℕ // a.sum (fun _ e => e) ≤ N}
abbrev CoefficientIndex (d s N : ℕ) := Fin s × BoundedMonomial d N × Bool

def CoefficientVector {d s N : ℕ} (f : Fin s → MvPolynomial (Fin d) ℂ) :
    CoefficientIndex d s N → ℝ :=
  fun a => if a.2.2 then ((f a.1).coeff a.2.1.val).im
    else ((f a.1).coeff a.2.1.val).re

noncomputable def TernarySign (x : ℝ) : Fin 3 :=
  if x < 0 then 0 else if x = 0 then 1 else 2

noncomputable def GramSum {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℂ) (r : ℕ) : ℂ :=
  ∑ I ∈ (Finset.univ : Finset (Fin q)).powersetCard r,
    ((M.conjTranspose * M).submatrix (fun i : I => i.val) (fun i : I => i.val)).det

end DenseProdQSAT.Testing


