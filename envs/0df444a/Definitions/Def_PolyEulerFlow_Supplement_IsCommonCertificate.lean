-- Prove2me | Definitions.Def_PolyEulerFlow_Supplement_IsCommonCertificate
-- name    : PolyEulerFlow_Supplement_IsCommonCertificate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:06:11.203311+00:00
-- url     : https://prove2.me/theorems/fab92ab9-3406-4cdb-8634-03b39ffd7d8a
-- title:
--   Common polynomial safety certificates (Definition 19) and their dense coefficient encoding
-- statement:
--   Let $f:\mathbb R^m\to\mathbb R^m$, let $\mathcal K$ be a compact box, $I$ an initial set, $U$ an unsafe set and $\delta>0$. A function $V$ is a **common certificate** (Definition 19) if
--   $$V\le-1\ \text{on } I,\qquad V\ge1\ \text{on } U\cup\partial\mathcal K,\tag{10}$$
--   and for every $z\in\mathcal K$ with $V(z)\le0$, every $0\le\eta\le1$ and every $\|\xi\|_\infty\le\delta$,
--   $$z+\eta(f(z)+\xi)\in\mathcal K,\qquad V\big(z+\eta(f(z)+\xi)\big)\le0.\tag{11}$$
--   The sublevel set $\{V\le0\}$ is then invariant under every allowed Euler update.
--
--   A rational polynomial $V\in\mathbb Q[Z_1,\dots,Z_m]$ of total degree $D$ is **dense-encoded** by $D$ in unary followed by its coefficients on all monomials of total degree at most $D$, in a fixed order, each rational in binary; its **bit length** is the length of this word. The input of the certificate checker of Theorem 20 is the binary word of $x$ followed by the dense code of $V$.
--
--   **Formalization Note** $V$ is a real function; a certificate in $\mathbb Q[Z]$ or $\mathbb R[Z]$ is its evaluation. The standing assumptions $I\subset\operatorname{int}\mathcal K$, $U\subset\mathcal K$ of Definition 19 are properties of the instance, not of the certificate. Monomials are listed lexicographically by exponent vectors. The degree prefix makes the list parsable and changes the length by at most the number of coefficients.
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow: Polynomial Dynamics for P and PSPACE (manuscript, STOC 2027 submission, sha256 c4e01b2beb237b48b48e97294deb3c15dae11d39c5f136914567c5ca2ae1b119), Definition 19, p.20 (PDF 22); Theorem 20, p.21 (PDF 23)

import Mathlib
import Definitions.Def_PolyEulerFlow_Supplement_encodeNatVec

namespace PolyEulerFlow.Supplement

/-- A common polynomial safety certificate, Definition 19, p.20 (PDF 22): for a field `f`, a compact box `𝒦`, an initial set `I`, an
unsafe set `U` and `δ > 0`, the function `V` satisfies `V ≤ −1` on `I`, `V ≥ 1` on `U ∪ ∂𝒦` (10), and for every `z ∈ 𝒦` with `V(z) ≤ 0`,
every `0 ≤ η ≤ 1` and every `‖ξ‖∞ ≤ δ`, the update `z + η(f(z) + ξ)` lies in `𝒦` and has `V ≤ 0` (11).
Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), p.20.
**Formalization Note.** `V` is a real function; a certificate in `ℚ[Z]` or `ℝ[Z]` is its evaluation. The standing assumptions `I ⊂ int 𝒦`
and `U ⊂ 𝒦` of Definition 19 concern the instance, not the certificate, and are not part of this predicate. -/
def IsCommonCertificate {m : ℕ} (f : (Fin m → ℝ) → Fin m → ℝ) (K I U : Set (Fin m → ℝ)) (δ : ℝ)
    (V : (Fin m → ℝ) → ℝ) : Prop :=
  (∀ z ∈ I, V z ≤ -1) ∧ (∀ z ∈ U ∪ frontier K, 1 ≤ V z) ∧
    ∀ z ∈ K, V z ≤ 0 → ∀ η : ℝ, 0 ≤ η → η ≤ 1 → ∀ ξ : Fin m → ℝ, ‖ξ‖ ≤ δ →
      z + η • (f z + ξ) ∈ K ∧ V (z + η • (f z + ξ)) ≤ 0

/-- All exponent vectors of total degree at most `D` in `m` variables, in a fixed (lexicographic) order. -/
def monomialsUpTo : (m D : ℕ) → List (Fin m → ℕ)
  | 0, _ => [fun i => Fin.elim0 i]
  | m + 1, D => (List.range (D + 1)).flatMap
      (fun e => (monomialsUpTo m (D - e)).map (fun t : Fin m → ℕ => (Fin.cons e t : Fin (m + 1) → ℕ)))

/-- The dense code of a rational polynomial `V` of total degree `D` (p.21, PDF 23): `D` in unary, then the binary codes of its
coefficients on all monomials of total degree at most `D`, in the fixed order. -/
noncomputable def denseCode {m : ℕ} (V : MvPolynomial (Fin m) ℚ) : List Bool :=
  unaryWord V.totalDegree ++
    (monomialsUpTo m V.totalDegree).flatMap (fun e => encodeRat (V.coeff (Finsupp.equivFunOnFinite.symm e)))

/-- The bit length of the dense code of `V`. -/
noncomputable def certBitLength {m : ℕ} (V : MvPolynomial (Fin m) ℚ) : ℕ :=
  (denseCode V).length

/-- The input of the certificate checker of Theorem 20: the binary word of `x`, then the dense code of `V`. -/
noncomputable def encodeCertInput {m : ℕ} (p : ℕ × MvPolynomial (Fin m) ℚ) : List Bool :=
  tagBits (PolyEulerFlow.binWord p.1) ++ denseCode p.2

end PolyEulerFlow.Supplement


