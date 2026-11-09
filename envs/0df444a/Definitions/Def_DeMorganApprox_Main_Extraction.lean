-- Prove2me | Definitions.Def_DeMorganApprox_Main_Extraction
-- name    : DeMorganApprox_Main_Extraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:54.940615+00:00
-- url     : https://prove2.me/theorems/8721386f-a80e-4c71-8cdd-0efc7b820536
-- title:
--   Lemma 4.1 proof objects — the symbolic matrix M(x) and the Chebyshev filter Ψ
-- statement:
--   Let a span program have target $\tau\in H$, column matrix $V$ indexed by $J$, and let $S\ge1$. Let $V(x)$ be obtained from $V$ by leaving always-available columns unchanged, multiplying an $x_i$-labelled column by the variable $x_i$ and a $\neg x_i$-labelled column by $1-x_i$. On $\mathbb Ro\oplus^\perp H\oplus^\perp\mathbb R^J$ the **symbolic matrix** is
--   $$M(x)=\begin{pmatrix}0&\frac{1}{10\sqrt S}\tau^\top&0\\ \frac{1}{10\sqrt S}\tau&0&V(x)\\ 0&V(x)^\top&0\end{pmatrix},\qquad \widetilde M(x)=\frac{1}{c_{\rm norm}}M(x),$$
--   a matrix of polynomials of degree at most one.
--
--   For $0<\varepsilon<1$ let $A_\varepsilon(t)=1+\frac{2(\varepsilon^2-t^2)}{1-\varepsilon^2}$ and, with $T_d$ the Chebyshev polynomial of the first kind,
--   $$\Phi(t)=\frac{T_d(A_\varepsilon(t))}{T_d\!\left(1+\frac{2\varepsilon^2}{1-\varepsilon^2}\right)},\qquad \Psi=\Phi^2 .$$
--   The proof chooses $\varepsilon=\frac1{1000\,c_{\rm norm}S}$ and $d=\lceil c_{\rm cheb}/\varepsilon\rceil$.
--
--   The approximating polynomial of Lemma 4.1 is $o^\top\Psi(\widetilde M(x))o$; Claims 4.1.1 and 4.1.2 bound the two factors of its coefficient norm.
--
--   **Formalization Note** The index set is `Unit ⊕ ι ⊕ J`, with `Sum.inl ()` the coordinate $o$. Entries are `MvPolynomial (Fin m) ℝ`; $\Phi$ and $\Psi$ are `Polynomial ℝ`, with Mathlib's `Polynomial.Chebyshev.T` at the integer index $d$. The denominator of $\Phi$ is at least $1$ for $0<\varepsilon<1$, so the division has no junk case.
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), proof of Lemma 4.1, PDF pp. 12–14 (printed pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf; ε on PDF p. 13, Φ, Ψ and M(x) on PDF p. 14

import Mathlib
import Definitions.Def_DeMorganApprox_Main_SpanPrograms

/-!
The objects of the proof of Lemma 4.1 (PDF pp. 12–14, printed pp. 10–12): the symbolic matrix `M(x)` on
`ℝo ⊕ H ⊕ ℝ^J` (index `Unit ⊕ ι ⊕ J`) and the Chebyshev filter `Ψ = Φ²`.
-/

namespace DeMorganApprox.Main

variable {m : ℕ}

/-- The polynomial multiplying a column of `V(x)`: `1` for always available, `xᵢ` for a column
labelled `xᵢ`, `1 − xᵢ` for a column labelled `¬xᵢ` (PDF p. 14). -/
noncomputable def labelPoly : Label m → MvPolynomial (Fin m) ℝ
  | .always => 1
  | .pos i => MvPolynomial.X i
  | .neg i => 1 - MvPolynomial.X i

/-- The symmetric symbolic matrix (PDF p. 14)
`M(x) = [[0, τ⊤/(10√S), 0], [τ/(10√S), 0, V(x)], [0, V(x)⊤, 0]]`. -/
noncomputable def symbolicMatrix {ι J : Type} (P : SpanProgram m ι J) (S : ℝ) :
    Matrix (Unit ⊕ ι ⊕ J) (Unit ⊕ ι ⊕ J) (MvPolynomial (Fin m) ℝ) :=
  fun a b =>
    match a, b with
    | .inl _, .inr (.inl i) => MvPolynomial.C (P.target i / (10 * Real.sqrt S))
    | .inr (.inl i), .inl _ => MvPolynomial.C (P.target i / (10 * Real.sqrt S))
    | .inr (.inl i), .inr (.inr j) => MvPolynomial.C (P.vec j i) * labelPoly (P.label j)
    | .inr (.inr j), .inr (.inl i) => MvPolynomial.C (P.vec j i) * labelPoly (P.label j)
    | _, _ => 0

/-- The normalized symbolic matrix `M̃(x) = M(x) / c_norm`. -/
noncomputable def scaledSymbolicMatrix {ι J : Type} (P : SpanProgram m ι J) (S cnorm : ℝ) :
    Matrix (Unit ⊕ ι ⊕ J) (Unit ⊕ ι ⊕ J) (MvPolynomial (Fin m) ℝ) :=
  cnorm⁻¹ • symbolicMatrix P S

/-- `A_ε(t) = 1 + 2(ε² − t²)/(1 − ε²)` (PDF pp. 14, 16). -/
noncomputable def chebArg (ε : ℝ) : Polynomial ℝ :=
  Polynomial.C (1 + 2 * ε ^ 2 / (1 - ε ^ 2)) - Polynomial.C (2 / (1 - ε ^ 2)) * Polynomial.X ^ 2

/-- `Φ(t) = T_d(A_ε(t)) / T_d(1 + 2ε²/(1 − ε²))`, with `T_d` the Chebyshev polynomial of the
first kind (PDF p. 14). -/
noncomputable def chebFilter (ε : ℝ) (d : ℕ) : Polynomial ℝ :=
  Polynomial.C ((Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (1 + 2 * ε ^ 2 / (1 - ε ^ 2)))⁻¹ *
    (Polynomial.Chebyshev.T ℝ (d : ℤ)).comp (chebArg ε)

/-- The filter `Ψ = Φ²` (PDF p. 14). -/
noncomputable def chebFilterSq (ε : ℝ) (d : ℕ) : Polynomial ℝ :=
  chebFilter ε d ^ 2

/-- The proof's choice `ε = 1/(1000 c_norm S)` (PDF p. 13). -/
noncomputable def filterEps (cnorm S : ℝ) : ℝ := 1 / (1000 * cnorm * S)

/-- The proof's choice `d = ⌈c_cheb / ε⌉` (PDF p. 14). -/
noncomputable def filterDeg (ccheb ε : ℝ) : ℕ := ⌈ccheb / ε⌉₊

end DeMorganApprox.Main


