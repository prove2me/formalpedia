-- Prove2me | Definitions.Def_RelDecoding_Supplement_targetExpectation
-- name    : RelDecoding_Supplement_targetExpectation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:13:22.489355+00:00
-- url     : https://prove2.me/theorems/369294f2-bfef-488d-b7ce-bf86a8bb4870
-- title:
--   Target expectation $\mathcal E_B(O_B;X_A)$ and the Gram and objective matrices
-- statement:
--   Let $\pi:\mathcal A\to B(H_B)$ be a unital $*$-homomorphism, $\tau_L=\operatorname{Tr}/N_L$ the normalized traces, and $X_A\in\mathcal A$ with $X_B=\pi(X_A)$.
--
--   1. For a self-adjoint target observable $O_B$ the **target expectation** is
--   $$\mathcal E_B(O_B;X_A)=\frac{\tau_B(X_B^*O_BX_B)}{\tau_B(X_B^*X_B)}\qquad(X_B\neq0)$$
--   (eq. (114)).
--   2. For a guide family $F_0,\dots,F_{R-1}$ with $Y_j=\pi(F_j)$, the **target Gram and objective matrices** are $(G_\pi)_{ij}=\tau_B(Y_i^*Y_j)$ and $(K_\pi)_{ij}=\tau_B(Y_i^*O_BY_j)$ (eq. (115)).
--   3. The **source Gram and objective matrices** are $(G_A)_{ij}=\tau_A(F_i^*F_j)$ and $(K_A)_{ij}=\tau_A(F_i^*O_AF_j)$ (App. C.1).
--
--   $\mathcal E_B$ is the energy (or score) of the target guide state; by Proposition 5.1 its optimum over a guide space is a generalized eigenvalue problem for $(K_\pi,G_\pi)$.
--
--   **Formalization Note** At $X_B=0$ the quotient is $0$ (Lean's $x/0=0$); the source uses it only for $X_B\ne0$.
-- source:
--   Shang, Stilck França, From Simple Sources to Quantum Advantage: Homomorphic Polynomial Transduction via Relative Decoding, arXiv:2609.35101 (held version, sha256 d2be7859…), eqs. (114)–(115), p.28; App. C.1, pp.72–73 (pdf_pages 28, 72–73)

import Mathlib
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_RelDecoding_markedSpace

set_option autoImplicit false

namespace RelDecoding.Supplement

open LIDT.MIPStarRE.Quantum RelDecoding

variable {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB] {s : ℕ}

/-- The **target expectation** `E_B(O_B; X_A) := τ_B(X_B∗ O_B X_B) / τ_B(X_B∗ X_B)` with
`X_B := π(X_A)`. Shang, Stilck França, *From Simple Sources to Quantum Advantage: Homomorphic
Polynomial Transduction via Relative Decoding*, arXiv:2609.35101 (held version, sha256 d2be7859…),
eq. (114), p.28.

**Formalization Note.** `τ_B` is `normalizedTrace`. The source uses it only for `X_B ≠ 0`; at
`X_B = 0` Lean's `x / 0 = 0` gives `0`. -/
noncomputable def targetExpectation {a : Fin s → Matrix nA nA ℂ}
    (π : genAlg a →⋆ₐ[ℂ] Matrix nB nB ℂ) (OB : Matrix nB nB ℂ) (XA : genAlg a) : ℂ :=
  normalizedTrace (star (π XA) * OB * π XA) / normalizedTrace (star (π XA) * π XA)

/-- The **target Gram matrix** `(G_π)_{ij} := τ_B(Y_i∗ Y_j)`, `Y_j = π(F_j)`, of a guide family
`F₀, …, F_{R−1}`. Eq. (115), p.28. -/
noncomputable def targetGram {a : Fin s → Matrix nA nA ℂ} (π : genAlg a →⋆ₐ[ℂ] Matrix nB nB ℂ)
    {R : ℕ} (F : Fin R → genAlg a) : Matrix (Fin R) (Fin R) ℂ :=
  Matrix.of fun i j => normalizedTrace (star (π (F i)) * π (F j))

/-- The **target objective matrix** `(K_π)_{ij} := τ_B(Y_i∗ O_B Y_j)`, `Y_j = π(F_j)`. Eq. (115),
p.28. -/
noncomputable def targetObjective {a : Fin s → Matrix nA nA ℂ}
    (π : genAlg a →⋆ₐ[ℂ] Matrix nB nB ℂ) (OB : Matrix nB nB ℂ) {R : ℕ} (F : Fin R → genAlg a) :
    Matrix (Fin R) (Fin R) ℂ :=
  Matrix.of fun i j => normalizedTrace (star (π (F i)) * OB * π (F j))

/-- The **source Gram matrix** `(G_A)_{ij} := τ_A(F_i∗ F_j)`. App. C.1, pp.72–73. -/
noncomputable def sourceGram {a : Fin s → Matrix nA nA ℂ} {R : ℕ} (F : Fin R → genAlg a) :
    Matrix (Fin R) (Fin R) ℂ :=
  Matrix.of fun i j => normalizedTrace (star (F i : Matrix nA nA ℂ) * (F j : Matrix nA nA ℂ))

/-- The **source objective matrix** `(K_A)_{ij} := τ_A(F_i∗ O_A F_j)`. App. C.1, pp.72–73. -/
noncomputable def sourceObjective {a : Fin s → Matrix nA nA ℂ} (OA : genAlg a) {R : ℕ}
    (F : Fin R → genAlg a) : Matrix (Fin R) (Fin R) ℂ :=
  Matrix.of fun i j => normalizedTrace
    (star (F i : Matrix nA nA ℂ) * (OA : Matrix nA nA ℂ) * (F j : Matrix nA nA ℂ))

end RelDecoding.Supplement


