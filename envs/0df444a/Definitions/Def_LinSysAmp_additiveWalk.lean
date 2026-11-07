-- Prove2me | Definitions.Def_LinSysAmp_additiveWalk
-- name    : LinSysAmp_additiveWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:57:06.764002+00:00
-- url     : https://prove2.me/theorems/9930f13e-dfa0-453e-b469-751b1d43d5ff
-- title:
--   The additive walk on $F^{n\times n}$ and the characters $\chi_C$
-- statement:
--   The **additive walk** $P$ on $F^{n\times n}$ moves from $A$ to $A+uv^\top$, for independent uniform $u,v\in F^n$. With $q=|F|$, it acts on functions by
--   $$
--   (Pf)(A)=q^{-2n}\sum_{u,v\in F^n}f(A+uv^\top),
--   $$
--   and its transition kernel is $P(A,A')=q^{-2n}\,\#\{(u,v):A+uv^\top=A'\}$.
--
--   Given a nontrivial additive character $\psi:F\to\mathbb C^*$, each $C\in F^{n\times n}$ gives the function $\chi_C(A)=\psi(\operatorname{tr}(C^\top A))$. These functions are the Fourier basis in which the spectrum of $P$ is computed.
--
--   **Formalization Note** The walk appears twice: as an operator on complex functions, for the eigen-relation, and as a real kernel, for the notions of §3.3. A character is a Mathlib `AddChar F ℂ`, and its nontriviality is a hypothesis of the statements that need it.
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), §4.1, p.17 (PDF p.19)

import Mathlib

set_option autoImplicit false

open Matrix

namespace LinSysAmp

/-!
# The additive walk on `F^{n×n}` and the characters `χ_C` (§4.1)

G. Couteau, N. Melissaris, T. Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and
Fine-Grained Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…), §4.1, p.17 (PDF p.19):
"Let P be the Markov operator on F_q^{n×n} which moves from A to A + uv⊤, for independent u, v ← F_qⁿ.
We call it the additive walk." and "Fix a nontrivial additive character ψ : F_q → ℂ*. For
C ∈ F_q^{n×n}, define χ_C(A) = ψ(tr(C⊤A))."

**Formalization Note.** `uv⊤` is `Matrix.vecMulVec u v`. The walk is given twice: as an averaging
operator on complex-valued functions (`additiveWalk`, used for the eigen-relation `Pχ_C = q^{-rank C}χ_C`)
and as its transition kernel `P(A, A') = q^{-2n}·#{(u, v) : A + uv⊤ = A'}` (`additiveKernel`, used with
the real-valued §3.3 notions). `q = Fintype.card F`. A character is a Mathlib `AddChar F ℂ`; the
nontriviality `ψ ≠ 1` is a hypothesis of the statements that need it, not part of this definition.
-/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The additive walk acting on complex functions: `(Pf)(A) = E_{u,v}[f(A + uv⊤)]`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §4.1, p.17 (PDF p.19).) -/
noncomputable def additiveWalk {n : ℕ} (f : Matrix (Fin n) (Fin n) F → ℂ)
    (A : Matrix (Fin n) (Fin n) F) : ℂ :=
  ((Fintype.card F : ℂ) ^ (2 * n))⁻¹ * ∑ u : Fin n → F, ∑ v : Fin n → F, f (A + vecMulVec u v)

/-- The transition kernel of the additive walk: `P(A, A') = Pr_{u,v}[A + uv⊤ = A']`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §4.1, p.17 (PDF p.19).) -/
noncomputable def additiveKernel {n : ℕ} (A A' : Matrix (Fin n) (Fin n) F) : ℝ :=
  ((Fintype.card F : ℝ) ^ (2 * n))⁻¹ *
    ((Finset.univ.filter fun p : (Fin n → F) × (Fin n → F) => A + vecMulVec p.1 p.2 = A').card : ℝ)

/-- The character `χ_C(A) = ψ(tr(C⊤A))`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §4.1, p.17 (PDF p.19).) -/
def chi {n : ℕ} (ψ : AddChar F ℂ) (C : Matrix (Fin n) (Fin n) F) (A : Matrix (Fin n) (Fin n) F) : ℂ :=
  ψ (trace (Cᵀ * A))

end LinSysAmp


