-- Prove2me | Definitions.Def_WildeQIT_Recover_spectralFun
-- name    : WildeQIT_Recover_spectralFun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:20:23.294477+00:00
-- url     : https://prove2.me/theorems/50fd15ef-91b6-46e9-ba8a-f959f81d6f70
-- title:
--   Functions of Hermitian operators, complex powers on the support, $\Pi_A$, $\log A$ and $\operatorname{supp}(\rho)\subseteq\operatorname{supp}(\sigma)$
-- statement:
--   Operators on a finite-dimensional Hilbert space are complex square matrices. For a Hermitian operator $A=\sum_i a_i\,|i\rangle\langle i|$ (a spectral decomposition) and a function $f$, the book's convention is
--
--   $$
--   f(A)=\sum_{i:\,a_i\in\operatorname{Dom}(f)} f(a_i)\,|i\rangle\langle i| .
--   $$
--
--   This module defines the instances of this convention used in the recoverability chapter:
--
--   1. the **complex power on the support** of a positive semi-definite $A$: $A^{z}=\sum_{i:\,a_i\neq 0} a_i^{z}\,|i\rangle\langle i|$ for $z\in\mathbb C$, with $a^{z}=e^{z\ln a}$; this gives $\sigma^{1/2}$, the inverse square root $[\mathcal N(\sigma)]^{-1/2}$ on the support, the imaginary powers $\sigma^{it}$ (so that $\sigma^{it}\sigma^{-it}=\Pi_\sigma$) and $A^{0}=\Pi_A$;
--   2. the **support projection** $\Pi_A=\sum_{i:\,a_i\neq0}|i\rangle\langle i|$;
--   3. the **binary logarithm** $\log A=\sum_{i:\,a_i\neq0}(\log_2 a_i)\,|i\rangle\langle i|$;
--   4. the **support containment** $\operatorname{supp}(\rho)\subseteq\operatorname{supp}(\sigma)$, where $\operatorname{supp}(A)=\ker(A)^{\perp}$.
--
--   These are the operator functions in which the Petz recovery map, the quantum relative entropy and the Rényi quantity $\widetilde\Delta_\alpha$ of the chapter are written.
--
--   **Formalization Note** The spectral decomposition is Mathlib's eigenvector unitary of a Hermitian matrix; on a non-Hermitian matrix the function is $0$ (never used). The excluded eigenvalue $0$ is sent to $0$. Support containment is stated as $\ker\sigma\subseteq\ker\rho$, which is equivalent.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 3.3.1, p. 83; Definition 11.8.1, (11.104)–(11.105), p. 340; §12.2.1, p. 367; §12.2.3, p. 369; (12.35)–(12.36), p. 372

import Mathlib

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 3.3.1, p. 83
(function of a Hermitian operator), Definition 11.8.1, p. 340 (kernel, support, support
projection), and the conventions of §12.2.1, p. 367, and §12.2.3, p. 369 (complex powers
`A^z = Σ_{i : λᵢ ≠ 0} λᵢ^z |i⟩⟨i|` of a positive semi-definite operator).

Operators on a finite-dimensional Hilbert space are complex matrices indexed by a finite type.
-/

open Matrix

namespace WildeQIT.Recover

/-- **Function of a Hermitian operator** (Wilde, arXiv:1106.1445v8, Definition 3.3.1, p. 83):
for a Hermitian `A = Σᵢ aᵢ |i⟩⟨i|` and `f : ℝ → ℂ`, `f(A) = Σᵢ f(aᵢ) |i⟩⟨i|`.

**Formalization Note** The spectral decomposition is Mathlib's
`Matrix.IsHermitian.eigenvectorUnitary` / `eigenvalues`; the value does not depend on the choice
of eigenbasis. The book's restriction to `aᵢ ∈ Dom(f)` is encoded by the callers below, which
send the excluded eigenvalue `0` to `0`. On a non-Hermitian matrix the value is `0`; the book never
applies `f` to one. -/
noncomputable def spectralFun {n : Type} [Fintype n] [DecidableEq n]
    (f : ℝ → ℂ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  if hA : A.IsHermitian then
    (hA.eigenvectorUnitary : Matrix n n ℂ) * Matrix.diagonal (fun i => f (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ
  else 0

/-- **Complex power on the support** (Wilde, arXiv:1106.1445v8, §12.2.3, p. 369, with
Definition 3.3.1): for a positive semi-definite `A = Σᵢ λᵢ |i⟩⟨i|` and `z ∈ ℂ`,
`A^z = Σ_{i : λᵢ ≠ 0} λᵢ^z |i⟩⟨i|`, where `λ^z = e^{z ln λ}` for `λ > 0`.

This gives `σ^{1/2}`, `[𝒩(σ)]^{-1/2}` (the inverse on the support, (12.30)), `σ^{it}` ((12.35))
and `A^0 = Π_A`, the projection onto the support. -/
noncomputable def supportPow {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  spectralFun (fun x => if x = 0 then 0 else Complex.exp (z * (Real.log x : ℂ))) A

/-- **Support projection** `Π_A = Σ_{i : aᵢ ≠ 0} |i⟩⟨i|` (Wilde, arXiv:1106.1445v8,
Definition 11.8.1, (11.105), p. 340). -/
noncomputable def supportProj {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : Matrix n n ℂ :=
  spectralFun (fun x => if x = 0 then 0 else 1) A

/-- **Binary logarithm of an operator** `log A = Σ_{i : aᵢ ≠ 0} (log₂ aᵢ) |i⟩⟨i|` (Wilde,
arXiv:1106.1445v8, Definition 3.3.1, p. 83, with `Dom(log) = (0, ∞)`; `log` is base 2 in the
book's entropies, Definition 11.8.2, p. 340). -/
noncomputable def log2Op {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : Matrix n n ℂ :=
  spectralFun (fun x => if x = 0 then 0 else (Real.logb 2 x : ℂ)) A

/-- **Support containment** `supp(ρ) ⊆ supp(σ)` (Wilde, arXiv:1106.1445v8, Definition 11.8.1,
p. 340, and condition (11.107)).

**Formalization Note** Since `supp(A) = ker(A)^⊥`, the containment is stated as
`ker(σ) ⊆ ker(ρ)`, which is equivalent to `supp(ρ) ⊆ supp(σ)` for every pair of operators. -/
def SuppSubset {n : Type} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ) : Prop :=
  LinearMap.ker (Matrix.toLin' σ) ≤ LinearMap.ker (Matrix.toLin' ρ)

end WildeQIT.Recover


