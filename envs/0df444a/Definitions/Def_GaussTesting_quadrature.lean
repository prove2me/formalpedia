-- Prove2me | Definitions.Def_GaussTesting_quadrature
-- name    : GaussTesting_quadrature
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:32.404529+00:00
-- url     : https://prove2.me/theorems/99b6a649-7b55-40d7-8ee7-1e25a41d6b28
-- title:
--   Bosonic ladder operators and quadratures on coefficient functions
-- statement:
--   On the $n$-mode bosonic Fock space with Fock basis $|x\rangle$, $x\in\mathbb N^n$, the annihilation and creation operators act on coefficient functions $f:\mathbb N^n\to\mathbb C$ by
--
--   $$
--   (a_jf)(x)=\sqrt{x_j+1}\,f(x+e_j),\qquad (a_j^\dagger f)(x)=\sqrt{x_j}\,f(x-e_j)
--   $$
--
--   (the latter is $0$ when $x_j=0$), i.e. $a|m\rangle=\sqrt m|m-1\rangle$ and $a^\dagger|m\rangle=\sqrt{m+1}|m+1\rangle$. The quadrature vector is $v=(q_1,\dots,q_n,p_1,\dots,p_n)$ with
--
--   $$
--   q_i=\frac{a_i+a_i^\dagger}{\sqrt2},\qquad p_i=\frac{a_i-a_i^\dagger}{i\sqrt2}.
--   $$
--
--   The module also defines the action of a one-copy operator on register $s$ of $k$ copies.
--
--   **Formalization Note** $a,a^\dagger$ are unbounded on $\ell^2(\mathbb N^n)$; acting on all coefficient functions, each coefficient of the result is a finite combination of coefficients of the input, so no domain is needed. Modes are $0$-based; `Sum.inl i` is $q_i$ and `Sum.inr i` is $p_i$.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), §2.3, p.18

import Mathlib

namespace GaussTesting

/-- The annihilation operator `a_j` acting on coefficient functions: `(a_j f)(x) = √(x_j+1) f(x + e_j)`. -/
noncomputable def lower {n : ℕ} (j : Fin n) (f : (Fin n → ℕ) → ℂ) : (Fin n → ℕ) → ℂ :=
  fun x => (Real.sqrt (x j + 1) : ℂ) * f (Function.update x j (x j + 1))

/-- The creation operator `a_j†` acting on coefficient functions: `(a_j† f)(x) = √(x_j) f(x − e_j)`
(which is `0` when `x_j = 0`). -/
noncomputable def raise {n : ℕ} (j : Fin n) (f : (Fin n → ℕ) → ℂ) : (Fin n → ℕ) → ℂ :=
  fun x => (Real.sqrt (x j) : ℂ) * f (Function.update x j (x j - 1))

/-- The quadrature vector `v = (q₁,…,q_n,p₁,…,p_n)` with `qᵢ = (aᵢ + aᵢ†)/√2` and
`pᵢ = (aᵢ − aᵢ†)/(i√2)`, acting on coefficient functions; `Sum.inl i` is `qᵢ` and `Sum.inr i` is `pᵢ`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), §2.3, p.18 ("define the vector of operators `v = (q₁, …, q_n, p₁, …, p_n)`
where the quadrature operators `qᵢ, pᵢ` are `qᵢ = (aᵢ + a†ᵢ)/√2`, `pᵢ = (aᵢ − a†ᵢ)/(i√2)`").

**Formalization Note.** `a, a†` are unbounded on `ℓ²(ℕⁿ)`; here they act on all coefficient functions
`(Fin n → ℕ) → ℂ` by the usual matrix elements `a|m⟩ = √m |m−1⟩`, `a†|m⟩ = √(m+1) |m+1⟩` (each
coefficient of the result is a finite combination of coefficients of the input). Modes are 0-based. -/
noncomputable def quadrature {n : ℕ} (m : Fin n ⊕ Fin n) (f : (Fin n → ℕ) → ℂ) : (Fin n → ℕ) → ℂ :=
  match m with
  | Sum.inl j => fun x => (lower j f x + raise j f x) / (Real.sqrt 2 : ℂ)
  | Sum.inr j => fun x => (lower j f x - raise j f x) / (Complex.I * (Real.sqrt 2 : ℂ))

/-- A one-copy operator `op` acting on register `s` of `k` copies: the slice of `F` in register `s`
(other registers fixed) is transformed by `op`. -/
def onReg {n k : ℕ} (s : Fin k) (op : ((Fin n → ℕ) → ℂ) → ((Fin n → ℕ) → ℂ))
    (F : (Fin k → Fin n → ℕ) → ℂ) : (Fin k → Fin n → ℕ) → ℂ :=
  fun x => op (fun y => F (Function.update x s y)) (x s)

end GaussTesting


