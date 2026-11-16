-- Prove2me | Definitions.Def_PCNonBool_Supplement_LinEqEncoding
-- name    : PCNonBool_Supplement_LinEqEncoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:28:48.211439+00:00
-- url     : https://prove2.me/theorems/923ba189-2c17-4c89-971e-5f336975c6ab
-- title:
--   Encoding (127) of linear equations over $\mathbb F_p$
-- statement:
--   Fix a field $\mathbb F$, $c\in\mathbb F\setminus\{0\}$ and a prime $p$; elements of $\mathbb F_p$ are represented by the integers $\{0,\dots,p-1\}$. For a linear equation $\ell=b$ with $\ell=\sum_i a_ix_i$, let $\|\ell\|=\sum_i a_i$ and $m_\ell=\prod_i y_i^{a_i}$, and for $N\ge0$ let
--   $$P_{N,b}(z)=\prod_{\substack{0\le k\le N\\ k\equiv b\ (\mathrm{mod}\ p)}}(z-c^k).$$
--   The equation is encoded by $P_{\|\ell\|,b}(m_\ell)$; a system is encoded by the encodings of its equations together with the range axioms $(y_i-1)(y_i-c)$. A system is **inconsistent** if no $x\in\mathbb F_p^n$ satisfies all its equations.
--
--   When $c$ is not a root of unity, the encoding of $\ell=b$ vanishes at $y=c^x$, $x\in\{0,1\}^n$, exactly when $\ell(x)\equiv b\pmod p$. This is the encoding of Theorem 8.8.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §8.2, (127), p.65 (PDF p.68)

import Mathlib

namespace PCNonBool.Supplement

open MvPolynomial

/-- A linear equation `ℓ = b` over `𝔽_p` in `n` variables, `ℓ = ∑ a_i x_i` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §8.2,
p.65 (PDF p.68)); elements of `𝔽_p` are represented by the integers `{0, …, p - 1}`
(`ZMod.val`). -/
structure LinEq (p n : ℕ) where
  /-- the coefficients `a_i` -/
  coeff : Fin n → ZMod p
  /-- the right-hand side `b` -/
  rhs : ZMod p

/-- `‖ℓ‖ = ∑ a_i`, with the integer representatives of the coefficients. -/
def LinEq.norm {p n : ℕ} (E : LinEq p n) : ℕ := ∑ i, (E.coeff i).val

/-- The encoding (127) of the equation `ℓ = b` over `{1, c}`-valued variables `y_i`: `P_{‖ℓ‖,b}(m_ℓ)`
where `m_ℓ = ∏ y_i^{a_i}` and `P_{N,b}(z) = ∏_{0 ≤ k ≤ N, k ≡ b (mod p)} (z - c^k)` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), (127),
p.65 (PDF p.68)). -/
noncomputable def eqPoly {F : Type*} [Field F] (c : F) {p n : ℕ} (E : LinEq p n) :
    MvPolynomial (Fin n) F :=
  ∏ k ∈ (Finset.range (E.norm + 1)).filter (fun k => k % p = (E.rhs).val),
    (∏ i, X i ^ (E.coeff i).val - C (c ^ k))

/-- The axioms of Theorem 8.8: the encodings (127) of the equations of the system, together with
the range axioms `(y_i - 1)(y_i - c)`, `i ∈ [n]`. -/
noncomputable def linAxioms {F : Type*} [Field F] (c : F) {p n : ℕ} (sys : List (LinEq p n)) :
    Set (MvPolynomial (Fin n) F) :=
  {q | (∃ E ∈ sys, q = eqPoly c E) ∨ (∃ i : Fin n, q = (X i - 1) * (X i - C c))}

/-- The system is inconsistent: no `x ∈ 𝔽_p^n` satisfies all its equations. -/
def LinInconsistent {p n : ℕ} (sys : List (LinEq p n)) : Prop :=
  ¬ ∃ x : Fin n → ZMod p, ∀ E ∈ sys, ∑ i, E.coeff i * x i = E.rhs

end PCNonBool.Supplement


