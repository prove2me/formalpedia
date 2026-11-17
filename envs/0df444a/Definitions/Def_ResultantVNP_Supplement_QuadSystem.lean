-- Prove2me | Definitions.Def_ResultantVNP_Supplement_QuadSystem
-- name    : ResultantVNP_Supplement_QuadSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:55:10.603353+00:00
-- url     : https://prove2.me/theorems/6f4b3b61-47a4-44d3-86de-ce9dfeded5d2
-- title:
--   Integer systems of quadratic forms, $\mathrm{Res}^{(2)}_n(f)\bmod 2^k$ and the sign language
-- statement:
--   An instance is a system $f=(f_1,\dots,f_n)$ of polynomials in $\mathbb Z[x_1,\dots,x_n]$. It is **valid** when $n\ge1$ and every $f_i$ is a quadratic form (homogeneous of degree $2$; the zero form is allowed). Its value is the integer
--   $$\mathrm{Res}^{(2)}_n(f_1,\dots,f_n)\in\mathbb Z,$$
--   obtained by substituting $u_{i,e}\mapsto[x^e]f_i$ into the integral resultant polynomial $\mathrm{Res}^{(2)}_n$.
--
--   The binary code of a system lists $n$ and then, for each $i$ and each pair $j\le k$, the coefficient of $x_jx_k$ in $f_i$ in signed binary.
--
--   1. $\mathrm{ResMod}$ maps the word $\langle \mathrm{code}(f),1^k\rangle$, for valid $f$ and $k\ge1$, to $\mathrm{Res}^{(2)}_n(f)\bmod 2^k\in\{0,\dots,2^k-1\}$ written in binary, and every other word to the empty word.
--   2. $\mathrm{ResPos}$ is the language of codes of valid systems with $\mathrm{Res}^{(2)}_n(f)>0$.
--
--   These are the problems of Theorems 1.8 and 1.11.
--
--   **Formalization Note** The value is computed over $\mathbb Z$. Requiring $n\ge1$ excludes the case $n=0$, where the resultant system of the base mission is unconstrained. The code is injective on valid systems.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Theorem 1.8 and Theorem 1.11, p.7

import Mathlib
import Definitions.Def_ResultantVNP_quadRes
import Definitions.Def_ResultantVNP_Supplement_Reductions

set_option autoImplicit false

namespace ResultantVNP

namespace Supplement

open ApproxPolySatCH.Main

/-- **Integer systems of quadratic forms, their binary code, the value `Res^{(2)}_n(f)`, the
modular function `ResMod` and the sign language `ResPos`.**

A system is `n` polynomials `f₀, …, f_{n-1} ∈ ℤ[x₀, …, x_{n-1}]`; it is *valid* when `n ≥ 1` and
every `f_i` is a quadratic form (homogeneous of degree 2, the zero form allowed). Its value is
`Res^{(2)}_n(f₁, …, fₙ) ∈ ℤ`, the evaluation of the integral polynomial `quadRes 𝓡 n` at the
coefficients `u_{i,e} ↦ [x^e] f_i`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real
Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Theorem 1.8 and Theorem
1.11, p.7 ("Given quadratic forms f₁, …, fₙ ∈ ℤ[x] with coefficients encoded in binary").

**Formalization Note** Code: `encodeNat n`, then for `i < n` and `j ≤ k < n` (lexicographic) the
published signed-binary `encodeInt` of the coefficient of `x_j x_k` in `f_i`. For valid systems the
code is injective. -/
structure QuadSystem where
  n : ℕ
  f : Fin n → MvPolynomial (Fin n) ℤ

/-- Valid instance: `n ≥ 1` and every `f_i` a quadratic form. -/
def QuadSystem.IsValid (q : QuadSystem) : Prop :=
  1 ≤ q.n ∧ ∀ i, (q.f i).IsHomogeneous 2

/-- The point of the coefficient variables: `u_{i,e} ↦ [x^e] f_i`. -/
noncomputable def QuadSystem.coeffPoint (q : QuadSystem) :
    CoeffVar (fun _ : Fin q.n => 2) → ℤ :=
  fun v => (q.f v.1).coeff v.2.1

/-- `Res^{(2)}_n(f₁, …, fₙ) ∈ ℤ`, evaluated over `ℤ`. -/
noncomputable def QuadSystem.res (𝓡 : ResultantSystem) (q : QuadSystem) : ℤ :=
  MvPolynomial.eval q.coeffPoint (quadRes 𝓡 q.n)

/-- Binary code of a system: `n`, then every coefficient of `x_j x_k` (`j ≤ k`) in every `f_i`. -/
noncomputable def QuadSystem.encode (q : QuadSystem) : Word :=
  encodeNat q.n ++ (List.finRange q.n).flatMap (fun i => (List.finRange q.n).flatMap (fun j =>
    ((List.finRange q.n).filter (fun k => decide (j ≤ k))).flatMap (fun k =>
      encodeInt ((q.f i).coeff (Finsupp.single j 1 + Finsupp.single k 1)))))

/-- `ResMod(f, 1^k) = Res^{(2)}_n(f) mod 2^k ∈ {0, …, 2^k − 1}` in binary (`Nat.bits`), on the
words `⟨code f, 1^k⟩` with `f` valid and `k ≥ 1`; every other word is mapped to `[]`. -/
noncomputable def ResMod (𝓡 : ResultantSystem) (w : Word) : Word := by
  classical
  exact if h : ∃ (q : QuadSystem) (k : ℕ), q.IsValid ∧ 1 ≤ k ∧
      w = pairW q.encode (List.replicate k true) then
    (Int.toNat (QuadSystem.res 𝓡 (Classical.choose h) %
      2 ^ (Classical.choose (Classical.choose_spec h)))).bits
  else []

/-- `ResPos`: the codes of valid systems with `Res^{(2)}_n(f) > 0`. -/
def ResPos (𝓡 : ResultantSystem) : Language :=
  {w | ∃ q : QuadSystem, q.IsValid ∧ w = q.encode ∧ 0 < q.res 𝓡}

end Supplement

end ResultantVNP


