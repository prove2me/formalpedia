-- Prove2me | Definitions.Def_QMAvsQCIP_multEnc
-- name    : QMAvsQCIP_multEnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:46:43.075915+00:00
-- url     : https://prove2.me/theorems/b5ac6f88-9662-4c8f-a1ef-cd88f3972e00
-- title:
--   Multiplicity-code encoding
-- statement:
--   Fix $\lambda$ and $q$. A coefficient vector $c=(c_0,\dots,c_{\lambda^3-1})\in\mathbb F_q^{\lambda^3}$ defines the polynomial $f=\sum_j c_jX^j$ of degree less than $\lambda^3$. Its codeword in the **univariate multiplicity code with multiplicity $\lambda$** has, at the coordinate $\alpha\in\mathbb F_q$, the symbol
--   $$
--   \big(f^{[0]}(\alpha),f^{[1]}(\alpha),\dots,f^{[\lambda-1]}(\alpha)\big)\in\Sigma=\mathbb F_q^{\lambda},
--   $$
--   where $f^{[k]}$ is the $k$-th Hasse derivative of $f$. The map is $\mathbb F_q$-linear.
--
--   **Formalization Note** The $q$ coordinates $i\in[q]$ are the field elements $\alpha$, in the order of their representatives $0,\dots,q-1$. Hasse derivatives $f^{[k]}=f^{(k)}/k!$ are the standard choice for multiplicity codes; since $\lambda<q$, $k!$ is invertible for $k<\lambda$, so ordinary derivatives give the same code up to an invertible scaling of each symbol component.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Lemma 2, p.18

import Definitions.Def_QMAvsQCIP_Sym

set_option autoImplicit false

namespace QMAvsQCIP

open Polynomial

/-- The **multiplicity-code encoding** with multiplicity `λ` and degree `< λ³`: a coefficient
vector `c = (c_0, …, c_{λ³−1}) ∈ F_q^{λ³}` defines `f = ∑_j c_j X^j`, and its codeword has, at
the coordinate `α ∈ F_q`, the symbol `(f^{[0]}(α), f^{[1]}(α), …, f^{[λ−1]}(α)) ∈ Σ = F_q^λ` of
the Hasse derivatives `f^{[k]}` of `f` evaluated at `α`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Lemma 2, p.18 (PDF p.21): "a univariate multiplicity code C ⊆ Σ^q over Σ = F_q^λ with
multiplicity λ and polynomials of degree less than λ³ … The code has an explicit polynomial-time
injective F_q-linear encoding."

**Formalization Note.** The coordinates `i ∈ [q]` are the field elements `α ∈ ZMod q` (all `q`
evaluation points). Multiplicity codes use Hasse derivatives `f^{[k]} = f^{(k)}/k!`
(`Polynomial.hasseDeriv`); since `λ < q`, `k!` is a unit for `k < λ`, so ordinary derivatives
give the same code up to an invertible scaling of each symbol component. The map is `F_q`-linear
by construction. -/
noncomputable def multEnc (lam q : ℕ) (c : Fin (lam ^ 3) → ZMod q) : ZMod q → Sym lam q :=
  fun α k => (hasseDeriv k.val (∑ j : Fin (lam ^ 3), C (c j) * X ^ j.val)).eval α

end QMAvsQCIP


