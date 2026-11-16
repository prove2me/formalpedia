-- Prove2me | Definitions.Def_FasterPrimeEnum_Supplement_kappa
-- name    : FasterPrimeEnum_Supplement_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:48:23.370267+00:00
-- url     : https://prove2.me/theorems/1f63be8d-d89e-4dbc-8a06-fdc5602105b2
-- title:
--   The compression map $\kappa:\mathbb F_2^T\to\mathbb F_2^S$ and the permutation map $Q_\pi$
-- statement:
--   Let $T$ and $R\le T/2$ be positive integers and $\lambda:=\mathrm{lg}(T+1)=\max(1,\lceil\log_2(T+1)\rceil)$. Fix an irreducible $h\in\mathbb F_2[z]$ of degree $\lambda$, so $\mathbb F_{2^\lambda}=\mathbb F_2[z]/h(z)$, and a generator $\beta$ of $\mathbb F_{2^\lambda}^*$ (multiplicative order $2^\lambda-1$).
--
--   For $a\in\mathbb F_2^T$ let $\phi_a(x)=a_0+a_1x+\dots+a_{T-1}x^{T-1}$. The **compression map** is
--
--   $$
--   \kappa(a):=\psi\big(\phi_a(1),\phi_a(\beta),\dots,\phi_a(\beta^{2R-1})\big)\in\mathbb F_2^S,\qquad S:=2\lambda R,
--   $$
--
--   where $\psi$ writes each $u_0+u_1z+\dots+u_{\lambda-1}z^{\lambda-1}\in\mathbb F_{2^\lambda}$ as $(u_0,\dots,u_{\lambda-1})$ and concatenates.
--
--   For a permutation $\pi$ of $\{0,\dots,T-1\}$, $Q_\pi(a_0,\dots,a_{T-1}):=(a_{\rho_0},\dots,a_{\rho_{T-1}})$ with $\rho=\pi^{-1}$, and $\kappa_\pi:=\kappa\circ Q_\pi$ (§9.1).
--
--   The map $\kappa$ is a Reed–Solomon-type syndrome: it is injective on vectors of weight at most $R$, which lets the core algorithm work with $S\ll R\log T$ bits per interval instead of $T$.
--
--   **Formalization Note** $h$ and $\beta$ are polynomials over `ZMod 2` (`FieldData`); `IsFieldData λ d` says $h$ is monic irreducible of degree $\lambda$ and the class of $\beta$ in `AdjoinRoot h` has order $2^\lambda-1$. The value $\phi_a(\beta^j)$ is computed as $\sum_t a_t\beta^{jt}$ reduced modulo $h$.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), §5.1, eqs. (5.1)–(5.2), pp.35–36; §9.1, p.87

import Mathlib

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

open Polynomial

/-- `lg x := max(1, ⌈log₂ x⌉)` (D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851, held
version, sha256 7fc13f17…, §1.1, p.1) at `x = T + 1`: the degree `λ := lg(T + 1)` of eq. (5.1), p.35.
For an integer `x ≥ 1`, `⌈log₂ x⌉` is `Nat.clog 2 x`. -/
def lam (T : ℕ) : ℕ := max 1 (Nat.clog 2 (T + 1))

/-- The data fixing the field `F_{2^λ} = F₂[z]/h(z)` and the generator `β` of §5.1, p.35: a
polynomial `h ∈ F₂[z]` and a polynomial `β ∈ F₂[z]` representing an element of `F₂[z]/h(z)`. -/
structure FieldData where
  /-- The modulus `h(z)`. -/
  h : Polynomial (ZMod 2)
  /-- A representative of `β`. -/
  β : Polynomial (ZMod 2)

/-- **Valid field data of degree `λ`** — §5.1, p.35: "we will represent the field F_{2^λ} as
F₂[z]/h(z) for a fixed irreducible h ∈ F₂[z] of degree λ. We also fix a generator β ∈ F*_{2^λ}, so
that ord β = 2^λ − 1 ⩾ T ⩾ 2R." `h` is monic irreducible of degree `λ`, and the class of `β` in
`F₂[z]/h(z)` has multiplicative order `2^λ − 1`, i.e. generates the multiplicative group.

**Formalization Note.** Over `F₂` every nonzero polynomial is monic; monicity is stated so that
reduction modulo `h` (`%ₘ`) is the usual one. -/
def IsFieldData (lam : ℕ) (d : FieldData) : Prop :=
  d.h.Monic ∧ Irreducible d.h ∧ d.h.natDegree = lam ∧
    orderOf (AdjoinRoot.mk d.h d.β) = 2 ^ lam - 1

/-- **The compression map `κ : F₂^T → F₂^S`** — D. Harvey, *Faster enumeration of primes*,
arXiv:2606.22851 (held version, sha256 7fc13f17…), §5.1, eqs. (5.1)–(5.2), pp.35–36: "Given a
vector a ∈ F₂^T, consider the polynomial φ_a(x) := a_0 + a_1x + ⋯ + a_{T−1}x^{T−1} ∈ F₂[x]_T.
Evaluating φ_a(x) at the points β^j for j = 0, …, 2R − 1, we obtain the vector
κ̃(a) := (φ_a(β^j))_{j=0}^{2R−1} ∈ (F_{2^λ})^{2R}. Each copy of F_{2^λ} = F₂[z]/h(z) is isomorphic to
F₂^λ via the map sending u_0 + u_1z + ⋯ + u_{λ−1}z^{λ−1} to (u_0, u_1, …, u_{λ−1}). By concatenating
these vectors for j = 0, …, 2R − 1 we obtain an isomorphism ψ : (F_{2^λ})^{2R} → F₂^S where
S := 2λR. Finally we put κ(a) := ψ(κ̃(a))."

`a` is the bit list `(a_0, …, a_{T−1})`. The value `φ_a(β^j) = Σ_t a_t β^{jt}` is computed in
`F₂[z]` and reduced modulo `h`; its `λ = lam T` coefficients `u_0, …, u_{λ−1}` are listed for
`j = 0, …, 2R − 1` in turn, giving `S = 2λR` bits.

**Formalization Note.** `κ` depends on the fixed `h` and `β` (`d`); it is the paper's `κ` exactly
when `IsFieldData (lam T) d`. -/
noncomputable def kappa (d : FieldData) (T R : ℕ) (a : List Bool) : List Bool :=
  (List.range (2 * R)).flatMap fun j => (List.range (lam T)).map fun i =>
    decide ((((Finset.range T).sum fun t => if a.getD t false then d.β ^ (j * t) else 0) %ₘ
      d.h).coeff i = 1)

/-- **The permutation map `Q_π`** — §9.1, p.87: "For any π = (π_0, …, π_{T−1}) ∈ Π_T define a
corresponding injective linear map Q_π : F₂^T → F₂^T by sending the basis element e_t to e_{π_t} for
each t = 0, …, T − 1. Equivalently, Q_π(a_0, …, a_{T−1}) := (a_{ρ_0}, …, a_{ρ_{T−1}}) where
ρ := π^{−1} is the inverse permutation." The permuted compression map is `κ_π := κ ∘ Q_π`. -/
def permVec {T : ℕ} (π : Equiv.Perm (Fin T)) (a : List Bool) : List Bool :=
  List.ofFn fun t : Fin T => a.getD (π.symm t) false

end Supplement

end FasterPrimeEnum


