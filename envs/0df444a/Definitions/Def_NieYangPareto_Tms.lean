-- Prove2me | Definitions.Def_NieYangPareto_Tms
-- name    : NieYangPareto_Tms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:13.564117+00:00
-- url     : https://prove2.me/theorems/e21cb4d1-9b45-452e-b97f-08ce7c82dca1
-- title:
--   Truncated multisequences, the monomial vector $[x]_d$ and the pairing (2.1)
-- statement:
--   The **power set of degree $d$** is $\mathbb N^n_d:=\{\alpha\in\mathbb N^n: |\alpha|\le d\}$, where $|\alpha|=\alpha_1+\dots+\alpha_n$. A **truncated multisequence** (tms) of degree $d$ is a vector $y=(y_\alpha)_{\alpha\in\mathbb N^n_d}$ in $\mathbb R^{\mathbb N^n_d}$. The **vector of monomials** is $[x]_d:=(x^\alpha)_{\alpha\in\mathbb N^n_d}$, with $x^\alpha=x_1^{\alpha_1}\cdots x_n^{\alpha_n}$. A tms gives a linear functional on polynomials of degree at most $d$ by
--
--   $$
--   \Big\langle \sum_{\alpha\in\mathbb N^n_d}p_\alpha x^\alpha,\,y\Big\rangle:=\sum_{\alpha\in\mathbb N^n_d}p_\alpha y_\alpha .
--   $$
--
--   In particular $\langle 1,y\rangle=y_0$.
--
--   **Formalization Note** $\mathbb N^n_d$ is a finite subtype of `Fin n →₀ ℕ`, so a tms lies in a finite-dimensional space with the product (Euclidean) topology, and interior and closure mean what the page means. The pairing is meaningful for $\deg p\le d$, the only use in the mission: the sum does not see coefficients above degree $d$.
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, §2, p.4; §2.2, eq. (2.1), p.5

import Mathlib

namespace NieYangPareto

/-- The power set of degree `d`, `ℕⁿ_d = {α ∈ ℕⁿ | |α| ≤ d}`: Nie–Yang, arXiv:2108.04336v2, §2,
p.4.

**Formalization Note** A subtype of the finitely supported functions `Fin n →₀ ℕ`, the exponent type
of `MvPolynomial`, with `|α| = α.degree`. -/
abbrev TmsIndex (n d : ℕ) : Type := {α : Fin n →₀ ℕ // α.degree ≤ d}

instance (n d : ℕ) : Finite (TmsIndex n d) :=
  Finite.of_injective
    (fun α (i : Fin n) => (⟨α.1 i, Nat.lt_succ_of_le ((Finsupp.le_degree i α.1).trans α.2)⟩ :
      Fin (d + 1)))
    (fun α β h => Subtype.ext (Finsupp.ext fun i => by
      simpa using congrArg Fin.val (congrFun h i)))

noncomputable instance (n d : ℕ) : Fintype (TmsIndex n d) := Fintype.ofFinite _

/-- The label `α = 0` of `ℕⁿ_d`, the coordinate `y₀` of a tms. -/
def TmsIndex.zero (n d : ℕ) : TmsIndex n d := ⟨0, by simp⟩

/-- A truncated multisequence (tms) of degree `d`, `y = (y_α)_{α ∈ ℕⁿ_d} ∈ ℝ^{ℕⁿ_d}`:
Nie–Yang, arXiv:2108.04336v2, §2.2, p.5.

**Formalization Note** Functions on the finite type `ℕⁿ_d`, with the product topology, which is the
Euclidean one. -/
abbrev Tms (n d : ℕ) : Type := TmsIndex n d → ℝ

/-- The monomial value `x^α = x₁^{α₁} ⋯ xₙ^{αₙ}`: Nie–Yang, arXiv:2108.04336v2, §2, p.4. -/
def monomialValue {n : ℕ} (x : Fin n → ℝ) (α : Fin n →₀ ℕ) : ℝ :=
  ∏ i, x i ^ α i

/-- The vector of monomials `[x]_d = (x^α)_{α ∈ ℕⁿ_d}`: Nie–Yang, arXiv:2108.04336v2, §2, p.4. -/
def monomialVector {n : ℕ} (d : ℕ) (x : Fin n → ℝ) : Tms n d :=
  fun α => monomialValue x α.1

/-- The pairing (2.1), `⟨Σ_{α ∈ ℕⁿ_d} p_α x^α, y⟩ = Σ_{α ∈ ℕⁿ_d} p_α y_α`: Nie–Yang,
arXiv:2108.04336v2, eq. (2.1), p.5.

**Formalization Note** The pairing is meaningful for `deg p ≤ d`, the only use in the mission. The
sum runs over `ℕⁿ_d`, so coefficients of `p` above degree `d` are not seen. -/
noncomputable def pair {n d : ℕ} (p : MvPolynomial (Fin n) ℝ) (y : Tms n d) : ℝ :=
  ∑ α : TmsIndex n d, p.coeff α.1 * y α

end NieYangPareto


