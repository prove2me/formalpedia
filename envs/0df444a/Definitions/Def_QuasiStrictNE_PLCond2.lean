-- Prove2me | Definitions.Def_QuasiStrictNE_PLCond2
-- name    : QuasiStrictNE_PLCond2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:17.42728+00:00
-- url     : https://prove2.me/theorems/021c6ae9-674b-4d2c-91b5-be99b582d283
-- title:
--   Condition 2 of Definition 6 (polynomial piecewise affinity)
-- statement:
--   For a family of maps $f_i:\mathbb R^{d_1(i)}\to\mathbb R^{d_2(i)}$ on domains $D_i$, indexed by instances $i$ of size $|i|$, **condition 2** holds when there is a polynomial $q$ such that every instance has a finite collection $H$ of rational hyperplanes $a^\top x=b$ dividing $D_i$ into closed regions on each of which $f_i$ is affine:
--
--   1. every coefficient of every hyperplane in $H$ is a rational number of encoding length at most $q(|i|)$;
--   2. for every choice of a side of every hyperplane of $H$ there are a rational matrix $C$ and vector $c$, all coefficients of encoding length at most $q(|i|)$, with $f_i(x)=Cx+c$ for every $x\in D_i$ on the chosen sides.
--
--   **Formalization Note** The regions are closed sign cells intersected with the domain, as in the paper's regions $R_T$ (p.16, "including its boundary"). The number of hyperplanes is not bounded, only encoding lengths.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 6.2, p.8

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding

namespace QuasiStrictNE

open QAlgorithms.LocalHamiltonian

/-- **Condition 2 of Definition 6: polynomial piecewise affinity** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Definition 6.2, p.8: "There
is a collection of hyperplanes dividing DI into polyhedral regions on each of which FI is affine.
For each cell, the coefficients of its affine formula, as well as those of each dividing hyperplane,
are rational numbers with encoding lengths polynomial in |I| uniformly").

The instances are indexed by `i : ι` with size `size i`, domain `D i ⊆ ℝ^{d₁ i}` and map
`f i : ℝ^{d₁ i} → ℝ^{d₂ i}`. The predicate holds iff there is a polynomial `q` such that for every
instance `i` there is a finite set `H` of rational hyperplanes `a⊤x = b` with

1. every coefficient of every hyperplane of `H` of encoding length at most `q(size i)`;
2. for every choice of a side of each hyperplane (a sign pattern `σ`: `true` for `a⊤x ≤ b`, `false`
   for `a⊤x ≥ b`), a rational matrix `C` and vector `c`, all coefficients of encoding length at most
   `q(size i)`, with `f i x = C x + c` for every `x ∈ D i` on the chosen side of every hyperplane.

**Formalization Note** A pair with `a = 0` is allowed and cuts nothing. The cells are the closed sign regions of the arrangement intersected with the
domain, as in the paper's own regions `R_T` on p.16 ("affine on R_T, including its boundary"). The
number of hyperplanes is not bounded (p.16 uses one for every subset `T ⊆ [m]`); only encoding lengths
are. Encoding lengths are those of the public `encRat`. The instance index and size are general so
that the condition applies to the instances of Definition 6 (strings) and to the maps of Lemma 4 and
of p.16. -/
def PLCond2 {ι : Type} (size : ι → ℕ) (d₁ d₂ : ι → ℕ) (D : ∀ i, Set (Fin (d₁ i) → ℝ))
    (f : ∀ i, (Fin (d₁ i) → ℝ) → (Fin (d₂ i) → ℝ)) : Prop :=
  ∃ q : Polynomial ℕ, ∀ i : ι, ∃ H : Finset ((Fin (d₁ i) → ℚ) × ℚ),
    (∀ h ∈ H, (∀ j, (encRat (h.1 j)).length ≤ q.eval (size i)) ∧
      (encRat h.2).length ≤ q.eval (size i)) ∧
    ∀ σ : (Fin (d₁ i) → ℚ) × ℚ → Bool,
      ∃ (C : Fin (d₂ i) → Fin (d₁ i) → ℚ) (c : Fin (d₂ i) → ℚ),
        (∀ a b, (encRat (C a b)).length ≤ q.eval (size i)) ∧
        (∀ a, (encRat (c a)).length ≤ q.eval (size i)) ∧
        ∀ x ∈ D i, (∀ h ∈ H, if σ h then ∑ j, (h.1 j : ℝ) * x j ≤ (h.2 : ℝ)
            else (h.2 : ℝ) ≤ ∑ j, (h.1 j : ℝ) * x j) →
          f i x = fun a => ∑ b, (C a b : ℝ) * x b + (c a : ℝ)

end QuasiStrictNE


