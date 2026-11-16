-- Prove2me | Definitions.Def_PCNonBool_Supplement_CuttingPlanes
-- name    : PCNonBool_Supplement_CuttingPlanes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:28:00.150998+00:00
-- url     : https://prove2.me/theorems/77aa0071-7a0c-4caa-bd14-f63ccd239ea9
-- title:
--   Cutting planes over literals: derivations, refutations, length and coefficient size
-- statement:
--   Cutting planes works with linear inequalities over the literals of $n$ Boolean variables in the normal form
--   $$\sum_i a_i x_i+\sum_i \bar a_i\bar x_i\ \ge\ b,\qquad a_i,\bar a_i\in\mathbb N,\ b\in\mathbb Z,$$
--   where $\bar x_i=1-x_i$. A **derivation** from a set $\mathcal L$ of inequalities is a sequence of inequalities each of which is
--
--   1. a literal axiom $x_i\ge0$ or $\bar x_i\ge0$;
--   2. an inequality of $\mathcal L$;
--   3. the sum of two earlier lines, in normalized form (each pair $x_i+\bar x_i$ on the left is replaced by $1$, i.e. subtracted from the right-hand side);
--   4. an earlier line multiplied by some $c\in\mathbb N$; or
--   5. an earlier line divided by some $c\ge1$ that divides all its coefficients, with right-hand side rounded up to $\lceil b/c\rceil$.
--
--   A **refutation** is a derivation of $0\ge1$. Its **length** is the number of its lines, and its **coefficient size** is the sum of the magnitudes of all coefficients in it, right-hand sides included.
--
--   **Formalization Note** A refutation is a derivation that contains the line $0\ge1$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.5, (4a)–(4e), p.12 (PDF p.15)

import Mathlib

namespace PCNonBool.Supplement

/-- A linear inequality over the literals of `n` Boolean variables, in the normal form used for
cutting planes with dual variables (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.5, p.12 (PDF p.15)):
`∑_i a_i x_i + ∑_i ā_i x̄_i ≥ b` with `a_i, ā_i ∈ ℕ` and `b ∈ ℤ`, where `x̄_i = 1 - x_i`. -/
structure Ineq (n : ℕ) where
  /-- the coefficient `a_i` of the positive literal `x_i` -/
  pos : Fin n → ℕ
  /-- the coefficient `ā_i` of the negative literal `x̄_i` -/
  neg : Fin n → ℕ
  /-- the right-hand side `b` -/
  rhs : ℤ

namespace Ineq

variable {n : ℕ}

/-- Normalized form (p.12): every pair `x_i + x̄_i` on the left-hand side is replaced by `1`, i.e.
`min(a_i, ā_i)` is subtracted from both coefficients and from the right-hand side. -/
def normalize (L : Ineq n) : Ineq n where
  pos i := L.pos i - min (L.pos i) (L.neg i)
  neg i := L.neg i - min (L.pos i) (L.neg i)
  rhs := L.rhs - ∑ i, ((min (L.pos i) (L.neg i) : ℕ) : ℤ)

/-- The addition rule (4c), followed by normalization. -/
def add (L L' : Ineq n) : Ineq n :=
  normalize ⟨fun i => L.pos i + L'.pos i, fun i => L.neg i + L'.neg i, L.rhs + L'.rhs⟩

/-- The scalar multiplication rule (4d) by `c ∈ ℕ`. -/
def smul (c : ℕ) (L : Ineq n) : Ineq n :=
  ⟨fun i => c * L.pos i, fun i => c * L.neg i, (c : ℤ) * L.rhs⟩

/-- The division rule (4e) by `c`: every coefficient divided by `c` (it is applied only when `c`
divides all of them) and the right-hand side rounded up, `⌈b/c⌉`. -/
def div (c : ℕ) (L : Ineq n) : Ineq n :=
  ⟨fun i => L.pos i / c, fun i => L.neg i / c, ⌈(L.rhs : ℚ) / (c : ℚ)⌉⟩

/-- The literal axiom `x_i ≥ 0` (4a). -/
def litPos (i : Fin n) : Ineq n := ⟨Pi.single i 1, 0, 0⟩

/-- The literal axiom `x̄_i ≥ 0`, the normalized form of `-x_i ≥ -1` (4a). -/
def litNeg (i : Fin n) : Ineq n := ⟨0, Pi.single i 1, 0⟩

/-- The contradiction `0 ≥ 1`. -/
def falsum : Ineq n := ⟨0, 0, 1⟩

/-- `‖ℓ‖ = ∑ a_i + ∑ ā_i`, the `L¹` norm of the left-hand side (p.58 (PDF p.61)). -/
def norm (L : Ineq n) : ℕ := ∑ i, (L.pos i + L.neg i)

/-- The sum of the coefficient magnitudes of one inequality, right-hand side included. -/
def coeffWeight (L : Ineq n) : ℕ := L.norm + L.rhs.natAbs

end Ineq

/-- A cutting planes derivation from the initial inequalities `Ls` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.5, (4a)–(4e), p.12
(PDF p.15)), over literals with dual variables: every line is a literal axiom `x_i ≥ 0` or
`x̄_i ≥ 0` (4a), an initial axiom (4b), the normalized sum of two earlier lines (4c), a multiple of
an earlier line by `c ∈ ℕ` (4d), or an earlier line divided by `c ≥ 1` dividing all its
coefficients, with right-hand side `⌈b/c⌉` (4e). -/
def IsCPDerivation {n : ℕ} (Ls : List (Ineq n)) (π : List (Ineq n)) : Prop :=
  ∀ (k : ℕ) (hk : k < π.length),
    (∃ i : Fin n, π[k] = Ineq.litPos i ∨ π[k] = Ineq.litNeg i) ∨
    π[k] ∈ Ls ∨
    (∃ (i j : ℕ) (hi : i < k) (hj : j < k),
      π[k] = (π[i]'(hi.trans hk)).add (π[j]'(hj.trans hk))) ∨
    (∃ (i : ℕ) (hi : i < k) (c : ℕ), π[k] = (π[i]'(hi.trans hk)).smul c) ∨
    (∃ (i : ℕ) (hi : i < k) (c : ℕ), 1 ≤ c ∧
      (∀ l, c ∣ (π[i]'(hi.trans hk)).pos l) ∧ (∀ l, c ∣ (π[i]'(hi.trans hk)).neg l) ∧
      π[k] = (π[i]'(hi.trans hk)).div c)

/-- A cutting planes refutation of `Ls`: a derivation containing `0 ≥ 1` (p.12). Its **length** is
`π.length`, the number of inequalities in it. -/
def IsCPRefutation {n : ℕ} (Ls : List (Ineq n)) (π : List (Ineq n)) : Prop :=
  IsCPDerivation Ls π ∧ Ineq.falsum ∈ π

/-- The **coefficient size** of a cutting planes derivation: the sum of all coefficient magnitudes
in it (p.12), `∑_lines (∑_i a_i + ∑_i ā_i + |b|)`.

**Formalization Note** The right-hand sides are counted (the line `0 ≥ 1` has coefficient size
`1`, so a refutation has coefficient size at least `1`). -/
def cpCoeffSize {n : ℕ} (π : List (Ineq n)) : ℕ := (π.map Ineq.coeffWeight).sum

end PCNonBool.Supplement


