-- Prove2me | Definitions.Def_CyclotomicRankTwoSVP_Main_Checker
-- name    : CyclotomicRankTwoSVP_Main_Checker
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:55.607166+00:00
-- url     : https://prove2.me/theorems/0088f9be-1282-4018-98e1-b15bb543fac1
-- title:
--   Rectangular X3C data, separated offsets and the concrete cyclotomic checker
-- statement:
--   The universe size $M$ and family size $n$ are independent. An incidence matrix $A$ is Boolean, and the X3C condition requires exactly three ones in every column. Nondegeneracy is the source construction regime $M,n>0$ with no zero row. Exact covers are Boolean vectors $\xi$ with $A\xi=1_M$ over the integers; the residual is $\|A\xi-1_M\|_2^2$.
--
--   The incidence set $I$ has size $W$. For integer Sidon positions $\alpha$, set $\tau=2\alpha_\star+1$, $\beta_i=\tau i$ using one-based row labels, and $d_{ij}=\beta_i-\alpha_j\pmod q$. Witness offsets and bad offsets are precisely the directed witness differences, the cross-row incidence differences, and all incidence sums, including repeated incidences. Define
--
--   $$g=\sum_{(i,j)\in I}(\zeta^{d_{ij}}+\zeta^{-d_{ij}}),\quad V=6\sum_j\zeta^{\alpha_j},\quad Q=128W^4h,\quad U=Q+g^2,\quad\kappa=2q/Q.$$
--
--   Cyclic correlations, the actual three-term error from (19), the remainder $N(g^2[x]-V)/Q^2$, the checker squared norm $N(U[x]-V)/Q^2$, and $B_0$ from (18) have explicit bodies. Admissibility is exactly (20). Neither positivity nor correctness of this checker is assumed by the definitions. This layer separates the general rectangular exact-cover data from the paper-specific checker.
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), §§2.3,4.1–4.3, printed pp. 7,14–19 / PDF pp. 8,15–20, (13)–(21)

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Counting

noncomputable section

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

abbrev Incidence (M n : ℕ) := Fin M → Fin n → Bool

def IsX3C {M n : ℕ} (A : Incidence M n) : Prop :=
  ∀ j, (Finset.univ.filter fun i => A i j).card = 3

def Nondegenerate {M n : ℕ} (A : Incidence M n) : Prop :=
  0 < M ∧ 0 < n ∧ ∀ i, ∃ j, A i j = true

def exactCover {M n : ℕ} (A : Incidence M n) (ξ : Fin n → Bool) : Prop :=
  ∀ i, (∑ j, if A i j && ξ j then (1 : ℤ) else 0) = 1

def residual {M n : ℕ} (A : Incidence M n) (ξ : Fin n → Bool) : ℝ :=
  ∑ i, ((∑ j, if A i j && ξ j then (1 : ℝ) else 0) - 1) ^ 2

def incidences {M n : ℕ} (A : Incidence M n) : Finset (Fin M × Fin n) :=
  Finset.univ.filter fun ij => A ij.1 ij.2

def W {M n : ℕ} (A : Incidence M n) : ℕ := (incidences A).card

def alphaStar {n : ℕ} (α : Fin n → ℕ) : ℕ := Finset.univ.sup α

def tau {n : ℕ} (α : Fin n → ℕ) : ℕ := 2 * alphaStar α + 1

def beta {n : ℕ} (α : Fin n → ℕ) (i : ℕ) : ℕ := tau α * i

def offset {M n : ℕ} (q : ℕ) (α : Fin n → ℕ) (ij : Fin M × Fin n) : ZMod q :=
  (beta α (ij.1.val + 1) : ZMod q) - (α ij.2 : ZMod q)

def Dwit {n : ℕ} (q : ℕ) (α : Fin n → ℕ) : Finset (ZMod q) :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter fun jl => jl.1 ≠ jl.2).image
    (fun jl => (α jl.2 : ZMod q) - (α jl.1 : ZMod q))

def Dbad {M n : ℕ} (q : ℕ) (A : Incidence M n) (α : Fin n → ℕ) : Finset (ZMod q) :=
  (((incidences A ×ˢ incidences A).filter fun p => p.1.1 ≠ p.2.1).image
    (fun p => offset q α p.1 - offset q α p.2)) ∪
  ((incidences A ×ˢ incidences A).image (fun p => offset q α p.1 + offset q α p.2))

def g {q M n : ℕ} [NeZero q] (A : Incidence M n) (α : Fin n → ℕ) : K q :=
  ∑ ij ∈ incidences A,
    (zeta q ^ (offset q α ij).val + zeta q ^ (-offset q α ij).val)

def V {q n : ℕ} (α : Fin n → ℕ) : K q := 6 * ∑ j, zeta q ^ α j

def Q {M n : ℕ} (k : ℕ) (A : Incidence M n) : ℕ := 128 * W A ^ 4 * h k

def U {q M n : ℕ} [NeZero q] (k : ℕ) (A : Incidence M n) (α : Fin n → ℕ) : K q :=
  (Q k A : K q) + (g (q := q) A α) ^ 2

def kappa {M n : ℕ} (q k : ℕ) (A : Incidence M n) : ℝ := 2 * q / Q k A

def B₀ {M n : ℕ} (q k : ℕ) (A : Incidence M n) : ℝ :=
  H q k + kappa q k A *
    (2 * W A * h k - 2 * M + (2 * h k * W A - 4 * (h k : ℝ) ^ 2 * W A ^ 2) / q)

def bitsZ {q : ℕ} (x : ZMod q → Bool) : ZMod q → ℤ := fun a => if x a then 1 else 0

def bitsR {q : ℕ} (x : ZMod q → Bool) : ZMod q → ℝ := fun a => if x a then 1 else 0

def weight {q : ℕ} [NeZero q] (x : ZMod q → Bool) : ℕ :=
  (Finset.univ.filter fun a => x a).card

def selected {q n : ℕ} (α : Fin n → ℕ) (x : ZMod q → Bool) : Fin n → Bool :=
  fun j => x (α j : ZMod q)

def correlation {q : ℕ} [NeZero q] (x : ZMod q → Bool) (d : ZMod q) : ℝ :=
  ∑ a, bitsR x a * bitsR x (a + d)

def errorTerm {q M n : ℕ} [NeZero q] (A : Incidence M n) (α : Fin n → ℕ)
    (x : ZMod q → Bool) : ℝ :=
  2 * (∑ i, ∑ j, ∑ l,
    if A i j && A i l && decide (j ≠ l) then
      correlation x ((α l : ZMod q) - α j) - bitsR x (α j) * bitsR x (α l) else 0) +
  2 * (∑ p ∈ incidences A ×ˢ incidences A,
    if p.1.1 ≠ p.2.1 then correlation x (offset q α p.1 - offset q α p.2) else 0) +
  2 * (∑ p ∈ incidences A ×ˢ incidences A, correlation x (offset q α p.1 + offset q α p.2))

def remainder {q M n : ℕ} [NeZero q] (k : ℕ) (A : Incidence M n) (α : Fin n → ℕ)
    (x : ZMod q → Bool) : ℝ :=
  N ((g A α) ^ 2 * evalZ (bitsZ x) - V α) / (Q k A : ℝ) ^ 2

def checkerSquared {q M n : ℕ} [NeZero q] (k : ℕ) (A : Incidence M n)
    (α : Fin n → ℕ) (x : ZMod q → Bool) : ℝ :=
  N (U k A α * evalZ (bitsZ x) - V α) / (Q k A : ℝ) ^ 2

def admissible {q M n : ℕ} [NeZero q] (A : Incidence M n) (α : Fin n → ℕ)
    (x : ZMod q → Bool) : Prop :=
  (∀ j l : Fin n, j ≠ l →
    correlation x ((α l : ZMod q) - α j) = bitsR x (α j) * bitsR x (α l)) ∧
  ∀ d ∈ Dbad q A α, correlation x d = 0

end CyclotomicRankTwoSVP.Main


