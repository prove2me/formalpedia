-- Prove2me | Definitions.Def_GeoQAC_Supplement_fourierCoeff
-- name    : GeoQAC_Supplement_fourierCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:17:02.652593+00:00
-- url     : https://prove2.me/theorems/b017290f-762e-4260-9023-9ed73f2552ff
-- title:
--   Fourier coefficients, the tail weight $W^{\ge k}$, the sign representation
-- statement:
--   For $S\subseteq[n]$ the **character** is $\chi_S(x)=(-1)^{\sum_{j\in S}x_j}$. For a function $u$ on the cube, its **Fourier coefficient** and its **Fourier weight at degrees at least $k$** are
--   $$
--   \hat u(S)=\mathbb E_x[u(x)\chi_S(x)],\qquad W^{\ge k}[u]=\sum_{|S|\ge k}|\hat u(S)|^2,
--   $$
--   with $x$ uniform on $\{0,1\}^n$. For a Boolean function $f$, the **sign representation** is $h=(-1)^f$ and its mean is $\mu=\mathbb E_x[h(x)]$.
--
--   These quantities state the Fourier tail bound of Theorem 3.13.
--
--   **Formalization Note** Coordinates are $\mathrm{Fin}\,n$ and subsets are finsets. The definitions are stated for real-valued $u$, which is all that is used ($h$ is real), so $|\hat u(S)|^2=\hat u(S)^2$.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), §2.1, p.9

import Mathlib

namespace GeoQAC.Supplement

/-!
# Fourier coefficients on the cube and the Fourier tail weight `W^{≥k}`

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), §2.1, p.9: "For a Boolean function
`f : {0,1}^n → {0,1}`, write `h = (−1)^f` for its sign representation … and `µ = E_x[h(x)]`. …
For `S ⊆ [n]`, define `χ_S(x) = (−1)^{Σ_{j∈S} x_j}`. For a complex-valued function `u` on the cube,
define `û(S) = E_x[u(x)χ_S(x)]` … The Fourier weight at degrees at least `k` is
`W^{≥k}[u] = Σ_{|S|≥k} |û(S)|²`." Expectations over `x` are uniform (p.9).

**Formalization Note.** Coordinates are `Fin n` (the paper's `[n]` is `{1, …, n}`); a subset is a
`Finset (Fin n)`. These definitions are stated for real-valued `u`, which is all the supplement uses
(`h = (−1)^f` is real); then `|û(S)|² = û(S)²`.
-/

/-- The character `χ_S(x) = (−1)^{Σ_{j∈S} x_j}` (p.9). -/
def chiS {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  (-1) ^ (S.filter fun j => x j = true).card

/-- The Fourier coefficient `û(S) = E_x[u(x) χ_S(x)]`, `x` uniform on `{0,1}^n` (p.9). -/
noncomputable def fourierCoeff {n : ℕ} (u : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) : ℝ :=
  (∑ x, u x * chiS S x) / 2 ^ n

/-- The Fourier weight at degrees at least `k`: `W^{≥k}[u] = Σ_{|S| ≥ k} û(S)²` (p.9). -/
noncomputable def fourierWeightGe {n : ℕ} (u : (Fin n → Bool) → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => k ≤ S.card), fourierCoeff u S ^ 2

/-- The sign representation `h = (−1)^f` of a Boolean function (p.9): `h(x) = −1` when `f(x) = 1`
and `h(x) = 1` when `f(x) = 0`. -/
def signFn {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℝ :=
  if f x then -1 else 1

/-- The mean `µ = E_x[h(x)]` of the sign representation, `x` uniform (p.9). -/
noncomputable def signMean {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  (∑ x, signFn f x) / 2 ^ n

end GeoQAC.Supplement


