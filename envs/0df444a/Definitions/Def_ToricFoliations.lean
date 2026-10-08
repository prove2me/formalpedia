-- Prove2me | Definitions.Def_ToricFoliations
-- name    : ToricFoliations
-- status  : Definition
-- author  : @hiraeth
-- created : 2026-10-07T12:29:49.040023+00:00
-- url     : https://prove2.me/theorems/cab2756f-7fab-442b-836a-d1d2ee34f2b7
-- title:
--   Toric foliations — lattice, wall data, foliated length, and $\mathbb P^r$-bundle data
-- statement:
--   **definition_name:** `ToricFoliations`
--   **definition_title:** Toric foliations — lattice, wall data, foliated length, and $\mathbb P^r$-bundle data
--
--   Define the toric combinatorial core used in the proof of Theorem 1.3 of
--   Fujino–Sato.
--
--   Fix a dimension $n\ge1$. The lattice is $N=\mathbb Z^n$ and its
--   complexification is $N_{\mathbb C}=\mathbb C^n$; a toric foliation is
--   represented, via Pang's correspondence, by a $\mathbb C$-subspace
--   $V\subseteq N_{\mathbb C}$ of rank $r=\dim_{\mathbb C}V$.
--
--   For a torus-invariant curve $C=V(W)$ of a complete simplicial fan, let
--   $v_1,\dots,v_{n+1}$ be the primitive vectors appearing in Reid's description
--   of the wall $W$ and of the two adjacent maximal cones $\sigma,\sigma'$. The
--   type `WallData n` packages:
--
--   - the vectors $v_i\in N$ and the integers $a_i\in\mathbb Z$ satisfying the
--     wall relation $\sum_i a_i v_i=0$ of equation (3.1), with
--     $a_n,a_{n+1}>0$, with the ordering $a_1\le\cdots\le a_{n+1}$, and with
--     $\gcd(a_1,\dots,a_{n+1})=1$ (stated as a Bézout identity);
--   - the multiplicities $\mathrm{mult}(W),\mathrm{mult}(\sigma),
--     \mathrm{mult}(\sigma')$, assumed positive with
--     $\mathrm{mult}(W)\mid\mathrm{mult}(\sigma)$ and
--     $\mathrm{mult}(W)\mid\mathrm{mult}(\sigma')$.
--
--   `divisorIntersection` implements the intersection numbers from equation (3.1):
--
--   $$
--   D_{v_i}\cdot C=
--   \begin{cases}
--   0 & v_i\notin\{v_1,\dots,v_{n+1}\},\\
--   \dfrac{a_i\,\mathrm{mult}(W)}{a_n\,\mathrm{mult}(\sigma)} & 1\le i\le n,\\[6pt]
--   \dfrac{\mathrm{mult}(W)}{\mathrm{mult}(\sigma')} & i=n+1.
--   \end{cases}
--   $$
--
--   `curveLength` is the foliated length
--   $-K_{\mathscr F}\cdot C=\sum_{v_i\in V}D_{v_i}\cdot C$; `ExtremalRay` and
--   `rayLength` package an abstract extremal ray and the minimum
--   $l_{\mathscr F}(R)=\min_{[C]\in R}\{-K_{\mathscr F}\cdot C\}$;
--   `IsProjectiveSpaceBundle` encodes the conclusion of Theorem 1.3(2): the tail
--   vectors sum to zero, span a saturated rank-$r$ sublattice, and give a lattice
--   splitting $N\cong\mathbb Z^r\times\mathbb Z^{n-r}$ — the toric data of a
--   $\mathbb P^r$-bundle.
--
--   **Formalization Note.** `Lattice n := Fin n → ℤ`, `Complexified n := Fin n → ℂ`,
--   `V` is a `Submodule ℂ (Complexified n)`, and the rank is
--   `Module.finrank ℂ V`. Division by zero is total in `ℚ`, so no side conditions
--   are needed inside `divisorIntersection`.
-- source:
--   Fujino--Sato 2024, A remark on toric foliations, Arch. Math. 122 (2024) 621--627, https://doi.org/10.1007/s00013-024-01991-1 (arXiv:2309.09461), Sections 1 and 3

import Mathlib

open scoped BigOperators

/-!
# Toric foliations: combinatorial core of Fujino--Sato, "A remark on toric foliations"

This file formalizes the *combinatorial core* of Theorem 1.3 of

  Osamu Fujino and Hiroshi Sato,
  *A remark on toric foliations*,
  Arch. Math. 122 (2024), 621--627.
  https://doi.org/10.1007/s00013-024-01991-1

The full statement of Theorem 1.3 lives in toric Mori theory (projective
`Q`-factorial toric varieties, saturated torus-equivariant subsheaves of the
tangent sheaf, the Mori cone, extremal contraction morphisms).  Mathlib does
not yet contain that machinery, so this mission fixes the combinatorial data
the proof of Section 3 actually uses:

* a lattice `N = Z^n` together with its complexification `N_C = C^n`;
* a wall `W` of a complete simplicial fan, i.e. a relation
  `sum_i a_i v_i = 0` among the `n+1` primitive vectors `v_1,...,v_{n+1}`
  appearing in Reid's description of toric extremal contractions;
* a toric foliation, represented (via Pang's correspondence) by a complex
  subspace `V <= N_C`;
* the intersection numbers `D_{v_i} . C` computed by equation (3.1) of the
  paper, which build the foliated length `-K_F . C`.

The geometric wrapper (sheaves, Mori cone, contraction morphisms, relative
tangent sheaf) is deliberately left as future work; the goal theorem is the
faithful lattice/fan content of Theorem 1.3.
-/

namespace ToricFoliations

/-- The lattice `N = Z^n` of a toric variety of dimension `n`. -/
abbrev Lattice (n : ℕ) := Fin n → ℤ

/-- The complexification `N_C = C^n`. -/
abbrev Complexified (n : ℕ) := Fin n → ℂ

/-- The natural inclusion `N -> N_C`. -/
def toComplex {n : ℕ} (x : Lattice n) : Complexified n :=
  fun i => (x i : ℂ)

/-- The index of `v_{n+1}` among the `n+1` vectors `v_1,...,v_{n+1}`.
(We use 0-based `Fin (n+1)` indices, so `lastIndex n = n`.) -/
def lastIndex (n : ℕ) : Fin (n + 1) :=
  ⟨n, Nat.lt_succ_self n⟩

/-- The index of `v_n` among the `n+1` vectors (0-based index `n-1`). -/
def wallIndex (n : ℕ) (hn : 0 < n) : Fin (n + 1) :=
  ⟨n - 1, by omega⟩

/--
The wall data of a torus-invariant curve `C = V(W)` in a complete simplicial
fan, following equations (3.1)--(3.3) and Proposition 14-1-5 of Matsuki's
book as used in the proof of Theorem 1.3.

`v : Fin (n+1) -> N` lists the primitive vectors; `a : Fin (n+1) -> Z` are the
integers in the wall relation `sum_i a_i v_i = 0`; `mWall`, `mSigma`,
`mSigma'` are the multiplicities of the wall `W` and of the two maximal cones
`sigma`, `sigma'` adjacent to `W`.
-/
structure WallData (n : ℕ) where
  hn : 0 < n
  v : Fin (n + 1) → Lattice n
  a : Fin (n + 1) → ℤ
  /-- The wall relation (3.1): `sum_i a_i v_i = 0`. -/
  relation : (∑ i : Fin (n + 1), a i • v i) = 0
  /-- `a_n > 0` (paper index `n`, Lean index `n-1`). -/
  an_pos : 0 < a (wallIndex n hn)
  /-- `a_{n+1} > 0`. -/
  aLast_pos : 0 < a (lastIndex n)
  /-- After reordering, (3.2): `a_1 <= ... <= a_{n+1}`. -/
  sorted : ∀ i j : Fin (n + 1), i.val ≤ j.val → a i ≤ a j
  /-- Multiplicity of the wall `W`. -/
  mWall : ℕ
  /-- Multiplicity of the maximal cone `sigma`. -/
  mSigma : ℕ
  /-- Multiplicity of the maximal cone `sigma'`. -/
  mSigma' : ℕ
  mWall_pos : 0 < mWall
  mSigma_pos : 0 < mSigma
  mSigma'_pos : 0 < mSigma'
  /-- `mult(W) | mult(sigma)`, used for `D . C <= 1`. -/
  wall_dvd_sigma : mWall ∣ mSigma
  /-- `mult(W) | mult(sigma')`, used for `D . C <= 1`. -/
  wall_dvd_sigma' : mWall ∣ mSigma'
  /-- `gcd(a_1,...,a_{n+1}) = 1` via a Bézout identity. -/
  gcd_one : ∃ b : Fin (n + 1) → ℤ, (∑ i : Fin (n + 1), b i * a i) = 1

/--
The intersection number `D_{v_i} . C` from equation (3.1) of the paper:
for `i = n+1` it is `mult(W)/mult(sigma')`, and for every other index it is
`a_i * mult(W) / (a_n * mult(sigma))`.  Division by zero is total in `Q`,
so no side conditions are needed in the definition.
-/
noncomputable def divisorIntersection {n : ℕ} (C : WallData n) (i : Fin (n + 1)) : ℚ :=
  if i = lastIndex n then
    (C.mWall : ℚ) / (C.mSigma' : ℚ)
  else
    (C.a i : ℚ) * (C.mWall : ℚ) / ((C.a (wallIndex n C.hn) : ℚ) * (C.mSigma : ℚ))

/--
The foliated length `-K_F . C = sum_{v_i in V} D_{v_i} . C` of a
torus-invariant curve `C`, for the toric foliation represented by the complex
subspace `V` (see equation (1.1)--(1.2) and the proof of Theorem 1.3).
-/
noncomputable def curveLength {n : ℕ} (C : WallData n)
    (V : Submodule ℂ (Complexified n)) : ℚ := by
  classical
  exact ∑ i : Fin (n + 1), if toComplex (C.v i) ∈ V then divisorIntersection C i else 0

/--
An abstract extremal ray of the Mori cone: a set of torus-invariant curves
plus an (intentionally opaque) extremality predicate.  Making `isExtremal`
concrete is part of the mission's future work of connecting this combinatorial
core to toric Mori theory.
-/
structure ExtremalRay (n : ℕ) where
  /-- The torus-invariant curves whose classes span the ray. -/
  curves : Finset (WallData n)
  nonempty : curves.Nonempty
  isExtremal : Prop

/--
The length `l_F(R) = min_{[C] in R} (-K_F . C)` of an extremal ray with
respect to the toric foliation represented by `V`.
-/
noncomputable def rayLength {n : ℕ} (R : ExtremalRay n)
    (V : Submodule ℂ (Complexified n)) : ℚ := by
  classical
  exact R.curves.inf' R.nonempty (fun C : WallData n => curveLength C V)

/--
The index of the paper's `v_{n-r+j}` (1-based) inside `Fin (n+1)`: for
`0 <= j <= r` this is `n-r+j`.  These are the tail indices that appear in
equations (3.5)--(3.6) once the long-ray case has been analyzed.
-/
def tailIndex {n r : ℕ} (hr : r ≤ n) (j : Fin (r + 1)) : Fin (n + 1) :=
  ⟨n - r + j.val, by
    have hj : j.val ≤ r := Nat.le_of_lt_succ j.isLt
    omega⟩

/--
Combinatorial encoding of the conclusion of Theorem 1.3(2): the extremal
contraction is a `P^r`-bundle.  In toric geometry this is equivalent to the
lattice splitting `N = N1 (+) N2` with `rank N1 = r`, where the tail vectors
`v_{n-r+1},...,v_{n+1}` span the saturated sublattice `N1` and satisfy
`v_{n-r+1} + ... + v_{n+1} = 0` (equations (3.10)--(3.11) and Fulton's
exercise quoted in the paper).
-/
structure IsProjectiveSpaceBundle {n r : ℕ} (hr : r ≤ n) (C : WallData n) : Prop where
  /-- `v_{n-r+1} + ... + v_{n+1} = 0` (equation (3.10)). -/
  tail_sum_zero : (∑ j : Fin (r + 1), C.v (tailIndex hr j)) = 0
  /-- The tail vectors span a rank-`r` saturated sublattice (3.11). -/
  tail_span :
    Nonempty
      ((Submodule.span ℤ (Set.range fun j : Fin (r + 1) => C.v (tailIndex hr j)) :
          Submodule ℤ (Lattice n)) ≃ₗ[ℤ] (Fin r → ℤ))
  /-- The splitting `N = N1 (+) N2` giving the `P^r`-bundle structure. -/
  lattice_split : Nonempty (Lattice n ≃ₗ[ℤ] ((Fin r → ℤ) × (Fin (n - r) → ℤ)))

end ToricFoliations


