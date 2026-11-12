-- Prove2me | Definitions.Def_L1Sparsifiers_Main_ConvexBodyVolumes
-- name    : L1Sparsifiers_Main_ConvexBodyVolumes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:11.890227+00:00
-- url     : https://prove2.me/theorems/07e5c351-b8fd-4aff-8222-bfe97e344980
-- title:
--   Convex bodies, coordinate sections $K_S$, reflected-intersection volume $f_K$ and barycenter
-- statement:
--   A **convex body** in $\mathbb R^m$ is a compact convex set with nonempty interior.
--
--   For $K\subseteq\mathbb R^m$ and $S\subseteq[m]$ the **coordinate section** is
--   $$K_S=\{x'\in\mathbb R^S:\ (x',0)\in K\},\qquad 0\in\mathbb R^{[m]\setminus S},$$
--   the intersection of $K$ with the coordinate subspace of $S$ (not a projection). Its volume $\mathrm{Vol}_S(K_S)$ is the $|S|$-dimensional Lebesgue measure on $\mathbb R^S$; for $S=\emptyset$, $\mathbb R^\emptyset$ is a point of measure $1$.
--
--   For $z\in\mathbb R^m$,
--   $$f_K(z)=\mathrm{Vol}_m\big(K\cap(2z-K)\big),\qquad 2z-K=\{2z-k:k\in K\},$$
--   is the volume of the intersection of $K$ with its reflection around $z$; for convex $K$ it vanishes outside $K$.
--
--   The **barycenter** of a convex body $K$ is $\mathbb E_{x\sim K}[x]=\mathrm{Vol}_m(K)^{-1}\int_K x\,dx$.
--
--   **Formalization Note** `coordSection K S` is a set of functions `S → ℝ` on the finset `S`, measured by `volume` on that finite product. `reflVol` and the barycenter use `(volume ·).toReal`; they are applied only to bounded sets and to convex bodies, whose volume is finite and positive. The symmetrizer $K\cap-K$ uses the pointwise negation of a set.
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §2, p.5 (barycenter); §5, p.11 ($K_S$); Proposition 23, p.12 ($f_K$)

import Mathlib

namespace L1Sparsifiers.Main

open MeasureTheory

/-- **Convex body** in `ℝ^m`: a compact convex set with nonempty interior. -/
def IsConvexBody {m : ℕ} (K : Set (Fin m → ℝ)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/-- Extension by zero of `u ∈ ℝ^S` to `(u, 0) ∈ ℝ^m`, with `0 ∈ ℝ^{[m] \ S}`. -/
def zeroExtend {m : ℕ} (S : Finset (Fin m)) (u : S → ℝ) : Fin m → ℝ :=
  fun i => if h : i ∈ S then u ⟨i, h⟩ else 0

/-- **Coordinate section** (§5, p.11): `K_S = {x' ∈ ℝ^S : (x', 0) ∈ K}`, the intersection of `K`
with the coordinate subspace of `S` (not a projection). Its volume `Vol_S(K_S)` is the
`|S|`-dimensional Lebesgue measure `volume` on `S → ℝ`; for `S = ∅` that space is a single
point of measure `1`. -/
def coordSection {m : ℕ} (K : Set (Fin m → ℝ)) (S : Finset (Fin m)) : Set (S → ℝ) :=
  {u | zeroExtend S u ∈ K}

/-- **Volume of the intersection of `K` with its reflection around `z`** (Proposition 23, p.12):
`f_K(z) = Vol_m(K ∩ (2z − K))`, with `2z − K = {2z − k : k ∈ K}`; as a real number (all sets to
which it is applied are bounded, so the volume is finite). -/
noncomputable def reflVol {m : ℕ} (K : Set (Fin m → ℝ)) (z : Fin m → ℝ) : ℝ :=
  (volume (K ∩ {y | ∃ k ∈ K, y = (2 : ℝ) • z - k})).toReal

/-- **Barycenter** of a convex body (§2, p.5): `E_{x∼K}[x] = Vol_m(K)⁻¹ ∫_K x dx`, the mean of the
uniform distribution on `K` (applied only to convex bodies, which have finite positive volume). -/
noncomputable def barycenter {m : ℕ} (K : Set (Fin m → ℝ)) : Fin m → ℝ :=
  (volume K).toReal⁻¹ • ∫ x in K, x

end L1Sparsifiers.Main


