-- Prove2me | Definitions.Def_PureDPQR_IsDP
-- name    : PureDPQR_IsDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:38.046946+00:00
-- url     : https://prove2.me/theorems/a36708e6-fdae-4bfe-834f-1575bd2d9e5d
-- title:
--   Histograms $H_{N,d}$, replacement adjacency and $(\varepsilon,\delta)$-differential privacy (Definition 4)
-- statement:
--   A **histogram** of $N$ records over the universe $[d]$ is a vector $h\in\mathbb N^d$ with $\sum_j h_j=N$; the set of them is
--
--   $$H_{N,d}=\{h\in\mathbb N^d:\ \textstyle\sum_j h_j=N\}.$$
--
--   Two histograms $h,h'\in H_{N,d}$ are **adjacent**, $h\sim h'$, if $h'=h+e_a-e_b$ for some $a,b\in[d]$ (one record of type $b$ is replaced by one of type $a$; $a=b$ is allowed). A randomized mechanism $M$, given by its output law $M(h)$ on a measurable space, is **$(\varepsilon,\delta)$-differentially private** if for every adjacent pair $h\sim h'$ in $H_{N,d}$ and every measurable output event $F$,
--
--   $$\Pr\{M(h)\in F\}\le e^{\varepsilon}\Pr\{M(h')\in F\}+\delta .$$
--
--   Pure $\varepsilon$-DP is the case $\delta=0$. Every privacy statement of the mission uses this definition.
--
--   **Formalization Note** Coordinates are 0-based (`Fin d`). Adjacency is written $h'+e_b=h+e_a$, which avoids truncated subtraction on $\mathbb N^d$ and describes the same pairs. The source defines DP for $\varepsilon\ge0$, $0\le\delta<1$; the predicate is the inequality, and each use states its parameter range. Probabilities are $[0,\infty]$-valued measures.
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Definition 4, p.13 (PDF p.14); §3, p.12 (PDF p.13)

import Mathlib

open MeasureTheory

namespace PureDPQR

/-!
# Histograms, replacement adjacency and `(ε, δ)`-differential privacy

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…), §3, p.12 (PDF p.13) and Definition 4, p.13 (PDF p.14).

**Formalization Note.**
* A histogram over the universe `[d]` is a vector `h : Fin d → ℕ` (0-based coordinates).
  `H_{N,d} = {h ∈ ℕ^d : ∑_j h_j = N}` is `histograms N d`.
* Adjacency `h′ = h + e_a − e_b` is written `h′ + e_b = h + e_a`, so no truncated natural-number
  subtraction occurs; the two are equivalent for `h, h′ ∈ ℕ^d`. `a = b` is allowed, as printed.
* A randomized mechanism with outputs in a measurable space `O` is the family `M h` of its output
  laws. Definition 4 is stated "for `ε ≥ 0` and `0 ≤ δ < 1`"; the predicate below is the
  inequality itself, and every use in this mission takes parameters in that range.
* Definition 4 compares every adjacent pair of histograms in `H_{N,d}`; the reverse comparison is
  covered because adjacency is symmetric (p.13).
-/

/-- The feasible set of histograms `H_{N,d} = {h ∈ ℕ^d : ∑_j h_j = N}` (§3, p.12). -/
def histograms (N d : ℕ) : Set (Fin d → ℕ) :=
  {h | ∑ j, h j = N}

/-- Replacement adjacency (Definition 4, p.13): `h ∼ h′` iff `h′ = h + e_a − e_b` for some
`a, b ∈ [d]`, written without subtraction as `h′ + e_b = h + e_a`. -/
def Adjacent {d : ℕ} (h h' : Fin d → ℕ) : Prop :=
  ∃ a b : Fin d, h' + Pi.single b 1 = h + Pi.single a 1

/-- `(ε, δ)`-differential privacy under replacement adjacency (Definition 4, p.13): for every
adjacent pair `h ∼ h′` of histograms of mass `N` and every measurable output event `F`,
`Pr{M(h) ∈ F} ≤ e^ε Pr{M(h′) ∈ F} + δ`. Pure `ε`-DP is `IsDP N d M ε 0`. -/
def IsDP {O : Type*} [MeasurableSpace O] (N d : ℕ) (M : (Fin d → ℕ) → Measure O)
    (ε δ : ℝ) : Prop :=
  ∀ h ∈ histograms N d, ∀ h' ∈ histograms N d, Adjacent h h' →
    ∀ F : Set O, MeasurableSet F →
      M h F ≤ ENNReal.ofReal (Real.exp ε) * M h' F + ENNReal.ofReal δ

end PureDPQR


