-- Prove2me | Definitions.Def_FewInnerTSP_Charges
-- name    : FewInnerTSP_Charges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:30:39.527202+00:00
-- url     : https://prove2.me/theorems/03aee8f2-c382-4275-bb33-cdc87a0b5252
-- title:
--   Dyadic grid, frames, the charges (7), clearance and balancing squares
-- statement:
--   Coordinates are normalized: the separator $\sigma_t$ is the closed square of side $t$ centered at $0$, with boundary $\partial\sigma_t=\{x:\|x\|_\infty=t/2\}$.
--
--   1. For a **dyadic scale** $s=2^{-j}$, $j\ge 0$, the half-open **grid cell** $(i,\ell)\in\mathbb Z^2$ is $[is,(i+1)s)\times[\ell s,(\ell+1)s)$ and its **frame** is $D_g=[(i-1)s,(i+2)s)\times[(\ell-1)s,(\ell+2)s)$. A frame is **active** at $t$ when $D_g\cap\partial\sigma_t\neq\emptyset$.
--   2. The **charge** of a finite point set $X$ at $t$ is
--   $$E_X(t)=\sum_{j\ge 0}\ \sum_{g\ \text{active at }t}\log_2\bigl(1+|X\cap D_g|\bigr)\in[0,\infty],$$
--   so $E_A$ and $E_H$ of (7) are the charges of the core and skeleton points. Its **expectation** over $t$ uniform on $[1,3]$ is $\tfrac12\int_1^3E_X(t)\,dt$.
--   3. The **clearance** is $\mu=1/[100(N_0+1)^3]$ and the **scale cut** is $J=\lceil\log_2(1/\mu)\rceil+1$.
--   4. A **minimum balancing square** for a finite set $Q$ is a closed axis-aligned square of side $u\ge0$ containing at least $|Q|/17$ points of $Q$ whose side is minimum among all such squares.
--
--   **Formalization Note** The charge takes values in $[0,\infty]$, so the double sum is unconditional and the expectation is a Lebesgue integral of a nonnegative function. The logarithm has base $2$, as in (7).
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), §4.2, (7), p.6 (PDF p.8); App. B.1–B.3, pp.16–17 (PDF pp.18–19); Lemma 4.5, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_FewInnerTSP_Packing

namespace FewInnerTSP

open scoped ENNReal

/-- The dyadic scale `s = 2^{-j}`, `j ≥ 0`.
Source: Li, Ma, Gong, STOC 2027 submission (manuscript sha256 6541f631…), App. B.2, p.16 (PDF p.18). -/
noncomputable def scale (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ j

/-- The half-open grid cell `[is, (i+1)s) × [ℓs, (ℓ+1)s)` at scale `s = 2^{-j}`.
Source: Li, Ma, Gong, App. B.2, p.16 (PDF p.18). -/
def gridCell (j : ℕ) (i l : ℤ) : Set Pt :=
  {x | (i : ℝ) * scale j ≤ x 0 ∧ x 0 < ((i : ℝ) + 1) * scale j ∧
    (l : ℝ) * scale j ≤ x 1 ∧ x 1 < ((l : ℝ) + 1) * scale j}

/-- The half-open frame `D_g = [(i−1)s, (i+2)s) × [(ℓ−1)s, (ℓ+2)s)`.
Source: Li, Ma, Gong, App. B.2, p.16 (PDF p.18). -/
def frame (j : ℕ) (i l : ℤ) : Set Pt :=
  {x | ((i : ℝ) - 1) * scale j ≤ x 0 ∧ x 0 < ((i : ℝ) + 2) * scale j ∧
    ((l : ℝ) - 1) * scale j ≤ x 1 ∧ x 1 < ((l : ℝ) + 2) * scale j}

/-- The boundary `∂σ_t = {x | ‖x‖∞ = t/2}` of the normalized separator of side `t`, center `0`.
Source: Li, Ma, Gong, App. B.2, p.17 (PDF p.19). -/
def sepBoundary (t : ℝ) : Set Pt :=
  {x | max |x 0| |x 1| = t / 2}

/-- A frame is active at `t` exactly when `D_g ∩ ∂σ_t ≠ ∅`.
Source: Li, Ma, Gong, App. B.2, p.17 (PDF p.19). -/
def FrameActive (t : ℝ) (j : ℕ) (i l : ℤ) : Prop :=
  (frame j i l ∩ sepBoundary t).Nonempty

open Classical in
/-- **The charge (7)** `Σ_{s, g active} log₂(1 + |X ∩ D_g|)` of a finite point set `X` at parameter `t`,
over all dyadic scales and all frames. `EA(t) = charge A t`, `EH(t) = charge H t`.
Source: Li, Ma, Gong, (7), p.6 (PDF p.8).

**Formalization Note** The value is in `ℝ≥0∞`, so the infinite sum is unconditional, and the
expectation over `t` is a `lintegral`, never a Bochner integral. The logarithm has base `2`, as (7)
has: it pays at least one for each nonempty bucket. Coordinates are normalized: center `0`, the
separator has side `t`. -/
noncomputable def charge (X : Finset Pt) (t : ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, ∑' g : ℤ × ℤ,
    if FrameActive t j g.1 g.2 then
      ENNReal.ofReal (Real.logb 2 (1 + ((X.filter fun x => x ∈ frame j g.1 g.2).card : ℝ)))
    else 0

/-- The expectation of the charge over `t` uniform on `[1, 3]`.
Source: Li, Ma, Gong, Lemmas 4.2, 4.4, p.7 (PDF p.9). -/
noncomputable def expectedCharge (X : Finset Pt) : ℝ≥0∞ :=
  (1 / 2 : ℝ≥0∞) * ∫⁻ t in Set.Icc (1 : ℝ) 3, charge X t

/-- The clearance `μ = 1/[100(N₀ + 1)³]`. Source: Li, Ma, Gong, Lemma 4.5, p.8 (PDF p.10). -/
noncomputable def clearance (N0 : ℕ) : ℝ := 1 / (100 * ((N0 : ℝ) + 1) ^ 3)

/-- The truncation scale `J = ⌈log₂(1/μ)⌉ + 1`, with `1/μ = 100(N₀ + 1)³`.
Source: Li, Ma, Gong, App. B.3, p.17 (PDF p.19). -/
def scaleCut (N0 : ℕ) : ℕ := Nat.clog 2 (100 * (N0 + 1) ^ 3) + 1

open Classical in
/-- **A minimum balancing square** for `Q`: a closed axis-aligned square of side `u ≥ 0` containing at
least `|Q|/17` points of `Q`, of minimum side among all such squares.
Source: Li, Ma, Gong, Lemma B.1, p.16 (PDF p.18). -/
def IsMinBalancingSquare (Q : Finset Pt) (c : Pt) (u : ℝ) : Prop :=
  0 ≤ u ∧ Q.card ≤ 17 * (Q.filter fun x => x ∈ closedSquare c u).card ∧
    ∀ (c' : Pt) (u' : ℝ), 0 ≤ u' →
      Q.card ≤ 17 * (Q.filter fun x => x ∈ closedSquare c' u').card → u ≤ u'

end FewInnerTSP


