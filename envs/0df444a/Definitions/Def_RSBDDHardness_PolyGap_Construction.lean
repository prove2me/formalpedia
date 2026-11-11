-- Prove2me | Definitions.Def_RSBDDHardness_PolyGap_Construction
-- name    : RSBDDHardness_PolyGap_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:01.691424+00:00
-- url     : https://prove2.me/theorems/5bdcfc60-8d0d-4523-be80-600f8696b6ef
-- title:
--   The moments-subset-sum instance $(A,k,M_1,\dots,M_{d_0})$ of §8.1
-- statement:
--   This module builds the instance of §8.1 explicitly from its data. Let $\varphi$ be a monotone Exact 1-in-3 formula with $m$ variables and $c$ clauses and put $t=m+c$ (for cubic formulas $t=2m$). Let $q$ be a prime, $P\in\mathbb F_q[Z]$, $\mathbb K=\mathbb F_q[Z]/(P)$, $B\subseteq\mathbb K$ a direction set and $d_0$ the preliminary number of moments. Then:
--
--   1. the Boolean-choice elements are $\ell_{i,b}=\sigma(v_{i,b})$ (Step 4);
--   2. the universe is $A=\{\ell_{i,b}: i\in[m],\ b\in\{0,1\}\}\cup D$ with $D=\bigcup_{\beta\in B}\beta\mathbb F_q^\times$ (Step 6);
--   3. the subset size is $k=m+|D|/2$;
--   4. the targets are
--   $$M_1=\sigma(T),\qquad M_2=\dots=M_{d_0}=0\qquad(42).$$
--
--   The parameters of Step 2 are $d_0=t^\nu$ and
--   $$Q_0=\max\Bigl\{1+\tfrac{d_0(d_0+1)}{2},\ \lceil d_0^{2+\rho}\rceil,\ h+1\Bigr\},\qquad h=Cd_0\qquad(39).$$
--
--   Theorem 8.1 is a statement about this explicit construction; no property of the instance is assumed.
--
--   **Formalization Note** $\lceil d_0^{2+\rho}\rceil$ uses the real power with rational $\rho$; $d_0(d_0+1)/2$ is an exact natural-number quotient since $d_0(d_0+1)$ is even. The universe is a finite set, so $|A|=2m+|D|$ only because the two parts are disjoint, which the source proves.
-- source:
--   Daqing Wan, Jun Zhang, NP-Hardness of Bounded Distance Decoding for Reed–Solomon Codes, STOC 2027 submission #449 (October 2026), §8.1 Steps 1–6, eqs. (39), (42), (43), PDF p. 24 (printed p. 23); continues on PDF pp. 25–26; PDF SHA-256 d60d9a54b73aa972494f130439dc6e07f8c7b33556741f8324d22cf45218e22b

import Mathlib
import Definitions.Def_RSBDDHardness_PolyGap_Algebra

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace RSBDDHardness.PolyGap

/-! ## The MSS instance of §8.1 (PDF 23–26)

Given the (padded) formula `φ` with `m` variables and `c` clauses, put `t = m + c`
(`= 2m` for cubic instances), a prime `q`, a polynomial `P ∈ 𝔽_q[Z]` (monic irreducible of
degree `2t+1` in the source), a direction set `B` and the preliminary moment count `d₀`. -/

namespace Sec8

variable (φ : OneInThree) (q : ℕ) (P : Polynomial (ZMod q))

/-- `t = m + c`, the dimension of the vector subset-sum instance. -/
def t : ℕ := φ.m + φ.c

/-- The Boolean-choice element `ℓ_{i,b} = σ(v_{i,b})` (Step 4). -/
def lift (i : Fin φ.m) (b : Bool) : AdjoinRoot P :=
  sigma P (t φ) (φ.vec q i b)

/-- The set `{ℓ_{i,b} : i ∈ [m], b ∈ {0,1}}` of Boolean-choice elements. -/
def lifts : Finset (AdjoinRoot P) :=
  Finset.univ.image fun p : Fin φ.m × Bool => lift φ q P p.1 p.2

/-- The MSS universe `A = {ℓ_{i,b}} ∪ D` with `D = ⨆_{β∈B} β𝔽_q^×` (Step 6). -/
def univA (B : Finset (AdjoinRoot P)) : Finset (AdjoinRoot P) :=
  lifts φ q P ∪ pool P B

/-- The required subset size `k = m + |D|/2` (Step 6). -/
def size (B : Finset (AdjoinRoot P)) : ℕ := φ.m + (pool P B).card / 2

/-- The targets `M_1 = σ(T)`, `M_2 = ⋯ = M_{d₀} = 0` of (42) (indexed from `1`). -/
def targets : ℕ → AdjoinRoot P := fun j =>
  if j = 1 then sigma P (t φ) (φ.target q) else 0

end Sec8

/-- `d₀ = t^ν` (Step 2). -/
def sec8d0 (t ν : ℕ) : ℕ := t ^ ν

/-- `Q₀ = max {1 + d₀(d₀+1)/2, ⌈d₀^{2+ρ}⌉, h + 1}` with `h = C d₀` (equation (39)). -/
def sec8Q0 (ρ : ℚ) (C d0 : ℕ) : ℕ :=
  max (1 + d0 * (d0 + 1) / 2) (max ⌈(d0 : ℝ) ^ (2 + (ρ : ℝ))⌉₊ (C * d0 + 1))

end RSBDDHardness.PolyGap


