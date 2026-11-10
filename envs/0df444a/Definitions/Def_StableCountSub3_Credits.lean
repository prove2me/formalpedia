-- Prove2me | Definitions.Def_StableCountSub3_Credits
-- name    : StableCountSub3_Credits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:51:07.995737+00:00
-- url     : https://prove2.me/theorems/9f3aaca8-3609-44d3-b203-2121ca8cb4d4
-- title:
--   Simple men, classes $B$, $C$, $I$, the image $\phi$, basic and additional credits, $e_s$, $p_c$
-- statement:
--   For a downset $D$ and a direction, write $s_m(k)$ for $s^\pm_{m,D}(k)$.
--
--   - Definition 5.2: $m$ is **simple** if $s_m(1)=2$; $C=\{m:s_m(1)=2,s_m(2)=3\}$; $B=\{m:s_m(1)=2,s_m(2)\ge4\}$ (including $s_m(2)=\infty$).
--   - Definition 5.4: for $m\in C$, the **image** $\phi(m)$ is the man $a\neq m$ who swaps partners with $m$ in $m$'s second rotation $\sigma=(m,a)$ in the outward order. $I=\phi(C)$.
--   - Definition 5.7 (Table 1): the basic credit $g^\pm_{\rm basic}(D,m)$ is $0$ on $C$, $\delta_2$ on $B$, $\delta_1+\delta_2$ on $I$, and $\delta_1$ on $M\setminus(B\cup C\cup I)$. These classes are pairwise disjoint (§5.2), so the case order is immaterial.
--   - For $n\ge1$, averages over a pointed matching $(\mu,m)$ uniform on $\Omega\times M$ with $D=D(\mu)$ (Definition 5.10, `avgDm`): $g_{\rm basic}=E_{D,m}[g^+_{\rm basic}+g^-_{\rm basic}]$ (Definition 5.7). $e_s$ is the probability that the backward direction is simple plus the probability that the forward direction is simple. $p_c$ is the probability that $m\in C$ in the backward direction (Definition 5.12).
--   - Definition 6.1: $m$ is **self-sufficient simple** if simple and ($s_m(3)\ge5$ or $s_m(4)\ge6$); a **self-sufficient image** if $m\in I$ and ($s_m(2)\ge5$ or $s_m(3)\ge6$); **strong** if $4\le s_m(1)<\infty$.
--   - Table 2: the additional credit $g^\pm_{\rm add}(D,m)$ is $t$, $4t$, $10t$ for these three types respectively, and $0$ otherwise ($t=\delta_4$). Definition 6.16: $g_{\rm add}=E_{D,m}[g^+_{\rm add}+g^-_{\rm add}]$.
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Definitions 5.2, 5.4, 5.7, 5.10, 5.12, pp. 26–30 (PDF 28–32); Definition 6.1, Table 2, pp. 32–33 (PDF 34–35); Definition 6.16, p. 41 (PDF 43)

import Mathlib
import Definitions.Def_StableCountSub3_Savings

open StableMatching

noncomputable section

namespace StableCountSub3

variable {n : ℕ}

/-- Definition 5.2: for the reference downset `D` and the direction `dir`, the man `m` is simple
if `s_m(1) = 2`. -/
def IsSimple (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir) : Prop :=
  ssize I D m dir 1 = 2

/-- Definition 5.2: `m ∈ C`, i.e. `s_m(1) = 2` and `s_m(2) = 3`. -/
def InC (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir) : Prop :=
  ssize I D m dir 1 = 2 ∧ ssize I D m dir 2 = 3

/-- Definition 5.2: `m ∈ B`, i.e. `s_m(1) = 2` and `s_m(2) ≥ 4` (including `s_m(2) = ∞`). -/
def InB (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir) : Prop :=
  ssize I D m dir 1 = 2 ∧ 4 ≤ ssize I D m dir 2

open Classical in
/-- Definition 5.4: the image `φ(m)` of `m ∈ C`: the man `a ≠ m` who swaps partners with `m` in
the second rotation `σ = (m, a)` of `m` (the second rotation involving `m` in the outward order,
Lemma 5.3). The value `m` is returned only when no such man exists, which never happens for
`m ∈ C`. -/
def image (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir) : Fin n :=
  if h : ∃ a ρ, kth I D m dir 2 = some ρ ∧ a ∈ participants ρ ∧ a ≠ m then h.choose else m

/-- Definition 5.4: `a ∈ I = φ(C)`. -/
def InI (I : Instance n) (D : Finset (Rot n)) (a : Fin n) (dir : Dir) : Prop :=
  ∃ m, InC I D m dir ∧ image I D m dir = a

open Classical in
/-- Definition 5.7 (Table 1): the basic credit `g^dir_basic(D, m)`: `0` on `C`, `δ₂` on `B`,
`δ₁ + δ₂` on `I`, and `δ₁` on `M \ (B ∪ C ∪ I)`. -/
def basicCredit (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir) : ℝ :=
  if InC I D m dir then 0
  else if InB I D m dir then delta 2
  else if InI I D m dir then delta 1 + delta 2
  else delta 1

/-- The average over a pointed matching `(μ, m)` uniform on `Ω × M` (with `D = D(μ)`) of
`f(D(μ), m)`: `(1/(|Ω| n)) ∑_{μ ∈ Ω} ∑_m f(D(μ), m)`. -/
def avgDm (I : Instance n) (f : Finset (Rot n) → Fin n → ℝ) : ℝ :=
  (1 / ((StableCount.numStable I : ℝ) * n)) * ∑ μ ∈ stableSet I, ∑ m : Fin n, f (Dof I μ) m

/-- Definition 5.7: `g_basic = E_{D,m}[g⁺_basic(D, m) + g⁻_basic(D, m)]`. -/
def gBasic (I : Instance n) : ℝ :=
  avgDm I fun D m => basicCredit I D m .fwd + basicCredit I D m .bwd

open Classical in
/-- Definition 5.12: `e_s`, for `(μ, m)` uniform on `Ω × M`, the probability that the backward
direction is simple plus the probability that the forward direction is simple. -/
def es (I : Instance n) : ℝ :=
  avgDm I fun D m =>
    (if IsSimple I D m .bwd then 1 else 0) + (if IsSimple I D m .fwd then 1 else 0)

open Classical in
/-- Definition 5.12: `p_c`, for `(μ, m)` uniform on `Ω × M`, the probability that `m ∈ C` in the
backward direction. -/
def pc (I : Instance n) : ℝ :=
  avgDm I fun D m => if InC I D m .bwd then 1 else 0

/-- Definition 6.1 (1): `m` is self-sufficient simple: simple, and `s_m(3) ≥ 5` or `s_m(4) ≥ 6`. -/
def SelfSuffSimple (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir) : Prop :=
  IsSimple I D m dir ∧ (5 ≤ ssize I D m dir 3 ∨ 6 ≤ ssize I D m dir 4)

/-- Definition 6.1 (2): `m` is a self-sufficient image: `m ∈ I`, and `s_m(2) ≥ 5` or
`s_m(3) ≥ 6`. -/
def SelfSuffImage (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir) : Prop :=
  InI I D m dir ∧ (5 ≤ ssize I D m dir 2 ∨ 6 ≤ ssize I D m dir 3)

/-- Definition 6.1 (3): `m` is strong: `4 ≤ s_m(1) < ∞`. -/
def Strong (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir) : Prop :=
  4 ≤ ssize I D m dir 1 ∧ ssize I D m dir 1 < ⊤

open Classical in
/-- Table 2: the additional credit `g^dir_add(D, m)`: `t` for a self-sufficient simple man, `4t`
for a self-sufficient image, `10t` for a strong man, `0` otherwise (`t = δ₄`). -/
def addCredit (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir) : ℝ :=
  if SelfSuffSimple I D m dir then tCredit
  else if SelfSuffImage I D m dir then 4 * tCredit
  else if Strong I D m dir then 10 * tCredit
  else 0

/-- Definition 6.16: `g_add = E_{D,m}[g⁺_add(D, m) + g⁻_add(D, m)]`, `(μ, m)` uniform on
`Ω × M`, `D = D(μ)`. -/
def gAdd (I : Instance n) : ℝ :=
  avgDm I fun D m => addCredit I D m .fwd + addCredit I D m .bwd

end StableCountSub3


