-- Prove2me | Definitions.Def_TwoBoxMemory_Supplement_Cover
-- name    : TwoBoxMemory_Supplement_Cover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:13:42.733125+00:00
-- url     : https://prove2.me/theorems/d621066c-e137-46a5-b03c-ac4b558ac6e9
-- title:
--   Jump function $T$, exceptional sets $E$ and $\mathcal E$, cover constants $D_N,m_N$, covering numbers
-- statement:
--   With $u,v$ as in (E.2), the **jump function** is
--
--   $$T(\beta)=\frac{v(\beta)^+}{u(\beta)^++v(\beta)^+},\qquad x^+=\max(x,0),$$
--
--   and $c_0=\min\{u(1),v(1-)\}$, $v(1-)$ the left limit of $v$ at $1$. The **exceptional sets** are
--
--   $$\mathcal E=(0,\infty)\setminus\bigcup_{a,b\ge0}I_{ab},\qquad E=[0,1]\setminus\bigcup_{a,b\ge0}\bigl(T(\beta_{ab}-),T(\beta_{ab})\bigr).$$
--
--   For integers $n_B>1/t$, $n_A>1/p$ put $\ell=s^{n_B}$, $h=r^{-n_A}$; for integers $K_A,K_B\ge1$ and $\bar c>0$,
--
--   $$D_N=\frac{2}{\bar c}\Bigl[\frac{K_A(p+th)r^N}{p}+\frac{K_B(t+p/\ell)s^N}{t}\Bigr],\qquad m_N=\#\{(a,b):0\le a,b<N,\ \ell\le\beta_{ab}\le h\}.$$
--
--   For $S\subseteq\mathbb R$ and $\varepsilon>0$, $N(S,\varepsilon)$ is the least number of intervals of length at most $\varepsilon$ covering $S$, and $S$ has **upper box dimension zero** when $\log N(S,\varepsilon)/\log(1/\varepsilon)\to0$ as $\varepsilon\downarrow0$.
--
--   These objects state Theorem F.2.
--
--   **Formalization Note** The $\ell,h$ here are those of (F.1), not those of (A.4). $N(S,\varepsilon)$ is defined with closed intervals $[a_k,b_k]$, $b_k-a_k\le\varepsilon$ (closures do not change the count). For a nonempty bounded set and $\varepsilon<1$ the quotient $\log N/\log(1/\varepsilon)$ is nonnegative, so its tending to $0$ is exactly upper box dimension zero.
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), Lemma E.2, (E.9), pp.42–43 (PDF 44–45); Appendix F, p.48 (PDF 50); (F.1) and Theorem F.2, p.49 (PDF 51)

import Mathlib
import Definitions.Def_TwoBoxMemory_Supplement_CostDomain

namespace TwoBoxMemory.Supplement

/-!
# The jump function `T`, the exceptional sets `E` and `𝓔`, the cover constants, covering numbers

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
Lemma E.2, (E.9), pp.42–43 (PDF 44–45); Appendix F, p.48 (PDF 50); §F.2, (F.1) and Theorem F.2,
p.49 (PDF 51).

* (E.9) `T(β) = v(β)⁺ / (u(β)⁺ + v(β)⁺)`, `x⁺ = max(x, 0)`.
* Lemma E.2: `c₀ = min{u(1), v(1−)}`, with `v(1−)` the left limit of `v` at `1`.
* p.48: `𝓔 = (0, ∞) \ ⋃_{a,b ≥ 0} I_ab` and `E = [0, 1] \ ⋃_{a,b ≥ 0} (T(β_ab−), T(β_ab))`.
* (F.1): for integers `n_B > 1/t`, `n_A > 1/p`, put `ℓ = s^{n_B}`, `h = r^{−n_A}`; for integers
  `K_A, K_B ≥ 1` with `s^{K_A} < ℓ/h`, `r^{K_B} < ℓ/h` and `0 < c̄ ≤ c₀`,
  `D_N = (2/c̄) [K_A (p + t h) r^N / p + K_B (t + p/ℓ) s^N / t]` and
  `m_N = #{(a, b) : 0 ≤ a, b < N, ℓ ≤ β_ab ≤ h}`.
* Theorem F.2: `N(S, ε)` is the number of intervals of length at most `ε` needed to cover `S`.

**Formalization Note.**
* `u` is the published `uSaddle`, `v` is `vW` (A-first, weak `n_j`); `T(β_ab−)` and `v(1−)` are
  `Function.leftLim`.
* The `ℓ, h` of (F.1) are **not** those of (A.4); they are `coverL`, `coverH` here.
* `coverM` counts with a `Finset.filter` over `range N ×ˢ range N` (classical decidability).
* `coveringNumber S ε` is the least `n` such that `S` is covered by `n` closed intervals
  `[a_k, b_k]` with `b_k − a_k ≤ ε`; covering by arbitrary intervals of length `≤ ε` gives the
  same number (take closures). It is a `sInf` in `ℕ`; for a bounded `S` and `ε > 0` the set of
  admissible `n` is nonempty, so the empty-set value `0` arises only for unbounded `S` (never
  used) and the value `0` for `S = ∅` is correct.
* `UpperBoxDimZero S`: `log N(S, ε) / log(1/ε) → 0` as `ε ↓ 0`, the paper's own formulation
  ("`log N(E, ε)/log(1/ε) → 0`, proving the upper box assertion directly", p.50). For a nonempty
  bounded `S` and `ε < 1` the quotient is nonnegative, so this is exactly upper box dimension `0`.
-/

noncomputable section

/-- The jump function `T(β) = v(β)⁺ / (u(β)⁺ + v(β)⁺)` of (E.9). -/
def Tfun (r s : ℝ) (β : ℝ) : ℝ :=
  max (vW r s β) 0 / (max (TwoBoxMemory.uSaddle r s β) 0 + max (vW r s β) 0)

/-- `c₀ = min{u(1), v(1−)}` of Lemma E.2. -/
def cZero (r s : ℝ) : ℝ := min (TwoBoxMemory.uSaddle r s 1) (Function.leftLim (vW r s) 1)

/-- The exceptional set `E = [0, 1] \ ⋃_{a,b ≥ 0} (T(β_ab−), T(β_ab))` (p.48). -/
def Eset (r s : ℝ) : Set ℝ :=
  Set.Icc 0 1 \ ⋃ (a : ℕ) (b : ℕ),
    Set.Ioo (Function.leftLim (Tfun r s) (betaTie r s a b)) (Tfun r s (betaTie r s a b))

/-- The exceptional cost set `𝓔 = (0, ∞) \ ⋃_{a,b ≥ 0} I_ab` (p.48). -/
def EcalSet (r s : ℝ) : Set ℝ := Set.Ioi 0 \ Icost r s

/-- `ℓ = s^{n_B}` of (F.1). -/
def coverL (s : ℝ) (nB : ℕ) : ℝ := s ^ nB

/-- `h = r^{−n_A}` of (F.1). -/
def coverH (r : ℝ) (nA : ℕ) : ℝ := (r ^ nA)⁻¹

/-- `D_N = (2/c̄) [K_A (p + t h) r^N / p + K_B (t + p/ℓ) s^N / t]` of (F.1). -/
def coverD (r s : ℝ) (nA nB KA KB : ℕ) (cbar : ℝ) (N : ℕ) : ℝ :=
  2 / cbar * ((KA : ℝ) * ((1 - r) + (1 - s) * coverH r nA) * r ^ N / (1 - r) +
    (KB : ℝ) * ((1 - s) + (1 - r) / coverL s nB) * s ^ N / (1 - s))

open Classical in
/-- `m_N = #{(a, b) : 0 ≤ a, b < N, ℓ ≤ β_ab ≤ h}` of (F.1). -/
def coverM (r s : ℝ) (nA nB N : ℕ) : ℕ :=
  ((Finset.range N ×ˢ Finset.range N).filter fun q =>
    coverL s nB ≤ betaTie r s q.1 q.2 ∧ betaTie r s q.1 q.2 ≤ coverH r nA).card

/-- `N(S, ε)`: the least number of intervals of length at most `ε` covering `S`. -/
def coveringNumber (S : Set ℝ) (ε : ℝ) : ℕ :=
  sInf {n : ℕ | ∃ a b : Fin n → ℝ, (∀ k, b k - a k ≤ ε) ∧ S ⊆ ⋃ k, Set.Icc (a k) (b k)}

/-- Upper box dimension zero: `log N(S, ε) / log(1/ε) → 0` as `ε ↓ 0`. -/
def UpperBoxDimZero (S : Set ℝ) : Prop :=
  Filter.Tendsto (fun ε : ℝ => Real.log (coveringNumber S ε) / Real.log (1 / ε))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

end

end TwoBoxMemory.Supplement


