-- Prove2me | Definitions.Def_QCopyMono_PathExperiment
-- name    : QCopyMono_PathExperiment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:04.794219+00:00
-- url     : https://prove2.me/theorems/672cd131-a13f-43c6-bfdf-85519891c59a
-- title:
--   The Hamming band $\mathcal B$, the path experiment $p_t(f)$, the lengths $t_d$, the truncation $\tilde f$ and the walks
-- statement:
--   Fix $n$ and $0<\varepsilon\le 1/2$. The **Hamming band** is
--   $$
--   w=\Big\lceil\sqrt{\tfrac n2\log\tfrac{100}{\varepsilon}}\Big\rceil,\qquad \mathcal B=\big\{x\in\{0,1\}^n:\ \big||x|-\tfrac n2\big|\le w\big\}.
--   $$
--   For an integer $t\ge1$ the **path experiment** samples $x$ uniformly and a direction (upward or downward) with probability $1/2$ each. Upward, it chooses a uniformly random $t$-subset $S$ of $\{i:x_i=0\}$ and sets $y_i=1$ for $i\in S$, $y_i=x_i$ otherwise; downward, a uniformly random $t$-subset of $\{i:x_i=1\}$ is set to $0$. It fails if fewer than $t$ coordinates are available or if $x$ or $y$ lies outside $\mathcal B$; otherwise it succeeds if $(f(x),f(y))=(1,0)$ upward and $(0,1)$ downward. $p_t(f)$ is its success probability.
--
--   For constants $c_0>0$ and scales $d\in\mathcal D_n=\{1,2,4,\dots,2^{\lfloor\log_2 n\rfloor}\}$, the **path lengths** are $t_d=\max\{1,\lfloor c_0\varepsilon\sqrt n\,d^{-5/8}\rfloor\}$.
--
--   The **truncation** $\tilde f$ of $f$ agrees with $f$ on $\mathcal B$, equals $0$ below the band and $1$ above it.
--
--   For $h:\{0,1\}^n\to\{0,1\}$ and a uniform start $Y$, the **walk-change probabilities** are $\Pr[Y\in\mathcal B,\ h(Y)\neq h(Y^{\uparrow j})]$, where $Y^{\uparrow j}$ is reached by $j$ upward steps (a uniformly random $j$-subset of the zero coordinates set to one), the analogous downward quantity, and the per-step probabilities $\Pr[Y\in\mathcal B,\ h(U_i)\neq h(U_{i+1})]$ of traversing, at step $i+1$, an edge on which $h$ changes.
--
--   **Formalization Note** $\log$ is the natural logarithm (needed for $2e^{-2w^2/n}\le\varepsilon/50$). The step-by-step walk of the paper (each step flips one uniformly random remaining zero coordinate) has, after $j$ steps, a uniformly random $j$-subset of flipped coordinates, which is how it is written here. If fewer than $t$ (or $j$) coordinates are available the corresponding term is $0$.
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), §3.2, p.10 (t_d, D_n); §3.2.1, p.13 (eq. (15), the procedure, p_t(f)); proof of Lemma 6, pp.35–37 (f̃, the walks); proof of Lemma 7, p.40

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QCopyMono

open QAlgorithms

/-! # The Hamming band, the path experiment `p_t(f)`, path lengths, truncation, and walks

P. Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), §3.2, pp.10, 13 (eq. (15), the procedure,
`t_d`), and the proof of Lemma 6, pp.35–37 (`f̃`, the walks).

**Formalization Note.**
* `log` is the natural logarithm (eq. (15)), the paper's convention throughout (its step
  `e^{−r_d/8} ≤ 1/(12d)` on p.16 needs base `e`); with it Hoeffding's bound in the proof of
  Lemma 6 reads `2 exp(−2w²/n) ≤ ε/50`.
* The band (written `𝓑` on the page in a calligraphic letter) is `InBand ε`; it is a different
  set from the vertex set `B` of Lemma 5.
* The random `t`-step upward (downward) move of the procedure chooses a uniformly random
  `t`-subset `S` of the zero (one) coordinates of `x`, as printed. When fewer than `t`
  coordinates are available the subset family is empty and the move contributes `0`
  ("the procedure fails").
* The walks of the proof of Lemma 6 ("each `U_{j+1}` is obtained from `U_j` by changing a
  randomly chosen zero coordinate to one") are written through their law: after `j` steps of
  that walk the set of flipped coordinates is a uniformly random `j`-subset of the zero
  coordinates of the start, and the next step adds a uniformly random remaining zero coordinate.
  `upChange` uses the law of the endpoint `U_j`, `upStepChange` the joint law of `(U_i, U_{i+1})`.
* `t_d = max{1, ⌊c₀ ε √n d^{−5/8}⌋}` is `pathLen c₀ ε n d`, with `d` real (`d = 2^j`). -/

/-- eq. (15), p.13: `w = ⌈√((n/2) log(100/ε))⌉` (natural logarithm). -/
noncomputable def bandW (ε : ℝ) (n : ℕ) : ℕ :=
  ⌈Real.sqrt ((n : ℝ) / 2 * Real.log (100 / ε))⌉₊

/-- eq. (15), p.13: `x ∈ 𝓑 = {x : ||x| − n/2| ≤ w}`. -/
def InBand {n : ℕ} (ε : ℝ) (x : Qubits n) : Prop :=
  |(hammingWeight x : ℝ) - (n : ℝ) / 2| ≤ (bandW ε n : ℝ)

/-- The zero coordinates `{i ∈ [n] : xᵢ = 0}`. -/
def zeros {n : ℕ} (x : Qubits n) : Finset (Fin n) := Finset.univ.filter fun i => x i = false

/-- The one coordinates `{i ∈ [n] : xᵢ = 1}`. -/
def ones {n : ℕ} (x : Qubits n) : Finset (Fin n) := Finset.univ.filter fun i => x i = true

/-- p.13: `yᵢ = 1` for `i ∈ S`, `yᵢ = xᵢ` otherwise (the upward move). -/
def setOnes {n : ℕ} (x : Qubits n) (S : Finset (Fin n)) : Qubits n :=
  fun i => if i ∈ S then true else x i

/-- p.13: `yᵢ = 0` for `i ∈ S`, `yᵢ = xᵢ` otherwise (the downward move). -/
def setZeros {n : ℕ} (x : Qubits n) (S : Finset (Fin n)) : Qubits n :=
  fun i => if i ∈ S then false else x i

open Classical in
/-- p.13: from start `x`, the success probability of the upward branch: `S` uniform among the
`t`-subsets of the zero coordinates of `x`, success iff `x, y ∈ 𝓑` and `(f(x), f(y)) = (1, 0)`. -/
noncomputable def upSucc {n : ℕ} (ε : ℝ) (t : ℕ) (f : Qubits n → Bool) (x : Qubits n) : ℝ :=
  ∑ S ∈ (zeros x).powersetCard t, (((zeros x).card.choose t : ℕ) : ℝ)⁻¹ *
    (if InBand ε x ∧ InBand ε (setOnes x S) ∧ f x = true ∧ f (setOnes x S) = false then 1 else 0)

open Classical in
/-- p.13: from start `x`, the success probability of the downward branch: `S` uniform among the
`t`-subsets of the one coordinates of `x`, success iff `x, y ∈ 𝓑` and `(f(x), f(y)) = (0, 1)`. -/
noncomputable def downSucc {n : ℕ} (ε : ℝ) (t : ℕ) (f : Qubits n → Bool) (x : Qubits n) : ℝ :=
  ∑ S ∈ (ones x).powersetCard t, (((ones x).card.choose t : ℕ) : ℝ)⁻¹ *
    (if InBand ε x ∧ InBand ε (setZeros x S) ∧ f x = false ∧ f (setZeros x S) = true then 1
      else 0)

/-- p.13: `p_t(f)`, the success probability of the procedure: `x` uniform on `{0,1}ⁿ`, the
direction upward or downward with probability `1/2` each, independently. -/
noncomputable def pathProb {n : ℕ} (ε : ℝ) (t : ℕ) (f : Qubits n → Bool) : ℝ :=
  (∑ x : Qubits n, (upSucc ε t f x + downSucc ε t f x) / 2) / 2 ^ n

/-- Lemma 6, p.13 (and p.10): `t_d = max{1, ⌊c₀ ε √n d^{−5/8}⌋}`. -/
noncomputable def pathLen (c₀ ε : ℝ) (n : ℕ) (d : ℝ) : ℕ :=
  max 1 ⌊c₀ * ε * Real.sqrt n * d ^ (-(5 / 8 : ℝ))⌋₊

open Classical in
/-- Proof of Lemma 6, p.35: `f̃` agrees with `f` on `𝓑`, equals `0` below the band and `1`
above it. -/
noncomputable def truncate {n : ℕ} (ε : ℝ) (f : Qubits n → Bool) (x : Qubits n) : Bool :=
  if InBand ε x then f x else decide ((n : ℝ) / 2 < (hammingWeight x : ℝ))

open Classical in
/-- Proofs of Lemmas 6 and 7, pp.36–37, 40: `Pr[Y ∈ 𝓑, h(Y) ≠ h(Y^{↑j})]`, for `Y` uniform and
`Y^{↑j}` obtained from `Y` by `j` upward steps (a uniformly random `j`-subset of the zero
coordinates of `Y` set to one). -/
noncomputable def upChange {n : ℕ} (ε : ℝ) (j : ℕ) (h : Qubits n → Bool) : ℝ :=
  (∑ y : Qubits n, if InBand ε y then
      (((zeros y).card.choose j : ℕ) : ℝ)⁻¹ *
        (((zeros y).powersetCard j).filter fun S => h y ≠ h (setOnes y S)).card
    else 0) / 2 ^ n

open Classical in
/-- The downward counterpart of `upChange`: `j` downward steps (a uniformly random `j`-subset of
the one coordinates of `Y` set to zero). -/
noncomputable def downChange {n : ℕ} (ε : ℝ) (j : ℕ) (h : Qubits n → Bool) : ℝ :=
  (∑ y : Qubits n, if InBand ε y then
      (((ones y).card.choose j : ℕ) : ℝ)⁻¹ *
        (((ones y).powersetCard j).filter fun S => h y ≠ h (setZeros y S)).card
    else 0) / 2 ^ n

open Classical in
/-- Proof of Lemma 6, p.37, and of Lemma 7, p.40: `Pr[Y ∈ 𝓑, h(U_i) ≠ h(U_{i+1})]`, the
probability of starting in the band and traversing an edge on which `h` changes at the
`(i+1)`-st step of the upward walk `U_0 = Y, U_1, …`. Here `U_i = Y^{↑S}` for a uniformly random
`i`-subset `S` of the zero coordinates of `Y`, and `U_{i+1}` additionally sets one uniformly random
remaining zero coordinate `k` to one. -/
noncomputable def upStepChange {n : ℕ} (ε : ℝ) (i : ℕ) (h : Qubits n → Bool) : ℝ :=
  (∑ y : Qubits n, if InBand ε y then
      (((zeros y).card.choose i : ℕ) : ℝ)⁻¹ * ∑ S ∈ (zeros y).powersetCard i,
        (((zeros y \ S).card : ℕ) : ℝ)⁻¹ *
          (((zeros y \ S).filter fun k => h (setOnes y S) ≠ h (setOnes y (insert k S))).card)
    else 0) / 2 ^ n

open Classical in
/-- The downward counterpart of `upStepChange` (one coordinates set to zero). -/
noncomputable def downStepChange {n : ℕ} (ε : ℝ) (i : ℕ) (h : Qubits n → Bool) : ℝ :=
  (∑ y : Qubits n, if InBand ε y then
      (((ones y).card.choose i : ℕ) : ℝ)⁻¹ * ∑ S ∈ (ones y).powersetCard i,
        (((ones y \ S).card : ℕ) : ℝ)⁻¹ *
          (((ones y \ S).filter fun k => h (setZeros y S) ≠ h (setZeros y (insert k S))).card)
    else 0) / 2 ^ n

end QCopyMono


