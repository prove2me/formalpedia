-- Prove2me | Definitions.Def_FewInnerTSP_Supplement_BitModel
-- name    : FewInnerTSP_Supplement_BitModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:13:09.881293+00:00
-- url     : https://prove2.me/theorems/debd840f-ed3c-4904-b53c-abe3ac24fa2e
-- title:
--   Rational inputs of the bit model: binary codes, the encoding length $L$, the output code and $\log^+(1/\varepsilon)$
-- statement:
--   In the bit model of §6 an input consists of $n$ points with **rational** coordinates $p_i=(x_i,y_i)\in\mathbb Q^2$ and a rational accuracy $\varepsilon>0$. The point set $P$ is $P_i=(x_i,y_i)$ in the Euclidean plane $\mathbb R^2$, so general position, the interior count $k$ and the Euclidean tour length are those of the published instance definitions.
--
--   1. A natural number $m$ with binary digits $b_0b_1\dots b_{\ell-1}$ (least significant first) is coded **self-delimitingly** as $1^{\ell}\,0\,b_0\dots b_{\ell-1}$.
--   2. A rational $q$ in lowest terms $a/b$ ($b>0$) is coded as a sign bit, then the code of $|a|$, then the code of $b$. Its **encoding length** is the length of this code.
--   3. The **input string** is the code of $n$, then of $\varepsilon$, then of the $2n$ coordinates in the order $x_0,y_0,x_1,y_1,\dots$, each exactly.
--   4. The **encoding length** $L$ is the largest encoding length among the $2n$ coordinates and $\varepsilon$:
--   $$L=\max\Bigl(\mathrm{len}(\varepsilon),\ \max_{i}\max\bigl(\mathrm{len}(x_i),\mathrm{len}(y_i)\bigr)\Bigr).$$
--   5. The **output string** for a tour $\pi$ (the cycle $\pi(0),\dots,\pi(n-1),\pi(0)$) and a rational value $\bar c$ is the list of the codes of $\pi(0),\dots,\pi(n-1)$ followed by the code of $\bar c$. For fixed $n$, distinct pairs $(\pi,\bar c)$ have distinct output strings.
--   6. $\log^+(1/\varepsilon)=\max\bigl(0,\log_2(1/\varepsilon)\bigr)$.
--
--   These are the objects in which Theorem 6.1 counts bit operations; the paper imposes no bound on the spread of the points beyond $L$.
--
--   **Formalization Note** All codes are prefix-free. The page's "binary encoding length" is not tied to a particular code; this one is within a constant factor of $\log_2(|a|+1)+\log_2(b+1)$, the usual size of $a/b$, so the class of bounds $2^{O(\sqrt k)}\mathrm{poly}(n,L,\log^+(1/\varepsilon))$ does not depend on the choice.
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), §6, p.13 (PDF p.15), and Theorem 6.1, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_FewInnerTSP_Instance

namespace FewInnerTSP.Supplement

/-- **Self-delimiting code of a natural number.** The number `m` is written as its binary digits
`b₀ b₁ … b_{ℓ-1}` (least significant first, `ℓ` the number of binary digits, `ℓ = 0` for `m = 0`),
preceded by `ℓ` in unary and a separator: `1^ℓ 0 b₀ … b_{ℓ-1}`.
Source: Li, Ma, Gong, *Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent*,
STOC 2027 submission (manuscript sha256 6541f631…), §6, p.13 (PDF p.15): "binary encoding length".

**Formalization Note** The code is prefix-free: the unary prefix fixes how many digits follow, so a
concatenation of such codes is read back uniquely. Its length is `2ℓ + 1`. -/
def natCode (m : ℕ) : List Bool :=
  List.replicate (Nat.digits 2 m).length true ++ [false] ++ (Nat.digits 2 m).map (fun b => b == 1)

/-- **Binary code of a rational number.** A sign bit (`true` for negative), then the self-delimiting
code of `|numerator|`, then that of the positive denominator, numerator and denominator in lowest
terms (`q.num`, `q.den`). Source: Li, Ma, Gong, §6, p.13 (PDF p.15): "Let rational coordinates
have binary encoding length at most L per coordinate."

**Formalization Note** The code is prefix-free and determines `q` (lowest terms are unique). Its
length is within a constant factor of `log₂(|num|+1) + log₂(den+1)`, the usual size of `q`. -/
def ratCode (q : ℚ) : List Bool :=
  [decide (q < 0)] ++ natCode q.num.natAbs ++ natCode q.den

/-- The encoding length of a rational number: the length of its code `ratCode`. -/
def ratLen (q : ℚ) : ℕ := (ratCode q).length

/-- **The planar point of a rational coordinate pair**, as a point of the Euclidean plane
`Pt = EuclideanSpace ℝ (Fin 2)` (never `ℚ × ℚ` or `ℝ × ℝ`, whose distance is the sup metric).
Source: Li, Ma, Gong, §6, p.13 (PDF p.15): "rational coordinates". -/
noncomputable def toPt (x : ℚ × ℚ) : Pt := !₂[(x.1 : ℝ), (x.2 : ℝ)]

/-- The point set `P` of a rational input `p : Fin n → ℚ × ℚ`: `P i` is the Euclidean point with the
coordinates `p i`. The published `GeneralPos`, `interiorCount` and `tourLen` apply to it verbatim. -/
noncomputable def ptsOf {n : ℕ} (p : Fin n → ℚ × ℚ) : Fin n → Pt := fun i => toPt (p i)

/-- **The input string of the bit algorithm.** The code of `n`, then of the accuracy `ε`, then of the
`2n` coordinates in index order `x₀, y₀, x₁, y₁, …`, each exactly (no rounding).
Source: Li, Ma, Gong, §6, p.13 (PDF p.15) and Theorem 6.1. -/
def inputCode (n : ℕ) (p : Fin n → ℚ × ℚ) (ε : ℚ) : List Bool :=
  natCode n ++ ratCode ε ++ (List.finRange n).flatMap (fun i => ratCode (p i).1 ++ ratCode (p i).2)

/-- **The encoding length `L`.** The maximum, over the `2n` coordinates and the accuracy `ε`, of the
encoding length of that rational. Source: Li, Ma, Gong, §6, p.13 (PDF p.15): "Let rational
coordinates have binary encoding length at most L per coordinate. Accuracy and threshold data are
also rational with their encoding included in L where applicable."

**Formalization Note** `ε` is included, as the page requires; `n` is not (it enters the bound
separately). -/
def encLen {n : ℕ} (p : Fin n → ℚ × ℚ) (ε : ℚ) : ℕ :=
  max (ratLen ε) (Finset.univ.sup fun i => max (ratLen (p i).1) (ratLen (p i).2))

/-- **The output string of the bit algorithm.** The tour `π` as the list `π 0, π 1, …, π (n-1)`
(the cycle visiting the points in this order), each index as a self-delimiting natural, followed
by the code of the rational value `c̄`. Source: Li, Ma, Gong, Theorem 6.1, p.13 (PDF p.15): "a
Hamiltonian cycle T … The same construction outputs a rational value c̄".

**Formalization Note** For a fixed `n` the map `(π, c̄) ↦ outputCode π c̄` is injective, because all
codes are prefix-free; so an output string names exactly one pair. -/
def outputCode {n : ℕ} (π : Equiv.Perm (Fin n)) (c : ℚ) : List Bool :=
  (List.finRange n).flatMap (fun i => natCode (π i).val) ++ ratCode c

/-- **`log⁺(1/ε)`** `= max(0, log₂(1/ε))`. Source: Li, Ma, Gong, Theorem 6.1, eq. (17), p.13
(PDF p.15). -/
noncomputable def logPlusInv (ε : ℚ) : ℝ := max 0 (Real.logb 2 (1 / (ε : ℝ)))

end FewInnerTSP.Supplement


