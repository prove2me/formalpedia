-- Prove2me | Definitions.Def_CorrBoundsPoly_ExactDegree_ElemSym
-- name    : CorrBoundsPoly_ExactDegree_ElemSym
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:57:52.54321+00:00
-- url     : https://prove2.me/theorems/dec18ce7-1732-405e-9ca6-48583be5a982
-- title:
--   Eqs. (1.2), (1.4), §3.3 — dyadic integers, $\sigma_{D,m}$, $\eta(m,D)$, $a_D(m)$, $\mathbb E_{K\sim\mathrm{Bin}}$, pairing coordinates
-- statement:
--   An integer $D$ is **dyadic** if $D=2^a$ for an integer $a\ge 0$ (so $1$ is dyadic). For $x\in\mathbb F_2^m$, $|x|$ is its Hamming weight.
--
--   The **elementary symmetric core** is
--   $$\sigma_{D,m}(x)=\sum_{S\subseteq[m],\,|S|=D}\ \prod_{i\in S}x_i\quad\text{over }\mathbb F_2,$$
--   which is $0$ when $D>m$. With binomial coefficients outside their range equal to zero,
--   $$\eta(m,D)=2^{-m}\sum_{r=0}^{D-1}\Big|\sum_{j\ge0}(-1)^j\binom{m}{r+jD}\Big|.$$
--   The certificate $a_D(m)=\nu(\sigma_{D,m})=1-2\operatorname{rank}(\mu_{\sigma_{D,m}})/2^m$ (rank in the truncated algebra $A_m$), with $a_D(m)=1$ when $m<D$. For a function $g$ on $\{0,\dots,r\}$, $\mathbb E_{K\sim\mathrm{Bin}(r,1/2)}g(K)=\sum_{k=0}^r\binom rk2^{-r}g(k)$.
--
--   **Pairing coordinates (Lemma 3.5).** For $r=\lfloor m/2\rfloor$ and $1\le i\le r$,
--   $$u_i=x_{2i-1}+\sum_{j=2i+1}^m x_j,\qquad v_i=x_{2i}+\sum_{j=2i+1}^m x_j,$$
--   and, when $m$ is odd, the leftover coordinate $x_m$.
--
--   These are the objects of the exact correlation formula for dyadic elementary cores (Section 3).
--
--   **Formalization Note** `IsDyadic n` is `∃ a, n = 2 ^ a`; `hw x` counts the `i` with `x i = 1`. `sigma D m` is Mathlib's `MvPolynomial.esymm (Fin m) (ZMod 2) D`. In `eta m D` the inner sum runs over `0 ≤ j ≤ m`, which drops only zero terms when `D ≥ 1`. `aD D m` is `if m < D then 1 else nu (sigma D m)`. Variables and pair indices are 0-based: `pairU m i = X (2i) + ∑_{j ≥ 2i+2} X j`, `pairV m i = X (2i+1) + ∑_{j ≥ 2i+2} X j` for `i : Fin (m / 2)`, and `pairCoord m k = X k + ∑_{j ≥ 2⌊k/2⌋+2} X j` lists the whole coordinate system by old variable `k` (coordinate `2i` is $u_{i+1}$, `2i+1` is $v_{i+1}$, and for odd `m` the last one is $x_m$, its tail being empty).
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), pp. 3–4 (PDF 5–6), Eqs. (1.2), (1.4); p. 25 (PDF 27); §1.4, p. 17 (PDF 19); §3.3 and Lemma 3.5, p. 27 (PDF 29)

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_TruncAlg

namespace CorrBoundsPoly.ExactDegree

/-! Xin Li, *More on Correlation Bounds for Polynomials*, STOC 2027 submission (manuscript sha256
aa4ef6f7…), Eqs. (1.2), (1.4) (pp. 3–4, PDF 5–6; restated p. 25, PDF 27), §1.4 (pp. 17–18),
§3.3 (p. 27, PDF 29) and Lemma 3.5 (p. 27).

Dyadic integers, Hamming weight, the elementary symmetric cores `σ_{D,m}`, the residue sum
`η(m, D)`, the rank-defect certificate `a_D(m)`, the binomial expectation
`E_{K ∼ Bin(r, 1/2)}`, and the pairing coordinates of Lemma 3.5. -/

/-- A **dyadic** integer has the form `2^a` for an integer `a ≥ 0` (§1.4, p. 17); `1` is dyadic. -/
def IsDyadic (n : ℕ) : Prop := ∃ a : ℕ, n = 2 ^ a

/-- The Hamming weight `|x| = #{i : x_i = 1}` of `x ∈ F₂^m`. -/
def hw {m : ℕ} (x : Fin m → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i => x i = 1).card

/-- **Eq. (1.2).** `σ_{D,m}(x) = ∑_{S ⊆ [m], |S| = D} ∏_{i ∈ S} x_i` over `F₂` (zero when
`D > m`): Mathlib's elementary symmetric polynomial `esymm`. -/
noncomputable abbrev sigma (D m : ℕ) : MvPolynomial (Fin m) (ZMod 2) :=
  MvPolynomial.esymm (Fin m) (ZMod 2) D

/-- **Eq. (1.4).** `η(m, D) = 2^{−m} ∑_{r=0}^{D−1} |∑_{j ≥ 0} (−1)^j C(m, r + jD)|`, binomial
coefficients outside their range being zero. For `D ≥ 1` every nonzero term has `j ≤ m`, so the
inner sum is taken over `0 ≤ j ≤ m`. -/
noncomputable def eta (m D : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ m *
    ∑ r ∈ Finset.range D,
      |∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j * ((m.choose (r + j * D) : ℕ) : ℝ)|

/-- **§3.3 (p. 27).** `a_D(m) = ν(σ_{D,m}) = 1 − 2 rank(µ_{σ_{D,m}})/2^m` (rank in `A_m`), and
`a_D(m) = 1` when `m < D`. -/
noncomputable def aD (D m : ℕ) : ℝ :=
  if m < D then 1 else nu (sigma D m)

/-- `E_{K ∼ Bin(r, 1/2)} g(K) = ∑_{k=0}^{r} C(r,k) 2^{−r} g(k)`. -/
noncomputable def binomExp (r : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (r + 1), ((r.choose k : ℕ) : ℝ) / 2 ^ r * g k

/-- The tail `∑_{j=2i+1}^{m} x_j` of Lemma 3.5 for the (1-based) pair index `i + 1`: with 0-based
variables it is the sum of `x_j` over `j ≥ 2i + 2`. -/
noncomputable def pairTail (m i : ℕ) : MvPolynomial (Fin m) (ZMod 2) :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin m => 2 * i + 2 ≤ j.val), MvPolynomial.X j

/-- **Lemma 3.5.** `u_i = x_{2i−1} + ∑_{j=2i+1}^{m} x_j` for `1 ≤ i ≤ r = ⌊m/2⌋`, written with the
0-based pair index `i : Fin (m/2)` and 0-based variables: `X (2i) + ∑_{j ≥ 2i+2} X j`. -/
noncomputable def pairU (m : ℕ) (i : Fin (m / 2)) : MvPolynomial (Fin m) (ZMod 2) :=
  MvPolynomial.X ⟨2 * i.val, by omega⟩ + pairTail m i.val

/-- **Lemma 3.5.** `v_i = x_{2i} + ∑_{j=2i+1}^{m} x_j`, 0-based: `X (2i+1) + ∑_{j ≥ 2i+2} X j`. -/
noncomputable def pairV (m : ℕ) (i : Fin (m / 2)) : MvPolynomial (Fin m) (ZMod 2) :=
  MvPolynomial.X ⟨2 * i.val + 1, by omega⟩ + pairTail m i.val

/-- The full coordinate system of Lemma 3.5, indexed by the old variables: coordinate `2i` is
`u_{i+1}`, coordinate `2i+1` is `v_{i+1}` (0-based), and, when `m` is odd, the last coordinate is
the leftover `x_m` (its tail is the empty sum). In one formula: `X k + ∑_{j ≥ 2⌊k/2⌋+2} X j`. -/
noncomputable def pairCoord (m : ℕ) (k : Fin m) : MvPolynomial (Fin m) (ZMod 2) :=
  MvPolynomial.X k + pairTail m (k.val / 2)

end CorrBoundsPoly.ExactDegree


