-- Prove2me | Definitions.Def_DQI_Semicircle_Setting
-- name    : DQI_Semicircle_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:41.944335+00:00
-- url     : https://prove2.me/theorems/4cb36b86-f5b6-45ea-b526-e8e2b4e6427d
-- title:
--   Definition 2.1, §8.2.1, §9 — max-LINSAT over F_p, f, s(x), g_i, g̃_i, g̃(y), the DQI amplitudes, |P̃(f)⟩, ⟨s⟩_opt, d⊥ > t, A^(m,ℓ,d), λ_max, the limit value
-- statement:
--   This file fixes the objects of Theorem 4.1 of Jordan et al. (DQI, arXiv:2408.08292v5).
--
--   **Instance.** Let $p$ be a prime and $\mathbb F_p$ the field with $p$ elements. A max-LINSAT instance (Definition 2.1) consists of a matrix $B\in\mathbb F_p^{m\times n}$ with rows $\mathbf b_1,\dots,\mathbf b_m$ and subsets $F_1,\dots,F_m\subseteq\mathbb F_p$; constraint $i$ is $\mathbf b_i\cdot\mathbf x\in F_i$. Write $f_i(a)=+1$ if $a\in F_i$ and $f_i(a)=-1$ otherwise, so that $F_i=f_i^{-1}(+1)$. The objective and the number of satisfied constraints are
--   $$f(\mathbf x)=\sum_{i=1}^m f_i(\mathbf b_i\cdot\mathbf x),\qquad s(\mathbf x)=\sum_{i=1}^m \mathbb 1_{F_i}(\mathbf b_i\cdot\mathbf x).$$
--
--   **Rescaled constraint functions** (§8.2.1, (37)–(38)). With $\bar f_i=\frac1p\sum_{a\in\mathbb F_p}f_i(a)$ and $\varphi_i=\big(\sum_{a}|f_i(a)-\bar f_i|^2\big)^{1/2}$,
--   $$g_i(a)=\frac{f_i(a)-\bar f_i}{\varphi_i},\qquad \tilde g_i(y)=\frac1{\sqrt p}\sum_{x\in\mathbb F_p}\omega_p^{yx}g_i(x),\qquad \omega_p=e^{2\pi i/p},$$
--   and for $\mathbf y\in\mathbb F_p^m$, $\tilde g(\mathbf y)=\prod_{i:\,y_i\neq0}\tilde g_i(y_i)$ (empty product $=1$), (67). The Hamming weight $|\mathbf y|$ is the number of nonzero coordinates.
--
--   **DQI states.** For $\ell\ge0$ and real weights $\mathbf w=(w_0,\dots,w_\ell)$, the state $\sum_k w_k|P^{(k)}\rangle$ of (46), (51) has amplitude
--   $$a_{\mathbf w}(\mathbf x)=\sum_{k=0}^{\ell} w_k\,\frac{P^{(k)}\big(g_1(\mathbf b_1\cdot\mathbf x),\dots,g_m(\mathbf b_m\cdot\mathbf x)\big)}{\sqrt{p^{\,n-k}\binom mk}},$$
--   where $P^{(k)}$ is the $k$-th elementary symmetric polynomial, and its syndrome-space form (66) has amplitude at $\mathbf s\in\mathbb F_p^n$
--   $$\tilde P(\mathbf s)=\sum_{k=0}^{\ell}\frac{w_k}{\sqrt{\binom mk}}\sum_{|\mathbf y|=k,\ B^T\mathbf y=\mathbf s}\tilde g(\mathbf y).$$
--   For real amplitudes $a$ with $\sum_x a(\mathbf x)^2=1$, the expected number of satisfied constraints upon measuring $\sum_{\mathbf x}a(\mathbf x)|\mathbf x\rangle$ is $\sum_{\mathbf x}a(\mathbf x)^2 s(\mathbf x)$.
--
--   **The optimum.** $\langle s^{(m,\ell)}\rangle_{\rm opt}$ is the supremum of $\sum_{\mathbf x}P(f(\mathbf x))^2 s(\mathbf x)$ over real polynomials $P$ of degree at most $\ell$ with $\sum_{\mathbf x}P(f(\mathbf x))^2=1$, i.e. over the normalized DQI states $|P(f)\rangle$ of (8).
--
--   **Dual distance.** "$t<d^\perp$" means: every nonzero $\mathbf d\in\mathbb F_p^m$ with $B^T\mathbf d=0$ has Hamming weight greater than $t$.
--
--   **The tridiagonal matrix** (70)/(111). $A^{(m,\ell,d)}$ is the $(\ell+1)\times(\ell+1)$ real symmetric matrix with diagonal $0,d,2d,\dots,\ell d$ and off-diagonal entries $a_1,\dots,a_\ell$, $a_k=\sqrt{k(m-k+1)}$. The parameter value of Lemma 9.2 is $d=(p-2r)/\sqrt{r(p-r)}$. $\lambda_{\max}(M)$ is the largest real eigenvalue (supremum of the real spectrum).
--
--   **The limit value** (9)/(139): for $\rho,\mu\in\mathbb R$,
--   $$\Sigma(\rho,\mu)=\begin{cases}\big(\sqrt{\mu(1-\rho)}+\sqrt{\rho(1-\mu)}\big)^2 & \rho\le1-\mu,\\ 1&\text{otherwise.}\end{cases}$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb F_p$ is `ZMod p` with `[Fact p.Prime]`; constraint indices are `Fin m` (0-based, the paper's $i=1,\dots,m$). $\omega_p^a$ is `Complex.exp (2πi·a.val/p)`. $f_i$, $g_i$ and $\mathbf w$ are real; $p^{n-k}$ uses an integer exponent. $\bar f_i,\varphi_i$ are defined from $F_i$, so (39)–(40) are theorems. "Degree-$\ell$" is `natDegree ≤ ℓ`. The DQI amplitudes are decomposed in the $g_i$, as in (44)–(46) of §8.2.1. The dual-distance condition quantifies over nonzero codewords only (no `sInf`).
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, pp. 4, 11, 21–23, 26–27, 31, 34, Definition 2.1, (1), (8), (9), (37)–(38), (41), (46)–(47), (51), (66)–(67), (70)–(71), (111), (131), (139)

import Mathlib

namespace DQI.Semicircle

open scoped BigOperators

/-! Jordan et al., *Optimization by Decoded Quantum Interferometry*, arXiv:2408.08292v5:
Definition 2.1 (p. 4), (8) (p. 11), §8.2.1 (37)–(52) (pp. 21–23), §9 (65)–(71), (111), (131)
(pp. 26–34), (9) (p. 11).

A max-LINSAT instance over `𝔽_p = ZMod p` with `m` constraints in `n` variables is a matrix
`B : Matrix (Fin m) (Fin n) (ZMod p)` and the sets `F i ⊆ 𝔽_p` (`i : Fin m`, 0-based; the
paper's `i = 1, …, m`). Constraint `i` is satisfied by `x` iff `(B x)_i ∈ F i`. -/

section Instance

variable {p : ℕ} [Fact p.Prime] {m n : ℕ}

/-- `f_i : 𝔽_p → {+1, −1}`, with `f_i⁻¹(+1) = F_i` (§8.2.1, p. 21). -/
noncomputable def fval (F : Fin m → Finset (ZMod p)) (i : Fin m) (a : ZMod p) : ℝ :=
  if a ∈ F i then 1 else -1

/-- The max-LINSAT objective `f(x) = Σ_i f_i(b_i · x)` ((1), (41)). -/
noncomputable def obj (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (x : Fin n → ZMod p) : ℝ :=
  ∑ i, fval F i (B.mulVec x i)

/-- The number of satisfied constraints `s(x) = Σ_i 𝟙_{F_i}(b_i · x)` ((71)). -/
def sat (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (x : Fin n → ZMod p) : ℕ :=
  (Finset.univ.filter fun i => B.mulVec x i ∈ F i).card

/-- `f̄ = (1/p) Σ_{x ∈ 𝔽_p} f_i(x)` (p. 21, below (38)). -/
noncomputable def fbar (F : Fin m → Finset (ZMod p)) (i : Fin m) : ℝ :=
  (1 / (p : ℝ)) * ∑ a : ZMod p, fval F i a

/-- `φ = (Σ_{y ∈ 𝔽_p} |f_i(y) − f̄|²)^{1/2}` (p. 21, below (38)). -/
noncomputable def phi (F : Fin m → Finset (ZMod p)) (i : Fin m) : ℝ :=
  Real.sqrt (∑ a : ZMod p, (fval F i a - fbar F i) ^ 2)

/-- The shifted and rescaled `g_i(x) = (f_i(x) − f̄)/φ` ((38)). -/
noncomputable def g (F : Fin m → Finset (ZMod p)) (i : Fin m) (a : ZMod p) : ℝ :=
  (fval F i a - fbar F i) / phi F i

/-- `ω_p^a = exp(2πi · a / p)` for `a ∈ 𝔽_p`, computed from the representative `a.val ∈ {0, …, p−1}`
(well defined since `ω_p^p = 1`). -/
noncomputable def omega (a : ZMod p) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) / (p : ℂ))

/-- The Fourier transform `g̃_i(y) = (1/√p) Σ_{x ∈ 𝔽_p} ω_p^{yx} g_i(x)` ((37)). -/
noncomputable def gt (F : Fin m → Finset (ZMod p)) (i : Fin m) (y : ZMod p) : ℂ :=
  (1 / (Real.sqrt p : ℂ)) * ∑ x : ZMod p, omega (y * x) * (g F i x : ℂ)

/-- `g̃(y) = Π_{i : y_i ≠ 0} g̃_i(y_i)` for `y ∈ 𝔽_p^m`, the empty product being `1` ((67)). -/
noncomputable def gtil (F : Fin m → Finset (ZMod p)) (y : Fin m → ZMod p) : ℂ :=
  ∏ i ∈ Finset.univ.filter (fun i => y i ≠ 0), gt F i (y i)

/-- The Hamming weight `|y|`: the number of nonzero coordinates. -/
def wt (y : Fin m → ZMod p) : ℕ :=
  (Finset.univ.filter fun i => y i ≠ 0).card

/-- `P^{(k)}(g_1(b_1·x), …, g_m(b_m·x))`, the degree-`k` elementary symmetric polynomial
evaluated at the `g_i(b_i · x)` ((47)). -/
noncomputable def esymmG (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (k : ℕ) (x : Fin n → ZMod p) : ℝ :=
  (Finset.univ.val.map fun i => g F i (B.mulVec x i)).esymm k

/-- The amplitude at `x` of `Σ_{k=0}^ℓ w_k |P^{(k)}⟩`, where
`|P^{(k)}⟩ = (p^{n−k} C(m,k))^{−1/2} Σ_x P^{(k)}(g_1(b_1·x), …, g_m(b_m·x)) |x⟩` ((46), (51)).
The exponent `n − k` is an integer. -/
noncomputable def ampl (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (ℓ : ℕ) (w : Fin (ℓ + 1) → ℝ) (x : Fin n → ZMod p) : ℝ :=
  ∑ k : Fin (ℓ + 1), w k * esymmG B F k x /
    Real.sqrt ((p : ℝ) ^ ((n : ℤ) - (k : ℕ)) * (m.choose k : ℝ))

/-- The syndrome-space state `|P̃(f)⟩ = Σ_{k=0}^ℓ (w_k/√C(m,k)) Σ_{|y| = k} g̃(y) |Bᵀ y⟩` ((66)):
its amplitude at the syndrome `s ∈ 𝔽_p^n`. -/
noncomputable def Ptilde (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (ℓ : ℕ) (w : Fin (ℓ + 1) → ℝ) (s : Fin n → ZMod p) : ℂ :=
  ∑ k : Fin (ℓ + 1), ((w k / Real.sqrt (m.choose (k : ℕ)) : ℝ) : ℂ) *
    ∑ y ∈ Finset.univ.filter (fun y : Fin m → ZMod p => wt y = (k : ℕ) ∧ B.transpose.mulVec y = s),
      gtil F y

/-- The expected number of satisfied constraints `Σ_x a(x)² s(x)` when measuring the state
`Σ_x a(x)|x⟩` (real, normalized amplitudes) in the computational basis (p. 11, below (8)). -/
noncomputable def expSat (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (a : (Fin n → ZMod p) → ℝ) : ℝ :=
  ∑ x, a x ^ 2 * (sat B F x : ℝ)

/-- `⟨s⟩_opt`: the largest expected number of satisfied constraints over the DQI states
`|P(f)⟩ = Σ_x P(f(x))|x⟩` with `P` a real polynomial of degree at most `ℓ` normalized so that
`⟨P(f)|P(f)⟩ = 1` (Theorem 4.1, (131)). -/
noncomputable def optSat (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (ℓ : ℕ) : ℝ :=
  sSup {e : ℝ | ∃ P : Polynomial ℝ, P.natDegree ≤ ℓ ∧
    ∑ x, (P.eval (obj B F x)) ^ 2 = 1 ∧
    e = ∑ x, (P.eval (obj B F x)) ^ 2 * (sat B F x : ℝ)}

/-- Every nonzero codeword of `C^⊥ = {d ∈ 𝔽_p^m : Bᵀ d = 0}` has Hamming weight `> t`, i.e.
`t < d^⊥`. -/
def DistGt (B : Matrix (Fin m) (Fin n) (ZMod p)) (t : ℕ) : Prop :=
  ∀ d : Fin m → ZMod p, d ≠ 0 → B.transpose.mulVec d = 0 → t < wt d

end Instance

/-- The `(ℓ+1) × (ℓ+1)` symmetric tridiagonal matrix `A^{(m,ℓ,d)}` of (70)/(111): diagonal
`0, d, 2d, …, ℓd`, and `a_1, …, a_ℓ` beside it, `a_k = √(k(m − k + 1))`. Rows and columns are
indexed by `k = 0, …, ℓ`; entry `(k, k+1)` is `a_{k+1} = √((k+1)(m − k))`. -/
noncomputable def Atri (m ℓ : ℕ) (dpar : ℝ) : Matrix (Fin (ℓ + 1)) (Fin (ℓ + 1)) ℝ :=
  fun i j =>
    if (i : ℕ) = j then (i : ℕ) * dpar
    else if (j : ℕ) = (i : ℕ) + 1 then Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ)))
    else if (i : ℕ) = (j : ℕ) + 1 then Real.sqrt (((j : ℕ) + 1 : ℝ) * ((m : ℝ) - (j : ℕ)))
    else 0

/-- `d = (p − 2r)/√(r(p − r))` ((70)). -/
noncomputable def dparOf (p r : ℕ) : ℝ :=
  ((p : ℝ) - 2 * r) / Real.sqrt (r * ((p : ℝ) - r))

/-- The maximum eigenvalue of a real square matrix, as the supremum of its real spectrum. -/
noncomputable def lamMax {ℓ : ℕ} (M : Matrix (Fin (ℓ + 1)) (Fin (ℓ + 1)) ℝ) : ℝ :=
  sSup (spectrum ℝ M)

/-- The limit value of Theorem 4.1, (9)/(139): `(√(μ(1−ρ)) + √(ρ(1−μ)))²` if `ρ ≤ 1 − μ`,
and `1` otherwise. -/
noncomputable def semicircle (ρ μ : ℝ) : ℝ :=
  if ρ ≤ 1 - μ then (Real.sqrt (μ * (1 - ρ)) + Real.sqrt (ρ * (1 - μ))) ^ 2 else 1

end DQI.Semicircle


