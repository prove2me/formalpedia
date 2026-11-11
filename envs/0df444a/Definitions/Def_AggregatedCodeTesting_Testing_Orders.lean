-- Prove2me | Definitions.Def_AggregatedCodeTesting_Testing_Orders
-- name    : AggregatedCodeTesting_Testing_Orders
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:11.386391+00:00
-- url     : https://prove2.me/theorems/8991b8c7-4db3-4198-9b02-4cc3ae7fddd7
-- title:
--   Eq. (4), (11) — code polynomials, formal logarithm, detection orders $t_{C_D}(A)$, $s^*(C)$, character energy $\mathcal E_w$, and the selected-moment test
-- statement:
--   Let $C\le\mathbb F_2^m$ be a binary linear code with blocks, block duals $C_D^\perp$ and character counts as in the model definitions, and let $z=(z_1,\dots,z_m)$ be formal variables with $z^A=\prod_{e\in A}z_e$ and $\chi_A(\sigma)=(-1)^{A\cdot\sigma}$.
--
--   1. **Code polynomials.** For a block $D$ and a coset $\sigma$, $g_\sigma(z)=\sum_{A\in C_D^\perp}\chi_A(\sigma)z^A$, and $G_\ell(z)=\prod_\sigma g_\sigma(z)^{n_\sigma(\ell)}=\prod_j g_{\ell_j}(z)$ for the code polynomials of $C$ itself.
--   2. **Formal logarithm.** For a power series $f$ with constant coefficient $1$, $\log f=\sum_{k\ge1}(-1)^{k+1}(f-1)^k/k$, a formal power series over $\mathbb Q$ with zero constant term.
--   3. **Character logarithms and detection orders.** On a block $D$ with $q=|Q_D|$,
--   $$
--   L_A(z)=q^{-1}\sum_{\sigma\in Q_D}\chi_A(\sigma)\log g_\sigma(z),
--   $$
--   and the **detection order** $t_{C_D}(A)$ is the least total degree of a monomial of $L_A$ with nonzero coefficient. Further, $S=s^*(C)=\max t_{C_D}(A)$ over informative blocks $D$ and $0\ne A\in C_D^\perp$, with $s^*(C)=0$ if there is no informative block.
--   4. **Character energy** (eq. (11)). For two offset sequences of width $w$,
--   $$
--   \mathcal E_w(\ell,\ell')=\sum_{D\text{ informative}}\ \sum_{0\ne A\in C_D^\perp}\frac{\big(\hat n_{D,A}(\ell')-\hat n_{D,A}(\ell)\big)^2}{w^{t_{C_D}(A)}}.
--   $$
--   5. **Selected-moment test.** For a multi-index $r$ and $N$ observations $H^{(1)},\dots,H^{(N)}$, the moment test declares $\ell'$ exactly when the empirical mean $N^{-1}\sum_i\psi_r(H^{(i)})$ lies strictly beyond the midpoint $(c_\ell(r)+c_{\ell'}(r))/2$ on the side of $c_{\ell'}(r)$. A **blockwise index** is a multi-index $\nu$ with $1\le|\nu|\le S$ supported in a single informative block (entries $\nu_e>w$ allowed, with moment $0$); a **selected index** is a blockwise index maximizing the squared normalized mean gap $(c_{\ell'}(\nu)-c_\ell(\nu))^2/w^{|\nu|}$.
--
--   The detection orders are the code invariants that set the width exponents of testing; the energy weighs every changed character amplitude by its order, and the selected-moment test is the procedure of the proof of Theorem 10.
--
--   **Formalization Note.** $L_A$ is computed as $2^{-m}\sum_{x\in\mathbb F_2^m}\chi_A(x)\log g_x$, which counts each block coset $2^m/q$ times. The formal logarithm is defined coefficientwise: the coefficient at $z^v$ only involves $k\le|v|$. Detection orders take values in $\mathbb N\cup\{\infty\}$ (finiteness is part of Theorem 3), and an energy term with $t=\infty$ is read as $w^{-\infty}=0$; Theorem 3 shows this case does not occur. Ties at the midpoint are decided for $\ell$.
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), eq. (4) and t_C(A), printed p. 4 (PDF p. 5); s*(C), printed p. 5 (PDF p. 6); eq. (11), printed p. 8 (PDF p. 9); selected moment test, proof of Theorem 10 Steps 1–2, printed pp. 8–9 (PDF pp. 9–10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf

import Mathlib
import Definitions.Def_AggregatedCodeTesting_Testing_Model

open Finset Classical

namespace AggregatedCodeTesting.Testing

/-! # Code polynomials, the formal logarithm, detection orders, energy and the moment test

Wang–Wang–Pang–Xiao–Zhang–Fu–Zheng–Zou, STOC 2027 submission #1555, eq. (4) (printed p. 4,
PDF p. 5), definition of `s*(C)` (printed p. 5, PDF p. 6), eq. (11) (printed p. 8, PDF p. 9),
and the selected-moment test of the proof of Theorem 10 (printed pp. 8–9, PDF pp. 9–10).
Variables `z_e` are indexed by `Fin m`. -/

variable {m : ℕ}

/-- The character `χ_A(x) = (-1)^{A · x}`. -/
def chi (A x : Word m) : ℤ := (-1) ^ (dotProduct A x).val

/-- The monomial `z^A = ∏_{e ∈ A} z_e`. -/
noncomputable def monoOf (R : Type) [CommRing R] (A : Word m) : MvPolynomial (Fin m) R :=
  ∏ e ∈ supp A, MvPolynomial.X e

/-- The block code polynomial `g_σ(z) = ∑_{A ∈ C_D^⊥} χ_A(σ) z^A` of the coset `σ` of `x`
on the block `D`. For `D = univ` this is the code polynomial of `C` itself. -/
noncomputable def codePoly (R : Type) [CommRing R] (C : Submodule (ZMod 2) (Word m))
    (D : Finset (Fin m)) (x : Word m) : MvPolynomial (Fin m) R :=
  ∑ A ∈ blockDual C D, (chi A x : R) • monoOf R A

/-- `G_ℓ(z) = ∏_σ g_σ(z)^{n_σ(ℓ)} = ∏_j g_{ℓ_j}(z)`, with `g` the code polynomial of `C`
(over `ℤ`). -/
noncomputable def genPoly {w : ℕ} (C : Submodule (ZMod 2) (Word m)) (ℓ : Fin w → Word m) :
    MvPolynomial (Fin m) ℤ :=
  ∏ j, codePoly ℤ C univ (ℓ j)

/-- The formal logarithm of a power series `f` with constant coefficient `1`:
`log f = ∑_{k ≥ 1} (-1)^{k+1} (f - 1)^k / k`, with zero constant term. The coefficient at `v`
only involves `k ≤ |v|`, since `f - 1` has no constant term. -/
noncomputable def formalLog (f : MvPowerSeries (Fin m) ℚ) : MvPowerSeries (Fin m) ℚ :=
  fun v => ∑ k ∈ Icc 1 v.degree,
    ((-1 : ℚ) ^ (k + 1) / (k : ℚ)) * MvPowerSeries.coeff v ((f - 1) ^ k)

/-- `L_A(z) = q⁻¹ ∑_σ χ_A(σ) log g_σ(z)` on the block `D`, `q = |Q_D|`. Summing over all
`x ∈ F₂^m` counts each block coset `2^m / q` times, hence the factor `2^{-m}`. -/
noncomputable def logChar (C : Submodule (ZMod 2) (Word m)) (D : Finset (Fin m)) (A : Word m) :
    MvPowerSeries (Fin m) ℚ :=
  ((2 : ℚ) ^ m)⁻¹ • ∑ x : Word m,
    (chi A x : ℚ) • formalLog ((codePoly ℚ C D x : MvPolynomial (Fin m) ℚ) :
      MvPowerSeries (Fin m) ℚ)

/-- The detection order `t_{C_D}(A)`: the least total degree of a monomial of `L_A` with
nonzero coefficient (`⊤` if `L_A = 0`). -/
noncomputable def detOrder (C : Submodule (ZMod 2) (Word m)) (D : Finset (Fin m)) (A : Word m) :
    ℕ∞ :=
  ⨅ (v : Fin m →₀ ℕ) (_ : MvPowerSeries.coeff v (logChar C D A) ≠ 0), (v.degree : ℕ∞)

/-- `S = s*(C) = max_{D informative, 0 ≠ A ∈ C_D^⊥} t_{C_D}(A)`, and `0` if there is no
informative block. -/
noncomputable def sStar (C : Submodule (ZMod 2) (Word m)) : ℕ∞ :=
  ⨆ D ∈ informativeBlocks C, ⨆ A ∈ blockDual C D, ⨆ (_ : A ≠ 0), detOrder C D A

/-- The character energy (11):
`ℰ_w(ℓ, ℓ′) = ∑_{D informative} ∑_{0 ≠ A ∈ C_D^⊥} (n̂_{D,A}(ℓ′) - n̂_{D,A}(ℓ))² / w^{t_{C_D}(A)}`.
A term with `t = ⊤` (which Theorem 3 excludes) is read as `w^{-∞} = 0`. -/
noncomputable def energy {w : ℕ} (C : Submodule (ZMod 2) (Word m)) (ℓ ℓ' : Fin w → Word m) : ℝ :=
  ∑ D ∈ informativeBlocks C, ∑ A ∈ (blockDual C D).filter (· ≠ 0),
    if detOrder C D A = ⊤ then 0
    else ((hatCount A ℓ' - hatCount A ℓ : ℤ) : ℝ) ^ 2 / (w : ℝ) ^ (detOrder C D A).toNat

/-- The midpoint test of the moment `ψ_r` with `N` samples, for the two known profiles
`ℓ` (first hypothesis) and `ℓ′` (second): with `μ = c_ℓ(r)`, `μ′ = c_{ℓ′}(r)` and the
empirical mean `ψ̄ = N⁻¹ ∑_i ψ_r(H^{(i)})`, declare `ℓ′` (value `1`) iff `ψ̄` lies strictly
beyond the midpoint `(μ + μ′)/2` on the side of `μ′`. -/
noncomputable def momentTest {w : ℕ} (C : Submodule (ZMod 2) (Word m)) (ℓ ℓ' : Fin w → Word m)
    (r : Fin m → ℕ) (N : ℕ) : (Fin N → (Fin m → Fin (w + 1))) → ℝ :=
  fun xs =>
    if (moment C ℓ r < moment C ℓ' r ∧
          (moment C ℓ r + moment C ℓ' r) / 2 < (∑ i, (psi w r (xs i) : ℝ)) / N) ∨
        (moment C ℓ' r < moment C ℓ r ∧
          (∑ i, (psi w r (xs i) : ℝ)) / N < (moment C ℓ r + moment C ℓ' r) / 2)
    then 1 else 0

/-- The blockwise moment indices of the proof of Theorem 10: `1 ≤ |ν| ≤ S` and `ν` supported in
a single informative block (indices `ν_e > w` allowed; their moments are `0`). -/
def IsBlockwiseIndex (C : Submodule (ZMod 2) (Word m)) (ν : Fin m → ℕ) : Prop :=
  1 ≤ absIdx ν ∧ (absIdx ν : ℕ∞) ≤ sStar C ∧
    ∃ D ∈ informativeBlocks C, ∀ e, ν e ≠ 0 → e ∈ D

/-- The squared normalized mean gap `(c_{ℓ′}(ν) - c_ℓ(ν))² / w^{|ν|}`. -/
noncomputable def momentGap {w : ℕ} (C : Submodule (ZMod 2) (Word m)) (ℓ ℓ' : Fin w → Word m)
    (ν : Fin m → ℕ) : ℝ :=
  (moment C ℓ' ν - moment C ℓ ν) ^ 2 / (w : ℝ) ^ absIdx ν

/-- `ν` is a selected index: a blockwise index maximizing the squared normalized mean gap. -/
def IsSelectedIndex {w : ℕ} (C : Submodule (ZMod 2) (Word m)) (ℓ ℓ' : Fin w → Word m)
    (ν : Fin m → ℕ) : Prop :=
  IsBlockwiseIndex C ν ∧ ∀ ν', IsBlockwiseIndex C ν' → momentGap C ℓ ℓ' ν' ≤ momentGap C ℓ ℓ' ν

end AggregatedCodeTesting.Testing


