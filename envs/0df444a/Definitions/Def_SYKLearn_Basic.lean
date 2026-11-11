-- Prove2me | Definitions.Def_SYKLearn_Basic
-- name    : SYKLearn_Basic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:11.651448+00:00
-- url     : https://prove2.me/theorems/81eab1c3-5961-456e-980b-12e4b7a19f5e
-- title:
--   SYK scale $\sigma_n$, coefficient vectors $H_v=\sum_S v_S\Gamma_S$, Majorana coefficients $X|_{\mathbb M_k}$, Jordan–Wigner register
-- statement:
--   The **SYK model** on $n$ Majorana modes ($n$ even, $D=2^{n/2}$) is
--
--   $$H_g=\sum_{I\in\binom{[n]}{4}} g_I\Gamma_I,\qquad g_I\overset{\text{i.i.d.}}{\sim}\mathcal N(0,\sigma_n^2),\qquad \sigma_n=\sqrt{6/n^3},\qquad m=\binom n4,$$
--
--   where $\psi_1,\dots,\psi_n$ are Hermitian Majorana operators ($\{\psi_i,\psi_j\}=2\delta_{ij}I$) on $\mathbb C^D$ and $\Gamma_S=\psi_{s_1}\cdots\psi_{s_k}$ is their ordered product for $S=\{s_1<\dots<s_k\}$. This module fixes the notation shared by every statement of the mission.
--
--   1. $\sigma_n=\sqrt{6/n^3}$ and $m=\binom n4$.
--   2. The **exterior algebra** $\bigoplus_k\mathbb M_k$, $\mathbb M_k=\Lambda^k\mathbb R^n$, written in its basis $e_S$, $S\subseteq[n]$; a vector $u$ lies in $\mathbb M_k$ when it is supported on $k$-sets. The coupling vector is $|g\rangle=\sum_I g_I|I\rangle\in\mathbb M_4$, and for any coefficient vector $v$ the operator $H_v=\sum_S v_S\Gamma_S$.
--   3. The **coefficient** of $\Gamma_S$ in an operator $X$ is $\mathrm{Tr}[\Gamma_S^\dagger X]$, with the normalized trace $\mathrm{Tr}=2^{-n/2}\mathrm{tr}$. Since the $\Gamma_S$ are orthonormal for $\langle X,Y\rangle=\mathrm{Tr}[X^\dagger Y]$, the vector of these coefficients on $k$-sets is the paper's restriction $X|_{\mathbb M_k}$.
--   4. The **Jordan–Wigner** Majorana operators on $n/2$ qubits, $\psi_{2j}=Z^{\otimes j}\otimes X\otimes I$, $\psi_{2j+1}=Z^{\otimes j}\otimes Y\otimes I$, and the identification of $\mathbb C^D$ with the $n/2$-qubit register of a learner.
--
--   These are the objects in terms of which the learning theorem, the direction matrix, the commutator identities and the scale experiment are stated.
--
--   **Formalization Note** The SYK model is the published `SYKFastMix.FastMixing.Model` with $J=1$: it carries $n\ge4$, $n$ even, and a Hermitian CAR family on $\mathbb C^{2^{n/2}}$; `rawString` is the unphased product $\Gamma_S$ (the paper's phase $-i^{q/2}$ is $1$ at $q=4$), `hamiltonian` is $H_g$. Modes are `Fin n`. The coefficient $\mathrm{Tr}[\Gamma_S^\dagger X]$ is complex; only `resReal` takes a real part, for operators with real coefficients. The Jordan–Wigner operators are the published `FermiCap.Gaussian.majorana`, transported to $\mathbb C^{2^{n/2}}$ through $\{0,1\}\cong$ `Bool` and `QAlgorithms.bitsEquivFin`; that they form a CAR family is proved in the mission's sanity file.
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), (1)–(2), p.2; Notation, pp.10–11; §2.1, p.11; Lemma 4.9, p.39

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Model
import Definitions.Def_FermiCap_Gaussian_Majorana
import Definitions.Def_QAlgorithms_Defs_Basic

noncomputable section
open Matrix MeasureTheory

namespace SYKLearn

/-!
# SYK scale, coefficient vectors, Majorana coefficients, the Jordan–Wigner register

A. Anshu, S. Arunachalam, S. Chen, Y. Hwang, *Efficiently Learning SYK Hamiltonians*, STOC 2027
submission (held file sha256 5d7d199a…), model (1)–(2), p.2; Notation, pp.10–11; §2.1, p.11;
Lemma 4.9, p.39 (Jordan–Wigner).

**Formalization Note.**
* The SYK layer is the published `SYKFastMix.FastMixing.Model`: `Q : Model N` carries `4 ≤ N`,
  `N` even, a scale `J > 0` and a Hermitian CAR family `Q.γ : Fin N → Mat (Fin (2^(N/2)))`
  (the paper's Majoranas `ψ_i`, `{ψ_i, ψ_j} = 2δ_ij I`); `Disorder N = KSet N 4 → ℝ` is the
  coupling vector `g = (g_I)_{|I|=4}`; `disorderLaw Q` is the product of `N(0, 6J²/N³)`, so every
  statement of the mission takes `Q.J = 1`, which makes the variance the paper's `σ_n² = 6/n³`;
  `rawString Q S` is the unphased ordered product `Γ_S = ψ_{s₁}⋯ψ_{s_k}`, `s₁ < ⋯ < s_k`
  (at `q = 4` the paper's phase `−i^{q/2}` is `1`, p.2); `hamiltonian Q w = Σ_I w_I Γ_I = H_w`.
  Modes are `Fin N` (the page's `[n]`, shifted to start at `0`).
* `Ext N` is the exterior algebra `⊕_k M_k = ⊕_k Λ^k ℝ^N` written in the basis `e_S`,
  `S ⊆ Fin N`: a vector is its coefficient function on finsets (degree = card). `IsHomog k u`
  says `u ∈ M_k`. `ham Q v = Σ_S v_S Γ_S = H_v` (Notation, p.10) for a vector of any degree;
  `emb4 w` is the coupling vector `|g⟩ = Σ_I g_I |I⟩ ∈ M_4` (p.11).
* `coeff Q X S = Tr[Γ_S^† X]` with the normalized trace `Tr = 2^{−N/2} tr` (`SYKEdge.ntr`). The
  `Γ_S` are orthonormal for `⟨X, Y⟩ = Tr[X^† Y]` (any CAR family in dimension `2^{N/2}` is
  irreducible), so `coeff Q X S` is the coefficient of `Γ_S` in `X`; the paper's restriction
  `X|M_k` (p.11, p.14) is the vector `S ↦ coeff Q X S` on `k`-sets. It is complex-valued: no real
  part is taken unless a statement says so. `resReal Q k X` is its real part on `k`-sets, used only
  for operators with real coefficients (`H²` of a real coupling vector).
* `jw Q i` is the Jordan–Wigner Majorana operator: the published `FermiCap.Gaussian.majorana`
  on `N/2` qubits (`γ_{2j} = Z^{⊗j} ⊗ X ⊗ I`, `γ_{2j+1} = Z^{⊗j} ⊗ Y ⊗ I`, qubit `k` = tensor
  factor `k`), transported to `Fin (2^(N/2))` by `Fin 2 ≃ Bool` (`0 ↦ false`) and the published
  `QAlgorithms.bitsEquivFin`. `toReg` transports a matrix on `Fin (2^(N/2))` back to the learner's
  register `QAlgorithms.Qubits (N/2)`, so `toReg (jw Q i)` is the Jordan–Wigner operator on the
  learner's wires. The paper uses this encoding for its circuits (Lemma 4.9, p.39; §5, p.43).
-/

open SYKFastMix.FastMixing

/-- The SYK coupling standard deviation `σ_n = √(6/n³)` ((1), p.2). -/
def sigma (N : ℕ) : ℝ := Real.sqrt (6 / (N : ℝ) ^ 3)

/-- `m = C(n, 4)`, the number of quartic couplings ((1), p.2). -/
abbrev m (N : ℕ) : ℕ := Fintype.card (SYKEdge.KSet N 4)

/-- The exterior algebra `⊕_k Λ^k ℝ^N` in the basis `e_S` (§2.1, p.11). -/
abbrev Ext (N : ℕ) := Finset (Fin N) → ℝ

/-- `u ∈ M_k`: `u` is supported on `k`-sets. -/
def IsHomog {N : ℕ} (k : ℕ) (u : Ext N) : Prop := ∀ S : Finset (Fin N), S.card ≠ k → u S = 0

/-- The coupling vector `|g⟩ = Σ_{|I|=4} g_I |I⟩ ∈ M_4` (Notation, p.11). -/
def emb4 {N : ℕ} (w : Disorder N) : Ext N :=
  fun S => if h : S.card = 4 then w ⟨S, h⟩ else 0

/-- The Euclidean inner product `⟨u, v⟩ = Σ_S u_S v_S` on `Ext N`. -/
def extInner {N : ℕ} (u v : Ext N) : ℝ := ∑ S, u S * v S

/-- The Euclidean norm `‖g‖₂ = (Σ_I g_I²)^{1/2}` of a coupling vector. -/
def cnorm {N : ℕ} (w : Disorder N) : ℝ := Real.sqrt (∑ I, w I ^ 2)

/-- `H_v = Σ_S v_S Γ_S` for a coefficient vector of any degree (Notation, p.10). -/
def ham {N : ℕ} (Q : Model N) (v : Ext N) : Mat (SiteHilbert N) :=
  ∑ S, (v S : ℂ) • rawString Q S

/-- The coefficient `Tr[Γ_S^† X]` of `Γ_S` in `X` (normalized trace); on `k`-sets this is the
paper's restriction `X|M_k`. -/
def coeff {N : ℕ} (Q : Model N) (X : Mat (SiteHilbert N)) (S : Finset (Fin N)) : ℂ :=
  SYKEdge.ntr ((rawString Q S)ᴴ * X)

/-- The real part of `X|M_k`, as a vector of `M_k` (zero off `k`-sets). -/
def resReal {N : ℕ} (Q : Model N) (k : ℕ) (X : Mat (SiteHilbert N)) : Ext N :=
  fun S => if S.card = k then (coeff Q X S).re else 0

/-- The qubit-basis bijection `{0,1}^{N/2} ≃ Fin (2^{N/2})`: `Fin 2 ≃ Bool` on each qubit, then the
published `QAlgorithms.bitsEquivFin` (wire `0` most significant). -/
def regEquiv (N : ℕ) : FermiCap.Gaussian.Qubits (N / 2) ≃ Fin (2 ^ (N / 2)) :=
  (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv).trans (QAlgorithms.bitsEquivFin (N / 2))

/-- The Jordan–Wigner Majorana operator `ψ_i` on `N/2` qubits (`FermiCap.Gaussian.majorana`),
transported to `Fin (2^{N/2})`. -/
def jw {N : ℕ} (Q : Model N) (i : Fin N) : Mat (SiteHilbert N) :=
  Matrix.reindex (regEquiv N) (regEquiv N)
    (FermiCap.Gaussian.majorana (N / 2) (Fin.cast (Nat.two_mul_div_two_of_even Q.even).symm i))

/-- A matrix on `Fin (2^{N/2})`, transported to the learner's register `Qubits (N/2)`. -/
def toReg {N : ℕ} (X : Mat (SiteHilbert N)) :
    Matrix (QAlgorithms.Qubits (N / 2)) (QAlgorithms.Qubits (N / 2)) ℂ :=
  Matrix.reindex (QAlgorithms.bitsEquivFin (N / 2)).symm (QAlgorithms.bitsEquivFin (N / 2)).symm X

end SYKLearn


