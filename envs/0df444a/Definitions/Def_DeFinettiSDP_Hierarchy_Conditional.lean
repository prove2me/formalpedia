-- Prove2me | Definitions.Def_DeFinettiSDP_Hierarchy_Conditional
-- name    : DeFinettiSDP_Hierarchy_Conditional
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:54:01.943012+00:00
-- url     : https://prove2.me/theorems/d43b872d-deed-4b79-b347-783b38489f92
-- title:
--   §2.4, p. 5, and proof of Theorem 2.3, p. 8 — conditional states ρ_{A|z}, ρ_{AZ_{m+1}|z^m_1}, ρ_{B_{m+1}|z^m_1}
-- statement:
--   This file defines the conditional states used in Lemma 2.1 and in the proof of Theorem 2.3.
--
--   **Classical-quantum states.** A state on $A\otimes Z_1\cdots Z_N$ with classical $Z$-systems (alphabet $\{1,\dots,t\}$) is $\rho_{AZ_1^N}=\sum_z|z\rangle\langle z|\otimes\tilde\rho(z)$ with $\tilde\rho(z)\succeq0$ and $\sum_z\mathrm{Tr}\,\tilde\rho(z)=1$. For an outcome string $w=z_1^j$ of the first $j$ systems:
--
--   1. $\tilde\rho_j(w)=\sum\tilde\rho(z)$ over the strings $z$ that begin with $w$, and $p(w)=\mathrm{Tr}\,\tilde\rho_j(w)$;
--   2. the conditional cq-state $\rho_{AZ_{m+1}|z_1^m=w}=\sum_{z'}|z'\rangle\langle z'|\otimes\tilde\rho_{m+1}(w,z')/p(w)$;
--   3. the conditional marginals $\rho_{A|w}=\tilde\rho_m(w)/p(w)$ and $\rho_{Z_{m+1}|w}=\sum_{z'}\frac{p(w,z')}{p(w)}|z'\rangle\langle z'|$, and their product $\rho_{A|w}\otimes\rho_{Z_{m+1}|w}$.
--
--   This is the notation $\rho_{A|z}=\mathrm{Tr}_Z[\rho_{AZ}(\mathbb 1_A\otimes|z\rangle\langle z|)]/\mathrm{Tr}[\rho_{AZ}(\mathbb 1_A\otimes|z\rangle\langle z|)]$ of p. 5.
--
--   **Measuring $B_1\cdots B_m$.** For an operator $\rho$ on $A\otimes B_1\cdots B_{n+1}$, a family $\{M_z\}$ on $B$, $m\le n$ and outcomes $w=(z_1,\dots,z_m)$:
--
--   4. $\tilde\rho_A(w)=\mathrm{Tr}_{B_1^{n+1}}[(\mathbb 1_A\otimes M_{z_1}\otimes\cdots\otimes M_{z_m}\otimes\mathbb 1)\rho]$;
--   5. $\tilde\rho_{B_{m+1}}(w)=\mathrm{Tr}_{AB_1\cdots B_mB_{m+2}\cdots B_{n+1}}[(\mathbb 1_A\otimes M_{z_1}\otimes\cdots\otimes M_{z_m}\otimes\mathbb 1)\rho]$;
--   6. $p(w)=\mathrm{Tr}[(\mathbb 1_A\otimes M_{z_1}\otimes\cdots\otimes M_{z_m}\otimes\mathbb 1)\rho]$, and the conditional states $\rho_{A|w}=\tilde\rho_A(w)/p(w)$, $\rho_{B_{m+1}|w}=\tilde\rho_{B_{m+1}}(w)/p(w)$.
--
--   These are the states of the candidate mixture $\mathbf E_{z_1^m}\{\rho_{A|z_1^m}\otimes\rho_{B_{m+1}|z_1^m}\}$ in the proof of Theorem 2.3.
--
--   **Formalization Note** The cq-state is given by its blocks $\tilde\rho:\{1,\dots,t\}^N\to\mathbb C^{d_A\times d_A}$; the first $j$ classical systems are positions $0,\dots,j-1$, and $B_{m+1}$ is position $m$ (0-based). Partial traces and measured systems are written as explicit index sums with $\mathrm{Tr}[MX]=\sum_{c,c'}M_{cc'}X_{c'c}$. When $p(w)=0$ the conditional states are the zero matrix (division by zero); every statement either weights them by $p(w)$ or assumes $p(w)>0$.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, §2.4, pp. 5–6 (ρ_{A|z}, Lemma 2.1); proof of Theorem 2.3, pp. 7–8

import Mathlib

/-!
Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, §2.4 (pp. 5–6: conditional states
`ρ_{A|z}`, Lemma 2.1) and the proof of Theorem 2.3 (p. 8: the states conditioned on the outcomes
of measuring `B₁ ⋯ B_m`).

Classical-quantum states. A state `ρ_{A Z₁⋯Z_N} = ∑_z |z⟩⟨z| ⊗ ρ̃(z)` on `A` and `N` classical
systems with alphabet `Fin t` is given by its blocks `ρ : (Fin N → Fin t) → Matrix (Fin dA) (Fin dA) ℂ`
(`ρ z ⪰ 0`, `∑_z Tr ρ z = 1`). The first `j` classical systems take positions `0, …, j - 1`.
-/

namespace DeFinettiSDP.Hierarchy

open Matrix

/-- The unnormalized `A`-block of the marginal on `A Z₁ ⋯ Z_j` at outcome `w = z^j_1`:
`∑ ρ̃(z)` over the full outcome strings `z` whose first `j` entries are `w`. -/
def margZ {dA t N : ℕ} (ρ : (Fin N → Fin t) → Matrix (Fin dA) (Fin dA) ℂ) (j : ℕ)
    (w : Fin j → Fin t) : Matrix (Fin dA) (Fin dA) ℂ :=
  ∑ z ∈ Finset.univ.filter (fun z : Fin N → Fin t => ∀ (i : Fin N) (h : i.val < j),
      z i = w ⟨i.val, h⟩), ρ z

/-- The probability `p(z^j_1 = w) = Tr (margZ ρ j w)` of the first `j` outcomes. -/
noncomputable def pZ {dA t N : ℕ} (ρ : (Fin N → Fin t) → Matrix (Fin dA) (Fin dA) ℂ) (j : ℕ)
    (w : Fin j → Fin t) : ℝ :=
  (Matrix.trace (margZ ρ j w)).re

/-- The conditional classical-quantum state `ρ_{A Z_{m+1} | z^m_1 = w}` on `A ⊗ Z_{m+1}`
(block diagonal, `Z_{m+1}` classical): its `z'` block is `margZ ρ (m+1) (w, z') / p(w)`. -/
noncomputable def condAZ {dA t N : ℕ} (ρ : (Fin N → Fin t) → Matrix (Fin dA) (Fin dA) ℂ)
    (m : ℕ) (w : Fin m → Fin t) : Matrix (Fin dA × Fin t) (Fin dA × Fin t) ℂ :=
  Matrix.blockDiagonal fun z' =>
    ((pZ ρ m w)⁻¹ : ℂ) • margZ ρ (m + 1) (Fin.snoc (α := fun _ => Fin t) w z')

/-- The product `ρ_{A | z^m_1 = w} ⊗ ρ_{Z_{m+1} | z^m_1 = w}` of the two conditional marginals:
its `z'` block is `p(z' | w) · ρ_{A|w}` with `ρ_{A|w} = margZ ρ m w / p(w)` and
`p(z' | w) = p(w, z') / p(w)`. -/
noncomputable def prodAZ {dA t N : ℕ} (ρ : (Fin N → Fin t) → Matrix (Fin dA) (Fin dA) ℂ)
    (m : ℕ) (w : Fin m → Fin t) : Matrix (Fin dA × Fin t) (Fin dA × Fin t) ℂ :=
  Matrix.blockDiagonal fun z' =>
    ((pZ ρ (m + 1) (Fin.snoc (α := fun _ => Fin t) w z') / pZ ρ m w : ℝ) : ℂ) •
      (((pZ ρ m w)⁻¹ : ℂ) • margZ ρ m w)

/-- Position `r < m` of `B₁ ⋯ B_{n+1}`, for `m : Fin (n + 1)`. -/
def measPos {n : ℕ} (m : Fin (n + 1)) (r : Fin m) : Fin (n + 1) :=
  ⟨r.val, lt_trans r.isLt m.isLt⟩

/-- `Tr_{B₁⋯B_{n+1}}[(1_A ⊗ M_{w₁} ⊗ ⋯ ⊗ M_{w_m} ⊗ 1_{B_{m+1}⋯B_{n+1}}) ρ]`: measure the first `m`
copies of `B` (positions `0, …, m-1`) with the effects `M (w r)`, trace out all copies of `B`.
In entries, with `Tr[M X] = ∑ M_{cc'} X_{c'c}`. -/
def condAtilde {dA dB t n : ℕ}
    (ρ : Matrix (Fin dA × (Fin (n + 1) → Fin dB)) (Fin dA × (Fin (n + 1) → Fin dB)) ℂ)
    (M : Fin t → Matrix (Fin dB) (Fin dB) ℂ) (m : Fin (n + 1)) (w : Fin m → Fin t) :
    Matrix (Fin dA) (Fin dA) ℂ :=
  Matrix.of fun a a' => ∑ x : Fin (n + 1) → Fin dB, ∑ x' : Fin (n + 1) → Fin dB,
    if (∀ s : Fin (n + 1), m ≤ s → x s = x' s) then
      (∏ r : Fin m, M (w r) (x' (measPos m r)) (x (measPos m r))) * ρ (a, x) (a', x')
    else 0

/-- `Tr_{A B₁⋯B_m B_{m+2}⋯B_{n+1}}[(1_A ⊗ M_{w₁} ⊗ ⋯ ⊗ M_{w_m} ⊗ 1) ρ]`: measure the first `m`
copies of `B` with the effects `M (w r)`, keep the copy `B_{m+1}` (position `m`), trace out `A`
and every other copy. -/
def condBtilde {dA dB t n : ℕ}
    (ρ : Matrix (Fin dA × (Fin (n + 1) → Fin dB)) (Fin dA × (Fin (n + 1) → Fin dB)) ℂ)
    (M : Fin t → Matrix (Fin dB) (Fin dB) ℂ) (m : Fin (n + 1)) (w : Fin m → Fin t) :
    Matrix (Fin dB) (Fin dB) ℂ :=
  Matrix.of fun b b' => ∑ a : Fin dA, ∑ x : Fin (n + 1) → Fin dB, ∑ x' : Fin (n + 1) → Fin dB,
    if (x m = b ∧ x' m = b' ∧ ∀ s : Fin (n + 1), m < s → x s = x' s) then
      (∏ r : Fin m, M (w r) (x' (measPos m r)) (x (measPos m r))) * ρ (a, x) (a, x')
    else 0

/-- The probability `p(w) = Tr[(1_A ⊗ M_{w₁} ⊗ ⋯ ⊗ M_{w_m} ⊗ 1) ρ]` of the outcomes `w` on
`B₁ ⋯ B_m`. -/
noncomputable def pMeas {dA dB t n : ℕ}
    (ρ : Matrix (Fin dA × (Fin (n + 1) → Fin dB)) (Fin dA × (Fin (n + 1) → Fin dB)) ℂ)
    (M : Fin t → Matrix (Fin dB) (Fin dB) ℂ) (m : Fin (n + 1)) (w : Fin m → Fin t) : ℝ :=
  (Matrix.trace (condAtilde ρ M m w)).re

/-- The conditional state `ρ_{A | z^m_1 = w}` on `A`. -/
noncomputable def condA {dA dB t n : ℕ}
    (ρ : Matrix (Fin dA × (Fin (n + 1) → Fin dB)) (Fin dA × (Fin (n + 1) → Fin dB)) ℂ)
    (M : Fin t → Matrix (Fin dB) (Fin dB) ℂ) (m : Fin (n + 1)) (w : Fin m → Fin t) :
    Matrix (Fin dA) (Fin dA) ℂ :=
  ((pMeas ρ M m w)⁻¹ : ℂ) • condAtilde ρ M m w

/-- The conditional state `ρ_{B_{m+1} | z^m_1 = w}` on `B`. -/
noncomputable def condB {dA dB t n : ℕ}
    (ρ : Matrix (Fin dA × (Fin (n + 1) → Fin dB)) (Fin dA × (Fin (n + 1) → Fin dB)) ℂ)
    (M : Fin t → Matrix (Fin dB) (Fin dB) ℂ) (m : Fin (n + 1)) (w : Fin m → Fin t) :
    Matrix (Fin dB) (Fin dB) ℂ :=
  ((pMeas ρ M m w)⁻¹ : ℂ) • condBtilde ρ M m w

end DeFinettiSDP.Hierarchy


