-- Prove2me | Definitions.Def_SYKEdge_Fock
-- name    : SYKEdge_Fock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:05:48.684496+00:00
-- url     : https://prove2.me/theorems/7d730696-8634-49a3-9b53-c13b23b6f3fe
-- title:
--   The bosonic Fock space $\mathcal F$, the operators $b_i,b_i^*,N$, and the twisted bosons $a_i=K_ib_i$, $x=a+a^*$, $\varphi$, $L(R)$
-- statement:
--   Let $m\ge1$ be the number of modes. The **Fock space** $\mathcal F$ is the space of finite linear combinations of the basis vectors $f_r$, $r\in\mathbb Z_{\ge0}^m$, declared orthonormal; $\mathcal F_t=\operatorname{span}\{f_r:|r|=t\}$. The bosonic **annihilation and creation operators** are
--   $$b_if_r=\sqrt{r_i}\,f_{r-e_i},\qquad b_i^*f_r=\sqrt{r_i+1}\,f_{r+e_i},$$
--   with number operators $N_i=b_i^*b_i$, $N=\sum_iN_i$, and parity operators $(\pm1)^{N_i}f_r=(\pm1)^{r_i}f_r$.
--
--   For a hypergraph $\mathcal H=(S_1,\dots,S_m)$ write $\varepsilon_{ij}=\varepsilon_{S_i,S_j}$. The **twist operator** and the **twisted bosons** are
--   $$K_i=\prod_{j<i}\varepsilon_{ij}^{N_j},\qquad a_i=K_ib_i,\qquad a_i^*=K_ib_i^*,$$
--   and the collective operators are
--   $$a=\frac1{\sqrt m}\sum_ia_i,\qquad a^*=\frac1{\sqrt m}\sum_ia_i^*,\qquad x=a+a^*,\qquad x_{S_i}=a_i+a_i^*.$$
--   The **vacuum functional** is $\varphi(T)=\langle f_0,Tf_0\rangle$. For a matrix $R\in\mathbb C^{\mathcal H\times\mathcal H}$, $L(R)=\sum_{i,j}R_{ij}a_i^*a_j$. For operators $L,L'$ on $\mathcal F$, $L\preceq L'$ means $\langle\psi,L\psi\rangle\le\langle\psi,L'\psi\rangle$ for every $\psi\in\mathcal F$.
--
--   The twisted boson $x$ is the paper's deterministic surrogate for the SYK Hamiltonian: its vacuum moments equal the expected trace moments of $H$ (Proposition 4.7).
--
--   **Formalization Note** $\mathcal F$ is the space of finitely supported functions on $\mathbb Z^m_{\ge0}$ (footnote 15), so all operators are everywhere-defined linear maps. $K_i$ acts diagonally by the phase $\prod_{j<i}\varepsilon_{ij}^{r_j}$. $a_i^*$ is defined as $K_ib_i^*$, which is the adjoint of $a_i$. The order $\preceq$ compares real parts of expectation values.
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Definition 4.1, p.20 (footnote 15); Table 1 and Definition 4.3, pp.21–22; L(R) and ≼, p.22; φ, a, x, x_S, p.23

import Mathlib
import Definitions.Def_SYKEdge_Majorana

namespace SYKEdge

/-!
# The bosonic Fock space and the twisted bosonic operators

A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, §4: the Fock space and Definition 4.1, p.20 (footnote 15); Table 1, p.21;
Definition 4.3, pp.21–22; `L(R)` and the order `≼`, p.22; the vacuum functional `φ`, `a`, `x`,
`x_S`, p.23.

**Formalization Note.**
* Modes are `Fin m` (the page's `Λ`, and for the twisted operators the hyperedge indices of
  `H = (S₁, …, S_m)` in the page's "arbitrary ordering", p.21).
* `Fock m = (Fin m → ℕ) →₀ ℂ` is the span of the occupation basis `f_r`, `r ∈ ℤ^m_{⩾0}`, with
  finitely many nonzero coefficients (footnote 15, p.20). `fbasis r = f_r`.
* `fockInner ψ ψ' = Σ_r conj(ψ_r) ψ'_r` declares `{f_r}` orthonormal (p.20), conjugate-linear in the
  first slot; `normF ψ = ⟨ψ, ψ⟩^{1/2}`.
* `fockLevel m t = F_t = span{f_r : |r| = t}`.
* `bop i f_r = √r_i f_{r−e_i}` (zero when `r_i = 0`, since then the coefficient `√0` vanishes and the
  truncated decrement is irrelevant); `bdag i f_r = √(r_i+1) f_{r+e_i}` (Definition 4.1).
* `numOp i = N_i = b_i* b_i`, `numTot = N = Σ_i N_i`; `signPow s i = s^{N_i}`, `s^{N_i} f_r = s^{r_i} f_r`.
* `Kop S i = K_i = Π_{j<i} ε_{ij}^{N_j}` (Definition 4.3) acts diagonally:
  `K_i f_r = (Π_{j<i} ε_{ij}^{r_j}) f_r` with `ε_{ij} = ε_{S_i,S_j}` (`twistPhase`); the factors are
  commuting diagonal operators, so this is their product.
* `aop S i = a_i = K_i b_i`, `adag S i = a_i* := K_i b_i*` (Definition 4.3; the latter is a definition,
  and it is the adjoint of `a_i` for `fockInner`).
* `aTot S = a = |H|^{−1/2} Σ_i a_i`, `adagTot S = a* = |H|^{−1/2} Σ_i a_i*`, `xop S = x = a + a*`,
  `xS S i = x_{S_i} = a_i + a_i*` (p.23).
* `fockPhi T = φ(T) = ⟨f₀, T f₀⟩` (p.23).
* `Lmap S R = L(R) = Σ_{i,j} R_{ij} a_i* a_j` (p.22).
* `fockLE L L'` is the page's `L ≼ L'`: `⟨ψ, Lψ⟩ ⩽ ⟨ψ, L'ψ⟩` for every `ψ ∈ ⊕_{ℓ⩽t} F_ℓ` and every
  `t`, i.e. for every `ψ ∈ F` (each element of `F` lies in some `⊕_{ℓ⩽t}F_ℓ`). The page uses it for
  Hermitian operators, whose expectation values are real; the real parts are compared.
-/

/-- The bosonic Fock space `F = span{f_r : r ∈ ℤ^m_{⩾0}}` (finite linear combinations). -/
abbrev Fock (m : ℕ) := (Fin m → ℕ) →₀ ℂ

/-- The occupation basis vector `f_r`, `f_r(r') = 1(r = r')`. -/
noncomputable def fbasis {m : ℕ} (r : Fin m → ℕ) : Fock m := Finsupp.single r 1

/-- The inner product of `F` for which `{f_r}` is orthonormal: `⟨ψ, ψ'⟩ = Σ_r conj(ψ_r) ψ'_r`. -/
noncomputable def fockInner {m : ℕ} (ψ ψ' : Fock m) : ℂ :=
  ψ.sum fun r c => star c * ψ' r

/-- The norm `‖ψ‖ = ⟨ψ, ψ⟩^{1/2}` on `F`. -/
noncomputable def normF {m : ℕ} (ψ : Fock m) : ℝ :=
  Real.sqrt (fockInner ψ ψ).re

/-- The level-`t` subspace `F_t := span{f_r : |r| = t}`. -/
noncomputable def fockLevel (m t : ℕ) : Submodule ℂ (Fock m) :=
  Submodule.span ℂ (fbasis '' {r : Fin m → ℕ | ∑ i, r i = t})

/-- The annihilation operator `b_i f_r := √r_i f_{r−e_i}` (Definition 4.1). -/
noncomputable def bop {m : ℕ} (i : Fin m) : Fock m →ₗ[ℂ] Fock m :=
  Finsupp.linearCombination ℂ fun r =>
    ((Real.sqrt (r i : ℝ) : ℝ) : ℂ) • fbasis (Function.update r i (r i - 1))

/-- The creation operator `b_i* f_r := √(r_i+1) f_{r+e_i}` (Definition 4.1). -/
noncomputable def bdag {m : ℕ} (i : Fin m) : Fock m →ₗ[ℂ] Fock m :=
  Finsupp.linearCombination ℂ fun r =>
    ((Real.sqrt ((r i : ℝ) + 1) : ℝ) : ℂ) • fbasis (Function.update r i (r i + 1))

/-- The number operator of mode `i`, `N_i := b_i* b_i`. -/
noncomputable def numOp {m : ℕ} (i : Fin m) : Fock m →ₗ[ℂ] Fock m :=
  bdag i ∘ₗ bop i

/-- The total number operator `N := Σ_i N_i`. -/
noncomputable def numTot (m : ℕ) : Fock m →ₗ[ℂ] Fock m :=
  ∑ i, numOp i

/-- The operator `s^{N_i}`, `s^{N_i} f_r := s^{r_i} f_r` (for `s = ±1`, the page's `(±1)^{N_i}`). -/
noncomputable def signPow {m : ℕ} (s : ℂ) (i : Fin m) : Fock m →ₗ[ℂ] Fock m :=
  Finsupp.linearCombination ℂ fun r => s ^ (r i) • fbasis r

/-- The twist phase `Π_{j<i} ε_{ij}^{r_j}` of mode `i` at occupation `r`. -/
noncomputable def twistPhase {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m)
    (r : Fin m → ℕ) : ℂ :=
  ∏ j ∈ Finset.univ.filter (· < i), (((eps (S i) (S j) : ℤ) : ℂ)) ^ (r j)

/-- The twist operator `K_i := Π_{j<i} ε_{ij}^{N_j}` (Definition 4.3), acting diagonally. -/
noncomputable def Kop {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m) :
    Fock m →ₗ[ℂ] Fock m :=
  Finsupp.linearCombination ℂ fun r => twistPhase S i r • fbasis r

/-- The twisted annihilation operator `a_i := K_i b_i` (Definition 4.3). -/
noncomputable def aop {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m) :
    Fock m →ₗ[ℂ] Fock m :=
  Kop S i ∘ₗ bop i

/-- The twisted creation operator `a_i* := K_i b_i*` (Definition 4.3). -/
noncomputable def adag {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m) :
    Fock m →ₗ[ℂ] Fock m :=
  Kop S i ∘ₗ bdag i

/-- The collective annihilation operator `a := |H|^{−1/2} Σ_{S∈H} a_S` (p.23). -/
noncomputable def aTot {n m : ℕ} (S : Fin m → Finset (Fin n)) : Fock m →ₗ[ℂ] Fock m :=
  (((1 / Real.sqrt m : ℝ)) : ℂ) • ∑ i, aop S i

/-- The collective creation operator `a* = |H|^{−1/2} Σ_{S∈H} a_S*` (p.23). -/
noncomputable def adagTot {n m : ℕ} (S : Fin m → Finset (Fin n)) : Fock m →ₗ[ℂ] Fock m :=
  (((1 / Real.sqrt m : ℝ)) : ℂ) • ∑ i, adag S i

/-- The twisted boson position operator `x := a + a*` (p.23). -/
noncomputable def xop {n m : ℕ} (S : Fin m → Finset (Fin n)) : Fock m →ₗ[ℂ] Fock m :=
  aTot S + adagTot S

/-- The single-mode operator `x_{S_i} := a_{S_i} + a_{S_i}*` (p.23). -/
noncomputable def xS {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m) :
    Fock m →ₗ[ℂ] Fock m :=
  aop S i + adag S i

/-- The vacuum functional `φ(T) := ⟨f₀, T f₀⟩` (p.23). -/
noncomputable def fockPhi {m : ℕ} (T : Fock m →ₗ[ℂ] Fock m) : ℂ :=
  fockInner (fbasis 0) (T (fbasis 0))

/-- `L(R) := Σ_{S,T∈H} R_{S,T} a_S* a_T` (p.22). -/
noncomputable def Lmap {n m : ℕ} (S : Fin m → Finset (Fin n)) (R : Matrix (Fin m) (Fin m) ℂ) :
    Fock m →ₗ[ℂ] Fock m :=
  ∑ i, ∑ j, R i j • (adag S i ∘ₗ aop S j)

/-- The order `L ≼ L'` on operators of `F` (p.22): `⟨ψ, Lψ⟩ ⩽ ⟨ψ, L'ψ⟩` for every `ψ ∈ F`. -/
def fockLE {m : ℕ} (L L' : Fock m →ₗ[ℂ] Fock m) : Prop :=
  ∀ ψ : Fock m, (fockInner ψ (L ψ)).re ≤ (fockInner ψ (L' ψ)).re

end SYKEdge


