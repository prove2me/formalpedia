-- Prove2me | Definitions.Def_SmallBiasPRF_KB
-- name    : SmallBiasPRF_KB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:14.196431+00:00
-- url     : https://prove2.me/theorems/27f38eff-8e32-477d-9c68-a2794705e85c
-- title:
--   Update vectors, the state space $W$, vectorized states, active sets and the operators $Q_x$, $Q$, $D_B$, $K_{B,x}$, $K_B$
-- statement:
--   Fix a linear code $H:\mathbb F_2^n\to\mathbb F_2^{m_1}$, a finite set $A\subseteq\{0,1\}^n$ and $\Omega=[m_1]$.
--
--   1. For $x\in\Omega$ the **update vector** is $\tilde U_x:A\to\mathbb F_2$, $\tilde U_x(a)=H(a)_x$, viewed in $\mathbb F_3^A$.
--   2. The **reachable state space** is $W=\operatorname{span}_{\mathbb F_3}\{\tilde U_x:x\in\Omega\}\subseteq\mathbb F_3^A$.
--   3. For a selector $\pi$ and weights $w$, the **vectorized states** are $\tilde S_0=0$ and $\tilde S_j=\tilde S_{j-1}+w_j\tilde U_{\pi(j)}$.
--   4. For a family $\{S_a\}_{a\in A}$ of subsets of $[m_2]$, the **active set** of coordinate $j$ is $A_j=\{a\in A:j\in S_a\}$.
--   5. On real functions $f:W\to\mathbb R$:
--
--   $$(Q_xf)(S)=\mathop{\mathbb E}_{\rho\in\mathbb F_3}[f(S+\rho\tilde U_x)],\qquad Q=\mathop{\mathbb E}_{x\in\Omega}[Q_x],\qquad (D_Bf)(S)=\Lambda_B(S|_B)^2f(S),$$
--
--   with $D_\emptyset=I$, and the **weighted update operators** are $K_{B,x}=Q_xD_B$ and $K_B=QD_B=\mathbb E_{x\in\Omega}[K_{B,x}]$ for $B\subseteq A$.
--
--   These operators turn the bias of the construction into the norm of a product of operators (Lemma 13), whose factors contract on active coordinates (Lemma 16).
--
--   **Formalization Note** States are functions on the subtype of $A$. Operators on $L^2(W)$ are real matrices indexed by $W$, acting by $(Mf)(S)=\sum_{S'}M[S,S']f(S')$, so composition is the matrix product; $Q_x[S,S']=\tfrac13\#\{\rho:S+\rho\tilde U_x=S'\}$ and $D_B$ is diagonal. The paper's normalized inner product differs from the Euclidean one by the factor $|W|$, so adjoints and operator norms coincide. Indices are 0-based.
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §5.1, displays (5)–(6), pp.18–19 (PDF 21–22); §5.3, displays (9)–(10), p.20 (PDF 23)

import Mathlib
import Definitions.Def_SmallBiasPRF_basicF
import Definitions.Def_SmallBiasPRF_Lambda

namespace SmallBiasPRF

variable {n m₁ : ℕ}

/-- The **update vector** `Ũ_x : A → 𝔽₂`, `Ũ_x(a) = H(a)_x`, of the code coordinate `x ∈ Ω = [m₁]`,
viewed in `𝔽₃^A` (§5.1, p.18 (PDF p.21)).
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §5.1, p.18.

**Formalization Note.** `A` is a `Finset` of inputs and states are functions on the subtype `↥A`;
the bit `H(a)_x` is lifted to `𝔽₃` by value (`lift3`). -/
def updVec (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2)) (A : Finset (Fin n → ZMod 2))
    (x : Fin m₁) : A → ZMod 3 :=
  fun a => lift3 (H a.1 x)

/-- The **reachable state space** `W = span_{𝔽₃}{Ũ_x : x ∈ Ω} ⊆ 𝔽₃^A`, display (6), p.19 (PDF p.22).
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), (6), p.19. -/
def stateSpace (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2)) (A : Finset (Fin n → ZMod 2)) :
    Submodule (ZMod 3) (A → ZMod 3) :=
  Submodule.span (ZMod 3) (Set.range (updVec H A))

noncomputable instance (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2))
    (A : Finset (Fin n → ZMod 2)) : Fintype (stateSpace H A) :=
  Fintype.ofFinite _

noncomputable instance (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2))
    (A : Finset (Fin n → ZMod 2)) : DecidableEq (stateSpace H A) :=
  Classical.decEq _

/-- The **vectorized states** of display (5), p.18 (PDF p.21): `S̃₀ = 0` and
`S̃_j = S̃_{j−1} + w_j Ũ_{π(j)}` over `𝔽₃^A`, i.e. `S̃_j = ∑_{i ≤ j} w_i Ũ_{π(i)}`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), (5), p.18.

**Formalization Note.** 0-based: `stateVec H A π w j` is the paper's `S̃_{j+1}`. -/
def stateVec (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2)) (A : Finset (Fin n → ZMod 2))
    {m₂ : ℕ} (π : Fin m₂ → Fin m₁) (w : Fin m₂ → ZMod 3) (j : Fin m₂) : A → ZMod 3 :=
  ∑ i ∈ Finset.Iic j, w i • updVec H A (π i)

/-- The **active input set** `A_j = {a ∈ A : j ∈ S_a}` of coordinate `j ∈ [m₂]` (§5.1, p.19
(PDF p.22)); `A_j = ∅` is possible.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §5.1, p.19.

**Formalization Note.** The family `{S_a}_{a∈A}` is a function `Sfam : 𝔽₂ⁿ → Finset (Fin m₂)`
read on `A`. -/
def activeSet (A : Finset (Fin n → ZMod 2)) {m₂ : ℕ} (Sfam : (Fin n → ZMod 2) → Finset (Fin m₂))
    (j : Fin m₂) : Finset A :=
  Finset.univ.filter fun a => j ∈ Sfam a.1

/-- The **state update operator** `(Q_x f)(S) = E_{ρ∈𝔽₃}[f(S + ρŨ_x)]` on functions `f : W → ℝ`,
display (9), p.20 (PDF p.23), as a matrix indexed by `W`:
`Q_x[S, S′] = (1/3)·#{ρ ∈ 𝔽₃ : S + ρŨ_x = S′}`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), (9), p.20.

**Formalization Note.** Operators on the real function space of `W` are represented by real
matrices indexed by `↥W`, acting by `(Mf)(S) = ∑_{S′} M[S, S′] f(S′)`; composition of operators is
matrix multiplication. The paper's normalized inner product `E_{S∈W}[f g]` is a constant multiple of
the Euclidean one, so adjoints and operator norms are the same. -/
noncomputable def Qx (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2))
    (A : Finset (Fin n → ZMod 2)) (x : Fin m₁) : Matrix (stateSpace H A) (stateSpace H A) ℝ :=
  fun S S' => (1 / 3 : ℝ) *
    ((Finset.univ.filter fun ρ : ZMod 3 => (S : A → ZMod 3) + ρ • updVec H A x = S').card : ℝ)

/-- The **uniform update operator** `Q = E_{x∈Ω}[Q_x] = (1/|Ω|) ∑_{x∈Ω} Q_x` (p.20 (PDF p.23)). -/
noncomputable def Qavg (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2))
    (A : Finset (Fin n → ZMod 2)) : Matrix (stateSpace H A) (stateSpace H A) ℝ :=
  (Fintype.card (Fin m₁) : ℝ)⁻¹ • ∑ x, Qx H A x

/-- The multiplication operator `(D_B f)(S) = Λ_B(S|_B)² f(S)` for `B ⊆ A` (p.20 (PDF p.23)), with
`D_∅ = I`.

**Formalization Note.** A diagonal matrix; `D_∅ = I` holds because `Λ_∅ = 1`. -/
noncomputable def DB (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2))
    (A : Finset (Fin n → ZMod 2)) (B : Finset A) : Matrix (stateSpace H A) (stateSpace H A) ℝ :=
  Matrix.diagonal fun S => Lambda B (S : A → ZMod 3) ^ 2

/-- The **weighted update operator** `K_{B,x} = Q_x D_B`, display (10), p.20 (PDF p.23).
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), (10), p.20. -/
noncomputable def KBx (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2))
    (A : Finset (Fin n → ZMod 2)) (B : Finset A) (x : Fin m₁) :
    Matrix (stateSpace H A) (stateSpace H A) ℝ :=
  Qx H A x * DB H A B

/-- The **weighted update operator** `K_B = Q D_B = E_{x∈Ω}[K_{B,x}]`, display (10), p.20
(PDF p.23); `K_∅ = Q`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), (10), p.20. -/
noncomputable def KB (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2))
    (A : Finset (Fin n → ZMod 2)) (B : Finset A) : Matrix (stateSpace H A) (stateSpace H A) ℝ :=
  Qavg H A * DB H A B

end SmallBiasPRF


