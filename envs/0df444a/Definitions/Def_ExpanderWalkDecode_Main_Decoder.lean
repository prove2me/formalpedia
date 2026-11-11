-- Prove2me | Definitions.Def_ExpanderWalkDecode_Main_Decoder
-- name    : ExpanderWalkDecode_Main_Decoder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:49.321674+00:00
-- url     : https://prove2.me/theorems/0158b90f-528c-4230-9149-965cc30cc9fb
-- title:
--   The objects of Section 4: padded and amplified words, $\mathrm{LIST}$, the potential $J$, good vectors and the operators of Figure 3
-- statement:
--   Let $\iota:[n]\hookrightarrow A$ be an injection and $C_{\mathrm{base}}\subseteq\mathbb F_2^n$ a binary linear code. A base word $X$ is **padded** to $A$ by $X_a=(-1)^{X_i}$ if $a=\iota(i)$ and $X_a=+1$ otherwise; its **amplified codeword** at a walk $\vec a=(a_0,\dots,a_t)$ is $X_{\vec a}=X_{a_0}\cdots X_{a_t}$. Received words $Y\in\{\pm1\}$ live on the code coordinates, the latent points of the walks with $t$ edges, and
--   $$\mathrm{LIST}(Y,\rho)=\{X\in C_{\mathrm{base}} : \mathbb E_{\vec a\sim\mathrm{WRW}^t_s}[Y_{\vec a}X_{\vec a}]\ge\rho\}.$$
--
--   Vectors $x_{\vec a}$ and Gram matrices $P_{\vec a,\vec a'}=\langle x_{\vec a},x_{\vec a'}\rangle$ are indexed by $\mathrm{WRW}^{\le t}_s$; $\vec a_{\mathrm{tail}}$ drops the first vertex. $\mathcal E$ is the set of positive semidefinite matrices with diagonal entries at most $1$. Definition 3:
--   $$F(P)=\mathbb E_{\vec a\sim\mathrm{WRW}^t_s}\big(\langle x_{\vec a},x_\emptyset\rangle-2\rho Y_{\vec a}\big)^2,\qquad G(P)=\mathbb E_{a\sim A}\,\mathbb E_{\vec a,\vec a'\sim\mathrm{WRW}^{\le t}_s(a)}\big\langle x_{\vec a}-x_{\vec a_{\mathrm{tail}}},\,x_{\vec a'}+x_{\vec a'_{\mathrm{tail}}}\big\rangle^2,$$
--   $J=F+\alpha G$, and $\Gamma(P,Q)=\nabla J(P)\bullet(Q-P)$, the derivative of $\gamma\mapsto J(P+\gamma(Q-P))$ at $0$.
--
--   **Good vectors** (Definition 2): $\|x_{\vec a}\|\le1$ for all $\vec a$, $G(P)\le 10/\alpha$, and $\mathbb E_{\vec a\sim\mathrm{WRW}^t_s}[Z_{\vec a}\langle x_{\vec a},x_\emptyset\rangle]\ge\rho^2/2$ for every $Z\in\mathrm{LIST}(Y,\rho)$.
--
--   **Figure 3**: with $\theta=\rho^4/(32(t+1)^2)$ and $A_a=C_aC_a^{\mathsf T}$, where the columns of $C_a$ are $x_{\vec a}+x_{\vec a_{\mathrm{tail}}}$ for $\vec a\in\mathrm{WRW}^{\le t}_s(a)$, let $\Pi_a$ be the orthogonal projection onto the span of the eigenvectors of $A_a$ with eigenvalue at least $\theta$, and $T_a=2\Pi_a-I$.
--
--   **Good parity operators** (Definition 4): $T_a$ symmetric with $T_a^2=I$, $\operatorname{rank}((I+T_a)/2)\le R$, and $\|\mathbb E_{\vec a\sim\mathrm{WRW}^t_s}[(Z_{a_0}T_{a_0})\cdots(Z_{a_t}T_{a_t})]\|_{\mathrm{op}}\ge\rho^2/4$ for every $Z\in\mathrm{LIST}(Y,\rho)$.
--
--   The parameters of §4.1 are $\alpha=10240R^2(t+1)^3/\rho^8$, $M=\lceil144(4+64\alpha)/\rho^4\rceil$, $\gamma=\rho^2/(4(4+64\alpha))$ and the Gram dimension $\Delta=\lceil C(12+64\alpha)^2\rho^{-4}\log(2+NR)\rceil$ of the gradient step, $C$ the absolute constant of that step.
--
--   **Formalization Note** $\mathrm{LIST}(Y,\rho)$ is recorded by base codewords, each standing for its amplified codeword. The near-consistency average draws $\vec a,\vec a'$ uniformly from the set $\mathrm{WRW}^{\le t}_s(a)$. $\Delta$ uses the regularized logarithm $\log(2+NR)$, with $NR$ the bound on $|\mathrm{WRW}^{\le t}_s|$ used in Appendix C.1.
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), pp. 11–17 (§4, Definitions 2–4, Figures 2–3), p. 28 (Appendix C.1)

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Codes
import Definitions.Def_ExpanderWalkDecode_Main_WideWalk

namespace ExpanderWalkDecode.Main

open scoped Classical Matrix

/-!
# The objects of Section 4: the amplified code, `LIST(Y, ρ)`, the convex potential, good vectors,
# the parity operators of Figure 3 and good parity operators

Source: §4 (pp. 11–17), Definitions 2–4, Figures 2–3, Claims 8–11.

A base word `X ∈ F₂^n` is padded to `A` through an injection `ι : [n] ↪ A`, with sign `+1` off the
image, and its amplified codeword at the walk `⃗a = (a₀, …, a_t)` is `X_{a₀} ⋯ X_{a_t}`. Received
words `Y` live on the code coordinates, the latent points of the walks with `t` edges (§ WideWalk),
and correlation is the latent average. `LIST(Y, ρ)` is recorded as the set of base codewords whose
amplified codewords correlate at least `ρ` with `Y`.

Vectors `x_⃗a` and Gram matrices `P` are indexed by `WRW^{≤t}_s` (`WIdx`); `x_∅` is the vector of
the empty walk and `⃗a_tail` drops the first vertex. The near-consistency term averages over pairs
`(⃗a, ⃗a′)` drawn uniformly from the set `WRW^{≤t}_s(a)` for a uniform `a ∈ A`.
-/

section Setup

variable {A : Type} [Fintype A] {m s q : ℕ}

/-- The padded sign word: `X_a = (-1)^{x_i}` if `a = ι(i)`, and `+1` off the image of `ι`. -/
noncomputable def pad {n : ℕ} (ι : Fin n ↪ A) (x : Word n) : A → ℝ :=
  fun a => if h : ∃ i, ι i = a then sgn (x h.choose) else 1

/-- The product `Z_{⃗a} = Z_{a₀} ⋯ Z_{a_k}` along a walk. -/
def ampProd (Z : A → ℝ) {k : ℕ} (w : Fin (k + 1) → A) : ℝ := ∏ i, Z (w i)

/-- `LIST(Y, ρ)` (§4): the base codewords `x ∈ C_base` whose amplified codeword has correlation at
least `ρ` with the received word `Y` (a function on the code coordinates). -/
noncomputable def listSet (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (t : ℕ)
    {n : ℕ} (ι : Fin n ↪ A) (Cb : BinaryLinearCode n) (Y : Latent A m s q t → ℝ) (ρ : ℝ) :
    Finset (Word n) :=
  Finset.univ.filter fun x => x ∈ Cb ∧
    ρ ≤ avg fun l : Latent A m s q t => Y l * ampProd (pad ι x) (walk G u l)

/-- The index set `WRW^{≤t}_s` of the vectors and of the Gram matrices. -/
abbrev WIdx (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (t : ℕ) :=
  {w : List A // w ∈ wrwLe G u t}

variable (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (t : ℕ)

/-- The empty walk `∅`. -/
noncomputable def emptyW : WIdx G u t := ⟨[], nil_mem_wrwLe G u t⟩

/-- The code coordinate `l` as an element of `WRW^{≤t}_s`. -/
noncomputable def walkW (l : Latent A m s q t) : WIdx G u t :=
  ⟨walkList G u l, walkList_mem_wrwLe G u t l⟩

/-- `⃗a_tail`: the walk without its first vertex. -/
noncomputable def tailW (w : WIdx G u t) : WIdx G u t := ⟨w.1.tail, tail_mem_wrwLe G u t w.2⟩

/-- `WRW^{≤t}_s(a)` inside the index set. -/
noncomputable def fromW (a : A) : Finset (WIdx G u t) :=
  Finset.univ.filter fun w => w.1.head? = some a

/-- `⟨x_⃗a - x_{⃗a_tail}, x_{⃗a′} + x_{⃗a′_tail}⟩` in terms of the Gram matrix `P`. -/
noncomputable def consLin (P : Matrix (WIdx G u t) (WIdx G u t) ℝ) (w w' : WIdx G u t) : ℝ :=
  P w w' + P w (tailW G u t w') - P (tailW G u t w) w' - P (tailW G u t w) (tailW G u t w')

/-- `F(P) = E_{⃗a ∼ WRW^t_s} (⟨x_⃗a, x_∅⟩ - 2ρ Y_⃗a)²` (Definition 3). -/
noncomputable def Fpot (Y : Latent A m s q t → ℝ) (ρ : ℝ) (P : Matrix (WIdx G u t) (WIdx G u t) ℝ) :
    ℝ :=
  avg fun l : Latent A m s q t => (P (walkW G u t l) (emptyW G u t) - 2 * ρ * Y l) ^ 2

/-- `G(P) = E_{a ∼ A} E_{⃗a, ⃗a′ ∼ WRW^{≤t}_s(a)} ⟨x_⃗a - x_{⃗a_tail}, x_{⃗a′} + x_{⃗a′_tail}⟩²`
(Definition 3). -/
noncomputable def Gpot (P : Matrix (WIdx G u t) (WIdx G u t) ℝ) : ℝ :=
  avg fun a : A => favg (fromW G u t a ×ˢ fromW G u t a) fun ww => (consLin G u t P ww.1 ww.2) ^ 2

/-- The convex potential `J = F + α G` (Definition 3). -/
noncomputable def Jpot (α : ℝ) (Y : Latent A m s q t → ℝ) (ρ : ℝ)
    (P : Matrix (WIdx G u t) (WIdx G u t) ℝ) : ℝ :=
  Fpot G u t Y ρ P + α * Gpot G u t P

/-- `Γ(P, Q) = ∇J(P) • (Q - P)`, the directional derivative of `J` at `P` towards `Q`. -/
noncomputable def Gamma (α : ℝ) (Y : Latent A m s q t → ℝ) (ρ : ℝ)
    (P Q : Matrix (WIdx G u t) (WIdx G u t) ℝ) : ℝ :=
  deriv (fun γ : ℝ => Jpot G u t α Y ρ (P + γ • (Q - P))) 0

/-- The set `E` of positive semidefinite matrices with every diagonal entry at most `1`. -/
def Ell : Set (Matrix (WIdx G u t) (WIdx G u t) ℝ) :=
  {P | P.PosSemidef ∧ ∀ w, P w w ≤ 1}

/-- The Gram matrix `P_{⃗a,⃗a′} = ⟨x_⃗a, x_{⃗a′}⟩` of a vector family. -/
def gram {d : ℕ} (x : WIdx G u t → Fin d → ℝ) : Matrix (WIdx G u t) (WIdx G u t) ℝ :=
  fun w w' => x w ⬝ᵥ x w'

/-- Good output vectors (Definition 2): `‖x_⃗a‖ ≤ 1`, near consistency `G ≤ 10/α`, and level-`t`
agreement `E_{⃗a ∼ WRW^t_s} [Z_⃗a ⟨x_⃗a, x_∅⟩] ≥ ρ²/2` for every `Z ∈ LIST(Y, ρ)`. -/
def GoodVectors {n : ℕ} (ι : Fin n ↪ A) (Cb : BinaryLinearCode n) (Y : Latent A m s q t → ℝ)
    (ρ α : ℝ) {d : ℕ} (x : WIdx G u t → Fin d → ℝ) : Prop :=
  (∀ w, x w ⬝ᵥ x w ≤ 1) ∧ Gpot G u t (gram G u t x) ≤ 10 / α ∧
    ∀ z ∈ listSet G u t ι Cb Y ρ,
      ρ ^ 2 / 2 ≤ avg fun l : Latent A m s q t =>
        ampProd (pad ι z) (walk G u l) * (x (walkW G u t l) ⬝ᵥ x (emptyW G u t))

/-- `A_a = C_a C_aᵀ`, where the columns of `C_a` are `x_⃗a + x_{⃗a_tail}`, `⃗a ∈ WRW^{≤t}_s(a)`
(Figure 3). -/
noncomputable def Amat {d : ℕ} (x : WIdx G u t → Fin d → ℝ) (a : A) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ w ∈ fromW G u t a, Matrix.vecMulVec (x w + x (tailW G u t w)) (x w + x (tailW G u t w))

/-- Good parity operators (Definition 4): `T_a` symmetric with `T_a² = I`,
`rank((I + T_a)/2) ≤ R`, and level-`t` agreement
`‖E_{⃗a ∼ WRW^t_s} [(Z_{a₀} T_{a₀}) ⋯ (Z_{a_t} T_{a_t})]‖_op ≥ ρ²/4` for every `Z ∈ LIST(Y, ρ)`. -/
def GoodParityOps {n : ℕ} (ι : Fin n ↪ A) (Cb : BinaryLinearCode n) (Y : Latent A m s q t → ℝ)
    (ρ : ℝ) (R : ℕ) {d : ℕ} (T : A → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ a, (T a)ᵀ = T a ∧ T a * T a = 1 ∧ ((1 / 2 : ℝ) • (1 + T a)).rank ≤ R) ∧
    ∀ z ∈ listSet G u t ι Cb Y ρ,
      ρ ^ 2 / 4 ≤ opNorm (wrwAvg G u t fun w => (List.ofFn fun i => pad ι z (w i) • T (w i)).prod)

end Setup

/-- The orthogonal projection onto the span of the eigenvectors of a symmetric matrix whose
eigenvalue is at least `θ` (`0` for a non-symmetric matrix). -/
noncomputable def specProj {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (θ : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  if h : M.IsHermitian then
    ∑ k : Fin d, if θ ≤ h.eigenvalues k then
      Matrix.vecMulVec (fun i => h.eigenvectorBasis k i) (fun i => h.eigenvectorBasis k i) else 0
  else 0

/-- The parameter `θ = ρ⁴ / (32 (t+1)²)` of §4.2. -/
noncomputable def thetaOp (ρ : ℝ) (t : ℕ) : ℝ := ρ ^ 4 / (32 * ((t : ℝ) + 1) ^ 2)

/-- The operators of Figure 3: `T_a = 2 Π_a - I`, where `Π_a` projects onto the eigenvectors of
`A_a` with eigenvalue at least `θ = ρ⁴/(32(t+1)²)`. -/
noncomputable def figure3T {A : Type} [Fintype A] {m s q t : ℕ} (G : RotGraph A (Fin m → ZMod 2))
    (u : Fin q → Inner m s) {d : ℕ} (x : WIdx G u t → Fin d → ℝ) (ρ : ℝ) (a : A) :
    Matrix (Fin d) (Fin d) ℝ :=
  (2 : ℝ) • specProj (Amat G u t x a) (thetaOp ρ t) - 1

/-- `α = 10240 R² (t+1)³ / ρ⁸` (§4.1). -/
noncomputable def alphaP (R t : ℕ) (ρ : ℝ) : ℝ := 10240 * (R : ℝ) ^ 2 * ((t : ℝ) + 1) ^ 3 / ρ ^ 8

/-- `M = ⌈144 (4 + 64α) / ρ⁴⌉` (§4.1). -/
noncomputable def Mparam (α ρ : ℝ) : ℕ := ⌈144 * (4 + 64 * α) / ρ ^ 4⌉₊

/-- The step size `γ = ρ² / (4 (4 + 64α))` (Claim 8). -/
noncomputable def gammaStep (α ρ : ℝ) : ℝ := ρ ^ 2 / (4 * (4 + 64 * α))

/-- The Gram dimension `Δ = ⌈C (12 + 64α)² ρ⁻⁴ log(2 + N R)⌉` of the gradient step, for the
absolute constant `C` of the step routine (§4.1, Claim 7 and its proof). -/
noncomputable def deltaDim (C α ρ : ℝ) (N R : ℕ) : ℕ :=
  ⌈C * (12 + 64 * α) ^ 2 / ρ ^ 4 * Real.log (2 + (N : ℝ) * R)⌉₊

end ExpanderWalkDecode.Main


