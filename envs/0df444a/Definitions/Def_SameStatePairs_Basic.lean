-- Prove2me | Definitions.Def_SameStatePairs_Basic
-- name    : SameStatePairs_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T21:01:28.706978+00:00
-- url     : https://prove2.me/theorems/6eded158-99da-4e75-9158-c2dd1725d3ab
-- title:
--   Same-state pairs: hard-whitening objective, world kernel, scene-explained fraction, same-state operator and Procrustes objects
-- statement:
--   Objects of Sections 2–4 and Appendix A of Li (2026), arXiv:2611.16182.
--
--   1. **Encoders, centring, whitening.** On a finite set $\alpha$ carrying a law $w$, an encoder is $h:\alpha\to\mathbb{R}^k$, with $\|v\|^2=\sum_i v_i^2$. It is centred if $\sum_a w(a)h(a)=0$ and whitened if $\sum_a w(a)h(a)h(a)^\top=I_k$. An orthogonal $Q\in O(k)$ acts by $v\mapsto Qv$.
--   2. **Hard-whitening objective (Section 2.1).** For a law $\pi$ of positive pairs on $\alpha$, the prediction term is $L_\pi(h)=\sum_{a,a'}\pi(a,a')\|h(a)-h(a')\|^2$. The hard anti-collapse term is $\Omega(h)=0$ if $h$ is centred and whitened and $\Omega(h)=+\infty$ otherwise. A global minimiser is a centred, whitened $h$ with $L_\pi(h)\le L_\pi(h')$ for every centred, whitened $h'$. The span of $h$ is the span of its coordinate functions $h_1,\dots,h_k:\alpha\to\mathbb{R}$. The centred function space is $\{\varphi:\sum_a w(a)\varphi(a)=0\}$.
--   3. **World (Section 2.1).** $Z$ is a finite world with $p(z)>0$, $\sum_zp(z)=1$, $d_z=|Z|$. The same-state law is $\pi=\operatorname{diag}(p)$: $\pi(z,z)=p(z)$ and $\pi(z,z')=0$ for $z\ne z'$. The world kernel is $K_\pi=D^{-1/2}\Pi D^{-1/2}$ and the Markov operator is $T_\pi=D^{-1}\Pi$, with $D=\operatorname{diag}(p)$, $\Pi_{zz'}=\pi(z,z')$. The squared residual of state functions $f,g$ under $Q$ is $\mathbb{E}\|f-Qg\|^2=\sum_zp(z)\|f(z)-Qg(z)\|^2$.
--   4. **Scene-explained fraction (Section 3).** An observation of state $z$ is $(z,\nu)$ with a nuisance $\nu\sim q$ independent of $z$, and an encoder is written $e(z,\nu)$. $C_f$ is the covariance under $z\sim p$ of $\mathbb{E}[f\mid Z=z]=\sum_\nu q(\nu)e(z,\nu)$, and $\rho(f)=\operatorname{tr}(C_f^{1/2})/k$. The bound of eq. (2) is $2k(1-\min(\rho_1,\rho_2))$. The paired residual is $\mathbb{E}\|f_1(X_1)-Qf_2(X_2)\|^2=\sum_{z,\nu_1,\nu_2}p(z)q_1(\nu_1)q_2(\nu_2)\|e_1(z,\nu_1)-Qe_2(z,\nu_2)\|^2$.
--   5. **Same-state operator (Section 4.1).** A channel $\kappa(z,x)=P_{X\mid Z}(x\mid z)$ maps the world to a finite observation space $X$, with $P_X(x)=\sum_zp(z)\kappa(z,x)$. The same-state pair law is $P_s(x,x')=\sum_zp(z)\kappa(z,x)\kappa(z,x')$, and the mixture is $P_+^\varepsilon=\varepsilon P_s+(1-\varepsilon)P_X\otimes P_X$. The operator is $T_s=AA^*$, with matrix $T_s(x,x')=P_s(x,x')/P_X(x)$, and $\sum_j\langle f_j,T_sf_j\rangle_{L^2(P_X)}$ is the quadratic term of eq. (3).
--   6. **Spectrum of $T_s$.** $1=\lambda_0\ge\lambda_1\ge\cdots\ge\lambda_{|X|-1}$ are the eigenvalues of $T_s$ with multiplicity. $\lambda_0=1$ belongs to the constant function, and $\lambda_1,\lambda_2,\dots$ are the eigenvalues on the centred subspace. $\operatorname{rank}(T_s)$ on the centred subspace is the matrix rank of $T_s$ minus one. The top eigenspace is the span of the centred eigenfunctions with eigenvalue $\ge\lambda_k$. The positive eigenspace and $\ker T_s$ are also taken within the centred subspace.
--   7. **Pairing (Section 4.2).** For pairs $(x_i,y_i)_{i\le m}$ in $\mathbb{R}^k$, the orthogonal Procrustes objective is $\sum_i\|y_i-Rx_i\|^2$ over $R\in O(k)$. The exact solutions are the $R\in O(k)$ with $Rx_i=y_i$ for all $i$. $I_r\oplus S$ is block-diagonal with $I_r$ on the first $r$ coordinates.
--
--   **Formalization Note** The eigenvalues are the roots of the characteristic polynomial of the matrix $T_s$, sorted in decreasing order. Index $0$ is the constant eigenfunction's eigenvalue $1$, which is the largest, so index $i\ge1$ is the paper's $\lambda_i$ on the centred subspace. $\operatorname{tr}(C_f^{1/2})$ is the sum of the square roots of the eigenvalues of $C_f$. The observation-level objects are for a finite world and a finite observation space.
-- source:
--   Xin Li, Same-State Pairs Make One JEPA Proof of the Platonic Representation Hypothesis Vacuous: A Correction and a Gauge Ledger, arXiv:2611.16182v1 (2026), Section 2.1 (Notation, pp. 2-3), Section 3 (scene-explained fraction, eq. (2), p. 5), Section 4.1 (eq. (3), p. 6), Section 4.2 (p. 7), Appendix A.1-A.3 (pp. 11-12)

import Mathlib

/-!
Xin Li, *Same-State Pairs Make One JEPA Proof of the Platonic Representation Hypothesis Vacuous:
A Correction and a Gauge Ledger*, arXiv:2611.16182v1 (2026): the finite world, positive-pair
laws, world kernel and hard-whitening objective of Section 2.1, the scene-explained fraction of
Section 3, the same-state pair operator `T_s` and its spectrum of Section 4.1 and Appendix A.1, and
the orthogonal Procrustes objects of Section 4.2 and Appendix A.2.
-/

noncomputable section

namespace SameStatePairs

/-- Section 2.1: the squared Euclidean norm `‖v‖² = ∑ᵢ vᵢ²` of an embedding `v ∈ ℝ^k`. -/
def sqNorm {k : ℕ} (v : Fin k → ℝ) : ℝ := ∑ i, v i ^ 2

/-- Section 2.1: the action `v ↦ Q v` of an orthogonal matrix `Q ∈ O(k)` on `ℝ^k`. -/
def rot {k : ℕ} (Q : Matrix.orthogonalGroup (Fin k) ℝ) (v : Fin k → ℝ) : Fin k → ℝ :=
  (Q : Matrix (Fin k) (Fin k) ℝ).mulVec v

section Encoders

variable {α : Type*} [Fintype α] {k : ℕ}

/-- Section 2.1 (Notation): an encoder `h : α → ℝ^k` on a finite set `α` carrying the law `w` is
centred if `E h = ∑ₐ w(a) h(a) = 0`. -/
def IsCentered (w : α → ℝ) (h : α → Fin k → ℝ) : Prop :=
  ∀ i, ∑ a, w a * h a i = 0

/-- Section 2.1 (Notation): an encoder `h` is whitened under `w` if
`E h hᵀ = ∑ₐ w(a) h(a) h(a)ᵀ = I_k`. -/
def IsWhitened (w : α → ℝ) (h : α → Fin k → ℝ) : Prop :=
  ∀ i j, ∑ a, w a * h a i * h a j = if i = j then 1 else 0

/-- Section 2.1: the prediction term `L_π(h) = E_{(a,a')∼π} ‖h(a) - h(a')‖²` for a law `π` of
positive pairs on `α`. -/
def pairLoss (π : α → α → ℝ) (h : α → Fin k → ℝ) : ℝ :=
  ∑ a, ∑ a', π a a' * sqNorm (h a - h a')

open Classical in
/-- Section 2.1: the hard anti-collapse term `Ω ∈ {0, ∞}` of the hard-whitening objective:
`Ω(h) = 0` if `h` is centred and whitened under `w`, and `Ω(h) = +∞` otherwise. -/
def hardOmega (w : α → ℝ) (h : α → Fin k → ℝ) : EReal :=
  if IsCentered w h ∧ IsWhitened w h then 0 else ⊤

/-- Section 2.1: `h` is a global minimiser of the hard-whitening population objective, i.e. of the
prediction term `L_π` subject to `Ω(h) = 0`: `h` is centred and whitened under `w`, and
`L_π(h) ≤ L_π(h')` for every centred, whitened `h'`. -/
def IsGlobalMin (w : α → ℝ) (π : α → α → ℝ) (h : α → Fin k → ℝ) : Prop :=
  IsCentered w h ∧ IsWhitened w h ∧
    ∀ h' : α → Fin k → ℝ, IsCentered w h' → IsWhitened w h' → pairLoss π h ≤ pairLoss π h'

/-- Lemma 1 and Theorem 1: the span of an encoder `h`, i.e. the span of its coordinate functions
`h_1, …, h_k : α → ℝ` in the function space. -/
def coordSpan (h : α → Fin k → ℝ) : Submodule ℝ (α → ℝ) :=
  Submodule.span ℝ (Set.range fun i a => h a i)

/-- Lemma 1 and Section 4.1: the centred function space `{φ : α → ℝ | ∑ₐ w(a) φ(a) = 0}`. -/
def centeredSpace (w : α → ℝ) : Submodule ℝ (α → ℝ) :=
  LinearMap.ker (dotProductBilin ℝ ℝ w)

end Encoders

section StateLevel

variable {Z : Type*} [Fintype Z]

/-- Section 2.1, Lemma 1: the same-state positive-pair law `π = diag(p)`:
`π(z, z') = p(z)` if `z = z'` and `0` otherwise. -/
def sameStateLaw [DecidableEq Z] (p : Z → ℝ) (z z' : Z) : ℝ :=
  if z = z' then p z else 0

/-- Section 2.1 (Notation): the world kernel `K_π = D^{-1/2} Π D^{-1/2}` with `D = diag(p)` and
`Π_{zz'} = π(z, z')`. -/
def worldKernel (p : Z → ℝ) (π : Z → Z → ℝ) : Matrix Z Z ℝ :=
  fun z z' => π z z' / Real.sqrt (p z * p z')

/-- Section 2.1 (Notation): the Markov operator `T_π = D^{-1} Π` on state functions. -/
def markovOp (p : Z → ℝ) (π : Z → Z → ℝ) : Matrix Z Z ℝ :=
  fun z z' => π z z' / p z

/-- Proposition 1, eq. (1): the squared residual `E‖f - Q g‖² = ∑_z p(z) ‖f(z) - Q g(z)‖²` of two
state functions `f, g : Z → ℝ^k` under a rotation `Q ∈ O(k)`. -/
def rotResidual {k : ℕ} (p : Z → ℝ) (f g : Z → Fin k → ℝ)
    (Q : Matrix.orthogonalGroup (Fin k) ℝ) : ℝ :=
  ∑ z, p z * sqNorm (f z - rot Q (g z))

end StateLevel

section Nuisance

variable {Z N : Type*} [Fintype Z] [Fintype N] {k : ℕ}

/-- Section 3 and Appendix A.3: an encoder `f` of observations `X = (z, ν)` of world state `z`
with a nuisance `ν ∼ q` independent of `z` is written `e(z, ν) = f(X)`; this is
`E[f(X) | Z = z] = ∑_ν q(ν) e(z, ν)`. -/
def condMean (q : N → ℝ) (e : Z → N → Fin k → ℝ) (z : Z) : Fin k → ℝ :=
  fun i => ∑ ν, q ν * e z ν i

/-- Section 3: `C_f = Cov(E[f(X) | Z])`, the covariance under `z ∼ p` of the scene-related part
of `f`. -/
def sceneCov (p : Z → ℝ) (q : N → ℝ) (e : Z → N → Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => ∑ z, p z * (condMean q e z i - ∑ z', p z' * condMean q e z' i) *
    (condMean q e z j - ∑ z', p z' * condMean q e z' j)

/-- Section 3: the scene-explained fraction `ρ(f) = tr(C_f^{1/2}) / k`, where `tr(C_f^{1/2})` is the
sum of the square roots of the eigenvalues of `C_f` (the roots of its characteristic polynomial,
with multiplicity). -/
def sceneFraction (p : Z → ℝ) (q : N → ℝ) (e : Z → N → Fin k → ℝ) : ℝ :=
  ((sceneCov p q e).charpoly.roots.map Real.sqrt).sum / k

/-- Section 3, eq. (2): the lower bound `2k (1 - min(ρ₁, ρ₂))` on the aligned error. -/
def survivorBound (k : ℕ) (ρ₁ ρ₂ : ℝ) : ℝ :=
  2 * k * (1 - min ρ₁ ρ₂)

/-- Section 3, eq. (2), and Proposition 2: `E‖f₁(X₁) - Q f₂(X₂)‖²` over paired observations
`X₁ = (z, ν₁)`, `X₂ = (z, ν₂)` of one state `z ∼ p` with independent nuisances `ν₁ ∼ q₁`,
`ν₂ ∼ q₂`. -/
def pairedResidual {N₁ N₂ : Type*} [Fintype N₁] [Fintype N₂] (p : Z → ℝ) (q₁ : N₁ → ℝ)
    (q₂ : N₂ → ℝ) (e₁ : Z → N₁ → Fin k → ℝ) (e₂ : Z → N₂ → Fin k → ℝ)
    (Q : Matrix.orthogonalGroup (Fin k) ℝ) : ℝ :=
  ∑ z, ∑ ν₁, ∑ ν₂, p z * q₁ ν₁ * q₂ ν₂ * sqNorm (e₁ z ν₁ - rot Q (e₂ z ν₂))

end Nuisance

section Observation

variable {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq X] {k : ℕ}

/-- Section 4.1: `κ(z, x) = P_{X|Z}(x | z)` is an observation channel from the finite world `Z` to
the finite observation space `X`. -/
def IsChannel (κ : Z → X → ℝ) : Prop :=
  (∀ z x, 0 ≤ κ z x) ∧ ∀ z, ∑ x, κ z x = 1

/-- Section 4.1: the observation law `P_X(x) = ∑_z p(z) κ(z, x)`. -/
def obsLaw (p : Z → ℝ) (κ : Z → X → ℝ) (x : X) : ℝ :=
  ∑ z, p z * κ z x

/-- Section 4.1: the same-state pair law `P_s`: given `Z = z`, the two views are conditionally
independent with common law `κ(z, ·)`, so `P_s(x, x') = ∑_z p(z) κ(z, x) κ(z, x')`. -/
def sameStatePairLaw (p : Z → ℝ) (κ : Z → X → ℝ) (x x' : X) : ℝ :=
  ∑ z, p z * κ z x * κ z x'

/-- Section 4.1: the positive-pair mixture `P_+^ε = ε P_s + (1 - ε) P_X ⊗ P_X`. -/
def mixPairLaw (p : Z → ℝ) (κ : Z → X → ℝ) (ε : ℝ) (x x' : X) : ℝ :=
  ε * sameStatePairLaw p κ x x' + (1 - ε) * (obsLaw p κ x * obsLaw p κ x')

/-- Section 4.1: the operator `T_s = A A*` on functions of the observation, with
`(A φ)(x) = E[φ(Z) | X = x]` and `(A* f)(z) = E[f(X) | Z = z]`; as a matrix,
`T_s(x, x') = ∑_z p(z) κ(z, x) κ(z, x') / P_X(x)`. -/
def sameStateOp (p : Z → ℝ) (κ : Z → X → ℝ) : Matrix X X ℝ :=
  fun x x' => sameStatePairLaw p κ x x' / obsLaw p κ x

/-- Section 4.1, eq. (3): `∑_{j=1}^k ⟨f_j, T_s f_j⟩_{L²(P_X)}`. -/
def topQuad (p : Z → ℝ) (κ : Z → X → ℝ) (f : X → Fin k → ℝ) : ℝ :=
  ∑ j, ∑ x, obsLaw p κ x * f x j * (sameStateOp p κ).mulVec (fun x' => f x' j) x

/-- Section 4.1 and Appendix A.1: the eigenvalues of `T_s`, with multiplicity, as the roots of its
characteristic polynomial sorted in decreasing order. Index `0` is the eigenvalue `1` of the
constant function; for `1 ≤ i ≤ |X| - 1`, `obsEig p κ i` is `λ_i`, the `i`-th eigenvalue of `T_s` on
the centred subspace (`0` for `i ≥ |X|`; statements do not use those values). -/
def obsEig (p : Z → ℝ) (κ : Z → X → ℝ) (i : ℕ) : ℝ :=
  ((sameStateOp p κ).charpoly.roots.sort (· ≥ ·)).getD i 0

/-- Theorem 1: `rank(T_s)` on the centred subspace, i.e. the rank of the matrix `T_s` minus the
contribution `1` of the constant function. -/
def obsRank (p : Z → ℝ) (κ : Z → X → ℝ) : ℕ :=
  (sameStateOp p κ).rank - 1

/-- Theorem 1: the top eigenspace of `T_s`, the span of the centred eigenfunctions of `T_s` with
eigenvalue at least `λ_k`. -/
def topSpace (p : Z → ℝ) (κ : Z → X → ℝ) (k : ℕ) : Submodule ℝ (X → ℝ) :=
  (⨆ (μ : ℝ) (_ : obsEig p κ k ≤ μ), Module.End.eigenspace (Matrix.toLin' (sameStateOp p κ)) μ) ⊓
    centeredSpace (obsLaw p κ)

/-- Theorem 1: the span of the centred eigenfunctions of `T_s` with eigenvalue greater than
`λ_k`. -/
def strictTopSpace (p : Z → ℝ) (κ : Z → X → ℝ) (k : ℕ) : Submodule ℝ (X → ℝ) :=
  (⨆ (μ : ℝ) (_ : obsEig p κ k < μ), Module.End.eigenspace (Matrix.toLin' (sameStateOp p κ)) μ) ⊓
    centeredSpace (obsLaw p κ)

/-- Theorem 1: the positive eigenspace of `T_s` on the centred subspace. -/
def posSpace (p : Z → ℝ) (κ : Z → X → ℝ) : Submodule ℝ (X → ℝ) :=
  (⨆ (μ : ℝ) (_ : 0 < μ), Module.End.eigenspace (Matrix.toLin' (sameStateOp p κ)) μ) ⊓
    centeredSpace (obsLaw p κ)

/-- Theorem 1: `ker T_s` on the centred subspace. -/
def obsKerSpace (p : Z → ℝ) (κ : Z → X → ℝ) : Submodule ℝ (X → ℝ) :=
  LinearMap.ker (Matrix.toLin' (sameStateOp p κ)) ⊓ centeredSpace (obsLaw p κ)

end Observation

section Pairing

variable {m k : ℕ}

/-- Section 4.2: the orthogonal Procrustes objective `∑_i ‖y_i - R x_i‖²` of `m` synchronized
pairs `(x_i, y_i)` in whitened coordinates, for `R ∈ O(k)`. -/
def procrustesObj (x y : Fin m → Fin k → ℝ) (R : Matrix.orthogonalGroup (Fin k) ℝ) : ℝ :=
  ∑ i, sqNorm (y i - rot R (x i))

/-- Section 4.2 and Appendix A.2: the exact solutions `{R ∈ O(k) : 𝐗 Rᵀ = 𝐘}`, i.e. `R x_i = y_i`
for every pair. -/
def pairSolutions (x y : Fin m → Fin k → ℝ) : Set (Matrix.orthogonalGroup (Fin k) ℝ) :=
  {R | ∀ i, rot R (x i) = y i}

/-- Section 4.2, Theorem 2: the block-diagonal matrix `I_r ⊕ S` on `ℝ^k`, with `I_r` on the first
`r` coordinates and the `(k - r) × (k - r)` block `S` on the remaining ones. -/
def blockEmbed (r : ℕ) (S : Matrix (Fin (k - r)) (Fin (k - r)) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j =>
    if hij : r ≤ i.val ∧ r ≤ j.val then
      S ⟨i.val - r, by have := i.isLt; omega⟩ ⟨j.val - r, by have := j.isLt; omega⟩
    else if i = j then 1 else 0

end Pairing

end SameStatePairs


