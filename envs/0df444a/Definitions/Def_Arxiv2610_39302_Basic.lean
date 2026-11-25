-- Prove2me | Definitions.Def_Arxiv2610_39302_Basic
-- name    : Arxiv2610_39302_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T02:51:09.093156+00:00
-- url     : https://prove2.me/theorems/f2752c99-94eb-4782-9d8c-6a27fdd752c7
-- title:
--   Platonic Representation Theorem for JEPAs: world, positive pairs, spectral objective, nuisance, views and next-token loss
-- statement:
--   Objects of Section 2 and Appendix A of Balestriero and LeCun (2026), and of the subsample interval of Appendix C.
--
--   1. **World and positive pairs (Section 2.1).** A world is a finite set $Z$ of states with probabilities $p(z)>0$, $\sum_zp(z)=1$. A positive-pair law is a symmetric law $\pi(z,z')\ge0$ on pairs of states whose two marginals equal $p$. The same notion is used for a law $W$ on pairs of observations with marginal $\omega$.
--   2. **Embeddings and rotations.** An embedding is $h:Z\to\mathbb{R}^k$, with $\|a\|^2=\sum_ia_i^2$; an orthogonal matrix $Q\in O(k)$ acts by $a\mapsto Qa$. The law of the embeddings is $\sum_zp(z)\,\delta_{h(z)}$.
--   3. **JEPA objective (eq. 1).** For a prediction term $\ell$ and an anti-collapse term $\Omega$ that is a function of the law of the embeddings, $L_\pi(h)=\sum_{z,z'}\pi(z,z')\,\ell(h(z),h(z'))+\Omega(h)$, and a modality with rendering $g:Z\to X$ and encoder $f:X\to\mathbb{R}^k$ has $L_m(f)=\sum_{z,z'}\pi(z,z')\,\ell(f(g(z)),f(g(z')))+\Omega(f\circ g)$. The standing assumptions are that $\ell(Qa,Qb)=\ell(a,b)$, that rotating every embedding leaves $\Omega$ unchanged, and that $\Omega$ takes values in $\mathbb{R}\cup\{+\infty\}$. The minimisers of an objective are unique up to rotation if any two of them satisfy $h'=Qh$ for some $Q\in O(k)$.
--   4. **Spectral objective (Proposition 1).** $\ell(a,b)=\|a-b\|^2$, and $\Omega$ is $0$ if the law of the embeddings has mean $0$ and second moment $I_k$, and $+\infty$ otherwise. An embedding $f$ on a finite set with law $\omega$ is centred and whitened if $\sum_x\omega(x)f(x)=0$ and $\sum_x\omega(x)f(x)f(x)^\top=I_k$.
--   5. **Spectrum.** $K_\pi=D^{-1/2}\Pi D^{-1/2}$ with $D=\mathrm{diag}(p)$, $\Pi_{zz'}=\pi(z,z')$; its eigenvalues with multiplicity are $1=\mu_0\ge\mu_1\ge\cdots$, with $\mu_i:=-\infty$ for $i\ge|Z|$. The Markov operator is $T_\pi=D^{-1}\Pi$. A spectral embedding is $\Phi(z)=(v_1(z),\dots,v_k(z))/\sqrt{p(z)}$ for orthonormal eigenvectors $v_1,\dots,v_k$ of $K_\pi$, orthogonal to $D^{1/2}\mathbf 1$, with eigenvalues $\mu_1,\dots,\mu_k$. $\|\cdot\|_2$ and $\|\cdot\|_F$ are the spectral and Frobenius norms, $\|f-g\|_{L^2(\omega)}=(\sum_x\omega(x)\|f(x)-g(x)\|^2)^{1/2}$, and the right side of eq. (3) is $\frac{2\sqrt2}{\mu_k-\mu_{k+1}}\min(\sqrt k\|K_{\pi_1}-K_{\pi_2}\|_2,\|K_{\pi_1}-K_{\pi_2}\|_F)$, read as $0$ when $k+1=|Z|$.
--   6. **Observations and nuisance (Section 2.3).** An observation $x$ of a finite set $X$ with law $\omega$ is of the state $s(x)$; its state marginal is $\sum_{s(x)=z}\omega(x)$. $E[f\mid z]$ is the conditional mean, $C_f=\mathrm{Cov}(E[f(x)\mid z])$, and the scene-explained fraction is $\rho(f)=\operatorname{tr}C_f^{1/2}/k$. With nuisance $\nu\sim q$ independent of $z$, the observations are pairs $(z,\nu)$ with law $p(z)q(\nu)$ and $s(z,\nu)=z$.
--   7. **Good and bad views (Proposition 3).** A good-view JEPA has positive-pair law $\pi(z,z')q(\nu)q(\nu')$. For row-stochastic $A$, $B$ with stationary laws $p$, $q$, the bad-view law is the law of two corruptions $\tilde x,\tilde x'\sim\Gamma(\cdot\mid x)$, drawn independently given one clean observation $x\sim p\otimes q$, with $\Gamma=A\otimes B$. The $\alpha_i$ (resp. $\beta_j$) are the eigenvalues of $A^*A$ on $L^2(p)$ (resp. $B^*B$ on $L^2(q)$), i.e. those of the normalised kernel of $A^\top D_pA$. The $\xi_1\ge\xi_2\ge\cdots$ are the products $\alpha_i\beta_j$, $(i,j)\ne(0,0)$, with multiplicity, and $r$ is the number of pairs $(i,j)$ with $j\ge1$ and $\alpha_i\beta_j\ge\xi_k$.
--   8. **Formal Theorem 4 (Appendix A.4).** For a law $W$ on pairs of observations: the induced world kernel $\pi_W(z,z')=\sum_{s(x)=z,\,s(x')=z'}W(x,x')$; the conditional expectation $P$ onto functions of the state in $L^2(\omega)$; $\eta=\sup\{\langle h,T_Wh\rangle_\omega: Ph=0,\ \|h\|_\omega=1\}$ ($-\infty$ if there is no such $h$); $\varepsilon$ and $\varepsilon^{\mathrm{HS}}$, the operator and Hilbert–Schmidt norms of $(I-P)T_WP$ on $L^2(\omega)$; $\delta=\mu_k-\max(\mu_{k+1},\eta)$ for the eigenvalues $\mu_i$ of $\pi_W$; $\tau=\frac{2\sqrt2}{\delta}\min(\sqrt k\,\varepsilon,\sqrt2\,\varepsilon^{\mathrm{HS}})$ ($0$ if $\delta=+\infty$). A paired coupling is a law $\gamma$ on $X_1\times X_2$ with marginals $\omega_1,\omega_2$ that only pairs observations of the same state. Merging observations by $c:X\to Y$ sums $\omega$ and $W$ over the groups.
--   9. **Next-token prediction (eq. 6).** $A(h)=\log\sum_ve^{\langle h,w_v\rangle}$, the loss is $-\log\big(e^{\langle h,w_y\rangle}/\sum_ve^{\langle h,w_v\rangle}\big)$, and the expected loss over finitely many contexts with weights $P(c)$ and conditionals $p(\cdot\mid c)$ is $\sum_cP(c)\sum_vp(v\mid c)\,(\text{loss})$.
--   10. **Subsample spread (Appendix C).** For scores $x_1,\dots,x_N$: $\bar x$, the subset mean $\bar x_S$, $s^2=\sum_i(x_i-\bar x)^2/(N-1)$, and the spread $\big(\binom Nn^{-1}\sum_{|S|=n}(\bar x_S-\bar x)^2\big)^{1/2}$ over uniformly random $n$-subsets.
--
--   **Formalization Note** The eigenvalues $\mu_i$ are the roots of the characteristic polynomial of $K_\pi$ in decreasing order. The convention $\mu_{|Z|}=-\infty$ appears either as a hypothesis that applies only when $k+1<|Z|$ or through an extended-real eigenvalue equal to $-\infty$ beyond $|Z|$. $\operatorname{tr}C_f^{1/2}$ is the sum of the square roots of the eigenvalues of $C_f$. Operators on $L^2(\omega)$ are written as matrices acting on functions $X\to\mathbb{R}$; their norms are taken in the $L^2(\omega)$ metric.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), Sections 2.1-2.4, Appendix A.1-A.5 (PDF pp. 2-6, 20-23), Appendix C 'Uncertainty on WIT' (PDF p. 31)

import Mathlib

/-!
Balestriero and LeCun, *Proving and Improving the Platonic Representation Hypothesis with JEPAs*,
arXiv:2610.39302v1 (2026). Objects of Section 2 (Sections 2.1-2.4) and Appendix A (A.1-A.5): the
finite world, positive-pair laws, the JEPA objective of eq. (1), the normalised adjacency and its
spectrum, spectral embeddings, observations with nuisance, good-view and bad-view positive laws,
the operators of the formal Theorem 4, and the next-token loss of eq. (6); and the subsample
spread of Appendix C ("Uncertainty on WIT").
-/

open MeasureTheory

noncomputable section

namespace Arxiv2610_39302

/-! ### Section 2.1: world, embeddings, JEPA objective -/

/-- Section 2.1: squared Euclidean norm `‖a‖² = ∑ᵢ aᵢ²` of an embedding `a ∈ ℝ^k`. -/
def sqNorm {k : ℕ} (a : Fin k → ℝ) : ℝ := ∑ i, a i ^ 2

/-- Proposition 1 (Section 2.1): the prediction term `ℓ(a, b) = ‖a - b‖²`. -/
def sqDist {k : ℕ} (a b : Fin k → ℝ) : ℝ := sqNorm (a - b)

/-- Section 2.1: the action `a ↦ Q a` of an orthogonal matrix `Q ∈ O(k)` on an embedding. -/
def rot {k : ℕ} (Q : Matrix.orthogonalGroup (Fin k) ℝ) (a : Fin k → ℝ) : Fin k → ℝ :=
  (Q : Matrix (Fin k) (Fin k) ℝ).mulVec a

/-- Section 2.1: `p` is a law on the finite set `Z` with `p(z) > 0`, and `π` is a symmetric law on
pairs whose two marginals equal `p` (a positive-pair distribution). Used verbatim for laws `W` on
pairs of observations with marginal `ω` (Appendix A.4, formal Theorem 4). -/
def IsPairLaw {Z : Type*} [Fintype Z] (p : Z → ℝ) (π : Z → Z → ℝ) : Prop :=
  (∀ z, 0 < p z) ∧ (∑ z, p z = 1) ∧ (∀ z z', 0 ≤ π z z') ∧ (∀ z z', π z z' = π z' z) ∧
    (∀ z, ∑ z', π z z' = p z)

/-- Section 2.1: the distribution of the embeddings `h(z)`, `z ∼ p`, namely `∑_z p(z) δ_{h(z)}`. -/
def embLaw {Z : Type*} [Fintype Z] {k : ℕ} (p : Z → ℝ) (h : Z → Fin k → ℝ) :
    Measure (Fin k → ℝ) :=
  ∑ z, ENNReal.ofReal (p z) • Measure.dirac (h z)

/-- Section 2.1, standing assumptions on eq. (1): the prediction term is rotation invariant,
`ℓ(Qa, Qb) = ℓ(a, b)`; rotating every embedding leaves the anti-collapse term unchanged; and the
anti-collapse term takes values in `ℝ ∪ {+∞}` (a hard constraint is `Ω ∈ {0, ∞}`). The
anti-collapse term is a function of the law of the embeddings, as the paper requires. -/
def IsJEPAObjective {Z : Type*} [Fintype Z] {k : ℕ} (p : Z → ℝ)
    (ℓ : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (Om : Measure (Fin k → ℝ) → EReal) : Prop :=
  (∀ (Q : Matrix.orthogonalGroup (Fin k) ℝ) (a b : Fin k → ℝ), ℓ (rot Q a) (rot Q b) = ℓ a b) ∧
    (∀ (h : Z → Fin k → ℝ) (Q : Matrix.orthogonalGroup (Fin k) ℝ),
      Om (embLaw p (fun z => rot Q (h z))) = Om (embLaw p h)) ∧
    (∀ μ, Om μ ≠ ⊥)

/-- Section 2.1: the objective written on world states,
`L_π(h) = E_{(z,z')∼π} ℓ(h(z), h(z')) + Ω(h)`, for `h : Z → ℝ^k`. -/
def worldLoss {Z : Type*} [Fintype Z] {k : ℕ} (p : Z → ℝ) (π : Z → Z → ℝ)
    (ℓ : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (Om : Measure (Fin k → ℝ) → EReal)
    (h : Z → Fin k → ℝ) : EReal :=
  ((∑ z, ∑ z', π z z' * ℓ (h z) (h z') : ℝ) : EReal) + Om (embLaw p h)

/-- Eq. (1), Section 2.1: the objective `L_m(f) = E_{(z,z')∼π} ℓ(f(g(z)), f(g(z'))) + Ω(f)` of a
JEPA of a modality with rendering `g : Z → X` and encoder `f : X → ℝ^k`; `Ω` sees the law of the
embeddings `f(g(z))`, `z ∼ p`. -/
def modalityLoss {Z X : Type*} [Fintype Z] {k : ℕ} (p : Z → ℝ) (π : Z → Z → ℝ)
    (ℓ : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (Om : Measure (Fin k → ℝ) → EReal) (g : Z → X)
    (f : X → Fin k → ℝ) : EReal :=
  ((∑ z, ∑ z', π z z' * ℓ (f (g z)) (f (g z')) : ℝ) : EReal) + Om (embLaw p (fun z => f (g z)))

/-- Theorem 1 (Section 2.1): the minimisers of an objective `L` on embeddings `h : Z → ℝ^k` are
unique up to rotation: any two minimisers `h, h'` satisfy `h' = Q h` for some `Q ∈ O(k)`. -/
def UniqueUpToRotation {Z : Type*} {k : ℕ} (L : (Z → Fin k → ℝ) → EReal) : Prop :=
  ∀ h h' : Z → Fin k → ℝ, (∀ h'', L h ≤ L h'') → (∀ h'', L h' ≤ L h'') →
    ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, ∀ z, h' z = rot Q (h z)

open Classical in
/-- Proposition 1 (Section 2.1): the anti-collapse term that whitens the embeddings as a hard
constraint: `0` if the law `μ` of the embeddings has mean `0` and second moment `I_k`, `+∞`
otherwise. -/
def whiteningReg {k : ℕ} (μ : Measure (Fin k → ℝ)) : EReal :=
  if (∀ i, ∫ v, v i ∂μ = 0) ∧ (∀ i j, ∫ v, v i * v j ∂μ = if i = j then 1 else 0) then 0 else ⊤

/-- Proposition 1 (Section 2.1): the spectral objective, eq. (1) on world states with
`ℓ(a, b) = ‖a - b‖²` and the whitening constraint as anti-collapse term. -/
def spectralLoss {Z : Type*} [Fintype Z] {k : ℕ} (p : Z → ℝ) (π : Z → Z → ℝ)
    (h : Z → Fin k → ℝ) : EReal :=
  worldLoss p π sqDist whiteningReg h

/-- Proposition 1 and Section 2.3: `f : X → ℝ^k` is centred and whitened under the law `ω` on the
finite set `X`: `E_ω f = 0` and `E_ω f fᵀ = I_k`. -/
def IsWhitened {X : Type*} [Fintype X] {k : ℕ} (ω : X → ℝ) (f : X → Fin k → ℝ) : Prop :=
  (∀ i, ∑ x, ω x * f x i = 0) ∧ (∀ i j, ∑ x, ω x * f x i * f x j = if i = j then 1 else 0)

/-! ### Section 2.1 and Appendix A.1: spectrum -/

/-- Section 2.1: the normalised adjacency `K_π = D^{-1/2} Π D^{-1/2}`, `D = diag(p)`,
`Π_{zz'} = π(z, z')`. -/
def kerMat {Z : Type*} (p : Z → ℝ) (π : Z → Z → ℝ) : Matrix Z Z ℝ :=
  fun z z' => π z z' / Real.sqrt (p z * p z')

/-- Section 2.1: the eigenvalues `1 = μ₀ ≥ μ₁ ≥ ⋯` of `K_π` with multiplicity, as the roots of its
characteristic polynomial in decreasing order (`μ_i := 0` for `i ≥ |Z|`; statements never use
those values, see `extEig`). -/
def eigs {Z : Type*} [Fintype Z] [DecidableEq Z] (p : Z → ℝ) (π : Z → Z → ℝ) (i : ℕ) : ℝ :=
  ((kerMat p π).charpoly.roots.sort (· ≥ ·)).getD i 0

/-- Proposition 1 and Appendix A.4: `μ_i` with the paper's convention `μ_i := -∞` for
`i ≥ |Z|`, as an extended real. -/
def extEig {Z : Type*} [Fintype Z] [DecidableEq Z] (p : Z → ℝ) (π : Z → Z → ℝ) (i : ℕ) : EReal :=
  if i < Fintype.card Z then (eigs p π i : EReal) else ⊥

/-- Appendix A.1: the Markov operator `T_π = D^{-1} Π`, `(T_π h)(z) = E_π[h(z') | z]`, as a matrix
acting on functions `h : Z → ℝ`. -/
def markovOp {Z : Type*} (p : Z → ℝ) (π : Z → Z → ℝ) : Matrix Z Z ℝ :=
  fun z z' => π z z' / p z

/-- Proposition 1 (Section 2.1): `Φ` is a spectral embedding of `π`,
`Φ(z) = (v₁(z), …, v_k(z)) / √p(z)`, for orthonormal eigenvectors `v₁, …, v_k` of `K_π`, orthogonal
to `v₀ = D^{1/2} 1`, with eigenvalues `μ₁, …, μ_k` (any such choice when `K_π` has ties). -/
def IsSpectralEmbedding {Z : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ} (p : Z → ℝ)
    (π : Z → Z → ℝ) (Phi : Z → Fin k → ℝ) : Prop :=
  ∃ v : Fin k → Z → ℝ, (∀ i j, ∑ z, v i z * v j z = if i = j then 1 else 0) ∧
    (∀ i, ∑ z, Real.sqrt (p z) * v i z = 0) ∧
    (∀ i : Fin k, (kerMat p π).mulVec (v i) = eigs p π (i.val + 1) • v i) ∧
    ∀ z i, Phi z i = v i z / Real.sqrt (p z)

/-- Theorem 2 (Section 2.2): the spectral (operator) norm `‖A‖₂` of a real matrix. -/
def specNorm {Z : Type*} [Fintype Z] (A : Matrix Z Z ℝ) : ℝ :=
  sSup ((fun v : Z → ℝ => Real.sqrt (∑ z, (A.mulVec v z) ^ 2)) '' {v | ∑ z, v z ^ 2 ≤ 1})

/-- Theorem 2 (Section 2.2): the Frobenius norm `‖A‖_F` of a real matrix. -/
def frobNorm {Z : Type*} [Fintype Z] (A : Matrix Z Z ℝ) : ℝ :=
  Real.sqrt (∑ z, ∑ z', A z z' ^ 2)

/-- Theorem 2 (Section 2.2) and formal Theorem 4: the `L²(ω)` distance
`(E_ω ‖f(x) - g(x)‖²)^{1/2}` of two embeddings. -/
def l2Dist {X : Type*} [Fintype X] {k : ℕ} (ω : X → ℝ) (f g : X → Fin k → ℝ) : ℝ :=
  Real.sqrt (∑ x, ω x * sqNorm (f x - g x))

/-- Eq. (3), Theorem 2 (Section 2.2): the bound
`(2√2 / δ) min(√k ‖K_{π₁} - K_{π₂}‖₂, ‖K_{π₁} - K_{π₂}‖_F)` with `δ = μ_k - μ_{k+1}` of `K_{π₂}`;
when `k + 1 = |Z|`, `μ_{k+1} = -∞` and the bound is `0`. -/
def kahanBound {Z : Type*} [Fintype Z] [DecidableEq Z] (p : Z → ℝ) (π₁ π₂ : Z → Z → ℝ)
    (k : ℕ) : ℝ :=
  if k + 1 < Fintype.card Z then
    2 * Real.sqrt 2 / (eigs p π₂ k - eigs p π₂ (k + 1)) *
      min (Real.sqrt k * specNorm (kerMat p π₁ - kerMat p π₂)) (frobNorm (kerMat p π₁ - kerMat p π₂))
  else 0

/-! ### Section 2.3 and Appendix A.4: observations, nuisance, good and bad views -/

/-- Section 2.3 and formal Theorem 4: the state marginal `z ↦ ∑_{x : s(x) = z} ω(x)` of a law `ω`
on observations, each observation `x` being of the world state `s(x)`. -/
def stateMarg {X Z : Type*} [Fintype X] [DecidableEq Z] (ω : X → ℝ) (s : X → Z) (z : Z) : ℝ :=
  ∑ x, if s x = z then ω x else 0

/-- Section 2.3: `E[f(x) | z]`, the conditional mean of the embedding given the world state. -/
def condMean {X Z : Type*} [Fintype X] [DecidableEq Z] {k : ℕ} (ω : X → ℝ) (s : X → Z)
    (f : X → Fin k → ℝ) (z : Z) : Fin k → ℝ :=
  fun i => (∑ x, if s x = z then ω x * f x i else 0) / stateMarg ω s z

/-- Section 2.3: `E_ω f`, the mean of the embedding. -/
def meanVec {X : Type*} [Fintype X] {k : ℕ} (ω : X → ℝ) (f : X → Fin k → ℝ) : Fin k → ℝ :=
  fun i => ∑ x, ω x * f x i

/-- Section 2.3: `C_f = Cov(E[f(x) | z])`, the covariance of the part of the embedding that the
world state explains. -/
def stateCov {X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq Z] {k : ℕ} (ω : X → ℝ)
    (s : X → Z) (f : X → Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => ∑ z, stateMarg ω s z * (condMean ω s f z i - meanVec ω f i) *
    (condMean ω s f z j - meanVec ω f j)

/-- Section 2.3: the scene-explained fraction `ρ(f) = tr C_f^{1/2} / k`, with `tr C_f^{1/2}` the sum
of the square roots of the eigenvalues of `C_f` (roots of its characteristic polynomial, with
multiplicity). -/
def rho {X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq Z] {k : ℕ} (ω : X → ℝ) (s : X → Z)
    (f : X → Fin k → ℝ) : ℝ :=
  ((stateCov ω s f).charpoly.roots.map Real.sqrt).sum / k

/-- Section 2.3 and Appendix A.4: the law `p(z) q(ν)` of an observation `(z, ν)` of state `z` with
nuisance `ν ∼ q` drawn independently of `z`. -/
def prodLaw {Z N : Type*} (p : Z → ℝ) (q : N → ℝ) (x : Z × N) : ℝ := p x.1 * q x.2

/-- Proposition 3 (i), Appendix A.4: the positive-pair law of a good-view JEPA on observations
`(z, ν)`: `(z, z') ∼ π` and independent nuisances `ν, ν' ∼ q`, i.e. the kernel `Π ⊗ q qᵀ`. -/
def goodViewLaw {Z N : Type*} (π : Z → Z → ℝ) (q : N → ℝ) (x y : Z × N) : ℝ :=
  π x.1 y.1 * q x.2 * q y.2

/-- Proposition 3 (ii), Appendix A.4: `A` is row-stochastic with stationary law `p`
(`A ≥ 0`, `A 1 = 1`, `pᵀ A = pᵀ`). -/
def IsStationaryStochastic {Z : Type*} [Fintype Z] (p : Z → ℝ) (A : Matrix Z Z ℝ) : Prop :=
  (∀ z z', 0 ≤ A z z') ∧ (∀ z, ∑ z', A z z' = 1) ∧ (∀ z', ∑ z, p z * A z z' = p z')

/-- Proposition 3 (ii), Appendix A.4: the positive-pair law of a bad-view JEPA: two corruptions
`x̃, x̃' ∼ Γ(· | x)` of one clean observation `x ∼ p ⊗ q`, drawn independently given `x`, for the
product corruption `Γ = A ⊗ B`. -/
def badViewLaw {Z N : Type*} [Fintype Z] [Fintype N] (p : Z → ℝ) (q : N → ℝ) (A : Matrix Z Z ℝ)
    (B : Matrix N N ℝ) (x x' : Z × N) : ℝ :=
  ∑ y : Z × N, prodLaw p q y * (A y.1 x.1 * B y.2 x.2) * (A y.1 x'.1 * B y.2 x'.2)

/-- Proposition 3 (ii), Appendix A.4: the law `Aᵀ D_p A` of two corruptions of one state, whose
Markov operator on `L²(p)` is `A* A`. -/
def twoCorruptLaw {Z : Type*} [Fintype Z] (p : Z → ℝ) (A : Matrix Z Z ℝ) (z z' : Z) : ℝ :=
  ∑ y, p y * A y z * A y z'

/-- Proposition 3 (ii), Appendix A.4: the eigenvalues `1 = α₀ ≥ α₁ ≥ ⋯` of `A* A` on `L²(p)`
(for `B` and `q`: the `β_j`), i.e. the eigenvalues of the normalised kernel of `Aᵀ D_p A`. -/
def corrEig {Z : Type*} [Fintype Z] [DecidableEq Z] (p : Z → ℝ) (A : Matrix Z Z ℝ) (i : ℕ) : ℝ :=
  eigs p (twoCorruptLaw p A) i

/-- Proposition 3 (ii), Appendix A.4: the index pairs `(i, j) ≠ (0, 0)`, `i < |Z|`, `j < |N|`. -/
def badPairs (nZ nN : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range nZ ×ˢ Finset.range nN).erase (0, 0)

/-- Proposition 3 (ii), Appendix A.4: the eigenvalue `α_i β_j` of the bad-view kernel. -/
def badEig {Z N : Type*} [Fintype Z] [DecidableEq Z] [Fintype N] [DecidableEq N] (p : Z → ℝ)
    (q : N → ℝ) (A : Matrix Z Z ℝ) (B : Matrix N N ℝ) (ij : ℕ × ℕ) : ℝ :=
  corrEig p A ij.1 * corrEig q B ij.2

/-- Proposition 3 (ii), Appendix A.4: `ξ₁ ≥ ξ₂ ≥ ⋯`, the values `α_i β_j` with `(i, j) ≠ (0, 0)`,
with multiplicity, in decreasing order (`ξ_l` for `l ≥ 1`). -/
def xi {Z N : Type*} [Fintype Z] [DecidableEq Z] [Fintype N] [DecidableEq N] (p : Z → ℝ)
    (q : N → ℝ) (A : Matrix Z Z ℝ) (B : Matrix N N ℝ) (l : ℕ) : ℝ :=
  (((badPairs (Fintype.card Z) (Fintype.card N)).val.map (badEig p q A B)).sort (· ≥ ·)).getD
    (l - 1) 0

/-- Proposition 3 (ii), Appendix A.4: `r`, the number of the top `k` pairs `(i, j)` (those with
`α_i β_j ≥ ξ_k`; exactly `k` of them when `ξ_k > ξ_{k+1}`) that have `j ≥ 1`. -/
def nuisanceCount {Z N : Type*} [Fintype Z] [DecidableEq Z] [Fintype N] [DecidableEq N]
    (p : Z → ℝ) (q : N → ℝ) (A : Matrix Z Z ℝ) (B : Matrix N N ℝ) (k : ℕ) : ℕ :=
  ((badPairs (Fintype.card Z) (Fintype.card N)).filter
    (fun ij => 1 ≤ ij.2 ∧ xi p q A B k ≤ badEig p q A B ij)).card

/-! ### Appendix A.4: formal Theorem 4 -/

/-- Formal Theorem 4 (Appendix A.4): the induced world kernel `π_W(z, z')`, the probability that a
positive pair `(x, x') ∼ W` joins an observation of `z` to one of `z'`. -/
def inducedKernel {X Z : Type*} [Fintype X] [DecidableEq Z] (s : X → Z) (W : X → X → ℝ) (z z' : Z) : ℝ :=
  ∑ x, ∑ x', if s x = z ∧ s x' = z' then W x x' else 0

/-- Formal Theorem 4 (Appendix A.4): the conditional expectation `P` onto functions of the state
in `L²(ω)`, `(P h)(x) = E_ω[h | s = s(x)]`, as a matrix. -/
def condExpMat {X Z : Type*} [Fintype X] [DecidableEq Z] (ω : X → ℝ) (s : X → Z) :
    Matrix X X ℝ :=
  fun x x' => if s x' = s x then ω x' / stateMarg ω s (s x) else 0

/-- Appendix A.1: the inner product `⟨h, h'⟩_ω = ∑ₓ ω(x) h(x) h'(x)` of `L²(ω)`. -/
def l2Inner {X : Type*} [Fintype X] (ω : X → ℝ) (h h' : X → ℝ) : ℝ :=
  ∑ x, ω x * h x * h' x

/-- Formal Theorem 4 (Appendix A.4): `η`, the largest eigenvalue of the compression
`(I - P) T_W (I - P)` to nuisance functions (`P h = 0`), i.e. the largest value of `⟨h, T_W h⟩_ω`
over nuisance functions of unit norm; `η = -∞` (the supremum of the empty set) if every state has
one observation. -/
def nuisanceTop {X Z : Type*} [Fintype X] [DecidableEq Z] (ω : X → ℝ) (s : X → Z)
    (W : X → X → ℝ) : EReal :=
  sSup ((fun h : X → ℝ => ((l2Inner ω h ((markovOp ω W).mulVec h) : ℝ) : EReal)) ''
    {h | (condExpMat ω s).mulVec h = 0 ∧ l2Inner ω h h = 1})

/-- Formal Theorem 4 (Appendix A.4): the mixing operator `(I - P) T_W P`. -/
def mixOp {X Z : Type*} [Fintype X] [DecidableEq X] [DecidableEq Z] (ω : X → ℝ) (s : X → Z)
    (W : X → X → ℝ) : Matrix X X ℝ :=
  (1 - condExpMat ω s) * markovOp ω W * condExpMat ω s

/-- Formal Theorem 4 (Appendix A.4): the operator norm of a matrix `M` acting on `L²(ω)`. -/
def opNormL2 {X : Type*} [Fintype X] (ω : X → ℝ) (M : Matrix X X ℝ) : ℝ :=
  sSup ((fun h : X → ℝ => Real.sqrt (l2Inner ω (M.mulVec h) (M.mulVec h))) ''
    {h | l2Inner ω h h ≤ 1})

/-- Formal Theorem 4 (Appendix A.4): the Hilbert-Schmidt norm of a matrix `M` acting on `L²(ω)`,
`(∑_{x,x'} ω(x) M(x,x')² / ω(x'))^{1/2}`. -/
def hsNormL2 {X : Type*} [Fintype X] (ω : X → ℝ) (M : Matrix X X ℝ) : ℝ :=
  Real.sqrt (∑ x, ∑ x', ω x * M x x' ^ 2 / ω x')

/-- Formal Theorem 4 (Appendix A.4): `ε`, the operator norm of `(I - P) T_W P` on `L²(ω)`. -/
def mixNorm {X Z : Type*} [Fintype X] [DecidableEq X] [DecidableEq Z] (ω : X → ℝ) (s : X → Z)
    (W : X → X → ℝ) : ℝ :=
  opNormL2 ω (mixOp ω s W)

/-- Formal Theorem 4 (Appendix A.4): `ε^{HS}`, the Hilbert-Schmidt norm of `(I - P) T_W P` on
`L²(ω)`. -/
def mixHSNorm {X Z : Type*} [Fintype X] [DecidableEq X] [DecidableEq Z] (ω : X → ℝ) (s : X → Z)
    (W : X → X → ℝ) : ℝ :=
  hsNormL2 ω (mixOp ω s W)

/-- Formal Theorem 4 (Appendix A.4): `δ = μ_k - max(μ_{k+1}, η)`, with `μ_i` the eigenvalues of
the induced world kernel (`μ_{|Z|} := -∞`), as an extended real (`+∞` when `μ_{k+1} = η = -∞`). -/
def worldGap {X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq Z] (ω : X → ℝ) (s : X → Z)
    (W : X → X → ℝ) (k : ℕ) : EReal :=
  (eigs (stateMarg ω s) (inducedKernel s W) k : EReal) -
    max (extEig (stateMarg ω s) (inducedKernel s W) (k + 1)) (nuisanceTop ω s W)

/-- Formal Theorem 4 (i) (Appendix A.4): `τ = (2√2 / δ) min(√k ε, √2 ε^{HS})`, read as `0` when
`δ = +∞`. -/
def tau {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] (ω : X → ℝ)
    (s : X → Z) (W : X → X → ℝ) (k : ℕ) : ℝ :=
  if worldGap ω s W k = ⊤ then 0 else
    2 * Real.sqrt 2 / (worldGap ω s W k).toReal *
      min (Real.sqrt k * mixNorm ω s W) (Real.sqrt 2 * mixHSNorm ω s W)

/-- Formal Theorem 4 (ii) (Appendix A.4): `γ` is a law of paired observations `(x₁, x₂)` of one
world state with `x_m ∼ ω_m`: `z ∼ p` and `x_m | z ∼ ω_m(· | z)`, under any coupling. -/
def IsPairedCoupling {X₁ X₂ Z : Type*} [Fintype X₁] [Fintype X₂] (ω₁ : X₁ → ℝ) (s₁ : X₁ → Z)
    (ω₂ : X₂ → ℝ) (s₂ : X₂ → Z) (γ : X₁ → X₂ → ℝ) : Prop :=
  (∀ x₁ x₂, 0 ≤ γ x₁ x₂) ∧ (∀ x₁, ∑ x₂, γ x₁ x₂ = ω₁ x₁) ∧ (∀ x₂, ∑ x₁, γ x₁ x₂ = ω₂ x₂) ∧
    ∀ x₁ x₂, γ x₁ x₂ ≠ 0 → s₁ x₁ = s₂ x₂

/-- Formal Theorem 4 (ii) (Appendix A.4): `(E_γ ‖f₁(x₁) - Q f₂(x₂)‖²)^{1/2}`. -/
def pairedRMS {X₁ X₂ : Type*} [Fintype X₁] [Fintype X₂] {k : ℕ} (γ : X₁ → X₂ → ℝ)
    (f₁ : X₁ → Fin k → ℝ) (f₂ : X₂ → Fin k → ℝ) (Q : Matrix.orthogonalGroup (Fin k) ℝ) : ℝ :=
  Real.sqrt (∑ x₁, ∑ x₂, γ x₁ x₂ * sqNorm (f₁ x₁ - rot Q (f₂ x₂)))

/-- Appendix A.4, "Special cases and scope": the law of the merged observations when the
observations are grouped by `c : X → Y`. -/
def mergeWeights {X Y : Type*} [Fintype X] [DecidableEq Y] (c : X → Y) (ω : X → ℝ) (y : Y) : ℝ :=
  ∑ x, if c x = y then ω x else 0

/-- Appendix A.4, "Special cases and scope": the positive-pair law on merged observations,
`W'(y, y') = ∑_{c(x) = y, c(x') = y'} W(x, x')`. -/
def mergeLaw {X Y : Type*} [Fintype X] [DecidableEq Y] (c : X → Y) (W : X → X → ℝ) (y y' : Y) :
    ℝ :=
  ∑ x, ∑ x', if c x = y ∧ c x' = y' then W x x' else 0

/-! ### Section 2.4: next-token prediction -/

/-- Eq. (6), Proposition 4 (Section 2.4): the anti-collapse term `A(h) = log ∑_v exp ⟨h, w_v⟩`. -/
def ntpAntiCollapse {V : Type*} [Fintype V] {k : ℕ} (w : V → Fin k → ℝ) (h : Fin k → ℝ) : ℝ :=
  Real.log (∑ v, Real.exp (h ⬝ᵥ w v))

/-- Eq. (6), Proposition 4 (Section 2.4): the next-token loss with a linear softmax head,
`-log (e^{⟨h, w_y⟩} / ∑_v e^{⟨h, w_v⟩})`. -/
def ntpLoss {V : Type*} [Fintype V] {k : ℕ} (w : V → Fin k → ℝ) (h : Fin k → ℝ) (y : V) : ℝ :=
  -Real.log (Real.exp (h ⬝ᵥ w y) / ∑ v, Real.exp (h ⬝ᵥ w v))

/-- Proposition 4 (iii) and its proof (Appendix A.5): the expected next-token loss
`∑_c P(c) ∑_v p(v | c) · (-log softmax(W h(c))_v)` over finitely many contexts. -/
def ntpRisk {C V : Type*} [Fintype C] [Fintype V] {k : ℕ} (P : C → ℝ) (cond : C → V → ℝ)
    (h : C → Fin k → ℝ) (w : V → Fin k → ℝ) : ℝ :=
  ∑ c, P c * ∑ v, cond c v * ntpLoss w (h c) v

/-! ### Appendix C: subsample intervals -/

/-- Appendix C ("Uncertainty on WIT"): the mean `(1/N) ∑ᵢ xᵢ` of a score over the full set of `N`
pairs. -/
def popMean {N : ℕ} (x : Fin N → ℝ) : ℝ := (∑ i, x i) / N

/-- Appendix C ("Uncertainty on WIT"): the mean of the score over a subset `S` of the pairs. -/
def subMean {N : ℕ} (x : Fin N → ℝ) (S : Finset (Fin N)) : ℝ := (∑ i ∈ S, x i) / S.card

/-- Appendix C ("Uncertainty on WIT"): the sample variance `s² = ∑ᵢ (xᵢ - x̄)² / (N - 1)`, so that
the standard error of the full score is `s / √N`. -/
def sampleVar {N : ℕ} (x : Fin N → ℝ) : ℝ := (∑ i, (x i - popMean x) ^ 2) / ((N : ℝ) - 1)

/-- Appendix C ("Uncertainty on WIT"): the spread of the score over uniformly random `n`-subsets
drawn without replacement around the full score,
`(E_S (x̄_S - x̄)²)^{1/2}`. -/
def subsampleSpread {N : ℕ} (x : Fin N → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt ((∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n, (subMean x S - popMean x) ^ 2) /
    (N.choose n))

end Arxiv2610_39302


