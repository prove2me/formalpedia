-- Prove2me | Definitions.Def_JEPAGeneralization_Basic
-- name    : JEPAGeneralization_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T04:41:09.445906+00:00
-- url     : https://prove2.me/theorems/c36bdf50-359f-4ba1-9f9a-7238f6eac18f
-- title:
--   Action-conditioned co-occurrence model, JEPA and spectral JEPA risks, planning regret and finite-sample objects
-- statement:
--   Objects of Section 3 and Appendix A.1 of Cui, Zhang, Wen, Cheng and Wang (2026).
--
--   1. **Observations, actions, embeddings.** The observation space is a finite set $\mathcal X$ and $\mathcal A$ is a set of actions. An encoder is a map $f:\mathcal X\to\mathbb R^k$ and a predictor is a map $g:\mathbb R^k\times\mathcal A\to\mathbb R^k$. We write $u^\top v=\sum_i u_iv_i$ and $\|v\|^2=\sum_i v_i^2$.
--   2. **Co-occurrence model (Section 3.1).** For each action $a$, $w(x,x^+,a)=\mathrm P(x,x^+\mid a)\ge0$ is the joint law of a current observation $x\sim\mathrm P_X$ and the next observation $x^+\sim\mathrm P(\cdot\mid x,a)$. Hence $\sum_{x^+}w(x,x^+,a)=w(x)=\mathrm P_X(x)$ for every $a$, with $\sum_xw(x)=1$. The second marginal is $w(x^+\mid a)=\sum_xw(x,x^+,a)$ and the transition probability is $\mathrm P(x^+\mid x,a)=w(x,x^+,a)/w(x)$. Both marginals are required to be positive.
--   3. **Co-occurrence matrices.** $M(a)=(w(x,x^+,a))_{x,x^+}$, and $\bar M(a)=D^{-1/2}M(a)D_+(a)^{-1/2}$ with $D=\mathrm{diag}(w(x))$ and $D_+(a)=\mathrm{diag}(w(x^+\mid a))$, that is $\bar M(a)_{x,x^+}=w(x,x^+,a)/\sqrt{w(x)w(x^+\mid a)}$. Its singular values are $\sigma_1(a)\ge\sigma_2(a)\ge\dots\ge\sigma_{|\mathcal X|}(a)\ge0$, the square roots of the eigenvalues of $\bar M(a)^\top\bar M(a)$, counted with multiplicity.
--   4. **Risks (eq. 3 and Theorem 3.1).** The JEPA risk is
--   $$\mathcal R_{\mathrm{JEPA}}(f,g,a)=\sum_{x,x^+}w(x,x^+,a)\,\|g(f(x),a)-f(x^+)\|^2+\sum_{x,x'}w(x)\,w(x'\mid a)\,\big[g(f(x),a)^\top f(x')\big]^2.$$
--   With $F=[\sqrt{w(x\mid a)}\,f(x)]_{x\in\mathcal X}$ and $G(F,a)=[\sqrt{w(x)}\,g(f(x),a)]_{x\in\mathcal X}$ (two $k\times|\mathcal X|$ matrices), the spectral JEPA risk is $\mathcal R_{\mathrm{S\text{-}JEPA}}(f,g,a)=\|\bar M(a)-G(F,a)^\top F\|_F^2$. The pair $(f,g)$ is normalized at $a$ if $\|f(x)\|=\|g(f(x),a)\|=1$ for all $x$. The spectral loss is $\mathbb E\big[(g(f(z),a)^\top f(z'))^2-2g(f(z),a)^\top f(z^+)\big]$ with $z\sim\mathrm P_X$, $z^+\sim\mathrm P(\cdot\mid z,a)$ and an independent $z'\sim w(\cdot\mid a)$.
--   5. **Single-step planning (Sections 3.2–3.3, $T=1$).** The planning loss is $\mathcal L_{\mathrm{plan}}(a;f,g,x_0,x_g)=\|g(f(x_0),a)-f(x_g)\|^2$, the value is $V(a)=w(x_0,x_g,a)/w(x_0)$ and the regret is $r(a)=\max_{a'}V(a')-V(a)$. For a law $\rho$ of $(x_0,x_g)$ and an action rule $\tilde a(x_0,x_g)$, $\mathcal E(\tilde a)=\mathbb E_{(x_0,x_g)\sim\rho}\,r(\tilde a(x_0,x_g))$ and $c_0=\mathbb E_{(x_0,x_g)\sim\rho}\sqrt{\max_aw(x_g\mid a)/w(x_0)}$.
--   6. **Finite-sample objects (Appendix A.1).** For a dataset $x_1,\dots,x_n$ (probability $\prod_i\mathrm P_X(x_i)$), $\hat{\mathcal R}_n$ is the empirical JEPA risk of Definition A.1, with the uniform law on the dataset and the uniform law on ordered pairs $(x_i,x_j)$, $i\ne j$. For $n=2m$, Definition A.3 draws a uniform permutation $\pi$ and sets $z_i=x_{\pi(2i-1)}$, $z_i^+\sim\mathrm P(\cdot\mid z_i,a)$ and $z_i'\sim\mathrm P(\cdot\mid x_{\pi(2i)},a)$. The tuple risk is $\hat{\mathcal R}_S=\frac1m\sum_{i\le m}\big[(g(f(z_i),a)^\top f(z_i'))^2-2g(f(z_i),a)^\top f(z_i^+)\big]$. Unconditionally the $m$ tuples are i.i.d. with law $w(z,z^+,a)\,w(z'\mid a)$.
--   7. **Rademacher complexities (Theorem 4.4).** For a class $\Phi$ of real functions on $\mathcal X$, the worst-case Rademacher complexity is $\max_{z_1,\dots,z_m}\mathbb E_\sigma\sup_{\varphi\in\Phi}\frac1m\sum_i\sigma_i\varphi(z_i)$, with $\sigma_i$ i.i.d. uniform signs. $\mathfrak R_m(\mathcal F)$ is its maximum over coordinates $\ell$ of the classes $\{f_\ell:f\in\mathcal F\}$, and $\mathfrak R_m(\mathcal G\circ\mathcal F)$ is its maximum over coordinates $\ell$ of the classes $\{x\mapsto g(f(x),a)_\ell:f\in\mathcal F,g\in\mathcal G\}$.
--
--   **Formalization Note** The singular values are the square roots of the roots of the characteristic polynomial of $\bar M(a)^\top\bar M(a)$, sorted in decreasing order and zero-indexed, so the Lean `singVal i` is $\sigma_{i+1}$. All expectations over finite sets are written as exact finite sums. The paper does not specify the law of $(x_0,x_g)$, so it is a parameter $\rho$. Suprema over a class use Lean's real supremum; every class used is nonempty and bounded.
-- source:
--   Cui, Zhang, Wen, Cheng and Wang, A Generalization Theory for JEPA-Based World Models, arXiv:2606.27014v2 (2026), Sections 3.1-3.4 (eqs. (3), (5)-(6), (8), (10)-(12)), Section 4 (Theorems 4.1, 4.3, 4.4) and Appendix A.1 (Definitions A.1, A.3)

import Mathlib

/-!
Cui, Zhang, Wen, Cheng and Wang, *A Generalization Theory for JEPA-Based World Models*,
arXiv:2606.27014v2 (2026): the action-conditioned co-occurrence model, the JEPA and spectral
JEPA risks, single-step planning and regret, the singular values of the normalized co-occurrence
matrix, and the finite-sample objects (sampled tuples, empirical risks, Rademacher complexities)
of Section 3 and Appendix A.1.

The observation space is a finite type `X` (the paper indexes the co-occurrence matrix by
observations and writes all expectations as finite sums), latent embeddings are vectors
`Fin k → ℝ`, an encoder is `f : X → Fin k → ℝ` and a predictor is
`g : (Fin k → ℝ) → A → Fin k → ℝ`.
-/

noncomputable section

namespace JEPAGeneralization

variable {X A : Type*} [Fintype X] {k : ℕ}

/-- Euclidean inner product `uᵀv` of two latent vectors in `ℝ^k`. -/
def dot (u v : Fin k → ℝ) : ℝ := ∑ i, u i * v i

/-- Squared Euclidean norm `‖v‖²` of a latent vector in `ℝ^k`. -/
def sqNorm (v : Fin k → ℝ) : ℝ := ∑ i, v i ^ 2

/-- Section 3.1, p. 4: `w(x, x⁺, a) = P(x, x⁺ | a) ≥ 0` is the joint law of a current and a next
observation given the action `a`, with `x ∼ P_X` for every action, so that the first marginal
`w(x) = ∑_{x⁺} w(x, x⁺, a)` equals `P_X(x)` and does not depend on `a`. The normalization
`D^{-1/2} M(a) D_+(a)^{-1/2}` requires the marginals `w(x)` and `w(x⁺ | a)` to be positive;
this is written in. -/
def IsCoOccurrence (pX : X → ℝ) (w : X → X → A → ℝ) : Prop :=
  (∀ x x' a, 0 ≤ w x x' a) ∧ (∑ x, pX x = 1) ∧ (∀ x, 0 < pX x) ∧
    (∀ x a, ∑ x', w x x' a = pX x) ∧ (∀ x' a, 0 < ∑ x, w x x' a)

/-- Section 3.1, p. 4: the second marginal `w(x⁺ | a) = ∑_x w(x, x⁺, a) = P_{X|a}(x⁺)`. -/
def nextMarg (w : X → X → A → ℝ) (a : A) (x' : X) : ℝ := ∑ x, w x x' a

/-- Section 3.1–3.3: the transition probability `P(x⁺ | x, a) = w(x, x⁺, a) / w(x)`. -/
def transProb (pX : X → ℝ) (w : X → X → A → ℝ) (a : A) (x x' : X) : ℝ := w x x' a / pX x

/-- Section 3.1, eq. (5), p. 4: the conditional co-occurrence matrix
`M(a) = (w(x, x⁺, a))_{x, x⁺}`. -/
def coOccMat (w : X → X → A → ℝ) (a : A) : Matrix X X ℝ := fun x x' => w x x' a

/-- Section 3.1, p. 4: the normalized co-occurrence matrix `M̄(a) = D^{-1/2} M(a) D_+(a)^{-1/2}`
with `D = diag(w(x))` and `D_+(a) = diag(w(x⁺ | a))`, written entrywise as
`w(x, x⁺, a) / √(w(x) w(x⁺ | a))`. -/
def normCoOcc (pX : X → ℝ) (w : X → X → A → ℝ) (a : A) : Matrix X X ℝ :=
  fun x x' => coOccMat w a x x' / Real.sqrt (pX x * nextMarg w a x')

/-- Section 3.1, eq. (3), p. 3: the population JEPA risk
`R_JEPA(f, g, a) = E_{x∼P_X} E_{x⁺∼P(·|x,a)} ‖g(f(x), a) − f(x⁺)‖²
  + E_{x∼P_X, x'∼P_{X|a}} [g(f(x), a)ᵀ f(x')]²`, written as finite sums. -/
def jepaRisk (pX : X → ℝ) (w : X → X → A → ℝ) (f : X → Fin k → ℝ)
    (g : (Fin k → ℝ) → A → Fin k → ℝ) (a : A) : ℝ :=
  (∑ x, ∑ x', w x x' a * sqNorm (g (f x) a - f x')) +
    ∑ x, ∑ x', pX x * nextMarg w a x' * dot (g (f x) a) (f x') ^ 2

/-- Theorem 3.1, p. 4: the `k × |X|` matrix `F = [√(w(x | a)) f(x)]_{x ∈ X}`. -/
def encMat (w : X → X → A → ℝ) (f : X → Fin k → ℝ) (a : A) : Matrix (Fin k) X ℝ :=
  fun i x => Real.sqrt (nextMarg w a x) * f x i

/-- Theorem 3.1, p. 4: the `k × |X|` matrix `G(F, a) = [√(w(x)) g(f(x), a)]_{x ∈ X}`. -/
def predMat (pX : X → ℝ) (f : X → Fin k → ℝ) (g : (Fin k → ℝ) → A → Fin k → ℝ) (a : A) :
    Matrix (Fin k) X ℝ :=
  fun i x => Real.sqrt (pX x) * g (f x) a i

/-- The squared Frobenius norm `‖B‖_F² = ∑_{x, x'} B_{x x'}²` of a real `X × X` matrix. -/
def frobSq (B : Matrix X X ℝ) : ℝ := ∑ x, ∑ x', B x x' ^ 2

/-- Section 3.1, p. 4 (after Theorem 3.1): the spectral JEPA (matrix factorization) risk
`R_{S-JEPA}(f, g, a) = ‖M̄(a) − G(F, a)ᵀ F‖_F²`. -/
def sJepaRisk (pX : X → ℝ) (w : X → X → A → ℝ) (f : X → Fin k → ℝ)
    (g : (Fin k → ℝ) → A → Fin k → ℝ) (a : A) : ℝ :=
  frobSq (normCoOcc pX w a - (predMat pX f g a).transpose * encMat w f a)

/-- Theorem 3.1, p. 4: the embeddings `f(x)` and `g(f(x), a)` are normalized,
`‖f(x)‖ = ‖g(f(x), a)‖ = 1` for every observation `x`. -/
def IsNormalized (f : X → Fin k → ℝ) (g : (Fin k → ℝ) → A → Fin k → ℝ) (a : A) : Prop :=
  ∀ x, sqNorm (f x) = 1 ∧ sqNorm (g (f x) a) = 1

/-- The squared singular values `σ₁(a)² ≥ σ₂(a)² ≥ …` of `M̄(a)` with multiplicity: the
eigenvalues of `M̄(a)ᵀ M̄(a)`, i.e. the roots of its characteristic polynomial, sorted in
decreasing order (a list of length `|X|`). -/
def sqSingVals [DecidableEq X] (pX : X → ℝ) (w : X → X → A → ℝ) (a : A) : List ℝ :=
  ((normCoOcc pX w a).transpose * normCoOcc pX w a).charpoly.roots.sort (· ≥ ·)

/-- Theorem 4.3, p. 6: the singular values of `M̄(a)` in decreasing order, zero-indexed:
`singVal pX w a i = σ_{i+1}(a)` for `i < |X|` (and `0` for `i ≥ |X|`, never used). -/
def singVal [DecidableEq X] (pX : X → ℝ) (w : X → X → A → ℝ) (a : A) (i : ℕ) : ℝ :=
  Real.sqrt ((sqSingVals pX w a).getD i 0)

/-- Section 3.2, eq. (8), p. 4, for `T = 1`: the planning loss
`L_plan(a; f, g, x₀, x_g) = ‖g(f(x₀), a) − f(x_g)‖²`. -/
def planLoss1 (f : X → Fin k → ℝ) (g : (Fin k → ℝ) → A → Fin k → ℝ) (a : A) (x0 xg : X) : ℝ :=
  sqNorm (g (f x0) a - f xg)

/-- Section 3.3, eq. (10), p. 5, for `T = 1`: the value
`V(a) = P(x̂₁ = x_g | x₀, a) = w(x₀, x_g, a) / w(x₀)` of action `a` from `x₀` to the goal `x_g`. -/
def value1 (pX : X → ℝ) (w : X → X → A → ℝ) (a : A) (x0 xg : X) : ℝ := w x0 xg a / pX x0

/-- Section 3.3, eq. (11), p. 5, for `T = 1`: the pointwise regret
`r(a; x₀, x_g) = V(a**) − V(a)` with `V(a**) = max_{a'} V(a')`. -/
def regret1 (pX : X → ℝ) (w : X → X → A → ℝ) (a : A) (x0 xg : X) : ℝ :=
  (⨆ a' : A, value1 pX w a' x0 xg) - value1 pX w a x0 xg

/-- A probability law `ρ` of the pair `(x₀, x_g)` of initial and goal observations, with respect
to which `E_{x₀, x_g}` is taken in Section 3.3 (the paper does not specify it). -/
def IsPairDist (ρ : X → X → ℝ) : Prop :=
  (∀ x0 xg, 0 ≤ ρ x0 xg) ∧ ∑ x0, ∑ xg, ρ x0 xg = 1

/-- Section 3.3, eq. (12), p. 5, for `T = 1`: the expected planning regret
`E(ã) = E_{x₀, x_g} r(ã(x₀, x_g); x₀, x_g)` of an action rule `ã`, which may depend on
`(x₀, x_g)`. -/
def expRegret1 (pX : X → ℝ) (w : X → X → A → ℝ) (ρ : X → X → ℝ) (act : X → X → A) : ℝ :=
  ∑ x0, ∑ xg, ρ x0 xg * regret1 pX w (act x0 xg) x0 xg

/-- Theorem 4.1, p. 5: the constant `c₀ = E_{x₀, x_g} √(max_a w(x_g | a) / w(x₀))`. -/
def cZero (pX : X → ℝ) (w : X → X → A → ℝ) (ρ : X → X → ℝ) : ℝ :=
  ∑ x0, ∑ xg, ρ x0 xg * Real.sqrt ((⨆ a : A, nextMarg w a xg) / pX x0)

/-- Proof of Theorem 4.4, p. 15: the population spectral loss
`E[(g(f(z), a)ᵀ f(z'))² − 2 g(f(z), a)ᵀ f(z⁺)]` with `z ∼ P_X`, `z⁺ ∼ P(·|z, a)` and
`z' ∼ P_{X|a}` independent of `(z, z⁺)`; the quantity `R(f, g, a)` of Lemma A.2. -/
def spectralLoss (pX : X → ℝ) (w : X → X → A → ℝ) (f : X → Fin k → ℝ)
    (g : (Fin k → ℝ) → A → Fin k → ℝ) (a : A) : ℝ :=
  (∑ x, ∑ x', pX x * nextMarg w a x' * dot (g (f x) a) (f x') ^ 2) -
    2 * ∑ x, ∑ x', w x x' a * dot (g (f x) a) (f x')

/-- Definition A.1, eq. (26), p. 12: the empirical JEPA risk of a dataset `x₁, …, xₙ`,
`R̂ₙ(f, g, a) = −2 E_{x∼P̂_X, x⁺∼P(·|x,a)} [g(f(x), a)ᵀ f(x⁺)]
  + E_{(x, x⁻)∼P̂_{x,x⁻}, x'∼P(·|x⁻,a)} [g(f(x), a)ᵀ f(x')]²`, where `P̂_X` is uniform on the
dataset and `P̂_{x,x⁻}` is uniform on the ordered pairs `(xᵢ, xⱼ)`, `i ≠ j`. The expectations over
`x⁺` and `x'` are exact sums against the transition probabilities. -/
def empRiskN (pX : X → ℝ) (w : X → X → A → ℝ) (f : X → Fin k → ℝ)
    (g : (Fin k → ℝ) → A → Fin k → ℝ) (a : A) {n : ℕ} (D : Fin n → X) : ℝ :=
  -2 * ((1 / (n : ℝ)) * ∑ i, ∑ x', transProb pX w a (D i) x' * dot (g (f (D i)) a) (f x')) +
    (1 / ((n : ℝ) * ((n : ℝ) - 1))) * ∑ i, ∑ j,
      (if i = j then 0 else
        ∑ x', transProb pX w a (D j) x' * dot (g (f (D i)) a) (f x') ^ 2)

/-- Definition A.1, p. 12: the probability `∏ᵢ P_X(xᵢ)` of a dataset `x₁, …, xₙ` drawn i.i.d.
from `P_X`. -/
def datasetProb (pX : X → ℝ) {n : ℕ} (D : Fin n → X) : ℝ := ∏ i, pX (D i)

/-- Definition A.3, eq. (29), p. 12: the tuple loss
`(g(f(z), a)ᵀ f(z'))² − 2 g(f(z), a)ᵀ f(z⁺)` of a tuple `t = (z, z⁺, z')`. -/
def tupleLoss (f : X → Fin k → ℝ) (g : (Fin k → ℝ) → A → Fin k → ℝ) (a : A)
    (t : X × X × X) : ℝ :=
  dot (g (f t.1) a) (f t.2.2) ^ 2 - 2 * dot (g (f t.1) a) (f t.2.1)

/-- Definition A.3, eq. (29), p. 12: the tuple risk
`R̂_S(f, g, a) = (1/m) ∑_{i=1}^m [(g(f(zᵢ), a)ᵀ f(zᵢ'))² − 2 g(f(zᵢ), a)ᵀ f(zᵢ⁺)]` of
`S = ((zᵢ, zᵢ⁺, zᵢ'))_{i ≤ m}`, `m = n/2`. -/
def empRiskS (f : X → Fin k → ℝ) (g : (Fin k → ℝ) → A → Fin k → ℝ) (a : A) {m : ℕ}
    (S : Fin m → X × X × X) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, tupleLoss f g a (S i)

/-- Definition A.3, eq. (28), p. 12: the indices `(π(2i−1), π(2i))` (zero-indexed:
`(π(2i), π(2i+1))`) of the `i`-th pair of the permuted dataset, `i < m`, `n = 2m`. -/
def pairIdx {m : ℕ} (π : Equiv.Perm (Fin (2 * m))) (i : Fin m) : Fin (2 * m) × Fin (2 * m) :=
  (π ⟨2 * i.val, by have := i.isLt; omega⟩, π ⟨2 * i.val + 1, by have := i.isLt; omega⟩)

/-- Lemma A.4, eq. (30), p. 12: `E_S R̂_S(f, g, a)` given the dataset `x₁, …, x_{2m}`, for the
sampling of Definition A.3: a uniform permutation `π` of the indices, `zᵢ = x_{π(2i−1)}`,
`zᵢ⁺ ∼ P(·|zᵢ, a)` and `zᵢ' ∼ P(·|x_{π(2i)}, a)`, all draws independent given `π`. -/
def expEmpRiskS (pX : X → ℝ) (w : X → X → A → ℝ) (f : X → Fin k → ℝ)
    (g : (Fin k → ℝ) → A → Fin k → ℝ) (a : A) {m : ℕ} (D : Fin (2 * m) → X) : ℝ :=
  (1 / ((Nat.factorial (2 * m) : ℕ) : ℝ)) * ∑ π : Equiv.Perm (Fin (2 * m)),
    ∑ zp : Fin m → X, ∑ zq : Fin m → X,
      (∏ i, transProb pX w a (D (pairIdx π i).1) (zp i) *
          transProb pX w a (D (pairIdx π i).2) (zq i)) *
        empRiskS f g a (fun i => (D (pairIdx π i).1, zp i, zq i))

/-- Definition A.3, p. 12: the law of one sampled tuple `(z, z⁺, z')`:
`P(z, z⁺, z') = w(z, z⁺, a) · w(z' | a)`, since `z ∼ P_X`, `z⁺ ∼ P(·|z, a)` and
`z' ∼ P(·|x, a)` for an independent `x ∼ P_X`. -/
def tupleProb (w : X → X → A → ℝ) (a : A) (t : X × X × X) : ℝ :=
  w t.1 t.2.1 a * nextMarg w a t.2.2

open Classical in
/-- Definition A.3 and Theorem 4.4, p. 6: the probability of an event `E` about the sample
`S = ((zᵢ, zᵢ⁺, zᵢ'))_{i ≤ m}` of `m = n/2` tuples. The tuples of Definition A.3 come from disjoint
pairs of an i.i.d. dataset, so they are i.i.d. with law `tupleProb w a`. -/
def sampleProb (w : X → X → A → ℝ) (a : A) (m : ℕ) (E : (Fin m → X × X × X) → Prop) : ℝ :=
  ∑ S : Fin m → X × X × X, if E S then ∏ i, tupleProb w a (S i) else 0

/-- Theorem 4.4, p. 6: the empirical Rademacher average
`E_σ [sup_{φ ∈ H} (1/m) ∑_{i=1}^m σᵢ φ(zᵢ)]` of a class `H` of real functions at the points
`z₁, …, z_m`, with `σᵢ` i.i.d. uniform signs (`true ↦ +1`, `false ↦ −1`). -/
def empRad (m : ℕ) (H : Set (X → ℝ)) (z : Fin m → X) : ℝ :=
  (1 / 2 ^ m : ℝ) * ∑ σ : Fin m → Bool,
    ⨆ φ : H, (1 / (m : ℝ)) * ∑ i, (if σ i then (1 : ℝ) else -1) * φ.1 (z i)

/-- Theorem 4.4, p. 6: the worst-case Rademacher complexity `max_{z₁, …, z_m} E_σ […]` of a class
of real functions on `X`. -/
def worstRad (m : ℕ) (H : Set (X → ℝ)) : ℝ := ⨆ z : Fin m → X, empRad m H z

/-- The class `{x ↦ f(x)_ℓ : f ∈ 𝓕}` of `ℓ`-th coordinates of the encoders. -/
def encCoord (F : Set (X → Fin k → ℝ)) (l : Fin k) : Set (X → ℝ) :=
  {φ | ∃ f ∈ F, φ = fun x => f x l}

/-- Proof of Theorem 4.4, p. 15: the class `𝓗_{a,ℓ} = {x ↦ g(f(x), a)_ℓ : f ∈ 𝓕, g ∈ 𝓖}` of
`ℓ`-th coordinates of the composed predictions `h = g ∘ f ∘ a`. -/
def predCoord (F : Set (X → Fin k → ℝ)) (G : Set ((Fin k → ℝ) → A → Fin k → ℝ)) (a : A)
    (l : Fin k) : Set (X → ℝ) :=
  {φ | ∃ f ∈ F, ∃ g ∈ G, φ = fun x => g (f x) a l}

/-- Theorem 4.4, p. 6: `𝔑_m(𝓕) = max_ℓ max_{z₁, …, z_m} E_σ [sup_{f ∈ 𝓕} (1/m) ∑ᵢ σᵢ f_ℓ(zᵢ)]`. -/
def radEnc (m : ℕ) (F : Set (X → Fin k → ℝ)) : ℝ := ⨆ l : Fin k, worstRad m (encCoord F l)

/-- Proof of Theorem 4.4, pp. 15–16: the Rademacher complexity of the composed class
`𝓖 ∘ 𝓕` used in the proof, `max_ℓ max_{z₁, …, z_m} E_σ [sup_{f ∈ 𝓕, g ∈ 𝓖} (1/m) ∑ᵢ σᵢ g(f(zᵢ), a)_ℓ]`
(the coordinatewise complexity of `𝓗_a`, as `𝔑_m(𝓕)` is for `𝓕`). -/
def radPred (m : ℕ) (F : Set (X → Fin k → ℝ)) (G : Set ((Fin k → ℝ) → A → Fin k → ℝ)) (a : A) :
    ℝ :=
  ⨆ l : Fin k, worstRad m (predCoord F G a l)

end JEPAGeneralization


