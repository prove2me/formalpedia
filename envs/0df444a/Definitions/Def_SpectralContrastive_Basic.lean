-- Prove2me | Definitions.Def_SpectralContrastive_Basic
-- name    : SpectralContrastive_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T18:34:09.392318+00:00
-- url     : https://prove2.me/theorems/3fc70c74-35cc-41d3-8ce8-acc095c32975
-- title:
--   Augmentation graph, spectral contrastive loss, conductance and linear probe error
-- statement:
--   Objects of Sections 3.1-3.3, 4.1 and Appendices B, D.1 of HaoChen, Wei, Gaidon and Ma (2021).
--
--   1. **Data model.** The natural data form a finite set $\overline{\mathcal X}$ with population distribution $P$ ($P(\bar x)\ge0$, $\sum_{\bar x}P(\bar x)=1$). Each $\bar x$ has an augmentation distribution $\mathcal A(\cdot\mid\bar x)$ on the finite set $\mathcal X$ of augmented data ($N=|\mathcal X|$). The set $\mathcal X$ is the union of the supports of the $\mathcal A(\cdot\mid\bar x)$ with $P(\bar x)>0$. Labels are $y:\overline{\mathcal X}\to[r]$.
--   2. **Augmentation graph (eq. 2).** $w_{xx'}=\mathbb E_{\bar x\sim P}[\mathcal A(x\mid\bar x)\mathcal A(x'\mid\bar x)]$, with degree $w_x=\sum_{x'}w_{xx'}$. A general weighted graph $(V,w)$ has nonnegative symmetric weights and positive degrees.
--   3. **Spectra (eq. 3, Definition B.1).** $\overline A=D^{-1/2}AD^{-1/2}$ with $A_{xx'}=w_{xx'}$ and $D=\mathrm{diag}(w_x)$, and $\mathcal L=I-\overline A$. $\gamma_i$ is the $i$-th largest eigenvalue of $\overline A$ and $\lambda_i$ the $i$-th smallest eigenvalue of $\mathcal L$ ($i\ge1$, with multiplicity).
--   4. **Conductance (Definitions 3.3, 3.4).** For a set $S$, $\phi_G(S)=\sum_{x\in S,x'\notin S}w_{xx'}/\sum_{x\in S}w_x$. For $i\ge1$, $\rho_i=\min\max_j\phi_G(S_j)$, the minimum over partitions of the vertex set into $i$ nonempty sets $S_1,\dots,S_i$.
--   5. **Losses (eqs. 4, 6).** The spectral contrastive loss is
--   $$\mathcal L(f)=-2\,\mathbb E_{x,x^+}[f(x)^\top f(x^+)]+\mathbb E_{x,x^-}[(f(x)^\top f(x^-))^2]$$
--   for $f:\mathcal X\to\mathbb R^k$. Here $x,x^+\sim\mathcal A(\cdot\mid\bar x)$ independently with $\bar x\sim P$, and $x^-\sim\mathcal A(\cdot\mid\bar x')$ with an independent $\bar x'\sim P$. The matrix factorization loss is $\mathcal L_{\mathrm{mf}}(F)=\|\overline A-FF^\top\|_F^2$ for $F\in\mathbb R^{N\times k}$.
--   6. **Linear probes (eq. 1).** A head $B\in\mathbb R^{k\times r}$ predicts $g_{f,B}(x)\in\arg\max_i(f(x)^\top B)_i$ on augmented data and $\bar g_{f,B}(\bar x)\in\arg\max_i\Pr_{x\sim\mathcal A(\cdot\mid\bar x)}[g_{f,B}(x)=i]$ on natural data, with ties broken arbitrarily. The error is $\mathcal E(f,B)=\Pr_{\bar x\sim P}[y(\bar x)\ne\bar g_{f,B}(\bar x)]$, and the linear probe error is $\mathcal E(f)=\min_B\mathcal E(f,B)$.
--   7. **Label quantities (eqs. 18, 19).** For $\hat y:\mathcal X\to[r]$, $\phi^{\hat y}=\sum_{x,x'}w_{xx'}\mathbf 1[\hat y(x)\ne\hat y(x')]$ and $\Delta(y,\hat y)=\Pr_{\bar x\sim P,\,x\sim\mathcal A(\cdot\mid\bar x)}(\hat y(x)\ne y(\bar x))$. The squared probe loss is $\mathbb E_{\bar x,x}\|\vec y(\bar x)-B^\top f(x)\|_2^2$, where $\vec y$ is the one-hot vector, and $\|B\|_F$ is the Frobenius norm.
--   8. **Finite samples (Section 4.1).** For a dataset $\bar x_1,\dots,\bar x_n$ the empirical loss is
--   $$\widehat{\mathcal L}_n(f)=-\frac2n\sum_i\mathbb E_{x,x^+\sim\mathcal A(\cdot\mid\bar x_i)}[f(x)^\top f(x^+)]+\frac1{n(n-1)}\sum_{i\ne j}\mathbb E_{x\sim\mathcal A(\cdot\mid\bar x_i),\,x^-\sim\mathcal A(\cdot\mid\bar x_j)}[(f(x)^\top f(x^-))^2].$$
--   The Rademacher complexity is $\widehat{\mathcal R}_m(\mathcal F)=\max_{x_1,\dots,x_m}\mathbb E_\sigma[\sup_{f\in\mathcal F,\,i\in[k]}\frac1m\sum_j\sigma_jf_i(x_j)]$ with $\sigma$ uniform on $\{\pm1\}^m$. Dataset probabilities are taken under $P^{\otimes n}$.
--
--   **Formalization Note** Eigenvalues are the roots of the characteristic polynomial, sorted; indices outside $1,\dots,N$ give the value $0$. The sparsest $i$-partition value $\rho_i$ is likewise $0$ for $i>N$ (no surjection exists) and equals $\phi(\mathcal X)=0$ for $i=1$. Most statements exclude these values by hypothesis; Theorem B.2 (no condition $k\le N$, so $\lambda_k$ may be the value $0$) and part 2 of Theorem 3.8 (where $\rho_{\lfloor k/2\rfloor}$ may be $0$) do not, and remain true in those cases. A partition into $i$ nonempty sets is a surjection $\mathcal X\to\mathrm{Fin}\,i$. Because the paper breaks argmax ties arbitrarily, $\mathcal E(f,B)$ is defined as the largest error over all admissible tie-breaking choices at both levels, so every bound proved for it holds for every tie-breaking rule. Linear heads are $k\times r$ matrices acting by $f(x)^\top B$ as in Section 3; the $r\times k$ heads $B^*$ of Appendix B are their transposes, with the same Frobenius norm.
-- source:
--   HaoChen, Wei, Gaidon and Ma, Provable Guarantees for Self-Supervised Deep Learning with Spectral Contrastive Loss, arXiv:2106.04156v7 (NeurIPS 2021), Sections 3.1-3.3 (eqs. (1)-(6), Definitions 3.3-3.4, Assumptions 3.5-3.7), Section 4.1, Appendix B.1 (Definition B.1, eqs. (18)-(19)), Appendix D.1 (Definition D.1)

import Mathlib

/-!
HaoChen, Wei, Gaidon and Ma, *Provable Guarantees for Self-Supervised Deep Learning with Spectral
Contrastive Loss*, arXiv:2106.04156v7 (NeurIPS 2021): the finite natural/augmented data model,
the population augmentation graph, its normalized adjacency and Laplacian matrices and their
eigenvalues, Dirichlet conductance and sparsest partitions, the spectral contrastive and matrix
factorization losses, linear probes and their errors (Sections 3.1-3.3 and Appendix B), and the
empirical loss and Rademacher complexity of Section 4.1 and Appendix D.1.
-/

noncomputable section

namespace SpectralContrastive

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Section 3.1: the total weight (degree) `w_x = ∑_{x'} w_{xx'}` of a vertex. -/
def degree (w : V → V → ℝ) (x : V) : ℝ := ∑ x', w x x'

/-- Lemma B.4 (p. 27): `G = (V, w)` is a weighted graph: the edge weights are nonnegative and
symmetric, and every vertex has positive total weight (so that `D^{-1/2}` exists). -/
def IsWeightedGraph (w : V → V → ℝ) : Prop :=
  (∀ x x', 0 ≤ w x x') ∧ (∀ x x', w x x' = w x' x) ∧ (∀ x, 0 < degree w x)

/-- Eq. (3), p. 7: the normalized adjacency matrix `Ā = D^{-1/2} A D^{-1/2}`, with
`A_{xx'} = w_{xx'}` and `D = diag(w_x)`. -/
def normAdj (w : V → V → ℝ) : Matrix V V ℝ :=
  fun x x' => w x x' / Real.sqrt (degree w x * degree w x')

/-- Definition B.1, p. 26: the normalized Laplacian matrix `L = I - D^{-1/2} A D^{-1/2}`. -/
def normLap (w : V → V → ℝ) : Matrix V V ℝ := 1 - normAdj w

/-- Section 3.1, p. 7: `γ_i`, the `i`-th largest eigenvalue of `Ā` (`i = 1, 2, …`), counted with
multiplicity, as the roots of the characteristic polynomial sorted in decreasing order. Statements
only use `1 ≤ i ≤ |V|`. -/
def adjEig (w : V → V → ℝ) (i : ℕ) : ℝ :=
  ((normAdj w).charpoly.roots.sort (· ≥ ·)).getD (i - 1) 0

/-- Appendix B.1, p. 26: `λ_i`, the `i`-th smallest eigenvalue of `L` (`i = 1, 2, …`), counted
with multiplicity, as the roots of the characteristic polynomial sorted in increasing order.
Statements only use `1 ≤ i ≤ |V|`. -/
def lapEig (w : V → V → ℝ) (i : ℕ) : ℝ :=
  ((normLap w).charpoly.roots.sort (· ≤ ·)).getD (i - 1) 0

/-- Definition 3.3, p. 10: the Dirichlet conductance
`φ_G(S) = (∑_{x ∈ S, x' ∉ S} w_{xx'}) / (∑_{x ∈ S} w_x)`. -/
def conductance (w : V → V → ℝ) (S : Finset V) : ℝ :=
  (∑ x ∈ S, ∑ x' ∈ Sᶜ, w x x') / ∑ x ∈ S, degree w x

/-- Definition 3.4, p. 10: the sparsest `i`-partition
`ρ_i = min_{S_1, …, S_i} max_j φ_G(S_j)`, the minimum over partitions of `V` into `i` nonempty
sets. A partition is encoded by a surjective labelling `σ : V → Fin i`, with `S_j = σ⁻¹(j)`. -/
def sparsestPartition (w : V → V → ℝ) (i : ℕ) : ℝ :=
  ⨅ σ : {σ : V → Fin i // Function.Surjective σ},
    ⨆ j : Fin i, conductance w (Finset.univ.filter fun x => σ.1 x = j)

/-- Eq. (18), p. 26: `φ^ŷ = ∑_{x,x'} w_{xx'} 1[ŷ(x) ≠ ŷ(x')]` for an extended labeling
function `ŷ`. -/
def cutWeight {r : ℕ} (w : V → V → ℝ) (yhat : V → Fin r) : ℝ :=
  ∑ x, ∑ x', w x x' * if yhat x ≠ yhat x' then 1 else 0

end Graph

section Model

variable {Xbar X : Type*} [Fintype Xbar] [Fintype X] [DecidableEq X]

/-- Section 3, pp. 6-7: the finite data model. `P` is the population distribution `P_X̄` on the
natural data, `A x̄ x = 𝒜(x | x̄)` is the augmentation distribution of `x̄`, and the set `X` of
augmented data is the union of the supports of the `𝒜(· | x̄)`, `x̄` in the support of `P`. -/
def IsAugModel (P : Xbar → ℝ) (A : Xbar → X → ℝ) : Prop :=
  (∀ xb, 0 ≤ P xb) ∧ (∑ xb, P xb = 1) ∧ (∀ xb x, 0 ≤ A xb x) ∧ (∀ xb, ∑ x, A xb x = 1) ∧
    (∀ x, ∃ xb, 0 < P xb ∧ 0 < A xb x)

/-- Eq. (2), p. 7: the edge weights of the population augmentation graph,
`w_{xx'} = E_{x̄ ∼ P}[𝒜(x | x̄) 𝒜(x' | x̄)]`. -/
def augWeight (P : Xbar → ℝ) (A : Xbar → X → ℝ) (x x' : X) : ℝ :=
  ∑ xb, P xb * A xb x * A xb x'

/-- Eq. (6), p. 9 (written out on p. 26): the population spectral contrastive loss
`L(f) = -2 E_{x, x⁺}[f(x)ᵀ f(x⁺)] + E_{x, x⁻}[(f(x)ᵀ f(x⁻))²]`, where `x, x⁺ ∼ 𝒜(· | x̄)`
independently for `x̄ ∼ P`, and `x⁻ ∼ 𝒜(· | x̄')` for an independent `x̄' ∼ P`. -/
def scLoss {k : ℕ} (P : Xbar → ℝ) (A : Xbar → X → ℝ) (f : X → Fin k → ℝ) : ℝ :=
  -2 * (∑ xb, P xb * ∑ x, ∑ x', A xb x * A xb x' * ∑ i, f x i * f x' i) +
    ∑ xb, ∑ xb', P xb * P xb' * ∑ x, ∑ x', A xb x * A xb' x' * (∑ i, f x i * f x' i) ^ 2

/-- Eq. (4), p. 8: the matrix factorization loss `L_mf(F) = ‖Ā - F Fᵀ‖_F²` of an embedding
matrix `F ∈ ℝ^{N × k}` (row `x` of `F` is `F x`). -/
def mfLoss {k : ℕ} (w : X → X → ℝ) (F : X → Fin k → ℝ) : ℝ :=
  ∑ x, ∑ x', (normAdj w x x' - ∑ i, F x i * F x' i) ^ 2

/-- Section 3, p. 6: `i` is a prediction of the linear classifier `B ∈ ℝ^{k × r}` on the
representation `f(x)`, i.e. an index maximising `(f(x)ᵀ B)_i`. The paper breaks ties
arbitrarily; `g` is any such choice. -/
def IsProbePred {k r : ℕ} (f : X → Fin k → ℝ) (B : Matrix (Fin k) (Fin r) ℝ)
    (g : X → Fin r) : Prop :=
  ∀ x i, Matrix.vecMul (f x) B i ≤ Matrix.vecMul (f x) B (g x)

/-- Section 3, p. 6: `Pr_{x ∼ 𝒜(·|x̄)}[g(x) = i]`, the vote of the augmentations of `x̄`
for class `i`. -/
def votes {r : ℕ} (A : Xbar → X → ℝ) (g : X → Fin r) (xb : Xbar) (i : Fin r) : ℝ :=
  ∑ x, A xb x * if g x = i then 1 else 0

/-- Section 3, p. 6: `ḡ(x̄) = argmax_i Pr_{x ∼ 𝒜(·|x̄)}[g(x) = i]`, the ensembled prediction on
natural data (ties broken arbitrarily; `gbar` is any such choice). -/
def IsEnsemblePred {r : ℕ} (A : Xbar → X → ℝ) (g : X → Fin r) (gbar : Xbar → Fin r) : Prop :=
  ∀ xb i, votes A g xb i ≤ votes A g xb (gbar xb)

/-- Section 3, p. 6: `Pr_{x̄ ∼ P}[y(x̄) ≠ ḡ(x̄)]`. -/
def ensembleError {r : ℕ} (P : Xbar → ℝ) (y : Xbar → Fin r) (gbar : Xbar → Fin r) : ℝ :=
  ∑ xb, P xb * if gbar xb ≠ y xb then 1 else 0

/-- Section 3, p. 6: the error `E(f, B) = Pr_{x̄ ∼ P}[y(x̄) ≠ ḡ_{f,B}(x̄)]` of the representation
`f` with the linear head `B`. Since the paper breaks ties arbitrarily, this is the largest error
over all tie-breaking choices, so that a bound on it holds for every tie-breaking rule. -/
def probeError {k r : ℕ} (P : Xbar → ℝ) (A : Xbar → X → ℝ) (y : Xbar → Fin r)
    (f : X → Fin k → ℝ) (B : Matrix (Fin k) (Fin r) ℝ) : ℝ :=
  ⨆ c : {c : (X → Fin r) × (Xbar → Fin r) // IsProbePred f B c.1 ∧ IsEnsemblePred A c.1 c.2},
    ensembleError P y c.1.2

/-- Eq. (1), p. 6: the linear probe error `E(f) = min_{B ∈ ℝ^{k × r}} E(f, B)`. -/
def linearProbeError {k r : ℕ} (P : Xbar → ℝ) (A : Xbar → X → ℝ) (y : Xbar → Fin r)
    (f : X → Fin k → ℝ) : ℝ :=
  ⨅ B : Matrix (Fin k) (Fin r) ℝ, probeError P A y f B

/-- Eq. (19), p. 26: `Δ(y, ŷ) = Pr_{x̄ ∼ P, x ∼ 𝒜(·|x̄)}(ŷ(x) ≠ y(x̄))`. With `ŷ = g` this is
also the error of a classifier `g` on augmented data (Assumption 3.6, p. 11). -/
def labelDisagree {r : ℕ} (P : Xbar → ℝ) (A : Xbar → X → ℝ) (y : Xbar → Fin r)
    (yhat : X → Fin r) : ℝ :=
  ∑ xb, P xb * ∑ x, A xb x * if yhat x ≠ y xb then 1 else 0

/-- Theorem B.3, p. 27: the squared error `E_{x̄ ∼ P, x ∼ 𝒜(·|x̄)} ‖y⃗(x̄) - Bᵀ f(x)‖²` of the
linear head on the one-hot label `y⃗(x̄)`. -/
def probeSqLoss {k r : ℕ} (P : Xbar → ℝ) (A : Xbar → X → ℝ) (y : Xbar → Fin r)
    (f : X → Fin k → ℝ) (B : Matrix (Fin k) (Fin r) ℝ) : ℝ :=
  ∑ xb, P xb * ∑ x, A xb x *
    ∑ c, ((if c = y xb then 1 else 0) - Matrix.vecMul (f x) B c) ^ 2

/-- Frobenius norm `‖B‖_F` of a real matrix (Theorem B.3, p. 27). -/
def frobNorm {m n : Type*} [Fintype m] [Fintype n] (B : Matrix m n ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, B i j ^ 2)

/-- Section 4.1, p. 14 (Definition D.1, p. 37): the empirical spectral contrastive loss on a
dataset `x̄_1, …, x̄_n`:
`L̂_n(f) = -(2/n) ∑_i E_{x, x⁺ ∼ 𝒜(·|x̄_i)}[f(x)ᵀ f(x⁺)]
  + (1/(n(n-1))) ∑_{i ≠ j} E_{x ∼ 𝒜(·|x̄_i), x⁻ ∼ 𝒜(·|x̄_j)}[(f(x)ᵀ f(x⁻))²]`. -/
def empLoss {k n : ℕ} (A : Xbar → X → ℝ) (d : Fin n → Xbar) (f : X → Fin k → ℝ) : ℝ :=
  -(2 / n) * (∑ i, ∑ x, ∑ x', A (d i) x * A (d i) x' * ∑ l, f x l * f x' l) +
    (1 / (n * (n - 1) : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i),
      ∑ x, ∑ x', A (d i) x * A (d j) x' * (∑ l, f x l * f x' l) ^ 2

/-- Section 4.1, p. 14: the Rademacher complexity of a class `ℱ` of maps `X → ℝ^k` on `m` data,
`R̂_m(ℱ) = max_{x_1, …, x_m ∈ X} E_σ[sup_{f ∈ ℱ, i ∈ [k]} (1/m) ∑_j σ_j f_i(x_j)]`, with `σ`
uniform on `{-1, 1}^m` (encoded by `Bool`). -/
def rademacher {k : ℕ} (F : Set (X → Fin k → ℝ)) (m : ℕ) : ℝ :=
  ⨆ xs : Fin m → X, (1 / 2 ^ m : ℝ) * ∑ σ : Fin m → Bool,
    ⨆ p : F × Fin k, (1 / m : ℝ) * ∑ j, (if σ j then 1 else -1) * p.1.1 (xs j) p.2

open Classical in
/-- Section 4.1, p. 14: the probability, under a dataset `x̄_1, …, x̄_n` drawn i.i.d. from `P`,
of an event `E` of the dataset. -/
def datasetProb {n : ℕ} (P : Xbar → ℝ) (E : (Fin n → Xbar) → Prop) : ℝ :=
  ∑ d : Fin n → Xbar, (∏ i, P (d i)) * if E d then 1 else 0

end Model

end SpectralContrastive


