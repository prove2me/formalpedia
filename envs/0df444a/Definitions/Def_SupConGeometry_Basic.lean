-- Prove2me | Definitions.Def_SupConGeometry_Basic
-- name    : SupConGeometry_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T01:10:05.442113+00:00
-- url     : https://prove2.me/theorems/65070a4d-9b50-4f8e-ae72-b7a9ed82c05b
-- title:
--   Supervised contrastive and cross-entropy losses of labelled point configurations, and the sphere-inscribed regular simplex
-- statement:
--   Objects of Sections 2-3 and the Supplementary Material of Graf, Hofer, Niethammer and Kwitt (ICML 2021).
--
--   1. **Configurations and labels.** A free configuration is $Z=(z_1,\dots,z_N)$ with $z_n\in\mathbb{R}^h$, carrying labels $Y=(y_1,\dots,y_N)\in[K]^N$. Write $m_Y(y)=|\{n\in[N]:y_n=y\}|$. $Y$ is **balanced** if $m_Y(y)=N/K$ for every class $y$.
--   2. **Regular simplex (Definition 3).** $\zeta_1,\dots,\zeta_K\in\mathbb{R}^h$ form a regular simplex inscribed in the sphere of radius $\rho$ if (S1) $\sum_y\zeta_y=0$, (S2) $\|\zeta_y\|=\rho$ for all $y$, and (S3) $\langle\zeta_i,\zeta_j\rangle=d$ for one $d\in\mathbb{R}$ and all $i<j$.
--   3. **Cross-entropy loss (Definition 1).** For a weight matrix $W\in\mathbb{R}^{K\times h}$ with rows $w_1,\dots,w_K$,
--   $$\mathcal L_{CE}(Z,W;Y)=\frac1N\sum_{n=1}^N-\log\frac{\exp\langle z_n,w_{y_n}\rangle}{\sum_{l=1}^K\exp\langle z_n,w_l\rangle},$$
--   and $\|W\|_F=(\sum_y\|w_y\|^2)^{1/2}$.
--   4. **Supervised contrastive loss (Definition 2).** $\mathcal B$ is the set of all multisets $B=\{\!\{n_1,\dots,n_b\}\!\}$ of $b$ indices from $[N]$. For $B\in\mathcal B$, $B_y=\{\!\{j\in B:y_j=y\}\!\}$ and $B_y^C=\{\!\{j\in B:y_j\neq y\}\!\}$. The batch-wise loss is
--   $$\ell_{SC}(Z;Y,B)=-\sum_{i\in B}\frac{\mathbb 1_{\{|B_{y_i}|>1\}}}{|B_{y_i}|-1}\sum_{j\in B_{y_i}\setminus\{\!\{i\}\!\}}\log\frac{\exp\langle z_i,z_j\rangle}{\sum_{k\in B\setminus\{\!\{i\}\!\}}\exp\langle z_i,z_k\rangle},$$
--   where sums over a multiset count multiplicity and $\setminus\{\!\{i\}\!\}$ removes one copy of $i$. The loss is $\mathcal L_{SC}(Z;Y)=\sum_{B\in\mathcal B}\ell_{SC}(Z;Y,B)$. The class-specific batch-wise loss $\ell_{SC}(Z;Y,B,y)$ is the part of this sum with $i\in B_y$ when $|B_y|>1$, and $0$ otherwise.
--   5. **Batch partition (Definition 4).** $\mathcal B_{y,l}=\{B\in\mathcal B:|B_y|=l\}$ and $M_l=\sum_y|\mathcal B_{y,l}|$.
--   6. **Auxiliary functions (Definition 5).** With $l=|B_y|$:
--   $$S_{att}=-\frac{1}{l(l-1)}\sum_{i\in B_y}\sum_{j\in B_y\setminus\{\!\{i\}\!\}}\langle z_i,z_j\rangle,\qquad S_{rep}=\frac{1}{l\,|B_y^C|}\sum_{i\in B_y}\sum_{j\in B_y^C}\langle z_i,z_j\rangle\ (l\neq b),\ S_{rep}=0\ (l=b),$$
--   $S=S_{att}+S_{rep}$, and $S_i=-\frac{1}{l-1}\sum_{j\in B_y\setminus\{\!\{i\}\!\}}\langle z_i,z_j\rangle+\frac1{|B_y^C|}\sum_{j\in B_y^C}\langle z_i,z_j\rangle$, the second summand being omitted when $l=b$.
--   7. **Combinatorial factor (Lemma 5).** $K_{n,m}(y,l)=\frac{1}{l(b-l)}\sum_{B\in\mathcal B_{y,l}}m_{B_y}(n)\,m_{B_y^C}(m)$, where $m_M(x)$ is the multiplicity of $x$ in $M$.
--   8. **$L_2$ radius (Corollary 2, Lemma 14).** $f(x)=\log\big(1+(K-1)e^{-\rho K x/(K-1)}\big)+\lambda Kx^2$, and $r_{\mathcal W}(\rho,\lambda)$ is the solution in $x$ of $2\lambda x-\rho/(e^{K\rho x/(K-1)}+K-1)=0$.
--
--   **Formalization Note** Points live in `EuclideanSpace ℝ (Fin h)`, labels in `Fin K` and indices in `Fin N`. A batch is an element of `Sym (Fin N) b`, a multiset of size $b$, and $\mathcal L_{SC}$ sums over all of them. Balance is written $K\cdot m_Y(y)=N$, which avoids natural-number division. $r_{\mathcal W}(\rho,\lambda)$ is the infimum of the solution set of its equation. By Lemma 14 this set is a single point when $K\ge2$ and $\rho,\lambda>0$. $S_{rep}$ and $S_i$ follow the paper's case split on $|B_y|=b$.
-- source:
--   Graf, Hofer, Niethammer and Kwitt, Dissecting Supervised Contrastive Learning, ICML 2021, arXiv:2102.08817v4, Section 2.1 (Definitions 1-3, pp. 3-4), Section 3 (balanced labels, p. 4), Supplementary S1.1 (Definitions 4-5, eqs. (10), (16)-(21), pp. 13-14), S1.3 (Lemma 5, eq. (61), p. 20), S2 (Lemma 14, eqs. (147)-(148), p. 34) and Corollary 2 (p. 5)

import Mathlib

/-!
Graf, Hofer, Niethammer and Kwitt, *Dissecting Supervised Contrastive Learning*, ICML 2021,
arXiv:2102.08817v4: free point configurations with labels, the cross-entropy loss (Definition 1),
the supervised contrastive loss over all multiset batches (Definition 2), the sphere-inscribed
regular simplex (Definition 3), balanced labels (Section 3), and the auxiliary objects of the
proofs in Supplementary S1.1 (Definitions 4 and 5), S1.3 (Lemma 5) and S2 (Lemma 14, Corollary 2).
-/

noncomputable section

namespace SupConGeometry

/-- Section 2: the representation space `ℝ^h` with its Euclidean inner product and norm. -/
abbrev Rep (h : ℕ) : Type := EuclideanSpace ℝ (Fin h)

variable {N K h : ℕ}

/-- Supplementary S1.1: `m_Y(y) = |{n ∈ [N] : y_n = y}|`, the number of instances of class `y`. -/
def labelCount (Y : Fin N → Fin K) (y : Fin K) : ℕ :=
  (Finset.univ.filter (fun n => Y n = y)).card

/-- Section 3 (p. 4): the label configuration `Y` is balanced, `|{n ∈ [N] : y_n = y}| = N / K`
for every class `y`; written as `K · m_Y(y) = N` to avoid natural-number division. -/
def IsBalanced (Y : Fin N → Fin K) : Prop :=
  ∀ y : Fin K, K * labelCount Y y = N

/-- Definition 3 (S1)-(S3): `ζ_1, …, ζ_K` form the vertices of a regular simplex inscribed in the
hypersphere of radius `ρ`: they sum to `0`, all have norm `ρ`, and all inner products
`⟨ζ_i, ζ_j⟩`, `i < j`, equal one common value `d`. -/
def IsSphereInscribedRegularSimplex (ζ : Fin K → Rep h) (ρ : ℝ) : Prop :=
  (∑ y, ζ y = 0) ∧ (∀ y, ‖ζ y‖ = ρ) ∧
    ∃ d : ℝ, ∀ y y' : Fin K, y < y' → inner ℝ (ζ y) (ζ y') = d

/-- Definition 1, eq. (3): the instance loss
`ℓ_CE(Z, W; Y, n) = -log(exp⟨z_n, w_{y_n}⟩ / ∑_{l=1}^K exp⟨z_n, w_l⟩)`, where `w_y` is the `y`-th
row of the classifier weight matrix `W ∈ ℝ^{K×h}`. -/
def ceInstanceLoss (Z : Fin N → Rep h) (W : Fin K → Rep h) (Y : Fin N → Fin K) (n : Fin N) : ℝ :=
  -Real.log (Real.exp (inner ℝ (Z n) (W (Y n))) / ∑ l, Real.exp (inner ℝ (Z n) (W l)))

/-- Definition 1, eq. (2): the cross-entropy loss `L_CE(Z, W; Y) = (1/N) ∑_n ℓ_CE(Z, W; Y, n)`. -/
def ceLoss (Z : Fin N → Rep h) (W : Fin K → Rep h) (Y : Fin N → Fin K) : ℝ :=
  (1 / (N : ℝ)) * ∑ n, ceInstanceLoss Z W Y n

/-- Theorem 1: the Frobenius norm `‖W‖_F = (∑_y ‖w_y‖²)^{1/2}` of the weight matrix with rows `w_y`. -/
def frobNorm (W : Fin K → Rep h) : ℝ :=
  Real.sqrt (∑ y, ‖W y‖ ^ 2)

/-- Definition 2: `B_y = {{j ∈ B : y_j = y}}`, the sub-multiset of a batch `B` with label `y`. -/
def batchClass (Y : Fin N → Fin K) (B : Multiset (Fin N)) (y : Fin K) : Multiset (Fin N) :=
  B.filter (fun j => Y j = y)

/-- Supplementary S1.1: `B_y^C = {{j ∈ B : y_j ≠ y}}`, the complement of `B_y` in the batch `B`. -/
def batchClassCompl (Y : Fin N → Fin K) (B : Multiset (Fin N)) (y : Fin K) : Multiset (Fin N) :=
  B.filter (fun j => Y j ≠ y)

/-- Definition 2, eq. (6): the summand `log(exp⟨z_i, z_j⟩ / ∑_{k ∈ B \ {{i}}} exp⟨z_i, z_k⟩)`, where
`B \ {{i}}` removes one copy of `i` from the multiset `B`. -/
def scLogRatio (Z : Fin N → Rep h) (B : Multiset (Fin N)) (i j : Fin N) : ℝ :=
  Real.log (Real.exp (inner ℝ (Z i) (Z j)) /
    ((B.erase i).map (fun k => Real.exp (inner ℝ (Z i) (Z k)))).sum)

/-- Definition 2, eq. (6): the batch-wise supervised contrastive loss
`ℓ_SC(Z; Y, B) = -∑_{i ∈ B} 1_{|B_{y_i}|>1} / (|B_{y_i}| - 1) ∑_{j ∈ B_{y_i} \ {{i}}} log(…)`,
sums over the multiset `B` counting multiplicity, with the paper's convention that the summand of
`i` is `0` when `|B_{y_i}| = 1`. -/
def scBatchLoss (Z : Fin N → Rep h) (Y : Fin N → Fin K) (B : Multiset (Fin N)) : ℝ :=
  -((B.map (fun i =>
      if 1 < Multiset.card (batchClass Y B (Y i)) then
        (1 / ((Multiset.card (batchClass Y B (Y i)) : ℝ) - 1)) *
          (((batchClass Y B (Y i)).erase i).map (fun j => scLogRatio Z B i j)).sum
      else 0)).sum)

/-- Definition 2, eqs. (4)-(5): the supervised contrastive loss
`L_SC(Z; Y) = ∑_{B ∈ 𝓑} ℓ_SC(Z; Y, B)`, summed over the set `𝓑` of all index multisets of size `b`
over `[N]` (here `Sym (Fin N) b`). -/
def scLoss (Z : Fin N → Rep h) (Y : Fin N → Fin K) (b : ℕ) : ℝ :=
  ∑ B : Sym (Fin N) b, scBatchLoss Z Y (B : Multiset (Fin N))

/-- Supplementary S1.1, eq. (10): the class-specific batch-wise loss `ℓ_SC(Z; Y, B, y)`, equal to
`-∑_{i ∈ B_y} 1/(|B_y| - 1) ∑_{j ∈ B_y \ {{i}}} log(…)` if `|B_y| > 1` and `0` otherwise. -/
def scClassBatchLoss (Z : Fin N → Rep h) (Y : Fin N → Fin K) (B : Multiset (Fin N)) (y : Fin K) :
    ℝ :=
  if 1 < Multiset.card (batchClass Y B y) then
    -(((batchClass Y B y).map (fun i =>
        (1 / ((Multiset.card (batchClass Y B y) : ℝ) - 1)) *
          (((batchClass Y B y).erase i).map (fun j => scLogRatio Z B i j)).sum)).sum)
  else 0

/-- Definition 4 (Supplementary S1.1), eq. (16): `𝓑_{y,l}`, the batches of size `b` containing exactly `l`
instances of class `y`. -/
def batchesWithCount (Y : Fin N → Fin K) (b : ℕ) (y : Fin K) (l : ℕ) : Finset (Sym (Fin N) b) :=
  Finset.univ.filter (fun B => Multiset.card (batchClass Y (B : Multiset (Fin N)) y) = l)

/-- Theorem 2 (p. 5) and Lemma 2: `M_l = ∑_{y ∈ 𝒴} |{B ∈ 𝓑 : |B_y| = l}| = ∑_y |𝓑_{y,l}|`. -/
def batchCountTotal (Y : Fin N → Fin K) (b : ℕ) (l : ℕ) : ℕ :=
  ∑ y, (batchesWithCount Y b y l).card

/-- Definition 5, eq. (19): the attraction term
`S_att(Z; Y, B, y) = -1/(|B_y|(|B_y| - 1)) ∑_{i ∈ B_y} ∑_{j ∈ B_y \ {{i}}} ⟨z_i, z_j⟩`. -/
def sAtt (Z : Fin N → Rep h) (Y : Fin N → Fin K) {b : ℕ} (B : Sym (Fin N) b) (y : Fin K) : ℝ :=
  -(1 / ((Multiset.card (batchClass Y (B : Multiset (Fin N)) y) : ℝ) *
      ((Multiset.card (batchClass Y (B : Multiset (Fin N)) y) : ℝ) - 1))) *
    ((batchClass Y (B : Multiset (Fin N)) y).map (fun i =>
      (((batchClass Y (B : Multiset (Fin N)) y).erase i).map (fun j => inner ℝ (Z i) (Z j))).sum)).sum

/-- Definition 5, eq. (20): the repulsion term
`S_rep(Z; Y, B, y) = 1/(|B_y| |B_y^C|) ∑_{i ∈ B_y} ∑_{j ∈ B_y^C} ⟨z_i, z_j⟩` if `|B_y| ≠ b`, and
`0` if `|B_y| = b`. -/
def sRep (Z : Fin N → Rep h) (Y : Fin N → Fin K) {b : ℕ} (B : Sym (Fin N) b) (y : Fin K) : ℝ :=
  if Multiset.card (batchClass Y (B : Multiset (Fin N)) y) = b then 0 else
    (1 / ((Multiset.card (batchClass Y (B : Multiset (Fin N)) y) : ℝ) *
        (Multiset.card (batchClassCompl Y (B : Multiset (Fin N)) y) : ℝ))) *
      ((batchClass Y (B : Multiset (Fin N)) y).map (fun i =>
        ((batchClassCompl Y (B : Multiset (Fin N)) y).map (fun j => inner ℝ (Z i) (Z j))).sum)).sum

/-- Definition 5, eqs. (17)-(18): `S(Z; Y, B, y) = S_att(Z; Y, B, y) + S_rep(Z; Y, B, y)`. -/
def sAux (Z : Fin N → Rep h) (Y : Fin N → Fin K) {b : ℕ} (B : Sym (Fin N) b) (y : Fin K) : ℝ :=
  sAtt Z Y B y + sRep Z Y B y

/-- Definition 5, eq. (21): the per-instance term
`S_i(Z; Y, B, y) = -1/(|B_y| - 1) ∑_{j ∈ B_y \ {{i}}} ⟨z_i, z_j⟩ + 1/|B_y^C| ∑_{j ∈ B_y^C} ⟨z_i, z_j⟩`
if `|B_y| ≠ b`, and only the first summand if `|B_y| = b`. -/
def sInd (Z : Fin N → Rep h) (Y : Fin N → Fin K) {b : ℕ} (B : Sym (Fin N) b) (y : Fin K)
    (i : Fin N) : ℝ :=
  -(1 / ((Multiset.card (batchClass Y (B : Multiset (Fin N)) y) : ℝ) - 1)) *
      (((batchClass Y (B : Multiset (Fin N)) y).erase i).map (fun j => inner ℝ (Z i) (Z j))).sum +
    if Multiset.card (batchClass Y (B : Multiset (Fin N)) y) = b then 0 else
      (1 / (Multiset.card (batchClassCompl Y (B : Multiset (Fin N)) y) : ℝ)) *
        ((batchClassCompl Y (B : Multiset (Fin N)) y).map (fun j => inner ℝ (Z i) (Z j))).sum

/-- Lemma 5 (Supplementary S1.3), eq. (61): the combinatorial factor
`K_{n,m}(y, l) = 1/(l(b - l)) ∑_{B ∈ 𝓑_{y,l}} m_{B_y}(n) m_{B_y^C}(m)`, where `m_M(x)` is the
multiplicity of `x` in the multiset `M`. -/
def combFactor (Y : Fin N → Fin K) (b : ℕ) (y : Fin K) (l : ℕ) (n m : Fin N) : ℝ :=
  (1 / ((l : ℝ) * ((b : ℝ) - l))) *
    ∑ B ∈ batchesWithCount Y b y l,
      ((Multiset.count n (batchClass Y (B : Multiset (Fin N)) y) : ℝ) *
        (Multiset.count m (batchClassCompl Y (B : Multiset (Fin N)) y) : ℝ))

/-- Lemma 14, eq. (147): `f(x) = log(1 + (K - 1) exp(-ρ K x/(K - 1))) + λ K x²`, the lower bound
of Theorem 1 plus the penalty `λ‖W‖_F²`, written in `x = ‖W‖_F / √K`. -/
def ceL2Profile (K : ℕ) (ρ lam x : ℝ) : ℝ :=
  Real.log (1 + ((K : ℝ) - 1) * Real.exp (-(ρ * ((K : ℝ) / ((K : ℝ) - 1)) * x))) +
    lam * (K : ℝ) * x ^ 2

/-- Corollary 2 (Section 3.1, p. 5) and Lemma 14, eq. (148): `r_W(ρ, λ)`, the solution in `x` of
`2λx - ρ / (exp(Kρx/(K - 1)) + K - 1) = 0` (unique by Lemma 14), taken as the infimum of the
solution set. -/
def ceL2Radius (K : ℕ) (ρ lam : ℝ) : ℝ :=
  sInf {x : ℝ | 2 * lam * x - ρ / (Real.exp ((K : ℝ) * ρ * x / ((K : ℝ) - 1)) + (K : ℝ) - 1) = 0}

end SupConGeometry


