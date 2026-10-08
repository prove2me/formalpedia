-- Prove2me | Definitions.Def_RobustPCA_Recovery_Setup
-- name    : RobustPCA_Recovery_Setup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:25.911993+00:00
-- url     : https://prove2.me/theorems/f44d26e7-35ad-4f19-8b69-cfaaba4b9367
-- title:
--   ℓ1 norm, sgn, incoherence (1.2)–(1.3), exactness of PCP (1.1), trimmed versions (Definition 2.1), random-sign and golfing laws, certificates W^L (2.5) and W^S (2.7)
-- statement:
--   This module fixes the objects of Candès, Li, Ma and Wright's analysis of **Principal Component Pursuit** for square real $n\times n$ matrices. It builds on the published matrix-completion modules, which supply the nuclear norm $\|M\|_*=\sum_i\sigma_i(M)$, the operator norm $\|M\|$ (largest singular value), the Frobenius norm and inner product, $\|M\|_\infty=\max_{ij}|M_{ij}|$, the projection $\mathcal P_\Omega$ keeping the entries in $\Omega$, compact SVD data $L_0=\sum_{k=1}^r\sigma_k u_kv_k^*$ with $UV^*=\sum_k u_kv_k^*$, the tangent-space projections $\mathcal P_T$, $\mathcal P_{T^\perp}$, and the Bernoulli and uniform laws on supports.
--
--   1. **Norms and signs.** $\|M\|_1=\sum_{ij}|M_{ij}|$; $\operatorname{sgn}(S)$ is the matrix of entrywise signs, with $\operatorname{sgn}(0)=0$; $\operatorname{supp}(S)=\{(i,j):S_{ij}\neq0\}$; $\mathcal P_{\Omega^\perp}X=X-\mathcal P_\Omega X$.
--   2. **Incoherence with parameter $\mu$** (1.2)–(1.3):
--   $$\max_i\|U^*e_i\|^2\le\frac{\mu r}{n},\qquad \max_i\|V^*e_i\|^2\le\frac{\mu r}{n},\qquad \|UV^*\|_\infty\le\sqrt{\frac{\mu r}{n^2}}.$$
--   3. **Exactness of PCP.** For a weight $\lambda$, PCP with input $M=L_0+S_0$ is the program
--   $$\text{minimize }\ \|L\|_*+\lambda\|S\|_1\quad\text{subject to}\quad L+S=M. \tag{1.1}$$
--   It is *exact* when $(L_0,S_0)$ is its unique solution: every other feasible pair has a strictly larger objective.
--   4. **Trimmed version** (Definition 2.1): $S'$ is a trimmed version of $S$ if $\operatorname{supp}(S')\subseteq\operatorname{supp}(S)$ and $S'_{ij}=S_{ij}$ whenever $S'_{ij}\neq0$.
--   5. **$\|\mathcal P_\Omega\mathcal P_T\|\le\sigma$**, the operator norm with respect to the Frobenius norm: $\|\mathcal P_\Omega\mathcal P_TX\|_F\le\sigma\|X\|_F$ for every $X$.
--   6. **Random sign model** (3.7) with parameter $\rho$: independent entries $E_{ij}$ equal to $1$ and $-1$ with probability $\rho/2$ each and to $0$ with probability $1-\rho$. It is realized as a support $\Omega\sim\mathrm{Ber}(\rho)$ followed by a uniformly random set $P\subseteq\Omega$ of $+1$ entries.
--   7. **Golfing law** (§2.4): $j_0$ independent sets $\Omega_1,\dots,\Omega_{j_0}\sim\mathrm{Ber}(q)$, with $\Omega=(\Omega_1\cup\dots\cup\Omega_{j_0})^c$; the iterates $Y_0=0$, $Y_j=Y_{j-1}+q^{-1}\mathcal P_{\Omega_j}\mathcal P_T(UV^*-Y_{j-1})$ and the certificate $W^L=\mathcal P_{T^\perp}Y_{j_0}$ (2.5).
--   8. **Least-squares certificate** via the Neumann series (2.7):
--   $$W^S=\lambda\,\mathcal P_{T^\perp}\sum_{k\ge0}(\mathcal P_\Omega\mathcal P_T\mathcal P_\Omega)^k\operatorname{sgn}(S_0).$$
--
--   These are the objects every statement of the mission is phrased in.
--
--   **Formalization Note** Probabilities are finite sums of product weights over supports (each law has total mass one). $W^S$ is defined by the series (2.7), which the paper calls an equivalent definition of (2.6); it equals (2.6) only when $\|\mathcal P_\Omega\mathcal P_T\|<1/2$, and every statement that uses it assumes this. The golfing iterates are indexed from $0$ (`Ωs j` is the paper's $\Omega_{j+1}$). "Exact" is the strict, unique-minimizer form.
-- source:
--   Candès, Li, Ma, Wright, Robust principal component analysis?, J. ACM 58(3) (2011), (1.1)–(1.3) pp. 4–5, §1.7 p. 9, Definition 2.1 p. 10, §2.4 (2.5)–(2.7) pp. 14–15, (3.7) p. 19

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_fixed_cardinality
import Mathlib.Data.Real.Sign
open MatrixCompletion

namespace RobustPCA.Recovery

open scoped Classical BigOperators

/-- The ℓ1 norm `‖M‖₁ = ∑_{ij} |M_ij|` of a matrix seen as a long vector (p. 4). -/
def l1Norm {n : ℕ} (X : RealMatrix n n) : ℝ :=
  ∑ i, ∑ j, |X i j|

/-- `sgn(S)`: the matrix of entrywise signs, with `sgn 0 = 0` (p. 9). Not to be confused with
`MatrixCompletion.signMatrix`, which is `UV*`. -/
noncomputable def sgnMatrix {n : ℕ} (X : RealMatrix n n) : RealMatrix n n :=
  fun i j => Real.sign (X i j)

/-- `supp(S) = {(i, j) : S_ij ≠ 0}`. -/
noncomputable def supp {n : ℕ} (X : RealMatrix n n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => X p.1 p.2 ≠ 0)

/-- `𝒫_{Ω⊥} X = X − 𝒫_Ω X`: the projection onto the matrices supported on the complement of `Ω`
(p. 9: `I = 𝒫_Ω + 𝒫_{Ω⊥}`). -/
noncomputable def compProj {n : ℕ} (Ω : Finset (Fin n × Fin n)) (X : RealMatrix n n) :
    RealMatrix n n :=
  X - samplingProjection Ω X

/-- The incoherence condition with parameter `μ`, (1.2)–(1.3), for an `n × n` matrix `L0` with
compact SVD `L0 = ∑_{k<r} σ_k u_k v_kᵀ`:
`max_i ‖U*e_i‖² ≤ μr/n`, `max_i ‖V*e_i‖² ≤ μr/n` and `‖UV*‖_∞ ≤ √(μr/n²)`. -/
def Incoherent {n r : ℕ} {L0 : RealMatrix n n} (S : SVD L0 r) (μ : ℝ) : Prop :=
  (∀ i : Fin n, ∑ k, (S.u k i) ^ 2 ≤ μ * r / n) ∧
    (∀ j : Fin n, ∑ k, (S.v k j) ^ 2 ≤ μ * r / n) ∧
    ∀ i j : Fin n, |signMatrix S i j| ≤ Real.sqrt (μ * r / ((n : ℝ) * n))

/-- Principal Component Pursuit (1.1) with weight `lam` and input `M = L0 + S0` has the unique
solution `(L0, S0)`: every other feasible pair `(L, S)`, `L + S = L0 + S0`, has a strictly larger
objective `‖L‖_* + lam ‖S‖₁`. ("PCP is exact", p. 5; "the solution … is unique and exact", p. 10.) -/
def IsPCPExact {n : ℕ} (lam : ℝ) (L0 S0 : RealMatrix n n) : Prop :=
  ∀ L S : RealMatrix n n, L + S = L0 + S0 → (L, S) ≠ (L0, S0) →
    nuclearNorm L0 + lam * l1Norm S0 < nuclearNorm L + lam * l1Norm S

/-- Definition 2.1 (p. 10): `S'` is a trimmed version of `S` if `supp(S') ⊂ supp(S)` and
`S'_ij = S_ij` whenever `S'_ij ≠ 0`. -/
def IsTrimmed {n : ℕ} (S' S : RealMatrix n n) : Prop :=
  supp S' ⊆ supp S ∧ ∀ i j, S' i j ≠ 0 → S' i j = S i j

/-- `‖𝒫_Ω 𝒫_T‖ ≤ σ`, the operator norm taken with respect to the Frobenius norm (p. 9):
`‖𝒫_Ω 𝒫_T X‖_F ≤ σ ‖X‖_F` for every matrix `X`. -/
def PTOpNormLe {n r : ℕ} {L0 : RealMatrix n n} (Ω : Finset (Fin n × Fin n)) (S : SVD L0 r)
    (σ : ℝ) : Prop :=
  ∀ X : RealMatrix n n,
    frobeniusNorm (samplingProjection Ω (tangentProjection S X)) ≤ σ * frobeniusNorm X

/-- The sign matrix with support `Ω` that equals `+1` on `P` and `−1` on `Ω \ P` (when `P ⊆ Ω`). -/
def signPattern {n : ℕ} (Ω P : Finset (Fin n × Fin n)) : RealMatrix n n :=
  fun i j => if (i, j) ∈ P then 1 else if (i, j) ∈ Ω then -1 else 0

/-- The random sign model (§2.2, (3.7)) with parameter `ρ`: the entries `E_ij` are independent,
equal to `1` and `−1` with probability `ρ/2` each and to `0` with probability `1 − ρ`.
Realized as the support `Ω ∼ Ber(ρ)` followed by a uniformly random subset `P ⊆ Ω` of `+1`
entries; `randomSignProb ρ Event` is the probability of `Event E`. -/
noncomputable def randomSignProb {n : ℕ} (ρ : ℝ) (Event : RealMatrix n n → Prop) : ℝ :=
  ∑ Ω : Finset (Fin n × Fin n), ∑ P ∈ Ω.powerset,
    bernoulliObservationWeight ρ Ω * (1 / 2 : ℝ) ^ Ω.card *
      (if Event (signPattern Ω P) then 1 else 0)

/-- The golfing law (§2.4): `j0` independent sets `Ω_1, …, Ω_{j0}`, each `∼ Ber(q)`
(0-indexed: `Ωs j` is the paper's `Ω_{j+1}`); `golfingProb q j0 Event` is the probability of
`Event Ωs`. -/
noncomputable def golfingProb {n : ℕ} (q : ℝ) (j0 : ℕ)
    (Event : (Fin j0 → Finset (Fin n × Fin n)) → Prop) : ℝ :=
  ∑ Ωs : Fin j0 → Finset (Fin n × Fin n),
    (∏ j, bernoulliObservationWeight q (Ωs j)) * (if Event Ωs then 1 else 0)

/-- `Ω = (Ω_1 ∪ ⋯ ∪ Ω_{j0})ᶜ`, the support set determined by the golfing partition (§2.4). -/
def golfOmega {n j0 : ℕ} (Ωs : Fin j0 → Finset (Fin n × Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ \ Finset.univ.biUnion Ωs

/-- The golfing iterates (§2.4): `Y_0 = 0`, `Y_j = Y_{j−1} + q⁻¹ 𝒫_{Ω_j} 𝒫_T (UV* − Y_{j−1})` for
`1 ≤ j ≤ j0` (frozen after `j0`). -/
noncomputable def golfY {n r : ℕ} {L0 : RealMatrix n n} (S : SVD L0 r) (q : ℝ) {j0 : ℕ}
    (Ωs : Fin j0 → Finset (Fin n × Fin n)) : ℕ → RealMatrix n n
  | 0 => 0
  | j + 1 =>
    if h : j < j0 then
      golfY S q Ωs j + q⁻¹ • samplingProjection (Ωs ⟨j, h⟩)
        (tangentProjection S (signMatrix S - golfY S q Ωs j))
    else golfY S q Ωs j

/-- The golfing certificate `W^L = 𝒫_{T⊥} Y_{j0}`, (2.5). -/
noncomputable def WL {n r : ℕ} {L0 : RealMatrix n n} (S : SVD L0 r) (q : ℝ) {j0 : ℕ}
    (Ωs : Fin j0 → Finset (Fin n × Fin n)) : RealMatrix n n :=
  normalProjection S (golfY S q Ωs j0)

/-- The least-squares certificate via the Neumann series (2.7):
`W^S = λ 𝒫_{T⊥} ∑_{k ≥ 0} (𝒫_Ω 𝒫_T 𝒫_Ω)^k E`, with `E = sgn(S0)`. Meaningful (equal to (2.6))
only when `‖𝒫_Ω 𝒫_T‖ < 1/2`, which every statement using it assumes. -/
noncomputable def WS {n r : ℕ} {L0 : RealMatrix n n} (lam : ℝ) (Ω : Finset (Fin n × Fin n))
    (S : SVD L0 r) (E : RealMatrix n n) : RealMatrix n n :=
  lam • normalProjection S
    (∑' k : ℕ,
      (fun X => samplingProjection Ω (tangentProjection S (samplingProjection Ω X)))^[k] E)

end RobustPCA.Recovery


