-- Prove2me | Definitions.Def_FiniteSampleDependence_Rigidity_Supplement_Model
-- name    : FiniteSampleDependence_Rigidity_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:48:10.874293+00:00
-- url     : https://prove2.me/theorems/61cb2dea-6154-42b0-ad84-1d1750456c32
-- title:
--   Independence-faithfulness, fixed-sample estimability, the §6 peer-prediction model, $F_{\mathrm{QMI}}$, $M_{\mathrm{QMI}}$ and the restricted channels $C_n$
-- statement:
--   Throughout, $\Delta_{n,m}$ is the joint-distribution simplex, $r(U)=U\mathbf 1_m$ and $c(U)=U^\top\mathbf 1_n$ are the marginals, and a channel $T\in\mathbb R^{n\times n}$ is column-stochastic if its entries are nonnegative and its columns sum to one (published definitions of the mission).
--
--   1. **Independence-faithful functional** (§5.1). $F$ is independence-faithful if, for every $U\in\Delta_{n,m}$, $F(U)=0$ exactly when $\operatorname{rank}U=1$.
--   2. **Fixed-sample unbiased estimability** (Definition 2.3). For a finite set $Z$ let $\Delta(Z)=\{P\in\mathbb R^Z:P\ge0,\ \sum_zP(z)=1\}$. A functional $F$ on $\Delta(Z)$ is $d$-sample unbiasedly estimable if some statistic $\hat F:Z^d\to\mathbb R$ satisfies
--   $$\mathbb E_P[\hat F(Z_1,\dots,Z_d)]=\sum_{z\in Z^d}\hat F(z)\prod_{t=1}^dP(z_t)=F(P)\qquad\text{for every }P\in\Delta(Z),$$
--   with $Z_1,\dots,Z_d$ i.i.d. from $P$. $F$ is represented on $\Delta(Z)$ by a polynomial of degree at most $d$ if some real polynomial $Q$ in the variables $(P(z))_{z\in Z}$ of total degree at most $d$ agrees with $F$ on $\Delta(Z)$.
--   3. **Peer prediction** (§6). Alice and Bob report $\ell$ pairs in $[n]\times[m]$. A payment rule is a signed function $M:([n]\times[m])^\ell\to\mathbb R$; its expected payment when the reports are i.i.d. with law $V$ is
--   $$\mathbb E_{V^{\otimes\ell}}[M]=\sum_{((x_t,y_t))_{t=1}^\ell}M\big((x_t,y_t)_{t}\big)\prod_{t=1}^\ell V_{x_ty_t}.$$
--   In the memoryless model Alice applies a column-stochastic $T\in\mathbb R^{n\times n}$ and Bob a column-stochastic $S\in\mathbb R^{m\times m}$ on every task, so the reports are i.i.d. from $TPS^\top$; truthful reporting is the identity. A payment is *independence-zero* if its expectation vanishes at every rank-one $U\in\Delta_{n,m}$, and *nontrivial* if its truthful expected payment is nonzero for some $P\in\Delta_{n,m}$. Alice's payment $M_A$ is *truthful against all memoryless deviations with Bob truthful* if $\mathbb E_{(TP)^{\otimes\ell}}[M_A]\le\mathbb E_{P^{\otimes\ell}}[M_A]$ for every $P$ and every $T$. A mechanism $(M_A,M_B)$ is *dominantly truthful* if, for every $P$ and every fixed channel of the other agent, truthful reporting maximizes one's expected payment over all own channels:
--   $$\mathbb E_{(TPS^\top)^{\otimes\ell}}[M_A]\le\mathbb E_{(PS^\top)^{\otimes\ell}}[M_A],\qquad \mathbb E_{(TPS^\top)^{\otimes\ell}}[M_B]\le\mathbb E_{(TP)^{\otimes\ell}}[M_B].$$
--   4. **Quadratic mutual information** (equation (7)): $F_{\mathrm{QMI}}(U)=\sum_{i,\alpha}\big(U_{i\alpha}-r_i(U)c_\alpha(U)\big)^2$.
--   5. **The four-task payment** (equation (8)): for reports $z_t=(x_t,y_t)$, $t=1,\dots,4$,
--   $$M_{\mathrm{QMI}}=\mathbf 1\{x_1=x_2,\,y_1=y_2\}-2\cdot\mathbf 1\{x_1=x_2,\,y_1=y_3\}+\mathbf 1\{x_1=x_2,\,y_3=y_4\}.$$
--   6. **Restricted channels** (§7.2). $DS_n$ is the set of doubly stochastic $n\times n$ matrices, $R1_n=\{q\mathbf 1_n^\top:q\ge0,\ \mathbf 1_n^\top q=1\}$ the signal-independent channels, and $C_n=\operatorname{conv}(DS_n\cup R1_n)$.
--
--   These are the objects of the supplement's companion theorems on faithfulness (§5.1), peer-prediction task bounds (§6) and four-task rewards (§7).
--
--   **Formalization Note** $\Delta(Z)$ is Mathlib's `stdSimplex ℝ Z` and $DS_n$ is Mathlib's `doublyStochastic ℝ (Fin n)`. The paper's sample indices $1,\dots,4$ are `0,…,3`. Expectations are the exact finite sums above, not integrals.
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), §5.1 (independence-faithful), PDF p. 15 (printed p. 14); Definition 2.3, PDF p. 7 (printed p. 6); §6 model, PDF p. 17 (printed p. 16), eq. (6); eq. (7), §7.2, PDF p. 18 (printed p. 17); eq. (8), PDF p. 19 (printed p. 18)

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model

/-!
# Supplement objects: faithfulness, fixed-sample estimation, peer prediction, QMI, restricted channels

Yuqing Kong, *Limits of Finite-Sample Dependence Measures under Data Processing Inequality*,
STOC 2027 submission #152 (October 2026), SHA-256
f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118.
Definition 2.3 (PDF p. 7), §5.1 (PDF p. 15), §6 (PDF p. 17), §7.1–7.3 (PDF pp. 18–19).

The joint-distribution simplex, column-stochastic channels, (LF-DPI), (IZ) and the marginals are
the published definitions of `FiniteSampleDependence.Rigidity` (imported, not re-declared).
-/

namespace FiniteSampleDependence.Rigidity.Supplement

open Matrix

/-- §5.1 (PDF p. 15): `F` is independence-faithful if, on the simplex `Δ_{n,m}`, `F(U) = 0`
exactly when `rank U = 1`. -/
def IndependenceFaithful {n m : ℕ} (F : Matrix (Fin n) (Fin m) ℝ → ℝ) : Prop :=
  ∀ U ∈ simplex n m, (F U = 0 ↔ U.rank = 1)

/-- The expectation `E_P[F̂(Z_1,…,Z_d)]` of a statistic `F̂ : Z^d → ℝ` when `Z_1,…,Z_d` are drawn
i.i.d. from `P` on the finite set `Z`, written as the exact finite sum
`∑_{z ∈ Z^d} F̂(z) ∏_t P(z_t)`. -/
def iidExpectation {Z : Type*} [Fintype Z] [DecidableEq Z] {d : ℕ} (Fhat : (Fin d → Z) → ℝ)
    (P : Z → ℝ) : ℝ :=
  ∑ z : Fin d → Z, Fhat z * ∏ t, P (z t)

/-- Definition 2.3 (PDF p. 7): a functional `F` on the probability simplex `Δ(Z)` (Mathlib's
`stdSimplex ℝ Z`) is `d`-sample unbiasedly estimable if some statistic `F̂ : Z^d → ℝ` has
`E_P[F̂(Z_1,…,Z_d)] = F(P)` for every `P ∈ Δ(Z)`. -/
def UnbiasedlyEstimable (Z : Type*) [Fintype Z] [DecidableEq Z] (d : ℕ)
    (F : (Z → ℝ) → ℝ) : Prop :=
  ∃ Fhat : (Fin d → Z) → ℝ, ∀ P ∈ stdSimplex ℝ Z, iidExpectation Fhat P = F P

/-- `F` is represented on `Δ(Z)` by a polynomial of degree at most `d` in the probabilities
`P(z)`: some real polynomial `Q` in the variables `(P(z))_{z ∈ Z}` of total degree `≤ d` agrees
with `F` at every point of the simplex. -/
def PolyRepresentable (Z : Type*) [Fintype Z] (d : ℕ) (F : (Z → ℝ) → ℝ) : Prop :=
  ∃ Q : MvPolynomial Z ℝ, Q.totalDegree ≤ d ∧ ∀ P ∈ stdSimplex ℝ Z, MvPolynomial.eval P Q = F P

/-! ### The peer-prediction model of §6 (PDF p. 17) -/

/-- §6, equation (6): the expected payment of a payment rule `M : ([n] × [m])^ℓ → ℝ` when the `ℓ`
reported pairs are i.i.d. with joint law `V`:
`E_{V^{⊗ℓ}}[M] = ∑_{z ∈ ([n]×[m])^ℓ} M(z) ∏_t V_{x_t y_t}`. Payments may be signed. -/
def expectedPayment {n m ℓ : ℕ} (M : (Fin ℓ → Fin n × Fin m) → ℝ)
    (V : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ z : Fin ℓ → Fin n × Fin m, M z * ∏ t, V (z t).1 (z t).2

/-- A payment is independence-zero: its expectation vanishes under every i.i.d. report law
`U ∈ Δ_{n,m}` of rank one. -/
def PaymentIZ {n m ℓ : ℕ} (M : (Fin ℓ → Fin n × Fin m) → ℝ) : Prop :=
  ∀ U ∈ simplex n m, U.rank = 1 → expectedPayment M U = 0

/-- A payment is nontrivial: its truthful expected payment is nonzero for at least one signal
distribution `P ∈ Δ_{n,m}`. -/
def PaymentNontrivial {n m ℓ : ℕ} (M : (Fin ℓ → Fin n × Fin m) → ℝ) : Prop :=
  ∃ P ∈ simplex n m, expectedPayment M P ≠ 0

/-- Alice's payment `M_A` is truthful against all memoryless deviations with Bob truthful: for
every `P ∈ Δ_{n,m}` and every column-stochastic `T ∈ ℝ^{n×n}` (Alice's channel; Bob reports
truthfully, so the report law is `TP`), `E_{(TP)^{⊗ℓ}}[M_A] ≤ E_{P^{⊗ℓ}}[M_A]`. -/
def AliceTruthful {n m ℓ : ℕ} (MA : (Fin ℓ → Fin n × Fin m) → ℝ) : Prop :=
  ∀ P ∈ simplex n m, ∀ T : Matrix (Fin n) (Fin n) ℝ, IsColumnStochastic T →
    expectedPayment MA (T * P) ≤ expectedPayment MA P

/-- Dominant truthfulness in the memoryless strategy model (§6): against every fixed
column-stochastic channel of the other agent, truthful reporting maximizes one's expected payment
over all own column-stochastic channels. With Alice's channel `T` and Bob's channel `S` the report
law is `T P Sᵀ`. -/
def DominantlyTruthful {n m ℓ : ℕ} (MA MB : (Fin ℓ → Fin n × Fin m) → ℝ) : Prop :=
  (∀ P ∈ simplex n m, ∀ S : Matrix (Fin m) (Fin m) ℝ, IsColumnStochastic S →
    ∀ T : Matrix (Fin n) (Fin n) ℝ, IsColumnStochastic T →
      expectedPayment MA (T * P * Sᵀ) ≤ expectedPayment MA (P * Sᵀ)) ∧
  (∀ P ∈ simplex n m, ∀ T : Matrix (Fin n) (Fin n) ℝ, IsColumnStochastic T →
    ∀ S : Matrix (Fin m) (Fin m) ℝ, IsColumnStochastic S →
      expectedPayment MB (T * P * Sᵀ) ≤ expectedPayment MB (T * P))

/-! ### Quadratic mutual information and the four-task payment (§7, PDF pp. 18–19) -/

/-- Equation (7): `F_QMI(U) = ‖U − r(U)c(U)ᵀ‖_F² = ∑_{i,α} (U_{iα} − r_i(U) c_α(U))²`. -/
def qmi {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ α, (U i α - rowMarginal U i * colMarginal U α) ^ 2

/-- Equation (8): for four reported pairs `z_t = (x_t, y_t)` (the paper's indices `1,2,3,4` are
`0,1,2,3` here),
`M_QMI = 1{x₁ = x₂, y₁ = y₂} − 2·1{x₁ = x₂, y₁ = y₃} + 1{x₁ = x₂, y₃ = y₄}`. -/
def qmiPayment {n m : ℕ} (z : Fin 4 → Fin n × Fin m) : ℝ :=
  (if (z 0).1 = (z 1).1 ∧ (z 0).2 = (z 1).2 then 1 else 0)
    - 2 * (if (z 0).1 = (z 1).1 ∧ (z 0).2 = (z 2).2 then 1 else 0)
    + (if (z 0).1 = (z 1).1 ∧ (z 2).2 = (z 3).2 then 1 else 0)

/-- The rank-one channel `q 1ₙᵀ`: every column equals the vector `q`. -/
def rankOneChannel {n : ℕ} (q : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i _ => q i

/-- `R1_n = {q 1ₙᵀ : q ≥ 0, 1ₙᵀ q = 1}`: the signal-independent report channels. -/
def rankOneChannels (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {T | ∃ q : Fin n → ℝ, q ∈ stdSimplex ℝ (Fin n) ∧ T = rankOneChannel q}

/-- §7.2: `C_n = conv(DS_n ∪ R1_n)`, with `DS_n` the doubly stochastic real `n × n` matrices
(Mathlib's `doublyStochastic`). -/
def restrictedChannels (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  convexHull ℝ ((doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ)) ∪ rankOneChannels n)

end FiniteSampleDependence.Rigidity.Supplement


