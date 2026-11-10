-- Prove2me | Definitions.Def_MinimaxATE_Learnability_DRScore
-- name    : MinimaxATE_Learnability_DRScore
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:01:24.102193+00:00
-- url     : https://prove2.me/theorems/835ab198-e846-41ea-bc1b-9f05a6c906dc
-- title:
--   The DR (AIPW) score, the per-part clipped AIPW estimator, per-part losses and the random split (§4.1, App. A.1, B.1)
-- statement:
--   For nuisance estimates $\hat p,\hat m_0,\hat m_1:\mathcal X\to\mathbb R$, the **DR (AIPW) score** of an observation $(X,T,Y)$ is
--   $$\psi_{\hat p,\hat m}(X,T,Y)=\hat m_1(X)-\hat m_0(X)+\frac{T\,(Y-\hat m_1(X))}{\hat p(X)}-\frac{(1-T)\,(Y-\hat m_0(X))}{1-\hat p(X)}.$$
--   Each index $i\in[n]$ is assigned independently to the training set $D_T$ or the validation set $D_V$ with probability $1/2$ (`fairCoin`; `true` means $i\in D_T$). Given a partition $\Pi$ of $[n]$ and nuisances $\hat p_R,\hat m_{R,0},\hat m_{R,1}$ for each part $R$, the **per-part AIPW estimator** (proof of Lemma 4.4) is
--   $$\tilde\tau=\frac2n\sum_{i}\mathbf 1\{i\in D_V\}\,\psi_{\hat p_{R(i)},\hat m_{R(i)}}(X_i,T_i,Y_i),\qquad\hat\tau=\mathrm{clip}_{[-1,1]}(\tilde\tau),$$
--   where $R(i)$ is the part containing $i$. For covariates $x_1,\dots,x_n$, a part $R$ and functions $f,g$, the **per-part loss** is $\frac1{|R|}\sum_{i\in R}(f(x_i)-g(x_i))^2$ (so $L_{P,R}(p)$ takes $g=p^\star$ and $L_{M,R,t}(m)$ takes $g=m^\star_t$), and the **empirical propensity loss** is $\hat L_{P,R}(p)=\frac2{|R|}\sum_{i\in R\cap D_T}(T_i-p(x_i))^2$. `bernoulliMeasure p` is the Bernoulli($p$) law on $\{0,1\}$, and `splitSampleLaw D n` is the law of $n$ i.i.d. observations from $C_D$ with an independent random split.
--
--   **Formalization Note.** Indices are `Fin n`; Lean division gives $a/0=0$, so the score is only meaningful for $\hat p$ with values in $(0,1)$ (every statement using it assumes $\hat p\in[c,1-c]$), and the per-part losses for nonempty parts. `bernoulliMeasure` projects its parameter onto $[0,1]$; it is only applied to propensities in $[c,1-c]$.
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 8 (PDF 10), DR score; p. 21 (PDF 23), L̂_{P,R}, L_{P,R}; p. 49 (PDF 51), proof of Lemma 4.4; p. 52 (PDF 54), §B.1

import Mathlib
import Definitions.Def_MinimaxATE_Learnability_Model

open MeasureTheory

namespace MinimaxATE.Learnability

/-- The DR (AIPW) score of an observation `(X, T, Y)` for nuisance estimates `p̂, m̂₀, m̂₁`
(p. 8 and §B.1, p. 52):
`ψ = m̂₁(X) − m̂₀(X) + T (Y − m̂₁(X))/p̂(X) − (1 − T)(Y − m̂₀(X))/(1 − p̂(X))`. -/
noncomputable def drScore {X : Type*} (pH m₀H m₁H : X → ℝ) (o : Obs X) : ℝ :=
  let t : ℝ := if o.2.1 then 1 else 0
  m₁H o.1 - m₀H o.1 + t * (o.2.2 - m₁H o.1) / pH o.1 - (1 - t) * (o.2.2 - m₀H o.1) / (1 - pH o.1)

/-- Clipping to `[−1, 1]`. -/
noncomputable def clipUnit (t : ℝ) : ℝ := max (-1) (min 1 t)

/-- The per-part AIPW estimator of the proof of Lemma 4.4 (p. 49): `train i = true` means
`i ∈ D_T`, otherwise `i ∈ D_V`; each `i` uses the nuisances `p̂_R, m̂_{R,0}, m̂_{R,1}` of the part
`R ∋ i` of the partition `part`; `τ̃ = (2/n) Σ_i 1{i ∈ D_V} ψ_i` and the estimate is `clip_{[−1,1]}(τ̃)`. -/
noncomputable def aipwPartition {X : Type*} {n : ℕ}
    (part : Finpartition (Finset.univ : Finset (Fin n)))
    (pH m₀H m₁H : Finset (Fin n) → X → ℝ) (z : Fin n → Obs X) (train : Fin n → Bool) : ℝ :=
  clipUnit ((2 / (n : ℝ)) * ∑ i, if train i then 0 else
    drScore (pH (part.part i)) (m₀H (part.part i)) (m₁H (part.part i)) (z i))

/-- The per-part population loss of §4.1 (p. 21): `(1/|R|) Σ_{i ∈ R} (f(x_i) − g(x_i))²`,
e.g. `L_{P,R}(p) = (1/|R|) Σ_{i ∈ R} (p(X_i) − p⋆(X_i))²`. -/
noncomputable def partLoss {X : Type*} {n : ℕ} (x : Fin n → X) (R : Finset (Fin n))
    (f g : X → ℝ) : ℝ :=
  (1 / (R.card : ℝ)) * ∑ i ∈ R, (f (x i) - g (x i)) ^ 2

/-- The per-part empirical propensity loss of §4.1 (p. 21):
`L̂_{P,R}(p) = (2/|R|) Σ_{i ∈ R ∩ D_T} (T_i − p(X_i))²`, where `ω i = (T_i, 1{i ∈ D_T})`. -/
noncomputable def empLossP {X : Type*} {n : ℕ} (x : Fin n → X) (R : Finset (Fin n))
    (ω : Fin n → Bool × Bool) (p : X → ℝ) : ℝ :=
  (2 / (R.card : ℝ)) * ∑ i ∈ R, if (ω i).2 then ((if (ω i).1 then 1 else 0) - p (x i)) ^ 2 else 0

/-- `Bernoulli(p)` on `Bool` (`true` with probability `p`), for `p ∈ [0, 1]` (`p` is projected
onto `[0, 1]`, which changes nothing for the propensities used here). -/
noncomputable def bernoulliMeasure (p : ℝ) : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false (Set.projIcc (0 : ℝ) 1 zero_le_one p)

/-- The fair coin `Bernoulli(1/2)` on `Bool`: the random training/validation split. -/
noncomputable def fairCoin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

/-- Law of `n` i.i.d. observations from `C_D` together with an independent random split. -/
noncomputable def splitSampleLaw {X : Type*} [MeasurableSpace X] (D : Study X) (n : ℕ) :
    Measure ((Fin n → Obs X) × (Fin n → Bool)) :=
  (Measure.pi fun _ : Fin n => observedLaw D).prod (Measure.pi fun _ : Fin n => fairCoin)

end MinimaxATE.Learnability


