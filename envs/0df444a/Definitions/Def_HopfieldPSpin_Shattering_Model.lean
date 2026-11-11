-- Prove2me | Definitions.Def_HopfieldPSpin_Shattering_Model
-- name    : HopfieldPSpin_Shattering_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:07:47.096044+00:00
-- url     : https://prove2.me/theorems/9e8c1551-2757-40f9-b8f7-5df9baaa86ee
-- title:
--   The $p$-spin Hopfield model: configurations, patterns, Hebbian couplings, Hamiltonian (2.1), Gibbs measure, $X_k$, $Q_{n,p}$, $v_{n,p}$ and the norm events
-- statement:
--   For $n\in\mathbb N$ the **configurations** are $\Sigma_n=\{-1,1\}^n$; for $I\subseteq[n]$, $\sigma_I=\prod_{i\in I}\sigma_i$. The **normalized overlap** is $R_n(\sigma,\tau)=\frac1n\sum_i\sigma_i\tau_i$ and the **normalized Hamming distance** is $d_n(\sigma,\tau)=d_H(\sigma,\tau)/n$.
--
--   The **disorder** consists of $M$ patterns $\eta^1,\dots,\eta^M\in\mathbb R^n$ whose $nM$ entries $\eta^k_i$ are i.i.d. with one of two **pattern laws**: standard Gaussian $N(0,1)$ or Rademacher $\tfrac12(\delta_{-1}+\delta_1)$. Their joint law is the product measure $\mathbb P$ on $\mathbb R^{M\times n}$.
--
--   With $\eta^k_I=\prod_{i\in I}\eta^k_i$, the **Hebbian couplings** and the **Hamiltonian** are
--   $$\hat J_I=\frac1{\sqrt M}\sum_{k=1}^M\eta^k_I,\qquad H_n(\sigma)=\frac{\sqrt{p!}}{n^{(p-1)/2}}\sum_{I\in\binom{[n]}{p}}\hat J_I\,\sigma_I ,$$
--   a sum over size-$p$ subsets only (distinct indices). The **partition function** is $Z_n(\beta)=\sum_{\sigma\in\Sigma_n}e^{\beta H_n(\sigma)}$ and the **Gibbs measure** is $\mu_{n,\beta}(\sigma)=e^{\beta H_n(\sigma)}/Z_n(\beta)$.
--
--   The one-pattern fields (4.1) are $X_k(\sigma)=\sqrt{p!}\,n^{-p/2}\sum_{|I|=p}\eta^k_I\sigma_I$, so that $H_n=\sqrt{n/M}\sum_kX_k$. Further, (4.2) $Q_{n,p}(\sigma,\tau)=\frac{p!}{n^p}\sum_{|I|=p}\sigma_I\tau_I$, $v_{n,p}=(n)_p/n^p$ with $(n)_p=n(n-1)\cdots(n-p+1)$, and $D_n=v_{n,p}+Q_{n,p}$.
--
--   With $L=2$, the **norm events** of Lemma 4.6 are $E_k=\{\|\eta^k\|_2\le L\sqrt n\}$ and $T_n=\bigcap_{k=1}^ME_k$; $\iota_L=\tfrac12(L^2-1-\log L^2)$ and $U_n=2L^pn^{p/2}/\sqrt{p!}$ (4.12). The truncated exponential moments are $\mathbb E[e^{sH_n(\sigma)}\mathbf 1_{T_n}]$ and $\mathbb E[e^{s(H_n(\sigma)+H_n(\tau))}\mathbf 1_{T_n}]$, and $A_n(\beta)$ is the first one at $s=\beta$, $\sigma=(1,\dots,1)$ (4.27). The **storage condition** (2.2) for a sequence $M=M_n$ is $M_n/n^{p-1}\to\alpha$.
--
--   **Formalization Note.** Spins are `Fin n → ℤˣ`; the disorder is a function `η : Fin M → Fin n → ℝ` (`η k i` $=\eta^{k+1}_{i+1}$) with law `Measure.pi` of `Measure.pi` of the entry law; the Rademacher law is `(1/2) • (dirac (-1) + dirac 1)` and the Gaussian law is Mathlib's `gaussianReal 0 1`. The Gibbs measure is a mass function on the finite set $\Sigma_n$. All logarithms are natural. For $M=0$ Lean's $1/\sqrt0=0$ gives $H_n=0$; only large $n$, where $M_n\ge1$, matters.
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), pp. 4–5 (PDF 6–7), (2.1), (2.2); pp. 15, 18, 19, 23 (PDF 17, 20, 21, 25), (4.1), (4.2), Lemma 4.6, (4.12), (4.27)

import Mathlib

open MeasureTheory

noncomputable section

namespace HopfieldPSpin.Shattering

/-- Spin configurations `Σ_n = {-1, 1}^n`, encoded as `Fin n → ℤˣ` (the units of `ℤ` are
exactly `-1` and `1`). Kızıldağ–Şahin, p. 4. -/
abbrev Config (n : ℕ) : Type := Fin n → ℤˣ

/-- The real value `σ_i ∈ {-1, 1}` of the `i`-th spin. -/
def spin {n : ℕ} (σ : Config n) (i : Fin n) : ℝ := ((σ i : ℤ) : ℝ)

/-- `σ_I = ∏_{i ∈ I} σ_i` for `I ⊆ [n]` (p. 4). -/
def spinProd {n : ℕ} (σ : Config n) (I : Finset (Fin n)) : ℝ := ∏ i ∈ I, spin σ i

/-- The all-ones configuration `1 = (1, …, 1)`. -/
def allOnes (n : ℕ) : Config n := fun _ => 1

/-- Normalized overlap `R_n(σ, τ) = n⁻¹ ∑_i σ_i τ_i` (p. 5). -/
def overlap {n : ℕ} (σ τ : Config n) : ℝ := (1 / (n : ℝ)) * ∑ i, spin σ i * spin τ i

/-- Normalized Hamming distance `d_n(σ, τ) = d_H(σ, τ) / n` (p. 5). -/
def normDist {n : ℕ} (σ τ : Config n) : ℝ := (hammingDist σ τ : ℝ) / (n : ℝ)

/-- The two pattern laws of the paper (p. 4): i.i.d. `N(0,1)` or i.i.d. Rademacher entries. -/
inductive PatternLaw : Type
  | gaussian : PatternLaw
  | rademacher : PatternLaw

/-- The Rademacher law `½(δ_{-1} + δ_1)` on `ℝ`. -/
def rademacherMeasure : Measure ℝ :=
  (1 / 2 : ENNReal) • (Measure.dirac (-1 : ℝ) + Measure.dirac (1 : ℝ))

/-- The one-dimensional law of a pattern entry. -/
def PatternLaw.measure : PatternLaw → Measure ℝ
  | .gaussian => ProbabilityTheory.gaussianReal 0 1
  | .rademacher => rademacherMeasure

instance isProbabilityMeasure_rademacherMeasure : IsProbabilityMeasure rademacherMeasure := by
  constructor
  simp only [rademacherMeasure, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply_of_mem,
    Set.mem_univ, smul_eq_mul]
  rw [← two_mul, ← mul_assoc, ENNReal.div_mul_cancel] <;> simp

instance isProbabilityMeasure_patternLaw (law : PatternLaw) : IsProbabilityMeasure law.measure := by
  cases law
  · exact (inferInstance : IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 1))
  · exact isProbabilityMeasure_rademacherMeasure

/-- The law of the disorder: the patterns `η^1, …, η^M ∈ ℝ^n` (pattern `k` is `η k`, its
`i`-th coordinate `η k i`), all `M · n` entries i.i.d. with the given pattern law. -/
def disorderLaw (n M : ℕ) (law : PatternLaw) : Measure (Fin M → Fin n → ℝ) :=
  Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin n => law.measure

/-- `η^k_I = ∏_{i ∈ I} η^k_i`. -/
def patternProd {n M : ℕ} (η : Fin M → Fin n → ℝ) (k : Fin M) (I : Finset (Fin n)) : ℝ :=
  ∏ i ∈ I, η k i

/-- Hebbian couplings `Ĵ_I = M^{-1/2} ∑_{k=1}^M η^k_I` (2.1). -/
def coupling {n M : ℕ} (η : Fin M → Fin n → ℝ) (I : Finset (Fin n)) : ℝ :=
  (1 / Real.sqrt (M : ℝ)) * ∑ k, patternProd η k I

/-- The Hamiltonian (2.1): `H_n(σ) = √(p!) n^{-(p-1)/2} ∑_{I ∈ ([n] choose p)} Ĵ_I σ_I`,
summing over size-`p` subsets (distinct indices only). -/
def hamiltonian (n M p : ℕ) (η : Fin M → Fin n → ℝ) (σ : Config n) : ℝ :=
  Real.sqrt (p.factorial : ℝ) / (n : ℝ) ^ (((p : ℝ) - 1) / 2) *
    ∑ I ∈ Finset.powersetCard p (Finset.univ : Finset (Fin n)), coupling η I * spinProd σ I

/-- One-pattern field (4.1): `X_k(σ) = √(p!) n^{-p/2} ∑_{|I| = p} η^k_I σ_I`. -/
def patternField (n M p : ℕ) (η : Fin M → Fin n → ℝ) (k : Fin M) (σ : Config n) : ℝ :=
  Real.sqrt (p.factorial : ℝ) / (n : ℝ) ^ ((p : ℝ) / 2) *
    ∑ I ∈ Finset.powersetCard p (Finset.univ : Finset (Fin n)), patternProd η k I * spinProd σ I

/-- Partition function `Z_n(β) = ∑_{σ ∈ Σ_n} e^{β H_n(σ)}` (p. 5). -/
def partitionFn (n M p : ℕ) (β : ℝ) (η : Fin M → Fin n → ℝ) : ℝ :=
  ∑ σ : Config n, Real.exp (β * hamiltonian n M p η σ)

/-- Gibbs measure `µ_{n,β}(σ) = e^{β H_n(σ)} / Z_n(β)` (p. 5), as a probability mass function
on `Σ_n`. -/
def gibbs (n M p : ℕ) (β : ℝ) (η : Fin M → Fin n → ℝ) (σ : Config n) : ℝ :=
  Real.exp (β * hamiltonian n M p η σ) / partitionFn n M p β η

/-- `Q_{n,p}(σ, τ) = p! n^{-p} ∑_{|I| = p} σ_I τ_I` (4.2). -/
def covQ (n p : ℕ) (σ τ : Config n) : ℝ :=
  (p.factorial : ℝ) / (n : ℝ) ^ p *
    ∑ I ∈ Finset.powersetCard p (Finset.univ : Finset (Fin n)), spinProd σ I * spinProd τ I

/-- `v_{n,p} = (n)_p / n^p`, `(n)_p = n(n-1)⋯(n-p+1)` (4.2). -/
def covV (n p : ℕ) : ℝ := (n.descFactorial p : ℝ) / (n : ℝ) ^ p

/-- `D_n(σ, τ) = v_{n,p} + Q_{n,p}(σ, τ)` (Lemma 4.1). -/
def covD (n p : ℕ) (σ τ : Config n) : ℝ := covV n p + covQ n p σ τ

/-- The norm cutoff `L = 2` of Lemma 4.6. -/
def Lcut : ℝ := 2

/-- The norm event `E_k = {‖η^k‖₂ ≤ L √n}` with `L = 2` (Lemma 4.6). -/
def normEvent (n M : ℕ) (k : Fin M) : Set (Fin M → Fin n → ℝ) :=
  {η | Real.sqrt (∑ i, η k i ^ 2) ≤ Lcut * Real.sqrt (n : ℝ)}

/-- `T_n = ⋂_{k=1}^M E_k` (Lemma 4.6). -/
def normEventAll (n M : ℕ) : Set (Fin M → Fin n → ℝ) := ⋂ k, normEvent n M k

/-- `ι_L = ½ (L² − 1 − log L²)` with `L = 2` (Lemma 4.6). -/
def iotaL : ℝ := (1 / 2) * (Lcut ^ 2 - 1 - Real.log (Lcut ^ 2))

/-- `U_n = 2 L^p n^{p/2} / √(p!)` (4.12). -/
def bigU (n p : ℕ) : ℝ := 2 * Lcut ^ p * (n : ℝ) ^ ((p : ℝ) / 2) / Real.sqrt (p.factorial : ℝ)

/-- Truncated one-replica exponential moment `E[e^{s H_n(σ)} 1_{T_n}]`. -/
def truncMGF1 (n M p : ℕ) (law : PatternLaw) (s : ℝ) (σ : Config n) : ℝ :=
  ∫ η, (normEventAll n M).indicator (fun η => Real.exp (s * hamiltonian n M p η σ)) η
    ∂(disorderLaw n M law)

/-- Truncated two-replica exponential moment `E[e^{s (H_n(σ) + H_n(τ))} 1_{T_n}]`. -/
def truncMGF2 (n M p : ℕ) (law : PatternLaw) (s : ℝ) (σ τ : Config n) : ℝ :=
  ∫ η, (normEventAll n M).indicator
    (fun η => Real.exp (s * (hamiltonian n M p η σ + hamiltonian n M p η τ))) η
    ∂(disorderLaw n M law)

/-- `A_n(β) = E[e^{β H_n(σ)} 1_{T_n}]` evaluated at `σ = 1` (4.27). -/
def truncA (n M p : ℕ) (law : PatternLaw) (β : ℝ) : ℝ := truncMGF1 n M p law β (allOnes n)

/-- The storage condition (2.2): `M_n / n^{p-1} → α`. -/
def StorageCondition (p : ℕ) (M : ℕ → ℕ) (α : ℝ) : Prop :=
  Filter.Tendsto (fun n : ℕ => (M n : ℝ) / (n : ℝ) ^ (p - 1)) Filter.atTop (nhds α)

end HopfieldPSpin.Shattering


