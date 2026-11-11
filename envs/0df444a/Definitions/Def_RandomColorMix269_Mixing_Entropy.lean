-- Prove2me | Definitions.Def_RandomColorMix269_Mixing_Entropy
-- name    : RandomColorMix269_Mixing_Entropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:49.910143+00:00
-- url     : https://prove2.me/theorems/58aecc07-2ca6-4161-9ffc-8833d145af00
-- title:
--   §5.1 — entropy, block entropy, Dirichlet forms, spectral gaps and relaxation times of heat-bath dynamics
-- statement:
--   For a law $\mu$ and a function $f$, $\mathbb E_\mu f=\sum_x\mu(x)f(x)$, $\mathrm{Var}_\mu f=\mathbb E_\mu f^2-(\mathbb E_\mu f)^2$ and, for $f\ge0$,
--   $$
--   \mathrm{Ent}_\mu f=\mathbb E_\mu[f\ln f]-\mathbb E_\mu f\ln\mathbb E_\mu f,\qquad 0\ln0=0 .
--   $$
--   For $T\subseteq V$, $\mathrm{Ent}^T_\mu(f)=\mathbb E_{\tau\sim\mu_{V\setminus T}}\mathrm{Ent}_{\mu^\tau}f$ is the average entropy after fixing all coordinates outside $T$; $\mathbb E_\mu[\mathrm{Var}(f\mid X_{V\setminus T})]$ is the analogous block variance (p.28).
--
--   For blocks $B_i$ with positive rates $w_i$, the heat-bath block dynamics $\mathcal L_{\mathcal B}=\sum_iw_i(K_{B_i}-I)$ has Dirichlet form $\mathcal E(f,f)=\sum_iw_i\,\mathbb E_\mu[\mathrm{Var}(f\mid X_{V\setminus B_i})]$. Its spectral gap is
--   $$
--   \lambda_{\mathrm{gap}}=\inf_{\mathrm{Var}_\mu f>0}\frac{\mathcal E(f,f)}{\mathrm{Var}_\mu f},\qquad T_{\mathrm{rel}}=\lambda_{\mathrm{gap}}^{-1},\ 1/0=\infty
--   $$
--   (p.27). The single-site continuous chain $\sum_v(K_v-I)$ has rate one per vertex; the discrete Glauber kernel $P^{GD}=|V|^{-1}\sum_vK_v$ has Dirichlet form $|V|^{-1}\sum_v\mathbb E_\mu[\mathrm{Var}(f\mid X_{V\setminus v})]$. The overlap factor of a weighted cover is $\max_v\sum_{i:\,v\in B_i}w_i$.
--
--   Block factorization with factor $C$ at size $r$ means $\frac r{|V|}\mathrm{Ent}_\mu f\le C\binom{|V|}r^{-1}\sum_{|T|=r}\mathrm{Ent}^T_\mu f$ for all $f\ge0$ (equation (10)); single-site factorization means $\mathrm{Ent}_\mu f\le C\sum_v\mathrm{Ent}^v_\mu f$. Also $R_0(\gamma,b)=\lceil4\gamma/b^2\rceil$ and the factor bound $\big((N-R_0)/(r-R_0)\big)^{R_0}$ of Theorem 5.7. The residual subspace $H=\{h:\mathbb E_\mu[h\mid X_U]=0\}$ is nonzero when some $h$ in it has $\mathbb E_\mu h^2>0$.
--
--   **Formalization Note** Gaps and relaxation times are in $[0,\infty]$: with no positive-variance function the gap is $\infty$ and the relaxation time $0$; a zero gap gives relaxation time $\infty$. Conditional expectations divide by the pinning mass and are used only under $\mu$-weighted sums.
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, pp.27–29 (§5.1), equation (9), equation (10), Remark 5.8

import Definitions.Def_RandomColorMix269_Mixing_Independence

open scoped Classical BigOperators ENNReal
open Finset
set_option autoImplicit false
noncomputable section

namespace RandomColorMix269.Mixing

/-! §5.1 pp.27–29. Gap and relaxation are extended nonnegative reals:
empty positive-variance class gives gap ∞ and relaxation 0;
zero gap gives relaxation ∞. All operators below are conditional
expectations, on genuine finite probability masses. -/
variable {A : Type*} [Fintype A]

def mean (μ f : A → ℝ) : ℝ := ∑ x, μ x * f x

def variance (μ f : A → ℝ) : ℝ := mean μ (fun x => (f x)^2) - (mean μ f)^2

def entropy (μ f : A → ℝ) : ℝ :=
  mean μ (fun x => f x * Real.log (f x)) - mean μ f * Real.log (mean μ f)

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}

def blockEntropy (μ : (V → Fin q) → ℝ) (T : Finset V) (f : (V → Fin q) → ℝ) : ℝ :=
  ∑ x, μ x *
    (SpinGirth5.condExp μ Tᶜ (fun y => f y * Real.log (f y)) x -
      SpinGirth5.condExp μ Tᶜ f x * Real.log (SpinGirth5.condExp μ Tᶜ f x))

def blockVariance (μ : (V → Fin q) → ℝ) (T : Finset V) (f : (V → Fin q) → ℝ) : ℝ :=
  ∑ x, μ x * (SpinGirth5.condExp μ Tᶜ (fun y => (f y)^2) x -
    (SpinGirth5.condExp μ Tᶜ f x)^2)

/-- Infimum in ℝ≥0∞, not a real infimum of a possibly empty set. -/
def variationalGap (μ : (V → Fin q) → ℝ) (E : ((V → Fin q) → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨅ f : {f : (V → Fin q) → ℝ // 0 < variance μ f},
    ENNReal.ofReal (E f / variance μ f)

def relaxation (μ : (V → Fin q) → ℝ) (E : ((V → Fin q) → ℝ) → ℝ) : ℝ≥0∞ :=
  (variationalGap μ E)⁻¹

def singleEnergy (μ : (V → Fin q) → ℝ) (f : (V → Fin q) → ℝ) : ℝ :=
  ∑ v : V, blockVariance μ {v} f

/-- Rate one at each vertex, the paper's continuous single-site chain. -/
def singleRelaxation (μ : (V → Fin q) → ℝ) : ℝ≥0∞ := relaxation μ (singleEnergy μ)

/-- One uniformly chosen vertex per discrete step. -/
def discreteRelaxation (μ : (V → Fin q) → ℝ) : ℝ≥0∞ :=
  relaxation μ (fun f => singleEnergy μ f / Fintype.card V)

def weightedEnergy {I : Type*} [Fintype I] (μ : (V → Fin q) → ℝ)
    (B : I → Finset V) (w : I → ℝ) (f : (V → Fin q) → ℝ) : ℝ :=
  ∑ i, w i * blockVariance μ (B i) f

def weightedRelaxation {I : Type*} [Fintype I] (μ : (V → Fin q) → ℝ)
    (B : I → Finset V) (w : I → ℝ) : ℝ≥0∞ :=
  relaxation μ (weightedEnergy μ B w)

def overlap [Nonempty V] {I : Type*} [Fintype I] (B : I → Finset V) (w : I → ℝ) : ℝ :=
  (univ : Finset V).sup' (by exact Finset.univ_nonempty_iff.mpr inferInstance)
    (fun v => ∑ i, if v ∈ B i then w i else 0)

/-- Uniform average on all r-subsets of W; used only with r ≤ |W|. -/
def subsetAverage (W : Finset V) (r : ℕ) (F : Finset V → ℝ) : ℝ :=
  let subsets := W.powerset.filter fun T => T.card = r
  (∑ T ∈ subsets, F T) / subsets.card

def BlockFactorization (μ : (V → Fin q) → ℝ) (r : ℕ) (C : ℝ) : Prop :=
  ∀ f : (V → Fin q) → ℝ, (∀ x, 0 ≤ f x) →
    (r : ℝ) / Fintype.card V * entropy μ f ≤
      C * subsetAverage univ r (fun T => blockEntropy μ T f)

def SingleFactorization (μ : (V → Fin q) → ℝ) (C : ℝ) : Prop :=
  ∀ f : (V → Fin q) → ℝ, (∀ x, 0 ≤ f x) →
    entropy μ f ≤ C * ∑ v : V, blockEntropy μ {v} f

def Rzero (γ b : ℝ) : ℕ := ⌈4 * γ / b^2⌉₊

def factorBound (N r R : ℕ) : ℝ := (((N : ℝ) - R) / ((r : ℝ) - R)) ^ R

def ResidualNonzero (μ : (V → Fin q) → ℝ) (U : Finset V) : Prop :=
  ∃ h : (V → Fin q) → ℝ, 0 < mean μ (fun x => (h x)^2) ∧
    ∀ x, 0 < μ x → SpinGirth5.condExp μ U h x = 0

end RandomColorMix269.Mixing


