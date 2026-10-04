-- Prove2me | Definitions.Def_IntermediateDisorder_PointToLine_WienerChaos
-- name    : IntermediateDisorder_PointToLine_WienerChaos
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:04:07.486377+00:00
-- url     : https://prove2.me/theorems/fd5b92a9-69b3-420a-8cbb-891a50cf7304
-- title:
--   White noise on $[0,1]\times\mathbb R$, multiple stochastic integrals $I_k$, the kernels $\varrho_k$ and the Wiener chaos $\mathcal Z_\beta$
-- statement:
--   This file defines the continuum objects of Sections 2.2 and 3 of the paper.
--
--   **Space.** Write a point of $[0,1]^k\times\mathbb R^k$ as $z=((t_1,x_1),\dots,(t_k,x_k))$ and equip it with Lebesgue measure $\mu_k$ (for $k=0$, the unit mass on the single point). The **simplex** is $\Delta_k=\{0=t_0<t_1<\dots<t_k\le1\}$.
--
--   **Heat kernels.** $\varrho(t,x)=e^{-x^2/2t}/\sqrt{2\pi t}$ is the standard Gaussian heat kernel, and
--   $$\varrho_k(t,x)=\prod_{j=1}^k\varrho(t_j-t_{j-1},x_j-x_{j-1}),\qquad t_0=x_0=0,$$
--   on $\Delta_k\times\mathbb R^k$, extended by zero to $[0,1]^k\times\mathbb R^k$ (so $\varrho_0=1$).
--
--   **White noise.** Let $\mathcal B_f$ be the Borel subsets of $[0,1]\times\mathbb R$ of finite Lebesgue measure. A family $W=\{W(A):A\in\mathcal B_f\}$ of random variables on a probability space $(\Omega',Q')$ is a **white noise on $[0,1]\times\mathbb R$** if every finite subfamily $(W(A_1),\dots,W(A_m))$ is jointly Gaussian, $E[W(A)]=0$ and
--   $$E[W(A)W(B)]=|A\cap B|.$$
--
--   **Multiple stochastic integrals.** A family $I=(I_k)_{k\ge0}$ of continuous linear maps $I_k:L^2([0,1]^k\times\mathbb R^k)\to L^2(\Omega',Q')$ is the family of **multiple stochastic integrals** of $W$ if, for all pairwise disjoint $A_1,\dots,A_k\in\mathcal B_f$,
--   $$I_k\big(\mathbf 1_{A_1\times\dots\times A_k}\big)=\prod_{j=1}^kW(A_j)\quad\text{almost surely}.$$
--   For $k=0$ this says $I_0(1)=1$. Since these indicators span a dense subspace (the diagonals are null), the condition determines each $I_k$ uniquely; it is the paper's (26)–(27) together with the convention $I_k(g)=I_k(\operatorname{Sym}g)$ for non-symmetric $g$.
--
--   **Fock map and chaos.** For $g=(g_k)_{k\ge0}$ with $g_k\in L^2([0,1]^k\times\mathbb R^k)$ set $I(g)=\sum_{k\ge0}I_k(g_k)$, a sum in $L^2(Q')$. The **Wiener chaos** (7) is
--   $$\mathcal Z_\beta=I(\boldsymbol\varrho(\beta))=\sum_{k\ge0}\beta^kI_k(\varrho_k)=1+\sum_{k\ge1}\beta^k\int_{\Delta_k}\int_{\mathbb R^k}\prod_{i=1}^kW(t_i,x_i)\,\varrho(t_i-t_{i-1},x_i-x_{i-1})\,dx_i\,dt_i .$$
--
--   **Formalization Note** The paper's normalisation of $I_k$ is not consistent: §3.2 claims $\operatorname{Var}I_k(g)=\|g\|^2$ for symmetric $g$, which with (26) is $k!\|g\|^2$, and the remark on p. 19 writes $I_k(g)=k!\int_{\Delta_k}$. The convention here is fixed by (7) and the first-order computation on p. 6 ($\sigma^2=2\beta^2/\sqrt\pi=(\sqrt2\beta)^2\|\varrho_1\|^2$): for $g$ vanishing outside $\Delta_k\times\mathbb R^k$, the $k$-th chaos term $I_k(g)$ has second moment $\|g\|^2$, which the indicator condition above gives. Theorem 2.1 speaks of white noise on $\mathbb R_+\times\mathbb R$; only $t\in[0,1]$ enters (7) and Section 3 works on $[0,1]\times\mathbb R$ throughout, so the noise is defined there. $\varrho_k$ is turned into an $L^2$ element by a case split on $\varrho_k\in L^2$, and the sums are `tsum`s in $L^2(Q')$; the theorem on Section 3.4 shows that neither default value (zero) is ever taken.
-- source:
--   Alberts, Khanin, Quastel, The intermediate disorder regime for directed polymers in dimension 1+1, arXiv:1202.4398v3, p. 8, eq. (7) and Theorem 2.1; p. 17, §3.1 (ϱ_k, Δ_k) and §3.2 (white noise); pp. 18–19, eqs. (25)–(27) and the remark on p. 19; p. 20, §3.3 (Fock space)

import Mathlib

namespace IntermediateDisorder.PointToLine

open MeasureTheory ProbabilityTheory

/-- Lebesgue measure `dt dx` on the strip `[0,1] × ℝ`, as a measure on `ℝ × ℝ`
(first coordinate time `t`, second coordinate space `x`). -/
noncomputable def stripMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure ℝ)

/-- Lebesgue measure on `[0,1]^k × ℝ^k`, with a point written as `z : Fin k → ℝ × ℝ`,
`z j = (t_j, x_j)`. For `k = 0` this is the Dirac mass on the single point. -/
noncomputable def kernelMeasure (k : ℕ) : Measure (Fin k → ℝ × ℝ) :=
  Measure.pi fun _ => stripMeasure

/-- The point `z` preceded by the origin `(t_0, x_0) = (0, 0)`. -/
def withOrigin {k : ℕ} (z : Fin k → ℝ × ℝ) : Fin (k + 1) → ℝ × ℝ :=
  Fin.cons ((0 : ℝ), (0 : ℝ)) z

/-- The simplex `Δ_k = {0 = t_0 < t_1 < ⋯ < t_k ≤ 1}` (times only; space is free). -/
def simplex (k : ℕ) : Set (Fin k → ℝ × ℝ) :=
  {z | ∀ j : Fin k, (withOrigin z j.castSucc).1 < (z j).1 ∧ (z j).1 ≤ 1}

/-- The standard Gaussian heat kernel `ϱ(t, x) = e^{-x²/2t} / √(2πt)` (used for `t > 0`). -/
noncomputable def heatKernel (t x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 / (2 * t)) / Real.sqrt (2 * Real.pi * t)

/-- `ϱ_k(t, x) = ∏_{j=1}^k ϱ(t_j - t_{j-1}, x_j - x_{j-1})` on `Δ_k × ℝ^k`, with
`t_0 = x_0 = 0`, extended by zero off `Δ_k × ℝ^k`. For `k = 0` it is the constant `1`. -/
noncomputable def rhoK (k : ℕ) : (Fin k → ℝ × ℝ) → ℝ :=
  (simplex k).indicator fun z =>
    ∏ j : Fin k, heatKernel ((z j).1 - (withOrigin z j.castSucc).1)
      ((z j).2 - (withOrigin z j.castSucc).2)

open scoped Classical in
/-- `ϱ_k` as an element of `L²([0,1]^k × ℝ^k)` (the junk value `0` is taken only if
`ϱ_k ∉ L²`, which the §3.4 milestone rules out). -/
noncomputable def rhoKLp (k : ℕ) : Lp ℝ 2 (kernelMeasure k) :=
  if h : MemLp (rhoK k) 2 (kernelMeasure k) then h.toLp _ else 0

/-- Borel subsets of the strip `[0,1] × ℝ` of finite Lebesgue measure: the index set `𝓑_f` of
the white noise. -/
def FiniteStripSet : Type :=
  {A : Set (ℝ × ℝ) // MeasurableSet A ∧ A ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ∧ volume A ≠ ⊤}

/-- `W` is a white noise on `[0,1] × ℝ` under `Q` (§3.2): the family
`{W(A) : A ∈ 𝓑_f}` is a centred Gaussian process with `E[W(A) W(B)] = |A ∩ B|`. -/
structure IsWhiteNoise {Ω : Type*} [MeasurableSpace Ω] (W : Set (ℝ × ℝ) → Ω → ℝ)
    (Q : Measure Ω) : Prop where
  gaussian : IsGaussianProcess (fun A : FiniteStripSet => W A.1) Q
  mean_zero : ∀ A : FiniteStripSet, ∫ a, W A.1 a ∂Q = 0
  covariance : ∀ A B : FiniteStripSet,
    ∫ a, W A.1 a * W B.1 a ∂Q = (volume (A.1 ∩ B.1)).toReal

/-- `I = (I_k)_{k ≥ 0}` is the family of multiple stochastic integrals of the white noise `W`
(§3.2): each `I_k : L²([0,1]^k × ℝ^k) → L²(Q)` is continuous linear, and for pairwise
disjoint `A_1, …, A_k ∈ 𝓑_f` it sends the indicator of `A_1 × ⋯ × A_k` to `∏_j W(A_j)`.
These values determine every `I_k` (the indicators span a dense subspace); the result is
the paper's `I_k(g) = I_k(Sym g)`. For `k = 0` the condition says `I_0 1 = 1`.
The measurability and finiteness proofs are quantified over (they always exist). -/
def IsMultipleIntegral {Ω : Type*} [MeasurableSpace Ω] (W : Set (ℝ × ℝ) → Ω → ℝ)
    (Q : Measure Ω) (I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q) : Prop :=
  ∀ (k : ℕ) (A : Fin k → FiniteStripSet),
    Pairwise (fun i j => Disjoint (A i).1 (A j).1) →
    ∀ (hA : MeasurableSet (Set.univ.pi fun j => (A j).1))
      (hfin : kernelMeasure k (Set.univ.pi fun j => (A j).1) ≠ ⊤),
      (I k (indicatorConstLp 2 hA hfin (1 : ℝ)) : Ω → ℝ) =ᵐ[Q] fun a => ∏ j, W (A j).1 a

/-- The Fock-space map `I(g) = ∑_{k ≥ 0} I_k(g_k)`, an `L²(Q)`-valued sum. -/
noncomputable def fockIntegral {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    (I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q)
    (g : (k : ℕ) → Lp ℝ 2 (kernelMeasure k)) : Lp ℝ 2 Q :=
  ∑' k, I k (g k)

/-- The Wiener chaos (7):
`𝒵_β = 1 + ∑_{k ≥ 1} β^k ∫_{Δ_k} ∫_{ℝ^k} ∏ W(t_i, x_i) ϱ(t_i - t_{i-1}, x_i - x_{i-1}) dx_i dt_i
     = ∑_{k ≥ 0} β^k I_k(ϱ_k) = I(ϱ(β))`, as a random variable on `Ω`. -/
noncomputable def wienerChaos {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    (I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q) (β : ℝ) : Ω → ℝ :=
  fockIntegral I (fun k => β ^ k • rhoKLp k)

end IntermediateDisorder.PointToLine


