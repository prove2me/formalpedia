-- Prove2me | Definitions.Def_GuthMaynardAffine
-- name    : GuthMaynardAffine
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T00:05:52.741313+00:00
-- url     : https://prove2.me/theorems/bbac149f-59ae-4804-b096-2c9d289e1a87
-- title:
--   Notation for the proof of Guth–Maynard's Lemma 9.2 — the affine sum gsum, the class Adm, the smoothing, the majorant G and its Fourier-side sums W, Σ, H, Z
-- statement:
--   Definitions used by the standalone steps `GuthMaynard.Affine.*` of the proof of Guth–Maynard's Proposition 9.1 (Lemma 9.2 and its proof, pp. 29–35). They build on the mission bundle `Def_GuthMaynard` (`GuthMaynard.dyadic M` is the set of integers $m$ with $M<m\le2M$, and `GuthMaynard.J M K f` is the paper's $J(f)$). Throughout, $\widehat f(\xi)=\int f(u)e(-\xi u)\,du$ with $e(x)=e^{2\pi ix}$ (Mathlib's `𝓕`).
--
--   - `gsum K M₁ M₂ M₃ f u` $=\sum_{|m_1|\sim M_1}\sum_{m_2\sim M_2}\sum_{|m_3|\le KM_3}f\big((m_1u+m_3)/m_2\big)$, where $|m_1|\sim M_1$ means $m_1$ or $-m_1$ is in `dyadic M₁`, $m_2\sim M_2$ means $m_2\in$ `dyadic M₂`, and $|m_3|\le KM_3$ means $|m_3|\le\lfloor KM_3\rfloor$. Then `J M K f` is the supremum over $M_1,M_2,M_3\in(0,M)$ of $\int\mathrm{gsum}^2$.
--   - `Adm C c T f` (the hypothesis class of Proposition 9.1): $f$ is $C^\infty$, $f\ge0$, its support lies in $[1/C,C]$, and $|\widehat f(\xi)|\le c(j,\varepsilon)\,T^\varepsilon(T/|\xi|)^j\sup f$ for every $j\in\mathbb N$, $\varepsilon>0$ and $\xi\ne0$.
--   - `β` is the smooth bump `βb` (a `ContDiffBump` about $0$ with radii $1$ and $2$), and `βint` $=\int\beta$. `ψ₁ K` is the bump `ψb K` with radii $|K|+1$ and $|K|+2$, and `B₀ K` $=\int\psi_1$.
--   - `ee x` $=e(x)$, and `fhat f` $=\widehat f$.
--   - `smooth T f x` $=T\int\beta(T(x-y))f(y)\,dy$ (the paper's $\tilde f$).
--   - `D₁ M₁` is the range $|m_1|\sim M_1$ of `gsum`, and `NK K M₃` $=\lceil(|K|+2)M_3\rceil$.
--   - `Gfun K M₁ M₂ M₃ f u` $=\sum_{|m_1|\sim M_1}\sum_{m_2\sim M_2}\sum_{|m_3|\le NK}\psi_1(m_3/M_3)f\big((m_1u+m_3)/m_2\big)$, and `Pfun K M₃ x` $=P(x)=\sum_{|m_3|\le NK}\psi_1(m_3/M_3)e(m_3x)$.
--   - `Ffun M₂ f m₁ ξ` $=F_{m_1}(\xi)=\sum_{m_2\sim M_2}(m_2/|m_1|)\widehat f(\xi m_2/m_1)$, and `Wfun K M₁ M₂ M₃ f ξ` $=W(\xi)=\sum_{|m_1|\sim M_1}|P(\xi/m_1)|\,|F_{m_1}(\xi)|$.
--   - `nearSet x r` is the set of integers $\ell$ with $\lceil x-r\rceil\le\ell\le\lfloor x+r\rfloor$, that is, $|\ell-x|\le r$. `Wnear K M₁ M₂ M₃ Q f ξ` $=\sum_{|m_1|\sim M_1}M_3B_0\,\#\{\ell:|\ell-\xi/m_1|\le Q/M_3\}\,|F_{m_1}(\xi)|$.
--   - `regII T η M₁ M₃` is the set of $\xi$ with $4T^\eta M_1/M_3<|\xi|\le T^{20}$.
--   - `Γfun M₂ f y` $=\Gamma(y)=\sum_{m_2\sim M_2}m_2\widehat f(m_2y)$, and `SigTerm Q M₂ M₃ f ℓ` $=\int_{|\tau|\le Q,\ |\ell+\tau/M_3|\ge2Q/M_3}|\Gamma(\ell+\tau/M_3)|^2\,d\tau$ (an extended nonnegative real).
--   - `Sig Q M₂ M₃ f` $=\Sigma=\sum_{\ell\ne0}$ `SigTerm` $\ell$. `SigLarge L …` and `SigSmall L …` are the parts of that sum with $|\ell|>L$ and with $|\ell|\le L$ respectively.
--   - `Hfun C M₂ g u` $=H(u)=\sum_{m_2,m_2'\sim M_2}\sum_{|j|\le\lfloor8CM_2\rfloor}g\big((m_2u+j)/m_2'\big)$.
--   - `Zfun L Δ` $=Z(\Delta)=\sum_{|\ell|\le\lceil2L\rceil}\beta(\ell/L)\,e(-\ell\Delta)$.
--   - `Regime T M M₁ M₂ M₃` collects the size conditions $1/2\le M_1<M$, $1/2\le M_2<M$, $1\le M_3\le2M$ and $M\le T^6$.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), pp. 29–35, notation for the proof of Proposition 9.1 (Lemma 9.2 and its proof)

import Mathlib
import Definitions.Def_GuthMaynard

/-!
# Notation for the proof of Guth–Maynard Proposition 9.1 (Lemma 9.2), pp. 29–35

The inner sum `gsum` of `GuthMaynard.J`, the hypothesis class `Adm`, and the objects used to state
the steps of the proof of Lemma 9.2: fixed bumps, the smoothing `smooth`, the majorant `Gfun`, the
exponential sum `Pfun`, the sums `Ffun`, `Wfun`, `Wnear`, `Γfun`, the sums `Sig`, `SigLarge`,
`SigSmall`, the affine sum `Hfun`, the sum `Zfun`, and the size hypotheses `Regime`.
-/

namespace GuthMaynard.Affine

open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal

/-- The inner sum of `J`: `∑_{|m₁| ∼ M₁, m₂ ∼ M₂, |m₃| ≤ K M₃} f((m₁u + m₃)/m₂)`. -/
noncomputable def gsum (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ m₁ ∈ dyadic M₁ ∪ (dyadic M₁).map (Equiv.neg ℤ).toEmbedding, ∑ m₂ ∈ dyadic M₂,
    ∑ m₃ ∈ Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋, f ((m₁ * u + m₃) / m₂)

/-- The hypothesis class of Proposition 9.1. -/
structure Adm (C : ℝ) (c : ℕ → ℝ → ℝ) (T : ℝ) (f : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) f
  nonneg : ∀ u, 0 ≤ f u
  supp : Function.support f ⊆ Set.Icc (1 / C) C
  decay : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
    ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * ⨆ u, f u

end GuthMaynard.Affine

namespace GuthMaynard.Affine

open GuthMaynard MeasureTheory FourierTransform
open scoped ENNReal

/-- The smooth bump with radii `1` and `2` about `0`. -/
noncomputable def βb : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The function of the bump `βb`. -/
noncomputable def β (x : ℝ) : ℝ := βb x

/-- `∫ β`. -/
noncomputable def βint : ℝ := ∫ x, β x

/-- The smooth bump with radii `|K| + 1` and `|K| + 2` about `0`. -/
noncomputable def ψb (K : ℝ) : ContDiffBump (0 : ℝ) :=
  ⟨|K| + 1, |K| + 2, by positivity, by linarith⟩

/-- The function of the bump `ψb K`. -/
noncomputable def ψ₁ (K x : ℝ) : ℝ := ψb K x

/-- `∫ ψ₁ K`. -/
noncomputable def B₀ (K : ℝ) : ℝ := ∫ x, ψ₁ K x

/-- `e(x) = exp(2πix)`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- `f̂ = 𝓕 f`. -/
noncomputable def fhat (f : ℝ → ℝ) (ξ : ℝ) : ℂ := 𝓕 (fun u => (f u : ℂ)) ξ

/-- The smoothing `f̃(x) = T ∫ β(T(x - y)) f(y) dy`. -/
noncomputable def smooth (T : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := T * ∫ y, β (T * (x - y)) * f y

/-- The range `|m₁| ∼ M₁` of `gsum`. -/
noncomputable def D₁ (M₁ : ℝ) : Finset ℤ := dyadic M₁ ∪ (dyadic M₁).map (Equiv.neg ℤ).toEmbedding

/-- The cut-off `⌈(|K| + 2) M₃⌉` for the `m₃`-sum of `Gfun`. -/
noncomputable def NK (K M₃ : ℝ) : ℤ := ⌈(|K| + 2) * M₃⌉

/-- `G(u) = ∑_{m₁, m₂} ∑_{|m₃| ≤ NK} ψ₁(m₃/M₃) f((m₁u + m₃)/m₂)`. -/
noncomputable def Gfun (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ m₁ ∈ D₁ M₁, ∑ m₂ ∈ dyadic M₂, ∑ m₃ ∈ Finset.Icc (-NK K M₃) (NK K M₃),
    ψ₁ K (m₃ / M₃) * f ((m₁ * u + m₃) / m₂)

/-- `P(x) = ∑_{m₃} ψ₁(m₃/M₃) e(m₃ x)`. -/
noncomputable def Pfun (K M₃ x : ℝ) : ℂ :=
  ∑ m₃ ∈ Finset.Icc (-NK K M₃) (NK K M₃), (ψ₁ K (m₃ / M₃) : ℂ) * ee (m₃ * x)

/-- `F_{m₁}(ξ) = ∑_{m₂} (m₂/|m₁|) f̂(ξ m₂/m₁)`. -/
noncomputable def Ffun (M₂ : ℝ) (f : ℝ → ℝ) (m₁ : ℤ) (ξ : ℝ) : ℂ :=
  ∑ m₂ ∈ dyadic M₂, (((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * fhat f (ξ * m₂ / m₁)

/-- `W(ξ) = ∑_{m₁} ‖P(ξ/m₁)‖ ‖F_{m₁}(ξ)‖`. -/
noncomputable def Wfun (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∑ m₁ ∈ D₁ M₁, ‖Pfun K M₃ (ξ / m₁)‖ * ‖Ffun M₂ f m₁ ξ‖

/-- The integers `ℓ` with `|ℓ - x| ≤ r`. -/
noncomputable def nearSet (x r : ℝ) : Finset ℤ := Finset.Icc ⌈x - r⌉ ⌊x + r⌋

/-- `∑_{m₁} M₃ B₀ #{ℓ : |ℓ - ξ/m₁| ≤ Q/M₃} ‖F_{m₁}(ξ)‖`. -/
noncomputable def Wnear (K M₁ M₂ M₃ Q : ℝ) (f : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∑ m₁ ∈ D₁ M₁, M₃ * B₀ K * ((nearSet (ξ / m₁) (Q / M₃)).card : ℝ) * ‖Ffun M₂ f m₁ ξ‖

/-- The set `4 T^η M₁/M₃ < |ξ| ≤ T²⁰`. -/
def regII (T η M₁ M₃ : ℝ) : Set ℝ := {ξ | 4 * T ^ η * M₁ / M₃ < |ξ| ∧ |ξ| ≤ T ^ 20}

/-- `Γ(y) = ∑_{m₂} m₂ f̂(m₂ y)`. -/
noncomputable def Γfun (M₂ : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℂ :=
  ∑ m₂ ∈ dyadic M₂, (m₂ : ℂ) * fhat f (m₂ * y)

/-- `∫_{|τ| ≤ Q, |ℓ + τ/M₃| ≥ 2Q/M₃} |Γ(ℓ + τ/M₃)|² dτ`. -/
noncomputable def SigTerm (Q M₂ M₃ : ℝ) (f : ℝ → ℝ) (ℓ : ℤ) : ℝ≥0∞ :=
  ∫⁻ τ in {τ : ℝ | |τ| ≤ Q ∧ 2 * Q / M₃ ≤ |(ℓ : ℝ) + τ / M₃|},
    ‖Γfun M₂ f (ℓ + τ / M₃)‖ₑ ^ 2

/-- `Σ = ∑_{ℓ ≠ 0} SigTerm ℓ`. -/
noncomputable def Sig (Q M₂ M₃ : ℝ) (f : ℝ → ℝ) : ℝ≥0∞ :=
  ∑' ℓ : ℤ, if ℓ = 0 then 0 else SigTerm Q M₂ M₃ f ℓ

/-- `∑_{ℓ ≠ 0, |ℓ| > L} SigTerm ℓ`. -/
noncomputable def SigLarge (L Q M₂ M₃ : ℝ) (f : ℝ → ℝ) : ℝ≥0∞ :=
  ∑' ℓ : ℤ, if ℓ ≠ 0 ∧ L < |(ℓ : ℝ)| then SigTerm Q M₂ M₃ f ℓ else 0

/-- `∑_{ℓ ≠ 0, |ℓ| ≤ L} SigTerm ℓ`. -/
noncomputable def SigSmall (L Q M₂ M₃ : ℝ) (f : ℝ → ℝ) : ℝ≥0∞ :=
  ∑' ℓ : ℤ, if ℓ ≠ 0 ∧ |(ℓ : ℝ)| ≤ L then SigTerm Q M₂ M₃ f ℓ else 0

/-- `H(u) = ∑_{m₂, m₂' ∼ M₂} ∑_{|j| ≤ 8CM₂} g((m₂u + j)/m₂')`. -/
noncomputable def Hfun (C M₂ : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂, ∑ j ∈ Finset.Icc (-⌊8 * C * M₂⌋) ⌊8 * C * M₂⌋,
    g ((m₂ * u + j) / m₂')

/-- `Z(Δ) = ∑_{|ℓ| ≤ ⌈2L⌉} β(ℓ/L) e(-ℓΔ)`. -/
noncomputable def Zfun (L Δ : ℝ) : ℂ :=
  ∑ ℓ ∈ Finset.Icc (-⌈2 * L⌉) ⌈2 * L⌉, (β (ℓ / L) : ℂ) * ee (-(ℓ * Δ))

/-- The size hypotheses `1/2 ≤ M₁ < M`, `1/2 ≤ M₂ < M`, `1 ≤ M₃ ≤ 2M`, `M ≤ T⁶`. -/
structure Regime (T M M₁ M₂ M₃ : ℝ) : Prop where
  h₁ : 1 / 2 ≤ M₁
  h₁M : M₁ < M
  h₂ : 1 / 2 ≤ M₂
  h₂M : M₂ < M
  h₃ : 1 ≤ M₃
  h₃M : M₃ ≤ 2 * M
  hMT : M ≤ T ^ 6

end GuthMaynard.Affine


