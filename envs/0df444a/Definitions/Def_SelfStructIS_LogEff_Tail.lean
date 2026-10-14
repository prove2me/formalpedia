-- Prove2me | Definitions.Def_SelfStructIS_LogEff_Tail
-- name    : SelfStructIS_LogEff_Tail
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:15.354636+00:00
-- url     : https://prove2.me/theorems/d5e1a959-24ae-47b3-9d7c-fbd05dea32e5
-- title:
--   §3.3, (16), (34a), App. A — the tail LDP, I*, Lᵤ, f_LD, c_ρ(u), T⁻¹, ψᵤ, λᵢ, aᵤ, bᵤ
-- statement:
--   This file fixes the objects of the paper's large-deviations analysis and of the proof of Theorem 5.1 (Appendix A).
--
--   1. **Large deviations principle** (§3.3, p. 11). A family of laws $(P_t)_{t>0}$ of random vectors $\xi_t$ satisfies an LDP with rate function $J:\mathbb R^d\to[-\infty,\infty]$ and speed $t$ if
--   $$\limsup_{t\to\infty}\frac1t\log P(\xi_t\in F)\le-\inf_{x\in F}J(x),\qquad \liminf_{t\to\infty}\frac1t\log P(\xi_t\in G)\ge-\inf_{x\in G}J(x)$$
--   for every closed $F$ and open $G$. A rate $I:\mathbb R^d_+\to\mathbb R$ is extended by $+\infty$ off $\mathbb R^d_+$.
--   2. **The constant $I^*$** ((16), p. 12). With $f_{LD}(y)=L^*(q^*y^{1/\alpha})$ ((34a), p. 27),
--   $$I^*=\inf\{I(y): L^*(q^*y^{1/\alpha})\ge 1,\ y\ge 0\}.$$
--   3. **Rescaled loss** ((34a), p. 27). $L_u(x)=u^{-1}L(q(t(u)x))$ on $\mathbb R^d_{++}$.
--   4. **Inverse map and its transport** (p. 27). $c_\rho(u)=(l/u)^{1/\rho}$, $T^{-1}$ the inverse of $T$, and $\psi_u=\Lambda\circ T^{-1}\circ q$.
--   5. **Hazard rates** (p. 33). $\lambda_i(x)=f_{X_i}(x)/\bar F_i(x)$, where $f_{X_i}$ is a density of $X_i$.
--   6. **The exponents of Lemma A.6** (p. 33). For $p\in\mathbb R^d_{++}$,
--   $$a_u(p)=\frac1{t(u)}\big[\log f_Y(\psi_u(t(u)p))-\log f_Y(t(u)p)\big],$$
--   $$b_u(p)=\frac1{t(u)}\Big[\sum_{i=1}^d\big(\log\lambda_i(T_i^{-1}(q(t(u)p)))-\log\lambda_i(q_i(t(u)p_i))\big)-\log J\big(T^{-1}(q(t(u)p))\big)\Big].$$
--
--   These quantities describe how the rare event $\{L(X)\ge u\}$ looks after the standardization $Y_u=Y/t(u)$, and how the self-structuring sampler's likelihood ratio factorizes along it.
--
--   **Formalization Note** Probabilities enter the LDP through `ENNReal.log`, so $\log 0=-\infty$ (in `EReal`) rather than Lean's real $\log 0=0$, and the rate takes values in `EReal`. $I^*$ is an `EReal` infimum: over an empty set it is $+\infty$. $T^{-1}$ is chosen by `Function.invFun`, which is the two-sided inverse whenever $T$ is bijective (Proposition 2.1's proof shows it is). The paper's p. 33 prints $\lambda_i=f_{X_i}/\Lambda_i$; the proof of Lemma A.6 on the same page uses the hazard rate $f_{X_i}/\bar F_i$, which is the one defined here.
-- source:
--   Deo, Murthy, Achieving Efficiency in Black-Box Simulation of Distribution Tails with Self-Structuring Importance Samplers, arXiv:2102.07060v3, p. 11, §3.3; p. 12, (16); p. 27, (34a); p. 33, Lemma A.6

import Mathlib
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler

namespace SelfStructIS.LogEff

open MeasureTheory Filter Topology

variable {d : ℕ}

/-- Large deviations principle with real speed, §3.3, p. 11: the family of laws `P t`
(of `ξ_t`) satisfies, as `t → ∞`,
`limsup (1/t) log P(ξ_t ∈ F) ≤ -inf_F J` for every closed `F` and
`liminf (1/t) log P(ξ_t ∈ G) ≥ -inf_G J` for every open `G`.
Logarithms are `ENNReal.log` (`log 0 = ⊥`) and the rate takes values in `EReal`. -/
def IsLDP (P : ℝ → Measure (Fin d → ℝ)) (J : (Fin d → ℝ) → EReal) : Prop :=
  (∀ F : Set (Fin d → ℝ), IsClosed F →
    limsup (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * ENNReal.log (P t F)) atTop ≤
      -(⨅ x ∈ F, J x)) ∧
  (∀ G : Set (Fin d → ℝ), IsOpen G →
    -(⨅ x ∈ G, J x) ≤
      liminf (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * ENNReal.log (P t G)) atTop)

/-- A rate `I : ℝᵈ₊ → ℝ` extended by `+∞` off `ℝᵈ₊`. -/
noncomputable def rateExt (I : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) : EReal :=
  if ∀ i, 0 ≤ y i then (I y : EReal) else ⊤

/-- `f_LD(y) = L*(q* y^{1/α})`, (34a), p. 27. -/
noncomputable def fLD (Lstar : (Fin d → ℝ) → ℝ) (qstar α : Fin d → ℝ) (y : Fin d → ℝ) : ℝ :=
  Lstar (qstar * fun i => y i ^ (1 / α i))

/-- `I* = inf {I(y) : L*(q* y^{1/α}) ≥ 1, y ≥ 0}`, (16), p. 12, in `EReal`
(an empty infimum is `+∞`). -/
noncomputable def Istar (Lstar : (Fin d → ℝ) → ℝ) (qstar α : Fin d → ℝ)
    (I : (Fin d → ℝ) → ℝ) : EReal :=
  ⨅ y ∈ {y : Fin d → ℝ | (∀ i, 0 ≤ y i) ∧ 1 ≤ fLD Lstar qstar α y}, (I y : EReal)

/-- `Lᵤ(x) = u⁻¹ L(q(t(u) x))`, (34a), p. 27 (used on `ℝᵈ₊₊`). -/
noncomputable def Lu (μ : Measure (Fin d → ℝ)) (L : (Fin d → ℝ) → ℝ) (ρ u : ℝ)
    (x : Fin d → ℝ) : ℝ :=
  u⁻¹ * L (qvec μ (tfun μ ρ u • x))

/-- `c_ρ(u) = (l/u)^{1/ρ}`, p. 27. -/
noncomputable def cRho (ρ u l : ℝ) : ℝ :=
  (l / u) ^ (1 / ρ)

/-- An inverse `T⁻¹` of the transformation `T`, chosen by `Function.invFun`
(it is the two-sided inverse whenever `T` is bijective). -/
noncomputable def Tinv (c : KappaChoice) (ρ u l : ℝ) : (Fin d → ℝ) → Fin d → ℝ :=
  Function.invFun (Tmap c ρ u l)

/-- `ψᵤ = Λ ∘ T⁻¹ ∘ q`, p. 27. -/
noncomputable def psiU (μ : Measure (Fin d → ℝ)) (c : KappaChoice) (ρ u l : ℝ)
    (y : Fin d → ℝ) : Fin d → ℝ :=
  hazardVec μ (Tinv c ρ u l (qvec μ y))

/-- The hazard rate `λᵢ(x) = f_{Xᵢ}(x)/F̄ᵢ(x)` of the `i`-th marginal with density `fXi i`,
p. 33. -/
noncomputable def hazardRate (μ : Measure (Fin d → ℝ)) (fXi : Fin d → ℝ → ℝ) (i : Fin d)
    (x : ℝ) : ℝ :=
  fXi i x / survival μ i x

/-- `aᵤ(p) = t(u)⁻¹ [log f_Y(ψᵤ(t(u)p)) - log f_Y(t(u)p)]`, Lemma A.6, p. 33. -/
noncomputable def aU (μ : Measure (Fin d → ℝ)) (fY : (Fin d → ℝ) → ℝ) (c : KappaChoice)
    (ρ u l : ℝ) (p : Fin d → ℝ) : ℝ :=
  (tfun μ ρ u)⁻¹ *
    (Real.log (fY (psiU μ c ρ u l (tfun μ ρ u • p))) - Real.log (fY (tfun μ ρ u • p)))

/-- `bᵤ(p) = t(u)⁻¹ [Σᵢ (log λᵢ(Tᵢ⁻¹(q(t(u)p))) - log λᵢ(qᵢ(t(u)pᵢ))) - log J(T⁻¹(q(t(u)p)))]`,
Lemma A.6, p. 33. -/
noncomputable def bU (μ : Measure (Fin d → ℝ)) (fXi : Fin d → ℝ → ℝ) (c : KappaChoice)
    (ρ u l : ℝ) (p : Fin d → ℝ) : ℝ :=
  (tfun μ ρ u)⁻¹ *
    ((∑ i, (Real.log (hazardRate μ fXi i (Tinv c ρ u l (qvec μ (tfun μ ρ u • p)) i)) -
        Real.log (hazardRate μ fXi i (qinv μ i (tfun μ ρ u * p i))))) -
      Real.log (Jac c ρ u l (Tinv c ρ u l (qvec μ (tfun μ ρ u • p)))))

end SelfStructIS.LogEff


