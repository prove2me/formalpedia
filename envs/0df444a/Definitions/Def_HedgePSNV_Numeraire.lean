-- Prove2me | Definitions.Def_HedgePSNV_Numeraire
-- name    : HedgePSNV_Numeraire
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:03:42.177359+00:00
-- url     : https://prove2.me/theorems/ea0dab0b-dc50-45ba-abd1-bf8ff6e768e6
-- title:
--   Numéraire measure $\mathbb P^R$, assets $N^0,N^1$, $\mathcal M_N$ and admissible strategies $\mathcal A_N$
-- statement:
--   The numéraire change of Gouriéroux–Laurent–Pham used in the proof of Theorem 1.
--
--   1. $\dfrac{d\mathbb P^R}{d\mathbb P}=\dfrac{(Z^M_T)^2}{Z^M_0}$ (EC.7.6).
--   2. $N^0_t=1/Z^M_t$ and $N^1_t=X_t/Z^M_t$ (EC.7.11).
--   3. $\mathcal M_N=\{\bar{\mathbb P}^R\sim\mathbb P:\ \frac{1}{Z^M_T}\frac{d\bar{\mathbb P}^R}{d\mathbb P}\in L^2(\mathbb P),\ N^0,N^1\text{ are }\bar{\mathbb P}^R\text{-martingales}\}$ (EC.7.14).
--   4. For an integrand $\zeta$ of $dZ^M_t=\zeta_t\,dX_t$, put $\psi_t=\sigma_tX_t\zeta_t$ (EC.7.8). By (EC.7.12), $dN^0_t=-(N^0_t)^2\psi_t\,dB^R_t$ and $dN^1_t=-N^0_t[N^1_t\psi_t-\sigma_tX_t]\,dB^R_t$ with $dB^R_t=dB_t+(\eta_t-\psi_tN^0_t)\,dt$. The gains $\pi_t(\varphi)=\int_0^t\varphi^0\,dN^0+\int_0^t\varphi^1\,dN^1$ (EC.7.18) of a portfolio $\varphi=(\varphi^0,\varphi^1)$ are defined through this decomposition.
--   5. $\mathcal A_N$ (EC.7.17): progressively measurable $\varphi$ with gains $\pi$, $Z^M_T\pi_T\in L^2(\mathbb P)$, and $\pi$ a $\bar{\mathbb P}^R$-martingale on $[0,T]$ for every $\bar{\mathbb P}^R\in\mathcal M_N$.
--
--   These objects appear in Lemmas EC.1, EC.3 and EC.4.
--
--   **Formalization Note** The paper integrates against the continuous semimartingales $N^0,N^1$, whose dynamics (EC.7.12) it derives by Itô's lemma from $dZ^M=\zeta\,dX$. The integral is defined through that decomposition, written under $\mathbb P$; the $dB$ part is the published `EthierKurtz.HasBrownianItoIntegral` relation and the drift is pathwise. Because $Z^M_t$ is a conditional expectation fixed separately for each $t$, the integrals run over progressively measurable versions of the coefficients, equal to them for almost every $t$, almost surely. Since the semimartingale decomposition is unique, it does not depend on which representing $\zeta$ is used; every statement carries $\zeta$ with the hypothesis $Z^M_t=Z^M_0+\int_0^t\zeta\,dX$.
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, (EC.7.6)–(EC.7.18), pp.ec28–ec30

import Mathlib
import Definitions.Def_HedgePSNV_Hedging

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV

namespace Model

variable {p : Params} {Ω : Type*} [m : MeasurableSpace Ω]

/-- The measure `P^R` of (EC.7.6), arXiv:2201.01026v4, p.ec28:
`dP^R/dP := (Z^M_T)²/Z^M_0`, so that `dP^R/dP^M = Z^M_T/Z^M_0`. -/
noncomputable def PR (M : Model p Ω) : Measure Ω :=
  M.P.withDensity (fun ω => ENNReal.ofReal (M.ZM p.T ω ^ 2 / M.ZM0))

/-- The numéraire-denominated dollar `N^0_t := 1/Z^M_t` of (EC.7.11), arXiv:2201.01026v4,
p.ec28. -/
noncomputable def N0 (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : ℝ := 1 / M.ZM t ω

/-- The numéraire-denominated asset `N^1_t := X_t/Z^M_t` of (EC.7.11), arXiv:2201.01026v4,
p.ec28. -/
noncomputable def N1 (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : ℝ := M.X t ω / M.ZM t ω

/-- The set `M_N` of (EC.7.14), arXiv:2201.01026v4, p.ec29:
`M_N := {P̄^R ∼ P : (1/Z^M_T)·dP̄^R/dP ∈ L²(P), N^0_t and N^1_t are P̄^R-martingales}`
(probability measures; martingales on `[0, T]` with respect to `F`). -/
def MN (M : Model p Ω) : Set (Measure Ω) :=
  {Q | IsProbabilityMeasure Q ∧ Q ≪ M.P ∧ M.P ≪ Q ∧
    MemLp (fun ω => (Q.rnDeriv M.P ω).toReal / M.ZM p.T ω) 2 M.P ∧
    IsMartingaleOn p.T M.F Q M.N0 ∧ IsMartingaleOn p.T M.F Q M.N1}

/-- `ψ_t := σ_tX_tζ_t` of (EC.7.8), arXiv:2201.01026v4, p.ec28, for an integrand `ζ` of
`dZ^M_t = ζ_t dX_t` (16), (EC.7.7). -/
def ψ (M : Model p Ω) (ζ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  M.σ t ω * M.X t ω * ζ t ω

/-- The `dB^R`-coefficient of a portfolio `(φ⁰, φ¹)` in the numéraire assets, read off the
dynamics (EC.7.12), arXiv:2201.01026v4, pp.ec28–ec29:
`dN^0_t = −(N^0_t)²ψ_t dB^R_t` and `dN^1_t = −N^0_t[N^1_tψ_t − σ_tX_t] dB^R_t`, so
`φ_t · dN_t = [φ⁰_t(−(N^0_t)²ψ_t) + φ¹_t(−N^0_t[N^1_tψ_t − σ_tX_t])] dB^R_t`. -/
noncomputable def NVol (M : Model p Ω) (ζ φ0 φ1 : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  φ0 t ω * (-(M.N0 t ω ^ 2 * M.ψ ζ t ω)) +
    φ1 t ω * (-(M.N0 t ω * (M.N1 t ω * M.ψ ζ t ω - M.σ t ω * M.X t ω)))

/-- The drift of `B^R` in terms of `B`, arXiv:2201.01026v4, (EC.7.10), p.ec28, with
`B^M_t = B_t + ∫_0^t η_s ds` (p.ec23): `dB^R_t = dB_t + (η_t − ψ_tN^0_t) dt`
(`ψ_t/Z^M_t = ψ_tN^0_t`). -/
noncomputable def RShift (M : Model p Ω) (ζ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  M.η t ω - M.ψ ζ t ω * M.N0 t ω

/-- `π` is the gains process `π_t(φ) = ∫_0^t φ⁰_s dN^0_s + ∫_0^t φ¹_s dN^1_s` of (EC.7.18),
arXiv:2201.01026v4, p.ec30, on `[0, T]` ("φ is N_t-integrable", (EC.7.17)), for the
numéraire assets driven by the integrand `ζ` of `dZ^M = ζ dX`: almost surely, for all `t ≤ T`,
`π_t = ∫_0^t w_u du + ∫_0^t v_u dB_u`, where `v`, `w` are progressively measurable versions of
`NVol ζ φ⁰ φ¹` and `NVol ζ φ⁰ φ¹ · (η − ψN^0)`.

**Formalization Note** The paper integrates against the continuous semimartingales `N^0`,
`N^1`, whose dynamics (EC.7.12) it derives by Itô's lemma from `dZ^M_t = ζ_t dX_t` (EC.7.7).
The integral is defined here through that decomposition, written under `P` with
`dB^R = dB + (η − ψN^0) dt`; the stochastic part is the published relation
`EthierKurtz.HasBrownianItoIntegral` (integrand cut off after `T`, every-path square
integrability) and the drift is a pathwise interval integral, as for `IsXGains`. `N^0`, `N^1`
are built on `Z^M_t`, a conditional expectation fixed separately for each `t` up to a null set,
so `t ↦ NVol … t ω` need not be measurable; the integrals therefore run over progressive
versions `v`, `w` that agree with it for almost every `t`, almost surely (the continuous
version of `Z^M` supplies them, and by Fubini the integrals do not depend on the versions). The
semimartingale decomposition of `N` is unique, so the relation does not depend on which
representing `ζ` is used; every statement using it carries `ζ` with the hypothesis
`Z^M_t = Z^M_0 + ∫_0^t ζ dX`. -/
def IsNGains (M : Model p Ω) (ζ φ0 φ1 π : ℝ≥0 → Ω → ℝ) : Prop :=
  ∃ v w K : ℝ≥0 → Ω → ℝ, IsStronglyProgressive M.F v ∧ IsStronglyProgressive M.F w ∧
    (∀ᵐ u ∂(volume.restrict (Set.Icc (0 : ℝ) (p.T : ℝ))), ∀ᵐ ω ∂M.P,
      v u.toNNReal ω = M.NVol ζ φ0 φ1 u.toNNReal ω ∧
      w u.toNNReal ω = M.NVol ζ φ0 φ1 u.toNNReal ω * M.RShift ζ u.toNNReal ω) ∧
    (∀ ω, ∀ t : ℝ≥0, t ≤ p.T →
      IntervalIntegrable (fun u : ℝ => w u.toNNReal ω) volume 0 (t : ℝ)) ∧
    EthierKurtz.HasBrownianItoIntegral M.P (fun t => M.F t) M.B
      (fun t ω => if t ≤ p.T then v t ω else 0) K ∧
    ∀ᵐ ω ∂M.P, ∀ t : ℝ≥0, t ≤ p.T →
      π t ω = (∫ u in (0 : ℝ)..(t : ℝ), w u.toNNReal ω) + K t ω

/-- The admissible strategies `A_N` in the numéraire assets, arXiv:2201.01026v4, (EC.7.17),
p.ec30, with the gains process attached: `((φ⁰, φ¹), π) ∈ A_N` when `φ⁰`, `φ¹` are
progressively measurable with respect to `F`, `π = ∫_0^· φ · dN` on `[0, T]` (`IsNGains`),
`Z^M_T π_T ∈ L²(P)`, and `π` is a `P̄^R`-martingale on `[0, T]` for every `P̄^R ∈ M_N`.

**Formalization Note** As for `A_X`, the paper's "adapted" integrand is taken progressively
measurable and the gains process is carried in an `F`-adapted version. -/
def AN (M : Model p Ω) (ζ : ℝ≥0 → Ω → ℝ) :
    Set (((ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) × (ℝ≥0 → Ω → ℝ)) :=
  {φπ | IsStronglyProgressive M.F φπ.1.1 ∧ IsStronglyProgressive M.F φπ.1.2 ∧
    StronglyAdapted M.F φπ.2 ∧ M.IsNGains ζ φπ.1.1 φπ.1.2 φπ.2 ∧
    MemLp (fun ω => M.ZM p.T ω * φπ.2 p.T ω) 2 M.P ∧
    ∀ Q ∈ M.MN, IsMartingaleOn p.T M.F Q φπ.2}

end Model

end HedgePSNV


