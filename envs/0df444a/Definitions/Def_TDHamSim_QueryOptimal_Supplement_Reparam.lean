-- Prove2me | Definitions.Def_TDHamSim_QueryOptimal_Supplement_Reparam
-- name    : TDHamSim_QueryOptimal_Supplement_Reparam
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:13:07.144737+00:00
-- url     : https://prove2.me/theorems/f37c94ff-ec92-4c71-983c-aeaa07465e59
-- title:
--   Integrated normalization, regularized time change and reparameterized Hamiltonian
-- statement:
--   Let $T>0$ and let $h:[0,T]\to[0,\infty)$ be an envelope of the Hamiltonian norm. Equations (88)–(90) define
--
--   $$\Lambda_h=\int_0^T h(t)\,dt,\qquad \mu=\frac{\Lambda_h}{T},\qquad g(t)=h(t)+\mu,\qquad F(t)=\int_0^t g(u)\,du,$$
--
--   the inverse clock $\tau=F^{-1}:[0,2\Lambda_h]\to[0,T]$, and the reparameterized Hamiltonian
--
--   $$\widetilde H(s)=\frac{H(\tau(s))}{g(\tau(s))}.$$
--
--   The inverse is constructed by choosing, for each $s$, a preimage of $s$ under $F$ in $[0,T]$; Lemma 14 proves that this preimage exists and is unique for $s\in[0,2\Lambda_h]$, so no property of $\tau$ is assumed. The module also defines the two resource scales of Theorem 15:
--
--   $$q_{L^1}(\Lambda,\varepsilon)=\Lambda+\frac{\log(1/\varepsilon)}{\log\big(e+\log(1/\varepsilon)/\Lambda\big)},\qquad N_{L^1}=a+\log\Big(1+\frac{\Lambda+(\beta+\beta_h)T^2}{\varepsilon}\Big).$$
--
--   These objects are the substrate of the time-integrated-norm extension in §8: they turn a Hamiltonian that is large only on part of the interval into one with normalization one on a longer interval of length $2\Lambda_h$.
--
--   **Formalization Note** Functions are total on $\mathbb R$; only their values on $[0,T]$ (respectively $[0,2\Lambda_h]$) are used. Logarithms are natural. The reparameterized oracle of Definition 4 is not a new definition: it is the base predicate `IsHAMT` applied to $\widetilde H$ with normalization $1$ and horizon $2\Lambda_h$.
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), (88)–(90), p.36; (95) and Theorem 15, p.38. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_Resources

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal.Supplement

open TDHamSim.QueryOptimal

/-- (88), p.36: the integrated normalization `Λ_h = ∫_0^T h(t) dt` of an envelope `h`. -/
noncomputable def intNorm (h : ℝ → ℝ) (T : ℝ) : ℝ := ∫ t in (0 : ℝ)..T, h t

/-- (89), p.36: `µ = Λ_h / T`. -/
noncomputable def mu (h : ℝ → ℝ) (T : ℝ) : ℝ := intNorm h T / T

/-- (89), p.36: the regularized rate `g(t) = h(t) + µ`. -/
noncomputable def gReg (h : ℝ → ℝ) (T : ℝ) (t : ℝ) : ℝ := h t + mu h T

/-- (89), p.36: the new clock `F(t) = ∫_0^t g(u) du`. -/
noncomputable def Fclock (h : ℝ → ℝ) (T : ℝ) (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, gReg h T u

/-- (90), p.36: `τ = F⁻¹`, the inverse of `F` restricted to `[0,T]`, built by choosing a
preimage in `[0,T]`; outside the range `F([0,T])` its value is an arbitrary default. -/
noncomputable def tau (h : ℝ → ℝ) (T : ℝ) : ℝ → ℝ :=
  Function.invFunOn (Fclock h T) (Set.Icc 0 T)

/-- (90), p.36: the reparameterized Hamiltonian `H̃(s) = H(τ(s)) / g(τ(s))`. -/
noncomputable def Htilde {n : ℕ} (H : ℝ → Mat (Bits n)) (h : ℝ → ℝ) (T : ℝ) (s : ℝ) :
    Mat (Bits n) :=
  ((gReg h T (tau h T s) : ℂ)⁻¹) • H (tau h T s)

/-- (95), p.38: `q_{L¹} = Λ + log(1/ε) / log(e + log(1/ε)/Λ)`. -/
noncomputable def qL1 (Λ ε : ℝ) : ℝ :=
  Λ + Real.log (1 / ε) / Real.log (Real.exp 1 + Real.log (1 / ε) / Λ)

/-- Theorem 15, p.38: the space and gate scale `a + log(1 + (Λ + (β+β_h)T²)/ε)`. -/
noncomputable def nL1 (a : ℕ) (β βh T Λ ε : ℝ) : ℝ :=
  a + Real.log (1 + (Λ + (β + βh) * T ^ 2) / ε)

end TDHamSim.QueryOptimal.Supplement


