-- Prove2me | Definitions.Def_MKVDPP_Weak_WeakControl
-- name    : MKVDPP_Weak_WeakControl
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T13:26:37.812468+00:00
-- url     : https://prove2.me/theorems/b2f0284e-3f41-422f-9fae-646776679da5
-- title:
--   Definition 2.1, (2.5), Remark 2.4, (3.1) — weak controls γ, the reward J(t,γ), the value V_W, the canonical space Ω⋆ and τ^γ
-- statement:
--   This file formalizes the weak formulation of the McKean–Vlasov control problem (Definition 2.1, (2.5), Remark 2.4 and §3.1.1 of Djete, Possamaï and Tan).
--
--   Fix $(t,\nu)\in[0,T]\times\mathcal P(\mathcal C^n)$, an exponent $p\ge0$ and $u_0\in U$. A **weak control** with initial condition $(t,\nu)$ is a tuple
--   $$\gamma=(\Omega^\gamma,\mathcal F^\gamma,\mathbb P^\gamma,\mathbb F^\gamma,\mathbb G^\gamma,X^\gamma,W^\gamma,B^\gamma,\bar\mu^\gamma,\mu^\gamma,\alpha^\gamma)$$
--   such that:
--
--   1. $\mathbb P^\gamma$ is a probability measure, $\mathcal G^\gamma_s\subseteq\mathcal F^\gamma_s$, and $\mathbb E[\mathbf 1_D\mid\mathcal G^\gamma_s]=\mathbb E[\mathbf 1_D\mid\mathcal G^\gamma_T]$ a.s. for all $D\in\mathcal F^\gamma_s\vee\sigma(W^\gamma)$ (2.2);
--   2. $X^\gamma$ is a continuous $\mathbb F^\gamma$-adapted $\mathbb R^n$-valued process, $\alpha^\gamma$ is a $U$-valued $\mathbb F^\gamma$-predictable process, and $\mathbb E[\|X^\gamma\|^p]+\mathbb E[\int_t^T\rho(\alpha^\gamma_s,u_0)^p\,ds]<\infty$ (2.3);
--   3. $(W^\gamma,B^\gamma)$ is continuous and $\mathbb F^\gamma$-adapted, $(W^{\gamma,t},B^{\gamma,t})$ is a standard $(d+\ell)$-dimensional $(\mathbb F^\gamma,\mathbb P^\gamma)$-Brownian motion on $[t,T]$, $B^{\gamma,t}$ is $\mathbb G^\gamma$-adapted, $\mathcal F^\gamma_t\vee\sigma(W^\gamma)$ is independent of $\mathcal G^\gamma_T$, and $\mu^\gamma,\bar\mu^\gamma$ are $\mathbb G^\gamma$-predictable with $\mu^\gamma_s=\mathcal L(X^\gamma_{s\wedge\cdot}\mid\mathcal G^\gamma_s)$ and $\bar\mu^\gamma_s=\mathcal L((X^\gamma_{s\wedge\cdot},\alpha^\gamma_s)\mid\mathcal G^\gamma_s)$ for $d\mathbb P\otimes ds$-a.e. $(s,\omega)\in[t,T]\times\Omega^\gamma$;
--   4. $\mathbb P^\gamma\circ(X^\gamma_{t\wedge\cdot})^{-1}=\nu(t)$ and, for $s\in[t,T]$, a.s.,
--   $$X^\gamma_s=X^\gamma_t+\int_t^s b(r,X^\gamma,\bar\mu^\gamma_r,\alpha^\gamma_r)\,dr+\int_t^s\sigma(r,X^\gamma,\bar\mu^\gamma_r,\alpha^\gamma_r)\,dW^\gamma_r+\int_t^s\sigma_0(r,X^\gamma,\bar\mu^\gamma_r,\alpha^\gamma_r)\,dB^\gamma_r.$$
--
--   Each weak control also carries the process $A^\gamma_s=\int_t^{s\vee t}\pi(\alpha^\gamma_r)\,dr$ of (2.6) and a continuous $\mathcal P(\mathcal C^n\times\mathcal C\times\mathcal C^d\times\mathcal C^\ell)$-valued process $\hat\mu^\gamma$ satisfying (2.7): $\hat\mu^\gamma_s$ is the law of $(X^\gamma_{s\wedge\cdot},A^\gamma_{s\wedge\cdot},W^\gamma,B^\gamma_{s\wedge\cdot})$ for $s\le t$ and its conditional law given $\mathcal G^\gamma_s$ for $s\in(t,T]$. The reward and the value function are
--   $$J(t,\gamma):=\mathbb E^{\mathbb P^\gamma}\Big[\int_t^T L(s,X^\gamma_{s\wedge\cdot},\bar\mu^\gamma_s,\alpha^\gamma_s)\,ds+g(X^\gamma_{T\wedge\cdot},\mu^\gamma_T)\Big],\qquad V_W(t,\nu):=\sup_{\gamma\in\Gamma_W(t,\nu)}J(t,\gamma),$$
--   with $\sup\emptyset=-\infty$. Finally $\Omega^\star:=\mathcal C^\ell\times C([0,T],\mathcal P(\mathcal C^n\times\mathcal C\times\mathcal C^d\times\mathcal C^\ell))$ with canonical process $(B^\star,\hat\mu^\star)$ and filtration $\mathcal G^\star_s:=\sigma\{(\hat\mu^\star_r,B^\star_r):r\le s\}$, and for a $\mathbb G^\star$-stopping time $\tau^\star$ one sets $\tau^\gamma:=\tau^\star(B^{\gamma,t},\hat\mu^\gamma)$ (3.1).
--
--   **Formalization Note** (a) The probability spaces range over `Type` (universe 0). (b) "The integrals are implicitly assumed to be well-defined" is read as: a.s. the drift is Lebesgue integrable and every entry of $\sigma,\sigma_0$ is square integrable on $[t,T]$, and the stochastic integrals are the local Itô integrals `EthierKurtz.HasBrownianItoIntegral` against the $\mathbb P$-completed filtration, of the integrands cut off to $(t,T]$ and to that full-measure set, taken against the shifted processes $W^{\gamma,t}$, $B^{\gamma,t}$ (the Brownian motions of item 3; before $t$ the processes $W^\gamma$, $B^\gamma$ are only continuous, and Itô step sums against them would leave the integral undetermined); no $L^2(\mathbb P)$ condition is imposed. (c) The "$d\mathbb P\otimes ds$-a.e." conditional-law requirement is read in Fubini form: for a.e. $s\in[t,T]$, $\mu^\gamma_s$ is a.s. equal to a version of the conditional law. (d) $\mu^\gamma_T$ in $J$ and $\mu^\gamma_{\tau^\gamma}$ in (3.2) are read as the $X$-marginals $\hat\mu^\gamma_s\circ(\hat X_{s\wedge\cdot})^{-1}$, because $\mu^\gamma$ is fixed only for a.e. time. (e) $\hat\mu^\gamma$ is carried with every path continuous; by Remark 2.4 and Lemma A.1 such a version always exists, so this does not change the set of weak controls up to the choice of version. (f) Predictability and adaptedness are required on all of $\mathbb R_{\ge0}$; a process given on $[t,T]$ extends by a constant.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, pp. 5–7 and 9, Definition 2.1, (2.2)–(2.5), Remark 2.4 (2.6)–(2.7), §3.1.1 (3.1)

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_completedSDEPast
import Definitions.Def_MKVDPP_Weak_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MKVDPP.Weak

noncomputable section

/-! ## The first canonical space `Ω̂` (Remark 2.4, p. 7; §4.1.1, p. 15) -/

/-- `Ω̂ := 𝒞ⁿ × 𝒞 × 𝒞^d × 𝒞^ℓ` (product σ-algebra of the Borel σ-algebras). -/
abbrev OmegaHat (T : ℝ≥0) (n d ℓ : ℕ) : Type := Cpath T n × CR T × Cpath T d × Cpath T ℓ

/-- `(x_{s∧·}, a_{s∧·}, w, b_{s∧·})`: the map of (2.7) and (4.6) (the `W` component is not stopped). -/
def stopHatW {T : ℝ≥0} {n d ℓ : ℕ} (s : ℝ≥0) (z : OmegaHat T n d ℓ) : OmegaHat T n d ℓ :=
  (stopPath s z.1, stopPath s z.2.1, z.2.2.1, stopPath s z.2.2.2)

theorem measurable_stopHatW {T : ℝ≥0} {n d ℓ : ℕ} (s : ℝ≥0) :
    Measurable (stopHatW (T := T) (n := n) (d := d) (ℓ := ℓ) s) :=
  ((measurable_stopPath s).comp measurable_fst).prodMk
    (((measurable_stopPath s).comp measurable_snd.fst).prodMk
      (measurable_snd.snd.fst.prodMk ((measurable_stopPath s).comp measurable_snd.snd.snd)))

/-- The joint vector `(w, b) ∈ ℝ^d × ℝ^ℓ ≅ ℝ^{d+ℓ}` (indexed by `Fin d ⊕ Fin ℓ`). -/
def pairVec {d ℓ : ℕ} (w : EuclideanSpace ℝ (Fin d)) (b : EuclideanSpace ℝ (Fin ℓ)) :
    EuclideanSpace ℝ (Fin d ⊕ Fin ℓ) :=
  WithLp.toLp 2 (Sum.elim (WithLp.ofLp w) (WithLp.ofLp b))

/-! ## The stochastic differential equation (2.4) under the "well-defined" pin -/

open Classical in
/-- Equation (2.4) on `[t,T]`, with the integrals "implicitly assumed to be well defined" read as:
for ℙ-a.e. ω the drift is Lebesgue integrable and every entry of `σ`, `σ₀` is square integrable on
`[t,T]` (the set `G`), and the stochastic integrals are local Itô integrals
(`EthierKurtz.HasBrownianItoIntegral`, w.r.t. the ℙ-completed filtration) of the integrands cut
off to `(t,T] × G`, against the shifted processes `W^t_r = W_{r∨t} − W_t` and `B^t_r = B_{r∨t} − B_t`
(Definition 2.1(iii) makes only these Brownian motions; `W`, `B` before `t` are merely continuous, and
step sums over `[0,t]` against them need not converge to `0`). The equation holds for every
`s ∈ [t,T]`, ℙ-a.s., coordinatewise. -/
def SatisfiesSDE {T : ℝ≥0} {n d ℓ : ℕ} {U : Type*} [MeasurableSpace U] (c : Coeffs T n d ℓ U)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (t : ℝ≥0)
    (X : Ω → Cpath T n) (W : Ω → Cpath T d) (B : Ω → Cpath T ℓ)
    (μbar : ℝ≥0 → Ω → ProbabilityMeasure (Cpath T n × U)) (α : ℝ≥0 → Ω → U) : Prop :=
  let bI : ℝ → Ω → EuclideanSpace ℝ (Fin n) := fun r ω =>
    c.b r.toNNReal (X ω) (μbar r.toNNReal ω) (α r.toNNReal ω)
  let σI : ℝ → Ω → Matrix (Fin n) (Fin d) ℝ := fun r ω =>
    c.σ r.toNNReal (X ω) (μbar r.toNNReal ω) (α r.toNNReal ω)
  let σ₀I : ℝ → Ω → Matrix (Fin n) (Fin ℓ) ℝ := fun r ω =>
    c.σ₀ r.toNNReal (X ω) (μbar r.toNNReal ω) (α r.toNNReal ω)
  let G : Set Ω := {ω | IntegrableOn (fun r => bI r ω) (Set.Icc (t:ℝ) T) ∧
    (∀ i j, IntegrableOn (fun r => (σI r ω i j) ^ 2) (Set.Icc (t:ℝ) T)) ∧
    (∀ i j, IntegrableOn (fun r => (σ₀I r ω i j) ^ 2) (Set.Icc (t:ℝ) T))}
  (∀ᵐ ω ∂P, ω ∈ G) ∧
  ∃ (Jσ : Fin n → Fin d → ℝ≥0 → Ω → ℝ) (Jσ₀ : Fin n → Fin ℓ → ℝ≥0 → Ω → ℝ),
    (∀ i j, EthierKurtz.HasBrownianItoIntegral P (EthierKurtz.completedSDEPast P F)
      (fun r ω => pathAt (shiftPath t (W ω)) r j)
      (fun r ω => if t < r ∧ r ≤ T ∧ ω ∈ G then σI r ω i j else 0) (Jσ i j)) ∧
    (∀ i j, EthierKurtz.HasBrownianItoIntegral P (EthierKurtz.completedSDEPast P F)
      (fun r ω => pathAt (shiftPath t (B ω)) r j)
      (fun r ω => if t < r ∧ r ≤ T ∧ ω ∈ G then σ₀I r ω i j else 0) (Jσ₀ i j)) ∧
    ∀ s : ℝ≥0, t ≤ s → s ≤ T → ∀ᵐ ω ∂P, ∀ i,
      pathAt (X ω) s i = pathAt (X ω) t i + (∫ r in Set.Ioc (t:ℝ) s, bI r ω) i
        + ∑ j, (Jσ i j s ω - Jσ i j t ω) + ∑ j, (Jσ₀ i j s ω - Jσ₀ i j t ω)

/-! ## Weak controls (Definition 2.1, pp. 5–6; Remark 2.4, p. 7) -/

/-- A weak control `γ` with initial condition `(t, ν)` (Definition 2.1), carrying the process
`A^γ` of (2.6) and a continuous version of `μ̂^γ` of (2.7). Times are in `ℝ≥0`; paths are
elements of `𝒞^k`, the value at time `s` being `pathAt · s`. -/
structure WeakControl {T : ℝ≥0} {n d ℓ : ℕ} {U : Type*} [MetricSpace U] [MeasurableSpace U]
    (c : Coeffs T n d ℓ U) (u₀ : U) (p : ℝ) (π : U → ℝ)
    (Ω : Type) [mΩ : MeasurableSpace Ω] (t : ℝ≥0) (ν : ProbabilityMeasure (Cpath T n)) where
  /-- (i) the probability `ℙ^γ` and the two filtrations `𝔽^γ`, `𝔾^γ`. -/
  P : Measure Ω
  isProb : IsProbabilityMeasure P
  F : Filtration ℝ≥0 mΩ
  G : Filtration ℝ≥0 mΩ
  /-- (ii)–(iii) the processes, as path-valued random variables. -/
  X : Ω → Cpath T n
  W : Ω → Cpath T d
  B : Ω → Cpath T ℓ
  α : ℝ≥0 → Ω → U
  μ : ℝ≥0 → Ω → ProbabilityMeasure (Cpath T n)
  μbar : ℝ≥0 → Ω → ProbabilityMeasure (Cpath T n × U)
  /-- `A^γ_s = ∫_t^{s∨t} π(α^γ_r) dr` (Remark 2.4, (2.6)). -/
  A : Ω → CR T
  /-- the continuous `𝒫(Ω̂)`-valued process `μ̂^γ` of (2.7). -/
  μhat : Ω → C(Set.Icc (0:ℝ) (T:ℝ), ProbabilityMeasure (OmegaHat T n d ℓ))
  /-- (i): `𝒢_s ⊆ ℱ_s` and (2.2). -/
  G_le_F : ∀ s, s ≤ T → G s ≤ F s
  eq_2_2 : ∀ s, s ≤ T → ∀ D : Set Ω,
    MeasurableSet[F s ⊔ MeasurableSpace.comap W inferInstance] D →
      condExp (G s) P (D.indicator (fun _ => (1:ℝ))) =ᵐ[P]
        condExp (G T) P (D.indicator (fun _ => (1:ℝ)))
  /-- (ii): `X` is `𝔽`-adapted and continuous; `α` is `𝔽`-predictable; (2.3). -/
  measurable_X : Measurable X
  adapted_X : ∀ s, s ≤ T → Measurable[F s] (fun ω => pathAt (X ω) s)
  predictable_α : Measurable[F.predictable] (fun q : ℝ≥0 × Ω => α q.1 q.2)
  eq_2_3 : ∫⁻ ω, ‖X ω‖ₑ ^ p ∂P +
    ∫⁻ ω, ∫⁻ r in Set.Icc (t:ℝ) T, edist (α r.toNNReal ω) u₀ ^ p ∂volume ∂P < ⊤
  /-- (iii): `(W, B)` adapted and continuous; `(W^t, B^t)` is a standard `(𝔽, ℙ)`-Brownian
  motion on `[t,T]` (jointly, in `ℝ^{d+ℓ}`); `B^t` is `𝔾`-adapted; `ℱ_t ∨ σ(W)` is independent
  of `𝒢_T`; `μ`, `μ̄` are `𝔾`-predictable and are the conditional laws for `dℙ ⊗ ds`-a.e.
  `(s, ω) ∈ [t,T] × Ω` (read in Fubini form). -/
  measurable_W : Measurable W
  measurable_B : Measurable B
  adapted_W : ∀ s, s ≤ T → Measurable[F s] (fun ω => pathAt (W ω) s)
  adapted_B : ∀ s, s ≤ T → Measurable[F s] (fun ω => pathAt (B ω) s)
  brownian : IsFBrownianOn F P t T (fun s ω => pairVec (pathAt (W ω) s) (pathAt (B ω) s))
  adapted_Bt : ∀ s, s ≤ T → Measurable[G s] (fun ω => pathAt (shiftPath t (B ω)) s)
  indep_FtW_GT : Indep (F t ⊔ MeasurableSpace.comap W inferInstance) (G T) P
  predictable_μ : Measurable[G.predictable] (fun q : ℝ≥0 × Ω => μ q.1 q.2)
  predictable_μbar : Measurable[G.predictable] (fun q : ℝ≥0 × Ω => μbar q.1 q.2)
  condLaw_μ : ∀ᵐ r ∂(volume.restrict (Set.Icc (t:ℝ) T)),
    ∃ m : Ω → ProbabilityMeasure (Cpath T n),
      IsCondLaw (G r.toNNReal) P (fun ω => stopPath r.toNNReal (X ω)) m ∧
      (fun ω => μ r.toNNReal ω) =ᵐ[P] m
  condLaw_μbar : ∀ᵐ r ∂(volume.restrict (Set.Icc (t:ℝ) T)),
    ∃ m : Ω → ProbabilityMeasure (Cpath T n × U),
      IsCondLaw (G r.toNNReal) P (fun ω => (stopPath r.toNNReal (X ω), α r.toNNReal ω)) m ∧
      (fun ω => μbar r.toNNReal ω) =ᵐ[P] m
  /-- (iv): initial condition `ℙ ∘ (X_{t∧·})⁻¹ = ν(t)` and the SDE (2.4). -/
  initial : P.map (fun ω => stopPath t (X ω)) = (lawStop ν t : Measure (Cpath T n))
  sde : SatisfiesSDE c P F t X W B μbar α
  /-- Remark 2.4, (2.6): the definition of `A^γ_s = ∫_t^{s∨t} π(α^γ_r) dr`, `s ∈ [0,T]`. -/
  A_eq : ∀ ω (s : ℝ≥0), s ≤ T → pathAt (A ω) s = ∫ r in Set.Ioc (t:ℝ) (max s t), π (α r.toNNReal ω)
  /-- Remark 2.4, (2.7): `μ̂^γ` is measurable, every path is continuous (by its type), it is the
  law of `(X_{s∧·}, A_{s∧·}, W, B_{s∧·})` for `s ≤ t` and a `𝒢_s`-measurable version of its
  conditional law given `𝒢_s` for `t < s ≤ T`. -/
  measurable_μhat : Measurable μhat
  μhat_le : ∀ s : ℝ≥0, s ≤ t → s ≤ T → ∀ᵐ ω ∂P,
    ((pathAt (μhat ω) s : ProbabilityMeasure (OmegaHat T n d ℓ)) : Measure (OmegaHat T n d ℓ)) =
      P.map (fun ω' => stopHatW s (X ω', A ω', W ω', B ω'))
  μhat_gt : ∀ s : ℝ≥0, t < s → s ≤ T →
    ∃ m : Ω → ProbabilityMeasure (OmegaHat T n d ℓ),
      IsCondLaw (G s) P (fun ω => stopHatW s (X ω, A ω, W ω, B ω)) m ∧
      (fun ω => pathAt (μhat ω) s) =ᵐ[P] m

variable {T : ℝ≥0} {n d ℓ : ℕ} {U : Type*} [MetricSpace U] [MeasurableSpace U]
  {c : Coeffs T n d ℓ U} {u₀ : U} {p : ℝ} {π : U → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {t : ℝ≥0} {ν : ProbabilityMeasure (Cpath T n)}

/-- The projection `Ω̂ → 𝒞ⁿ`, `(x, a, w, b) ↦ x_{s∧·}`. -/
def stopXHat (s : ℝ≥0) (z : OmegaHat T n d ℓ) : Cpath T n := stopPath s z.1

theorem measurable_stopXHat (s : ℝ≥0) : Measurable (stopXHat (T := T) (n := n) (d := d) (ℓ := ℓ) s) :=
  (measurable_stopPath s).comp measurable_fst

/-- `μ̂_s ∘ (X̂_{s∧·})⁻¹` for `μ̂_s ∈ 𝒫(Ω̂)`. -/
def margX (s : ℝ≥0) (m : ProbabilityMeasure (OmegaHat T n d ℓ)) : ProbabilityMeasure (Cpath T n) :=
  m.map (measurable_stopXHat s).aemeasurable

/-- `μ^γ_s` read as `μ̂^γ_s ∘ (X̂_{s∧·})⁻¹` (used at `s = T` in (2.5) and at `s = τ^γ` in (3.2)). -/
def muAt (γ : WeakControl c u₀ p π Ω t ν) (s : ℝ≥0) (ω : Ω) : ProbabilityMeasure (Cpath T n) :=
  margX s (pathAt (γ.μhat ω) s)

/-- The running reward `L(s, X^γ_{s∧·}, μ̄^γ_s, α^γ_s)` as an `EReal`-valued function of time. -/
def runReward (γ : WeakControl c u₀ p π Ω t ν) (ω : Ω) (s : ℝ≥0) : EReal :=
  ((c.L s (stopPath s (γ.X ω)) (γ.μbar s ω) (γ.α s ω) : ℝ) : EReal)

/-- The reward (2.5): `J(t, γ) := 𝔼^{ℙ^γ}[∫_t^T L(s, X^γ_{s∧·}, μ̄^γ_s, α^γ_s) ds + g(X^γ_{T∧·}, μ^γ_T)]`. -/
def J (γ : WeakControl c u₀ p π Ω t ν) : EReal :=
  eExp γ.P (fun ω => timeInt t T (runReward γ ω) +
    ((c.g (stopPath T (γ.X ω)) (muAt γ T ω) : ℝ) : EReal))

/-- The value function (2.5): `V_W(t, ν) := sup_{γ ∈ Γ_W(t,ν)} J(t, γ)` (`sup ∅ = −∞`), the
supremum running over weak controls on every probability space `Ω : Type`. -/
def VW (c : Coeffs T n d ℓ U) (u₀ : U) (p : ℝ) (π : U → ℝ) (t : ℝ≥0)
    (ν : ProbabilityMeasure (Cpath T n)) : EReal :=
  ⨆ (Ω : Type) (mΩ : MeasurableSpace Ω) (γ : @WeakControl T n d ℓ U _ _ c u₀ p π Ω mΩ t ν),
    @J T n d ℓ U _ _ c u₀ p π Ω mΩ t ν γ

/-! ## The canonical space `Ω⋆` and the random times `τ^γ` (§3.1.1, p. 9) -/

/-- `Ω⋆ := 𝒞^ℓ × C([0,T], 𝒫(𝒞ⁿ × 𝒞 × 𝒞^d × 𝒞^ℓ))`, canonical process `(B⋆, μ̂⋆)`. -/
abbrev OmegaStar (T : ℝ≥0) (n d ℓ : ℕ) : Type :=
  Cpath T ℓ × C(Set.Icc (0:ℝ) (T:ℝ), ProbabilityMeasure (OmegaHat T n d ℓ))

/-- The coordinate `(B⋆_r, μ̂⋆_r)` of `Ω⋆`. -/
def coordStar (r : ℝ≥0) (ω : OmegaStar T n d ℓ) :
    EuclideanSpace ℝ (Fin ℓ) × ProbabilityMeasure (OmegaHat T n d ℓ) :=
  (pathAt ω.1 r, pathAt ω.2 r)

theorem measurable_coordStar (r : ℝ≥0) :
    Measurable (coordStar (T := T) (n := n) (d := d) (ℓ := ℓ) r) := by
  refine Measurable.prodMk ?_ ?_
  · exact ((continuous_eval_const _).measurable).comp measurable_fst
  · exact (measurable_of_continuous_pm (continuous_eval_const _)).comp measurable_snd

/-- The canonical filtration `𝒢⋆_s := σ{(μ̂⋆_r, B⋆_r) : r ∈ [0,s]}`. -/
def GStar (T : ℝ≥0) (n d ℓ : ℕ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (OmegaStar T n d ℓ)) where
  seq s := ⨆ r ≤ s, MeasurableSpace.comap (coordStar r) inferInstance
  mono' _ _ hst := iSup₂_le fun r hr => le_iSup₂ (f := fun r (_ : r ≤ _) =>
    MeasurableSpace.comap (coordStar (T := T) (n := n) (d := d) (ℓ := ℓ) r) inferInstance) r
      (hr.trans hst)
  le' _ := iSup₂_le fun r _ => (measurable_coordStar r).comap_le

/-- `τ^γ := τ⋆(B^{γ,t}_·, μ̂^γ_·)` (3.1). -/
def tauGamma (γ : WeakControl c u₀ p π Ω t ν) (τstar : OmegaStar T n d ℓ → ℝ≥0) (ω : Ω) : ℝ≥0 :=
  τstar (shiftPath t (γ.B ω), γ.μhat ω)

/-- The reward to the stopping time in the DPP (3.2):
`𝔼^{ℙ^γ}[∫_t^{τ^γ} L(s, X^γ_{s∧·}, μ̄^γ_s, α^γ_s) ds + V_W(τ^γ, μ^γ_{τ^γ})]`. -/
def dppReward (γ : WeakControl c u₀ p π Ω t ν) (τstar : OmegaStar T n d ℓ → ℝ≥0) : EReal :=
  eExp γ.P (fun ω => timeInt t (tauGamma γ τstar ω) (runReward γ ω) +
    VW c u₀ p π (tauGamma γ τstar ω) (muAt γ (tauGamma γ τstar ω) ω))

end

end MKVDPP.Weak


