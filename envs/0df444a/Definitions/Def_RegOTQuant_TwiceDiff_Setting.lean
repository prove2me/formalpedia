-- Prove2me | Definitions.Def_RegOTQuant_TwiceDiff_Setting
-- name    : RegOTQuant_TwiceDiff_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:29.450388+00:00
-- url     : https://prove2.me/theorems/c1acc210-d13d-40b3-a526-96b577c82a46
-- title:
--   §2.1–2.2 and §3.2 — transport, divergence, quantization and Hessian setting
-- statement:
--   For $N\ge1$, the $i$th marginal space is Euclidean $X_i\subseteq\mathbb R^{d_i}$, and $X=\prod_i X_i$ has the Euclidean product norm. The definitions supply probability couplings $\Pi(\mu_1,\ldots,\mu_N)$, the independent reference law $P=\bigotimes_i\mu_i$, the divergence $D_f$, the transport values $\mathrm{OT}$ and $\mathrm{OT}_{f,\varepsilon}$, finite-support laws $\mathcal P^n(Y)$, the $W_2$ rate $\operatorname{quant}_2(C,\alpha)$, and the corrected Hessian condition.
--
--   $$
--   \mathrm{OT}_{f,\varepsilon}=\inf_{\pi\in\Pi(\mu_1,\ldots,\mu_N)}\left(\int c\,d\pi+\varepsilon D_f(\pi,P)\right).
--   $$
--
--   These definitions fix the shared mathematical objects for Theorem 3.8 and its supporting bounds.
--
--   **Formalization Note** The product is `PiLp 2` and indices start at zero. `D_f` is extended-real and is $+\infty$ if absolute continuity or integrability fails. A martingale coupling with a finitely supported first marginal has zero integrated displacement at every atom. The inverse $S_\varepsilon$ uses the inverse of $\widetilde f$ on $[x_0,\infty)$.
-- source:
--   Eckstein & Nutz, Convergence rates for regularized optimal transport via quantization, arXiv:2208.14391v3, pp. 5–6, 14–15, §2.1, §2.2, §3.2, Theorem 3.8 and Lemma 3.9

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory Filter Set Classical

namespace RegOTQuant.TwiceDiff

/-- The Euclidean space of the paper's marginal `i+1`. -/
abbrev Fi {N : ℕ} (d : Fin N → ℕ) (i : Fin N) := EuclideanSpace ℝ (Fin (d i))

/-- The product Euclidean space, with its ℓ² norm. -/
abbrev E {N : ℕ} (d : Fin N → ℕ) := PiLp 2 (Fi d)

/-- The product of the prescribed marginal domains. -/
def X {N : ℕ} {d : Fin N → ℕ} (Xs : ∀ i : Fin N, Set (Fi d i)) : Set (E d) :=
  {x | ∀ i, (WithLp.ofLp x) i ∈ Xs i}

/-- A probability law with finite second moment. -/
def IsP2 {G : Type*} [MeasurableSpace G] [NormedAddCommGroup G]
    (η : Measure G) : Prop :=
  IsProbabilityMeasure η ∧ (∫⁻ x, ENNReal.ofReal (‖x‖ ^ (2 : ℝ)) ∂η) < ⊤

/-- The probability couplings of the marginals. -/
def couplings {N : ℕ} {d : Fin N → ℕ} (μ : ∀ i : Fin N, Measure (Fi d i)) :
    Set (Measure (E d)) :=
  {π | IsProbabilityMeasure π ∧ ∀ i, π.map (fun x : E d => (WithLp.ofLp x) i) = μ i}

/-- The coordinate marginal of a law on the product. -/
noncomputable def marginal {N : ℕ} {d : Fin N → ℕ}
    (π : Measure (E d)) (i : Fin N) : Measure (Fi d i) :=
  π.map (fun x : E d => (WithLp.ofLp x) i)

/-- The independent product of the marginals. -/
noncomputable def prodRef {N : ℕ} {d : Fin N → ℕ}
    (μ : ∀ i : Fin N, Measure (Fi d i)) : Measure (E d) :=
  (Measure.pi μ).map (MeasurableEquiv.toLp 2 (∀ i : Fin N, Fi d i))

/-- The f-divergence, with +∞ for lack of absolute continuity or integrability. -/
noncomputable def fDiv {G : Type*} [MeasurableSpace G] (f : ℝ → ℝ)
    (ρ ν : Measure G) : EReal :=
  if ρ ≪ ν ∧ Integrable (fun x => f ((ρ.rnDeriv ν x).toReal)) ν then
    ((∫ x, f ((ρ.rnDeriv ν x).toReal) ∂ν : ℝ) : EReal)
  else ⊤

/-- The unregularized Kantorovich value. -/
noncomputable def OTval {N : ℕ} {d : Fin N → ℕ} (c : E d → ℝ)
    (μ : ∀ i : Fin N, Measure (Fi d i)) : ℝ :=
  sInf {r : ℝ | ∃ π ∈ couplings μ, r = ∫ x, c x ∂π}

/-- The f-divergence regularized Kantorovich value. -/
noncomputable def OTreg {N : ℕ} {d : Fin N → ℕ} (f : ℝ → ℝ)
    (ε : ℝ) (c : E d → ℝ) (μ : ∀ i : Fin N, Measure (Fi d i)) : EReal :=
  ⨅ (π : Measure (E d)) (_ : π ∈ couplings μ),
    ((∫ x, c x ∂π : ℝ) : EReal) + (ε : EReal) * fDiv f π (prodRef μ)

/-- Probability laws on at most n points of Y. -/
def IsAtMostN {G : Type*} [MeasurableSpace G] (n : ℕ) (Y : Set G)
    (ν : Measure G) : Prop :=
  IsProbabilityMeasure ν ∧ ∃ s : Finset G, s.card ≤ n ∧ (s : Set G) ⊆ Y ∧ ν (s : Set G)ᶜ = 0

/-- The W₂ quantization rate of a law on Y. -/
def Quant2 {G : Type*} [MeasurableSpace G] [NormedAddCommGroup G]
    (Y : Set G) (η : Measure G) (C α : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ ν : Measure G,
    IsAtMostN n Y ν ∧
      WassersteinDRO.Duality.wassersteinDistance 2 ν η ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (-α))

/-- The standing conditions on the divergence generator, on nonnegative arguments. -/
def FStanding (f : ℝ → ℝ) : Prop :=
  StrictConvexOn ℝ (Ici (0 : ℝ)) f ∧ BddBelow (f '' Ici (0 : ℝ)) ∧
    f 1 = 0 ∧ Tendsto (fun x : ℝ => f x / x) atTop atTop

/-- At every first-marginal atom, the integrable conditional displacement has zero mean. -/
def IsMartingaleCpl {G : Type*} [MeasurableSpace G] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] (θ : Measure (G × G)) : Prop :=
  ∀ a : G, Integrable (fun z : G × G => if z.1 = a then z.2 - z.1 else 0) θ ∧
    (∫ z : G × G, if z.1 = a then z.2 - z.1 else 0 ∂θ) = 0

/-- Corrected two-sided Hessian bound in every ambient direction. -/
def HessBound {N : ℕ} {d : Fin N → ℕ} (Xs : ∀ i : Fin N, Set (Fi d i))
    (c : E d → ℝ) (B : ℝ) : Prop :=
  ∀ x ∈ X Xs, ∀ w : E d,
    |iteratedFDeriv ℝ 2 c x ![w, w]| ≤ B * ‖w‖ ^ 2

/-- The finite-dimensional standing setting of §2.1 and §3.2. -/
def Setting {N : ℕ} {d : Fin N → ℕ} (Xs : ∀ i : Fin N, Set (Fi d i))
    (μ : ∀ i : Fin N, Measure (Fi d i)) (c : E d → ℝ) : Prop :=
  0 < N ∧
  (∀ i, IsClosed (Xs i) ∧ Convex ℝ (Xs i) ∧ IsP2 (μ i) ∧ (μ i) (Xs i)ᶜ = 0) ∧
  (∃ U : Set (E d), IsOpen U ∧ X Xs ⊆ U ∧ ContDiffOn ℝ 2 c U) ∧
  (∃ K : ℝ, 0 ≤ K ∧ ∃ xhat ∈ X Xs,
    ∀ x ∈ X Xs, |c x| ≤ K * (1 + ‖x - xhat‖ ^ 2))

/-- A plan attaining the unregularized value. -/
def IsOptimal {N : ℕ} {d : Fin N → ℕ} (c : E d → ℝ)
    (μ : ∀ i : Fin N, Measure (Fi d i)) (πs : Measure (E d)) : Prop :=
  πs ∈ couplings μ ∧ (∫ x, c x ∂πs) = OTval c μ

/-- The auxiliary generator of Theorem 3.8(ii). -/
noncomputable def ftilde (φ : ℝ → ℝ) (β x : ℝ) : ℝ := x * φ (x ^ β)

/-- The inverse value `Sε` on `[x₀,∞)` in Theorem 3.8(ii). -/
noncomputable def Sinv (φ : ℝ → ℝ) (β x0 ε : ℝ) : ℝ :=
  Function.invFunOn (ftilde φ β) (Ici x0) (1 / ε)

end RegOTQuant.TwiceDiff


