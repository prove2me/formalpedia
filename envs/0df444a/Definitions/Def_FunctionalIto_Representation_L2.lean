-- Prove2me | Definitions.Def_FunctionalIto_Representation_L2
-- name    : FunctionalIto_Representation_L2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:22.033732+00:00
-- url     : https://prove2.me/theorems/bab0dbfe-14d6-453f-aa5e-95baaa39223d
-- title:
--   Assumption 5.1 and §5.2, pp. 15–18 — the Brownian setting, the L² Itô integral, 𝓛²(X), 𝓘²(X), 𝒞_b^{1,2}(X), D(X), ∇_X, 𝒲^{1,2}(X) and the closure of ∇_X
-- statement:
--   This file fixes the setting of §5 and the function spaces on which the vertical derivative acts.
--
--   **Filtrations.** For a process $Z$, $\mathcal F^Z$ is its $\mathbb P$-completed natural filtration, $\mathcal F^Z_t=\sigma(Z(s),\,s\le t)\vee\{\mathbb P\text{-null sets}\}$.
--
--   **The square-integrable Itô integral.** Let $M$ be an $\mathbb R^d$-valued integrator with $d[M^i,M^j]=Q_{ij}\,ds$ and $\mathcal G$ a filtration. A *simple integrand* on the dyadic grid of level $n$ of $[0,T]$ is $\sum_{k<2^n}\xi_k1_{(kT/2^n,(k+1)T/2^n]}$ with $\xi_k$ bounded and $\mathcal G_{kT/2^n}$-measurable; its elementary integral is $\sum_k\xi_k\cdot\big(M((k+1)T/2^n\wedge t)-M(kT/2^n\wedge t)\big)$. A process $Y$ is the Itô integral $\int_0^\cdot\varphi\cdot dM$ on $[0,T]$ if $\varphi$ is progressively measurable with
--   $$E\int_0^T\varphi(s)^{\top}Q(s)\varphi(s)\,ds<\infty,$$
--   each $Y(t)$, $t\le T$, is $\mathcal G_t$-measurable, $Y$ has continuous paths on $[0,T]$ almost surely, and some simple integrands $\varphi_j\to\varphi$ in $L^2(Q\,ds\times d\mathbb P)$ have elementary integrals converging to $Y(t)$ in $L^2(\mathbb P)$ for every $t\le T$.
--
--   **Assumption 5.1 (p. 15) with the standing setting.** On a complete probability space, $W$ is a standard $d$-dimensional Brownian motion and $\mathcal G=\mathcal F^W$; $\sigma$ is a $\mathcal G$-progressively measurable $d\times d$ matrix process with
--   $$\det\sigma(t)\neq0\qquad dt\times d\mathbb P\text{-a.e. on }[0,T]\tag{43}$$
--   $X$ has continuous paths, $X(0)$ is $\mathcal G_0$-measurable and $X(t)=X(0)+\int_0^t\sigma(u)\cdot dW(u)$ on $[0,T]$; the working filtration is $\mathcal F=\mathcal F^X$ and is right-continuous on $[0,T)$; $A$ is an adapted cadlag process with values in $S_d^+$ with $A=\sigma\sigma^{\top}$ $dt\times d\mathbb P$-a.e. on $[0,T]$, so that $[X](t)=\int_0^tA(s)\,ds$ (3).
--
--   **Spaces (§4.2, §5.2).**
--   1. $\mathcal L^2(X)$ (47): progressively measurable $\varphi$ with $\|\varphi\|^2_{\mathcal L^2(X)}=E\int_0^T\varphi(s)^{\top}A(s)\varphi(s)\,ds<\infty$.
--   2. $\mathcal I^2(X)$ (48): the Itô integrals $\int_0^\cdot\varphi\cdot dX$, $\varphi\in\mathcal L^2(X)$, with $\|Y\|_2^2=E[Y(T)^2]$.
--   3. $\mathcal C_b^{1,2}(X)$ (42): adapted $Y$ with $Y(t)=F_t(X_t,A_t)$ $\mathbb P$-a.s. for each $t<T$, for some $F\in\mathbb C_b^{1,2}$ verifying (10).
--   4. $D(X)=\mathcal C_b^{1,2}(X)\cap\mathcal I^2(X)$ (50); a *vertical derivative* $\nabla_XY\in\mathcal L^2(X)$ of $Y\in D(X)$ is $\nabla_xF_t(X_t,A_t)$, $t<T$, for a representing $F$ (Defs. 4.5, 5.4).
--   5. $\mathcal W^{1,2}(X)$ (Def. 5.6): the closure of $D(X)$ in $\mathcal I^2(X)$.
--   6. The closure of $\nabla_X$: $(Y,\varphi)$ is in the closure of the graph of $\nabla_X:D(X)\to\mathcal L^2(X)$ if $Y\in\mathcal W^{1,2}(X)$, $\varphi\in\mathcal L^2(X)$, and some $Y_n\in D(X)$ with vertical derivatives $\psi_n$ satisfy $Y_n\to Y$ in $\mathcal I^2(X)$ and $\psi_n\to\varphi$ in $\mathcal L^2(X)$.
--   7. $E\int_0^T\psi^{\top}A\zeta\,ds$, the bilinear form $E\int_0^T\psi\,\zeta\,d[X]$, with its integrability on $(0,T]\times\Omega$.
--
--   These spaces carry the statements of Proposition 5.5, Lemma 5.7 and Theorem 5.8.
--
--   **Formalization Note.** Two hypotheses the paper uses without printing them are part of the setting. First, the working filtration is the completed natural filtration $\mathcal F^X$ (the paper names it on p. 3); Lemma 5.7 fails for a larger filtration. Its right-continuity on $[0,T)$ and $A$'s adaptedness are the standing conditions of §2. Second, the Itô integral defining $X$ is the square-integrable one, so $E[X](T)=E\int_0^T\|\sigma\|_F^2\,dt<\infty$; without it the cylindrical processes of Lemma 5.7 are not in $\mathcal L^2(X)$. $\sigma$ is assumed progressively measurable (the page says adapted). $X(0)$ is $\mathcal F^W_0$-measurable, hence a.s. constant. In (47) the scalar notation $\varphi_s^2\,d[X](s)$ is read as $\varphi^{\top}A\varphi\,ds$, and the integral runs over $[0,T]$ (the page prints $\int_0^t$). Every expectation of a square is an extended-nonnegative lower integral (`lintegral`), so no junk value arises; the derivative on $\mathcal W^{1,2}(X)$ is a relation, and its existence and uniqueness are the content of Theorem 5.8. The simple integrands use dyadic grids of $[0,T]$, which are dense among all simple predictable integrands.
-- source:
--   Cont and Fournié, Functional Itô calculus and stochastic integral representation of martingales, arXiv:1002.2446v5, p. 3, §2 (ℱ^X, (3)); p. 15, Definition 4.5 (42), Assumption 5.1 (43); p. 16, (47); p. 17, (48), Definitions 5.3 (50), 5.4; p. 18, Definition 5.6

import Mathlib
import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_FunctionalIto_Representation_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators Matrix

namespace FunctionalIto.Representation

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-! ## Filtrations -/

/-- `𝒢` is the `P`-completed natural filtration of the process `Z`:
`𝒢_t = σ(Z(s), s ≤ t) ∨ {P-null sets}`. -/
def IsCompletedNaturalFiltration {E : Type*} [MeasurableSpace E] (P : Measure Ω)
    (Z : ℝ≥0 → Ω → E) (𝒢 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) : Prop :=
  ∀ t, 𝒢 t = (⨆ s, ⨆ (_ : s ≤ t), MeasurableSpace.comap (Z s) ‹MeasurableSpace E›) ⊔
    MeasurableSpace.generateFrom {N | P N = 0}

/-! ## The square-integrable Itô integral -/

/-- The dyadic grid point `k T / 2^n` of `[0,T]`. -/
noncomputable def grid (T : ℝ≥0) (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) * T / 2 ^ n

/-- `ξ` defines a simple predictable integrand on the dyadic grid of level `n` of `[0,T]`:
`ξ k` is bounded (uniformly in `k`) and `𝒢_{kT/2^n}`-measurable. -/
def IsSimpleIntegrand (𝒢 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0) (n : ℕ)
    (ξ : ℕ → Ω → (Fin d → ℝ)) : Prop :=
  (∀ k, StronglyMeasurable[𝒢 (grid T n k)] (ξ k)) ∧ ∃ C : ℝ, ∀ k ω, ‖ξ k ω‖ ≤ C

/-- The simple process `∑_{k < 2^n} ξ_k 1_{(kT/2^n, (k+1)T/2^n]}`. -/
noncomputable def stepProcess (T : ℝ≥0) (n : ℕ) (ξ : ℕ → Ω → (Fin d → ℝ)) :
    ℝ≥0 → Ω → (Fin d → ℝ) :=
  fun t ω => ∑ k ∈ Finset.range (2 ^ n),
    (Set.Ioc (grid T n k) (grid T n (k + 1))).indicator (fun _ => ξ k ω) t

/-- The elementary stochastic integral `∫_0^t (stepProcess T n ξ) · dM`
`= ∑_k ξ_k · (M((k+1)T/2^n ∧ t) − M(kT/2^n ∧ t))`. -/
noncomputable def simpleIntegral (T : ℝ≥0) (n : ℕ) (ξ : ℕ → Ω → (Fin d → ℝ))
    (M : ℝ≥0 → Ω → (Fin d → ℝ)) : ℝ≥0 → Ω → ℝ :=
  fun t ω => ∑ k ∈ Finset.range (2 ^ n),
    ξ k ω ⬝ᵥ (M (min (grid T n (k + 1)) t) ω - M (min (grid T n k) t) ω)

/-- `E ∫_0^T ψ(s)ᵀ Q(s) ψ(s) ds ∈ [0, ∞]`, the squared `L²` norm of `ψ` against the matrix density
`Q` (`d[M] = Q ds`). -/
noncomputable def qNormSq (P : Measure Ω) (T : ℝ≥0) (Q : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (ψ : ℝ≥0 → Ω → (Fin d → ℝ)) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ s in Set.Ioc (0 : ℝ) T,
    ENNReal.ofReal (ψ s.toNNReal ω ⬝ᵥ (Q s.toNNReal ω *ᵥ ψ s.toNNReal ω))) ∂P

/-- `Y` is (a version of) the square-integrable Itô integral `∫_0^· φ · dM` on `[0,T]` with respect to
the filtration `𝒢`, for an integrator `M` with `d[M^i, M^j] = Q_{ij} ds`: `φ` is progressively
measurable with `E ∫_0^T φᵀ Q φ ds < ∞`, each `Y t` (`t ≤ T`) is `𝒢_t`-measurable, and there are
simple predictable integrands `φ_j` with `φ_j → φ` in `L²(Q ds × dP)` whose elementary integrals
converge to `Y t` in `L²(P)` for every `t ≤ T`. The integral process has almost-surely continuous
paths on `[0,T]`, selecting the continuous version from the per-time `L²` limits. -/
def IsItoIntegral (P : Measure Ω) (𝒢 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : ℝ≥0 → Ω → (Fin d → ℝ)) (Q : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (φ : ℝ≥0 → Ω → (Fin d → ℝ)) (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive 𝒢 φ ∧ qNormSq P T Q φ < ⊤ ∧
  (∀ t ≤ T, StronglyMeasurable[𝒢 t] (Y t)) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) ∧
  ∃ n : ℕ → ℕ, ∃ ξ : ℕ → ℕ → Ω → (Fin d → ℝ), (∀ j, IsSimpleIntegrand 𝒢 T (n j) (ξ j)) ∧
    Tendsto (fun j => qNormSq P T Q (stepProcess T (n j) (ξ j) - φ)) atTop (𝓝 0) ∧
    ∀ t ≤ T, Tendsto (fun j => ∫⁻ ω,
      ENNReal.ofReal ((simpleIntegral T (n j) (ξ j) M t ω - Y t ω) ^ 2) ∂P) atTop (𝓝 0)

/-! ## Assumption 5.1 (p. 15) with the standing setting of §2 -/

/-- The setting of §5: on a complete probability space, `W` is a standard `d`-dimensional Brownian
motion with completed natural filtration `𝒢 = 𝓕^W`; `σ` is a `𝒢`-progressively measurable
`d × d`-matrix process with `det σ(t) ≠ 0` `dt × dP`-a.e. on `[0,T]` (43); `X` has continuous paths,
`X 0` is `𝒢_0`-measurable and `X(t) = X(0) + ∫_0^t σ(u) · dW(u)` componentwise as a square-integrable
Itô integral on `[0,T]` (so `E[X](T) = E ∫_0^T ‖σ‖_F² dt < ∞`); `𝓕 = 𝓕^X` is the completed,
right-continuous natural filtration of `X` on `[0,T]`; `A` is an adapted cadlag process valued in positive semidefinite matrices
with `A = σ σᵀ` `dt × dP`-a.e. on `[0,T]`, i.e. `[X](t) = ∫_0^t A(s) ds` (3). -/
def IsBrownianSetting (P : Measure Ω) (T : ℝ≥0) (W : ℝ≥0 → Ω → EthierKurtz.SDEState d)
    (𝒢 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (X : ℝ≥0 → Ω → (Fin d → ℝ)) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  P.IsComplete ∧
  EthierKurtz.IsStandardBrownian P W ∧ IsCompletedNaturalFiltration P W 𝒢 ∧
  (∀ i j, IsStronglyProgressive 𝒢 (fun t ω => σ t ω i j)) ∧
  (∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), (σ s.toNNReal ω).det ≠ 0) ∧
  (∀ ω, Continuous (fun t => X t ω)) ∧ StronglyMeasurable[𝒢 0] (X 0) ∧
  (∀ i, IsItoIntegral P 𝒢 T (fun t ω j => W t ω j) (fun _ _ => 1)
    (fun t ω j => σ t ω i j) (fun t ω => X t ω i - X 0 ω i)) ∧
  IsCompletedNaturalFiltration P X ℱ ∧
  (∀ t < T, ℱ t = ⨅ s, ⨅ (_ : t < s ∧ s ≤ T), ℱ s) ∧
  (∀ t ≤ T, ∀ i j, StronglyMeasurable[ℱ t] (fun ω => A t ω i j)) ∧
  (∀ t ω, (A t ω).PosSemidef) ∧
  (∀ ω t, ContinuousWithinAt (fun s => A s ω) (Set.Ici t) t) ∧
  (∀ ω t, 0 < t → ∃ l, Tendsto (fun s => A s ω) (𝓝[<] t) (𝓝 l)) ∧
  (∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) T)),
    A s.toNNReal ω = σ s.toNNReal ω * (σ s.toNNReal ω)ᵀ)

/-! ## The spaces `𝓛²(X)`, `𝓘²(X)`, `𝒞_b^{1,2}(X)`, `D(X)`, `𝒲^{1,2}(X)` (§4.2, §5.2) -/

/-- `‖φ‖²_{𝓛²(X)} = E ∫_0^T φ(s)ᵀ A(s) φ(s) ds` (47), with `d[X] = A ds`. -/
noncomputable def L2XNormSq (P : Measure Ω) (T : ℝ≥0) (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (φ : ℝ≥0 → Ω → (Fin d → ℝ)) : ℝ≥0∞ :=
  qNormSq P T A φ

/-- `φ ∈ 𝓛²(X)`: progressively measurable with finite norm (47). -/
def MemL2X (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (φ : ℝ≥0 → Ω → (Fin d → ℝ)) : Prop :=
  IsStronglyProgressive ℱ φ ∧ L2XNormSq P T A φ < ⊤

/-- `Y ∈ 𝓘²(X)` (48): `Y = ∫_0^· φ · dX` for some `φ ∈ 𝓛²(X)`. -/
def MemI2X (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (X : ℝ≥0 → Ω → (Fin d → ℝ)) (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  ∃ φ, IsItoIntegral P ℱ T X A φ Y

/-- `‖Y − Z‖²_2 = E[(Y(T) − Z(T))²] ∈ [0, ∞]`, the squared distance of `𝓘²(X)`. -/
noncomputable def I2DistSq (P : Measure Ω) (T : ℝ≥0) (Y Z : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((Y T ω - Z T ω) ^ 2) ∂P

/-- `Y ∈ 𝒞_b^{1,2}(X)` (42) through the functional `F ∈ ℂ_b^{1,2}` (with derivatives `DF`, `gradF`,
`hessF`) satisfying (10): `Y` is `𝓕_t`-adapted on `[0,T]` and `Y(t) = F_t(X_t, A_t)` `P`-a.s. for
every `t < T`. -/
def MemC12bX (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (X : ℝ≥0 → Ω → (Fin d → ℝ)) (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (Y : ℝ≥0 → Ω → ℝ) (F DF : Functional d ℝ) (gradF : Functional d (Fin d → ℝ))
    (hessF : Functional d (Matrix (Fin d) (Fin d) ℝ)) : Prop :=
  (∀ t ≤ T, StronglyMeasurable[ℱ t] (Y t)) ∧ IsC12b T F DF gradF hessF ∧ PredictableInV T F ∧
  ∀ t < T, ∀ᵐ ω ∂P, Y t ω = F t (fun s => X s ω) (fun s => A s ω)

/-- `Y ∈ D(X) = 𝒞_b^{1,2}(X) ∩ 𝓘²(X)` (50) and `ψ ∈ 𝓛²(X)` is a vertical derivative
`∇_X Y` of it (Defs. 4.5, 5.4): `ψ(t) = ∇_x F_t(X_t, A_t)` for `t < T` for some
representing functional `F`. -/
def IsVertDerivD (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (X : ℝ≥0 → Ω → (Fin d → ℝ)) (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (Y : ℝ≥0 → Ω → ℝ) (ψ : ℝ≥0 → Ω → (Fin d → ℝ)) : Prop :=
  MemI2X P ℱ T X A Y ∧ MemL2X P ℱ T A ψ ∧
  ∃ (F DF : Functional d ℝ) (gradF : Functional d (Fin d → ℝ))
    (hessF : Functional d (Matrix (Fin d) (Fin d) ℝ)),
    MemC12bX P ℱ T X A Y F DF gradF hessF ∧
    ∀ t < T, ∀ ω, ψ t ω = gradF t (fun s => X s ω) (fun s => A s ω)

/-- `Y ∈ D(X)` (50). -/
def MemD (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (X : ℝ≥0 → Ω → (Fin d → ℝ)) (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  ∃ ψ, IsVertDerivD P ℱ T X A Y ψ

/-- `Y ∈ 𝒲^{1,2}(X)` (Def. 5.6): `Y` is in the closure of `D(X)` in `𝓘²(X)`. -/
def MemW12 (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (X : ℝ≥0 → Ω → (Fin d → ℝ)) (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  MemI2X P ℱ T X A Y ∧ ∃ Yn : ℕ → ℝ≥0 → Ω → ℝ, (∀ n, MemD P ℱ T X A (Yn n)) ∧
    Tendsto (fun n => I2DistSq P T (Yn n) Y) atTop (𝓝 0)

/-- `(Y, φ)` lies in the closure of the graph of `∇_X : D(X) → 𝓛²(X)` in `𝓘²(X) × 𝓛²(X)`:
`Y ∈ 𝒲^{1,2}(X)`, `φ ∈ 𝓛²(X)`, and some `Y_n ∈ D(X)` with vertical derivatives `ψ_n` satisfy
`Y_n → Y` in `𝓘²(X)` and `ψ_n → φ` in `𝓛²(X)`. -/
def IsClosureDeriv (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (X : ℝ≥0 → Ω → (Fin d → ℝ)) (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (Y : ℝ≥0 → Ω → ℝ) (φ : ℝ≥0 → Ω → (Fin d → ℝ)) : Prop :=
  MemW12 P ℱ T X A Y ∧ MemL2X P ℱ T A φ ∧
  ∃ (Yn : ℕ → ℝ≥0 → Ω → ℝ) (ψn : ℕ → ℝ≥0 → Ω → (Fin d → ℝ)),
    (∀ n, IsVertDerivD P ℱ T X A (Yn n) (ψn n)) ∧
    Tendsto (fun n => I2DistSq P T (Yn n) Y) atTop (𝓝 0) ∧
    Tendsto (fun n => L2XNormSq P T A (ψn n - φ)) atTop (𝓝 0)

/-- The integrand `ψ(s)ᵀ A(s) ζ(s)` of `∫_0^T ψ ζ d[X]`, integrable on `(0,T] × Ω` for
`ds × dP`. -/
def QIntegrable (P : Measure Ω) (T : ℝ≥0) (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (ψ ζ : ℝ≥0 → Ω → (Fin d → ℝ)) : Prop :=
  Integrable (fun p : ℝ × Ω => ψ p.1.toNNReal p.2 ⬝ᵥ (A p.1.toNNReal p.2 *ᵥ ζ p.1.toNNReal p.2))
    ((volume.restrict (Set.Ioc (0 : ℝ) T)).prod P)

/-- `E[∫_0^T ψ(s)ᵀ A(s) ζ(s) ds] = E[∫_0^T ψ ζ d[X]]` (a real Bochner integral; meaningful under
`QIntegrable`). -/
noncomputable def QInner (P : Measure Ω) (T : ℝ≥0) (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (ψ ζ : ℝ≥0 → Ω → (Fin d → ℝ)) : ℝ :=
  ∫ ω, (∫ s in Set.Ioc (0 : ℝ) T, ψ s.toNNReal ω ⬝ᵥ (A s.toNNReal ω *ᵥ ζ s.toNNReal ω)) ∂P

end FunctionalIto.Representation


