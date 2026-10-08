-- Prove2me | Definitions.Def_ReflectedBSDE_Existence_Solution
-- name    : ReflectedBSDE_Existence_Solution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:01.985427+00:00
-- url     : https://prove2.me/theorems/4cc176f7-089f-491e-be71-c689af4ec035
-- title:
--   §2, p. 704 — solutions of the reflected BSDE: conditions (v), (v′), (vi)–(viii)
-- statement:
--   Let $B$, $(\mathcal F_t)$, $T$ and the data $(\xi,f,S)$ be as in the setting of §2. Consider a triple $(Y,Z,K)$ of $\mathcal F_t$-progressively measurable processes with values in $\mathbb R$, $\mathbb R^d$ and $\mathbb R$. Write $\int_t^T(Z_s,dB_s)=\sum_{j=1}^d\big(J^j_T-J^j_t\big)$, where $J^j_t=\int_0^t Z^j_s\,dB^j_s$ is the Itô integral of $Z^j$ against $B^j$.
--
--   1. **(vi)–(viii) with integrals $J$.** Each $J^j$ is an Itô integral process of $Z^j$ (which requires $Z^j\in\mathbb H^2$), and almost surely: every $J^j$ is continuous on $[0,T]$; $s\mapsto f(s,Y_s,Z_s)$ is integrable on $[0,T]$; and for all $t\in[0,T]$
--   $$\text{(vi)}\quad Y_t=\xi+\int_t^T f(s,Y_s,Z_s)\,ds+K_T-K_t-\int_t^T(Z_s,dB_s),$$
--   $$\text{(vii)}\quad Y_t\ge S_t,$$
--   and (viii): $K$ is continuous and nondecreasing on $[0,T]$, $K_0=0$, and $\displaystyle\int_0^T(Y_t-S_t)\,dK_t=0$.
--   2. **Solution of the RBSDE.** $(Y,Z,K)$ satisfies (vi)–(viii) if this holds for some choice of the integrals $J$.
--   3. **(v).** $Z\in\mathbb H^2$: $E\int_0^T|Z_t|^2\,dt<\infty$.
--   4. **(v′).** $Y\in\mathcal S^2$ and $K_T\in\mathbb L^2$.
--   5. **Equality of solutions.** $(Y,Z,K)$ and $(Y',Z',K')$ are equal if $Y,Y'$ and $K,K'$ are indistinguishable on $[0,T]$ (almost surely equal at every $t\in[0,T]$) and $Z=Z'$ $dP\otimes dt$-almost everywhere, i.e. $E\int_0^T|Z_t-Z'_t|^2\,dt=0$.
--
--   The process $K$ is the minimal upward push that keeps $Y$ above the obstacle $S$; it acts only when $Y_t=S_t$. The integrability conditions are kept separate because the paper's results assume different subsets of them.
--
--   **Formalization Note** The stochastic integral is the $L^2$ Itô integral of the referenced `Peng1990.SMP.IsItoIntegral`, of which a version with continuous paths is chosen. Since that integral is only defined for $Z^j\in\mathbb H^2$, the predicate for (vi)–(viii) already contains (v). Equations (vi)–(vii) hold almost surely simultaneously for all $t\in[0,T]$. The integral in (viii) is taken against the Stieltjes measure of the path $t\mapsto K_{t\wedge T}$, and its integrand $Y-S$ is nonnegative by (vii). That $K$ takes values in $\mathbb R_+$ follows from $K_0=0$ and monotonicity.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 704 (PDF p. 3), conditions (v), (v′), (vi), (vii), (viii)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Skorohod
import Definitions.Def_ReflectedBSDE_Existence_Setting

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ReflectedBSDE.Existence

open Peng1990.SMP

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- (vi)–(viii) of p. 704, with a fixed choice `J = (J¹, …, Jᵈ)` of the stochastic integrals:
`Y`, `Z`, `K` are `𝓕`-progressively measurable; each `Jʲ` is the Itô integral process
`Jʲ_t = ∫₀ᵗ Zʲ_s dBʲ_s` (`Peng1990.SMP.IsItoIntegral`, which requires `Zʲ ∈ ℍ²`); and almost
surely, simultaneously for all `t ∈ [0, T]`:
* every `Jʲ` has continuous paths on `[0, T]` and `s ↦ f(s, Y_s, Z_s)` is integrable on `[0, T]`;
* (vi) `Y_t = ξ + ∫ₜᵀ f(s, Y_s, Z_s) ds + K_T − K_t − ∫ₜᵀ (Z_s, dB_s)`, where
  `∫ₜᵀ (Z_s, dB_s) = Σⱼ (Jʲ_T − Jʲ_t)`;
* (vii) `Y_t ≥ S_t`;
* (viii) `K` is continuous and nondecreasing on `[0, T]`, `K_0 = 0`, and
  `∫₀ᵀ (Y_t − S_t) dK_t = 0`, the integral being taken against the Stieltjes measure of the path
  `t ↦ K_{t ∧ T}`. -/
def SolvesRBSDEWith {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ)
    (S : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
    (J : Fin d → ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive 𝓕 Y ∧ IsStronglyProgressive 𝓕 Z ∧ IsStronglyProgressive 𝓕 K ∧
    (∀ j, IsItoIntegral 𝓕 P T (fun s ω => B s ω j) (fun s ω => Z s ω j) (J j)) ∧
    ∀ᵐ ω ∂P,
      (∀ j, ContinuousOn (fun t => J j t ω) (Iic T)) ∧
      IntegrableOn (fun s : ℝ => f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω))
        (Icc 0 (T : ℝ)) ∧
      (∀ t ≤ T, Y t ω = ξ ω
          + ∫ s in Icc (t : ℝ) T, f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω)
          + K T ω - K t ω - ∑ j, (J j T ω - J j t ω)) ∧
      (∀ t ≤ T, S t ω ≤ Y t ω) ∧
      Monotone (fun t => K (min t T) ω) ∧ Continuous (fun t => K (min t T) ω) ∧ K 0 ω = 0 ∧
      ∫⁻ t in Icc (0 : ℝ) T, ENNReal.ofReal (Y t.toNNReal ω - S t.toNNReal ω)
        ∂(pathMeasure fun t => K (min t T) ω) = 0

/-- `(Y, Z, K)` satisfies (vi)–(viii) of p. 704 for some choice of the stochastic integrals
`∫₀ᵗ Zʲ dBʲ` (see `SolvesRBSDEWith`). -/
def SolvesRBSDE {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ)
    (S : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ) :
    Prop :=
  ∃ J : Fin d → ℝ≥0 → Ω → ℝ, SolvesRBSDEWith 𝓕 P T B ξ f S Y Z K J

/-- (v): `Z ∈ ℍ²`, i.e. `Z` is progressively measurable with `E ∫₀ᵀ |Z_t|² dt < ∞`. -/
def SatisfiesV {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (Z : ℝ≥0 → Ω → Fin d → ℝ) : Prop :=
  L2F 𝓕 P T Z

/-- (v′): `Y ∈ 𝒮²` and `K_T ∈ 𝕃²`. -/
def SatisfiesVPrime (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (Y K : ℝ≥0 → Ω → ℝ) : Prop :=
  IsS2 𝓕 P T Y ∧ ∫⁻ ω, ‖K T ω‖ₑ ^ 2 ∂P < ⊤

/-- Two triples `(Y, Z, K)` and `(Y', Z', K')` are equal as solutions on `[0, T]`: `Y, Y'` and
`K, K'` are indistinguishable on `[0, T]` (almost surely `Y_t = Y'_t` and `K_t = K'_t` for all
`t ∈ [0, T]`), and `Z = Z'` `dP ⊗ dt`-almost everywhere on `Ω × [0, T]`, i.e.
`E ∫₀ᵀ |Z_t − Z'_t|² dt = 0`. -/
def SameSolution {d : ℕ} (P : Measure Ω) (T : ℝ≥0) (Y : ℝ≥0 → Ω → ℝ)
    (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ) (Y' : ℝ≥0 → Ω → ℝ)
    (Z' : ℝ≥0 → Ω → Fin d → ℝ) (K' : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, ∀ t ≤ T, Y t ω = Y' t ω ∧ K t ω = K' t ω) ∧
    ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T,
      ENNReal.ofReal (euclSq (Z s.toNNReal ω - Z' s.toNNReal ω)) ∂volume ∂P = 0

end ReflectedBSDE.Existence


