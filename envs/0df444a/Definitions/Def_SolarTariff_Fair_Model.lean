-- Prove2me | Definitions.Def_SolarTariff_Fair_Model
-- name    : SolarTariff_Fair_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:42.413074+00:00
-- url     : https://prove2.me/theorems/4a1984fe-c317-461f-8625-2070b913cafe
-- title:
--   §§3–4.3 — tiered customers, solar pricing, regulated tariffs, P2, T3, and T*
-- statement:
--   A market has finitely many customer tiers. Tier $i$ has $h_i$ households, each with annual demand $d_i$, potential solar generation $g_i$, and excess generation $e_i$. The solar firm's unit cost $c_s(y)$ depends on its total generation volume $y$. The model also records the baseline retail rate $p_{r0}$, baseline and target utility unit costs $c_u^0,c_u^{z^*}$, and required profit changes $\Delta_S,\Delta_U$.
--
--   For an adopting set $A$, write $E^0=\sum_i h_i d_i$, $\Delta_E^A=\sum_{i\in A}h_i g_i$, and $E^A=E^0-\Delta_E^A$. A tariff is represented by the two bills relevant to each tier: the nonadopter bill $T(d_i,0,0)$ and adopter bill $T(d'_i,e_i,1)$, where $d'_i=d_i-(g_i-e_i)$. Customers adopt at solar price $p$ exactly when $p\le t(i)=[T(d_i,0,0)-T(d'_i,e_i,1)]/g_i$. The solar firm earns
--
--   $$\Pi_S(p)=\bigl(p-c_s(\Delta_E^{A(p)})\bigr)\Delta_E^{A(p)},\qquad A(p)=\{i:p\le t(i)\}.$$
--
--   P2 feasibility requires exactly the target tiers to adopt at the prescribed price, that price to be the firm's unique profit maximizing response with profit $\Delta_S$, and the utility's profit change to equal $\Delta_U$. The regulator minimizes the largest per-household increase in customer cash outflow. Financial welfare improvement is $\Delta_{WF}=c_u^0E^0-c_u^{z^*}E^A-c_s(\Delta_E^A)\Delta_E^A$ and aggregate customer gain is $\Delta_C=\Delta_{WF}-\Delta_S-\Delta_U$.
--
--   Tariff $T_3$ charges nonadopters $p_r d_i$ and adopters $p_r d'_i-p_r e_i+f_i$. The constructed $T^*$ sets adopter thresholds to $c_s(\Delta_E^A)+\Delta_S/\Delta_E^A$, nonadopter thresholds to $c_s(\Delta_E^{\mathrm{all}})$, fees to $f_i=g_i(p_r-t(i))$, and chooses $p_r$ as the solution of the utility's profit constraint.
--
--   **Formalization Note** The finite tier type is unordered because the paper relabels tiers in Proposition 5. The standing assumptions include $h_i,d_i,g_i>0$, $0\le e_i\le g_i$, nonincreasing $c_s$, and $\Delta_S>0$; the three strict positivity conditions make the paper's divisions meaningful. The target has at least one adopter and $\Delta_E^A\le E^0$. The utility's total cost is outside the household sum in equation (16), as required by the welfare identity. The paper's tier inference from $d'_i$ licenses tier-indexed fees. Solar prices range over all real numbers, with adoption on a tie.
-- source:
--   Singh & Scheller-Wolf, That’s Not Fair: Tariff Structures for Electric Utilities with Rooftop Solar, SSRN 2926676 (SSRN Version), pp. 7–18 (PDF 7–18), §§3–4.3, equations (1)–(21), Definition 1 and T* construction

import Mathlib

namespace SolarTariff.Fair

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The tier data and the utility and solar-company parameters of §§3–4. -/
structure Market (ι : Type*) where
  h : ι → ℝ
  d : ι → ℝ
  g : ι → ℝ
  e : ι → ℝ
  cs : ℝ → ℝ
  pr0 : ℝ
  cu0 : ℝ
  cuStar : ℝ
  dS : ℝ
  dU : ℝ

/-- Standing assumptions, including the positive denominators implicit in the paper. -/
def Market.Standing (M : Market ι) : Prop :=
  (∀ i, 0 < M.h i) ∧ (∀ i, 0 < M.d i) ∧ (∀ i, 0 < M.g i) ∧
  (∀ i, 0 ≤ M.e i ∧ M.e i ≤ M.g i) ∧ Antitone M.cs ∧ 0 < M.dS

/-- Grid use `d'_i = d_i - (g_i - e_i)`. -/
def gridUsage (M : Market ι) (i : ι) : ℝ := M.d i - (M.g i - M.e i)

/-- Base-case demand `E⁰`. -/
def E0 (M : Market ι) : ℝ := ∑ i, M.h i * M.d i

/-- Generation from the adopting tiers, `Δ_E^z`. -/
def DeltaE (M : Market ι) (A : Finset ι) : ℝ := ∑ i ∈ A, M.h i * M.g i

/-- Net utility demand under the outcome `A`. -/
def EOf (M : Market ι) (A : Finset ι) : ℝ := E0 M - DeltaE M A

/-- The paper considers nonempty adoption outcomes with nonnegative net grid use. -/
def Admissible (M : Market ι) (A : Finset ι) : Prop :=
  A.Nonempty ∧ DeltaE M A ≤ E0 M

/-- The only two evaluations of a tariff used in P2, one for each adoption choice. -/
structure Bills (ι : Type*) where
  nonAdopt : ι → ℝ
  adopt : ι → ℝ

/-- Customer `i`'s adoption threshold, equation (15). -/
noncomputable def threshold (M : Market ι) (B : Bills ι) (i : ι) : ℝ :=
  (B.nonAdopt i - B.adopt i) / M.g i

/-- Ties are settled in favor of adoption. -/
noncomputable def adopters (M : Market ι) (B : Bills ι) (p : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => p ≤ threshold M B i)

/-- The solar company's profit at any real price, equation (2). -/
noncomputable def solarProfit (M : Market ι) (B : Bills ι) (p : ℝ) : ℝ :=
  (p - M.cs (DeltaE M (adopters M B p))) * DeltaE M (adopters M B p)

/-- Utility profit change, equation (16), with the total utility cost outside the sum. -/
def utilityChange (M : Market ι) (B : Bills ι) (A : Finset ι) : ℝ :=
  (∑ i, M.h i * (if i ∈ A then B.adopt i else B.nonAdopt i)) -
    M.cuStar * EOf M A - (M.pr0 - M.cu0) * E0 M

/-- A tier household's change in cash outflow, equation (14). -/
def outflowChange (M : Market ι) (B : Bills ι) (A : Finset ι)
    (ps : ℝ) (i : ι) : ℝ :=
  (if i ∈ A then B.adopt i + ps * M.g i else B.nonAdopt i) - M.pr0 * M.d i

/-- P2's largest increase in customer cash outflow. -/
noncomputable def objective [Nonempty ι] (M : Market ι) (B : Bills ι)
    (A : Finset ι) (ps : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (outflowChange M B A ps)

/-- Financial welfare improvement, page 10. -/
def dWF (M : Market ι) (A : Finset ι) : ℝ :=
  M.cu0 * E0 M - M.cuStar * EOf M A - M.cs (DeltaE M A) * DeltaE M A

/-- The customers' aggregate financial gain, from page 15. -/
def dC (M : Market ι) (A : Finset ι) : ℝ := dWF M A - M.dS - M.dU

/-- P2 feasibility as the induced equilibrium: target adopters, unique solar-price best
response with profit `Δ_S`, and the utility's required profit change `Δ_U`. -/
def FeasibleP2 (M : Market ι) (A : Finset ι) (B : Bills ι) (ps : ℝ) : Prop :=
  adopters M B ps = A ∧ solarProfit M B ps = M.dS ∧
  (∀ p : ℝ, p ≠ ps → solarProfit M B p < M.dS) ∧ utilityChange M B A = M.dU

/-- Tariff family T3 of equation (21): a common retail rate and tier-specific adopter fee. -/
structure T3 (ι : Type*) where
  pr : ℝ
  f : ι → ℝ

/-- The two bills for tariff T3. -/
def T3.bills (M : Market ι) (τ : T3 ι) : Bills ι :=
  ⟨fun i => τ.pr * M.d i,
   fun i => τ.pr * gridUsage M i - τ.pr * M.e i + τ.f i⟩

/-- The marginal adopter threshold in T*, page 18, step 3. -/
noncomputable def tm (M : Market ι) (A : Finset ι) : ℝ :=
  M.cs (DeltaE M A) + M.dS / DeltaE M A

/-- T*'s thresholds: marginal threshold for adopters, all-adopter cost otherwise. -/
noncomputable def tStar (M : Market ι) (A : Finset ι) (i : ι) : ℝ :=
  if i ∈ A then tm M A else M.cs (DeltaE M Finset.univ)

/-- The rate solving equation (16) after substituting `f_i = g_i (p_r - t(i))`.
This is the equation's root, rather than the subsequently proved welfare formula. -/
noncomputable def prStar (M : Market ι) (A : Finset ι) : ℝ :=
  (M.dU + M.cuStar * EOf M A + (M.pr0 - M.cu0) * E0 M +
    ∑ i ∈ A, M.h i * M.g i * tStar M A i) / E0 M

/-- The tariff T* constructed on page 18, steps 1–4. -/
noncomputable def TStar (M : Market ι) (A : Finset ι) : T3 ι :=
  ⟨prStar M A, fun i => M.g i * (prStar M A - tStar M A i)⟩

end SolarTariff.Fair


