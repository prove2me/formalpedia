-- Prove2me | Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_Mixed
-- name    : TransparencyTeamContracts_Submodular_Supplement_Mixed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:13:10.192638+00:00
-- url     : https://prove2.me/theorems/42025683-77d7-4720-9e81-22b1edfc083e
-- title:
--   Independent mixed equilibria, auxiliary instances and public mixed benchmarks
-- statement:
--   The multilinear extension is the referenced finite product-law expectation $F_f(x)=\mathbb E[f(R_x)]$, with independent inclusion probabilities $x_i\in[0,1]$. The partial marginal is $\partial_iF_f(x)=F_f(x_{i\leftarrow1})-F_f(x_{i\leftarrow0})$. Mixed equilibrium means $\alpha_i\partial_iF\le c_i$ at $x_i=0$, equality at $0<x_i<1$, and $\alpha_i\partial_iF\ge c_i$ at $x_i=1$. Principal utility is $(1-\sum_i\alpha_i)F_f(x)$; transfers are not multiplied by effort probabilities.
--
--   The stateless, no-information, full-information and joint public-information values optimize over contracts and mixed equilibria. Joint schemes retain the base finite-state joint law, Bayes identity, arbitrary compact Borel signals, measurable contracts and independent profiles, explicit integrability and principal-favorable equilibrium selection. There is no finite-support restriction. The auxiliary technology is $\widetilde f(T)=F_f(x^T)$ and auxiliary cost is $\widetilde c_i=x_ic_i$, both computed from the original data. Supermodularity is the referenced increasing-marginal predicate alone, without its neighboring normalization predicate.
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), §2 and Appendices A–B; printed pp. 5–8, 23–32 (PDF pp. 7–10, 25–34); Theorem 5.1, printed p. 18 (PDF p. 20)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Information
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_CritContracts_IsSupermodular

open Finset MeasureTheory
open scoped Classical

namespace TransparencyTeamContracts.Submodular.Supplement

abbrev IsSupermodular {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop := CritContracts.IsSupermodular f

abbrev F {n : ℕ} (f : Finset (Fin n) → ℝ) := NonmonotoneSubmod.Shared.F f
def InCube {n : ℕ} (x : Fin n → ℝ) : Prop := ∀ i, 0 ≤ x i ∧ x i ≤ 1
noncomputable def restrictProfile {n : ℕ} (x : Fin n → ℝ) (T : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ T then x i else 0

/-- Polynomial partial derivative; finite expectations include all boundary profiles. -/
noncomputable def mixedMarginal {n : ℕ} (f : Finset (Fin n) → ℝ)
    (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  F f (Function.update x i 1) - F f (Function.update x i 0)

/-- Equation (17), with the product (independent) mixed law supplied by F.
The paper-specific contract game extends the published base strategic game. -/
def IsMixedNE {n : ℕ} (f : Finset (Fin n) → ℝ) (c α x : Fin n → ℝ) : Prop :=
  InCube x ∧ ∀ i,
    (x i = 0 → α i * mixedMarginal f x i ≤ c i) ∧
    (0 < x i → x i < 1 → α i * mixedMarginal f x i = c i) ∧
    (x i = 1 → c i ≤ α i * mixedMarginal f x i)

noncomputable def mixedUtility {n : ℕ} (f : Finset (Fin n) → ℝ)
    (α x : Fin n → ℝ) : ℝ := (1 - ∑ i, α i) * F f x
def IsBestMixedNE {n : ℕ} (f : Finset (Fin n) → ℝ) (c α x : Fin n → ℝ) : Prop :=
  IsMixedNE f c α x ∧ ∀ y, IsMixedNE f c α y → mixedUtility f α y ≤ mixedUtility f α x
def mixedPayoffs {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ) : Set ℝ :=
  {u | ∃ α x, IsContract α ∧ IsMixedNE f c α x ∧ u = mixedUtility f α x}
noncomputable def mixedV {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ) : ℝ :=
  sSup (mixedPayoffs f c)
noncomputable def mixedFull {n m : ℕ} (M : Model n m) (D : Belief m) : ℝ :=
  ∑ ω, (D : Fin m → ℝ) ω * mixedV (M.f ω) M.c
noncomputable def mixedNo {n m : ℕ} (M : Model n m) (D : Belief m) : ℝ :=
  mixedV (posteriorReward M D) M.c

/-- Actual public information-and-contract schemes, with arbitrary compact Borel
signals as in the base definition; only the equilibrium selection is extended. -/
structure MixedPublicScheme {n m : ℕ} (M : Model n m) (D : Belief m)
    (Signal : Type) [MeasurableSpace Signal] where
  joint : Measure (Fin m × Signal)
  signaling : RiskPersuasion.Convex.IsSignalingScheme (D : Fin m → ℝ) joint
  posterior : Signal → Belief m
  bayes : RiskPersuasion.Convex.IsPosterior joint (fun s => (posterior s : Fin m → ℝ))
  contract : Signal → Fin n → ℝ
  contract_bounds : ∀ s, IsContract (contract s)
  contract_measurable : ∀ i, Measurable (fun s => contract s i)
  profile : Signal → Fin n → ℝ
  profile_measurable : ∀ i, Measurable (fun s => profile s i)
  favorable : ∀ᵐ s ∂(joint.map Prod.snd),
    IsBestMixedNE (posteriorReward M (posterior s)) M.c (contract s) (profile s)
  payoff_integrable : Integrable
    (fun p => mixedUtility (M.f p.1) (contract p.2) (profile p.2)) joint

noncomputable def MixedPublicScheme.value {n m : ℕ} {M : Model n m} {D : Belief m}
    {Signal : Type} [MeasurableSpace Signal] (A : MixedPublicScheme M D Signal) : ℝ :=
  ∫ p, mixedUtility (M.f p.1) (A.contract p.2) (A.profile p.2) ∂A.joint
def mixedPublicPayoffs {n m : ℕ} (M : Model n m) (D : Belief m) : Set ℝ :=
  {u | ∃ (Signal : Type) (t : TopologicalSpace Signal) (ms : MeasurableSpace Signal),
    @CompactSpace Signal t ∧ @BorelSpace Signal t ms ∧
    ∃ A : @MixedPublicScheme n m M D Signal ms, u = A.value}
noncomputable def mixedOptimal {n m : ℕ} (M : Model n m) (D : Belief m) : ℝ :=
  sSup (mixedPublicPayoffs M D)

/-- The auxiliary reward and cost in (18), not independently chosen instance data. -/
noncomputable def auxiliaryReward {n : ℕ} (f : Finset (Fin n) → ℝ)
    (x : Fin n → ℝ) (T : Finset (Fin n)) : ℝ := F f (restrictProfile x T)
def auxiliaryCost {n : ℕ} (c x : Fin n → ℝ) : Fin n → ℝ := fun i => x i * c i

end TransparencyTeamContracts.Submodular.Supplement


