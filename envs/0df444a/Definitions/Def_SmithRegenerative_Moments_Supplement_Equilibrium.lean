-- Prove2me | Definitions.Def_SmithRegenerative_Moments_Supplement_Equilibrium
-- name    : SmithRegenerative_Moments_Supplement_Equilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:40:35.006711+00:00
-- url     : https://prove2.me/theorems/b5dc0949-0557-4ad1-8535-9ddf03c5b756
-- title:
--   Equilibrium conditional probabilities, α-sets, non-null sets and renewal alternatives
-- statement:
--   Let $x_t$ be a measurable state process on the same probability space as the delayed renewal process, and let $\mathcal A$ be a class of measurable state sets. For each $A\in\mathcal A$, the equilibrium representation specifies a probability-valued kernel $\phi_A$ independent of the boundary parameter. If $L_t$ is the last regeneration epoch,
--   $$P_z(x_t\in A\mid n_t>0,L_t)=\phi_A(t-L_t).$$
--   This conditional identity is encoded by integration against every Borel set of last epochs. The renewal kernel is $\phi_A(v)P(t_1>v)$, retaining the mass of infinite cycles. The three alternatives inherited from Theorem 2 are integrability and monotonicity, or finite mean together with local bounded variation, or finite mean together with the class $\mathfrak S$ and measurable $\phi_A$.
--
--   An $\alpha$-set has constants $\tau,\epsilon>0$ such that, eventually in real time,
--   $$\epsilon P_z(x_t\in A)\le P_z(x_t\in A,n_{t+\tau}>n_t).$$
--   A non-null set is one whose probability does not tend to zero. These definitions retain the defective first-delay cases needed by Corollary 2·1 and Theorem 4.
--
--   **Formalization Note** The displayed conditional equation has an integrated meaning even on zero-probability conditioning events. The last epoch corrects the paper's shifted index. Global time measurability is required only in the class-$\mathfrak S$ alternative, not in Theorem 3. Conditional probability kernels are chosen in $[0,1]$ on irrelevant arguments as well.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, §3·4, p. 14; Definitions 4–5, p. 19

import Mathlib
import Definitions.Def_SmithRegenerative_Moments_Supplement_ExtendedRenewal

namespace SmithRegenerative.Moments.Supplement

open MeasureTheory ProbabilityTheory Filter Topology

/-- Smith (1955), §3·4, p. 14, (3·4·1), with the improper intervals expressly
permitted on p. 13. Formalization Note: integrated conditional-probability identity
for every Borel set of last epochs. `L_t` is the last event at or before t, correcting
printed `T_{n_t}`. No renewal convolution formula or limiting theorem is assumed.
The kernel is a [0,1]-valued version, as stated in the proof on p. 15.
Global time measurability is imposed only where the source requests it. -/
structure Equilibrium (Ω X Z : Type*) [MeasurableSpace Ω] [MeasurableSpace X]
    extends ExtendedRenewal Ω Z where
  x : ℝ → Ω → X
  measurable_x : ∀ t, Measurable (x t)
  sets : Set (Set X)
  measurable_sets : ∀ A ∈ sets, MeasurableSet A
  φ : Set X → ℝ → ℝ
  probability_φ : ∀ A ∈ sets, ∀ v : ℝ, 0 ≤ v → φ A v ∈ Set.Icc 0 1
  integrable_repr : ∀ z, ∀ A ∈ sets, ∀ t : ℝ, 0 ≤ t →
    IntegrableOn (fun ω => φ A (t - extLast τ t ω)) {ω | 0 < extCount τ t ω} (P z)
  repr : ∀ z, ∀ A ∈ sets, ∀ t : ℝ, 0 ≤ t → ∀ B : Set ℝ, MeasurableSet B →
    (P z {ω | x t ω ∈ A ∧ 0 < extCount τ t ω ∧ extLast τ t ω ∈ B}).toReal =
      ∫ ω in {ω | 0 < extCount τ t ω ∧ extLast τ t ω ∈ B}, φ A (t - extLast τ t ω) ∂P z

/-- Smith (1955), (3·5·1), p. 16. Formalization Note: the tail includes mass
at infinity, unlike the tail of the finite subprobability law alone. -/
noncomputable def kernel {Ω X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (E : Equilibrium Ω X Z) (A : Set X) (v : ℝ) : ℝ :=
  E.φ A v * (E.F (Set.Ioi (ENNReal.ofReal v))).toReal

/-- Smith (1955), Theorem 2(iv), pp. 14–15, inherited by Corollary 2·1.
Formalization Note: all three alternatives are retained; finite mean is required
only in the second branch. The class S and convolution convention are reused. -/
def RenewalConditions {Ω X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (E : Equilibrium Ω X Z) (A : Set X) : Prop :=
  (IntegrableOn (kernel E A) (Set.Ioi 0) ∧
    (MonotoneOn (kernel E A) (Set.Ioi 0) ∨ AntitoneOn (kernel E A) (Set.Ioi 0))) ∨
  (extendedMean E.F < ⊤ ∧
    ((∀ b : ℝ, BoundedVariationOn (kernel E A) (Set.Icc 0 b)) ∨
      (SmithRegenerative.Equilibrium.InClassS (finiteLaw E.F) ∧ Measurable (E.φ A))))

/-- Smith (1955), Definition 4, p. 19, (3·7·1).
Formalization Note: multiply the conditional lower bound by the state probability,
so that zero-probability conditioning events impose no artificial restriction. -/
def AlphaSet {Ω X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (R : ExtendedRenewal Ω Z) (x : ℝ → Ω → X) (z : Z) (A : Set X) : Prop :=
  ∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧ ∀ᶠ t : ℝ in atTop,
    ε * (R.P z {ω | x t ω ∈ A}).toReal ≤
      (R.P z {ω | x t ω ∈ A ∧ extCount R.τ t ω < extCount R.τ (t + τ) ω}).toReal

/-- Smith (1955), Definition 5, p. 19, (3·7·2).
Formalization Note: non-nullness negates convergence to zero; it does not assume
that a positive limit exists. -/
def NonNull {Ω X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (R : ExtendedRenewal Ω Z) (x : ℝ → Ω → X) (z : Z) (A : Set X) : Prop :=
  ¬ Tendsto (fun t : ℝ => (R.P z {ω | x t ω ∈ A}).toReal) atTop (𝓝 0)

end SmithRegenerative.Moments.Supplement


