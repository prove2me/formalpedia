-- Prove2me | Definitions.Def_TwoAssumptions_basic
-- name    : TwoAssumptions_basic
-- status  : Definition
-- author  : @LG
-- created : 2026-11-22T23:15:49.299098+00:00
-- url     : https://prove2.me/theorems/8eb35980-96c7-4091-a6e0-232ef562f83e
-- title:
--   Cosper thesis: reducibility, state variables, unit system, degrees of freedom, det/rev evolution
-- statement:
--   Foundational definitions for Cosper's *From Two Assumptions to Hamilton's Mechanics* (2022), Definitions 1, 2, 6, 9, 10, 13.
--
--   1. **Infinitesimal reducibility** (Def. 1): a measure $dS$ on the particle state space $S$ and, for each whole-system state $c$, a normalized nonnegative integrable density $\rho_c:S\to\mathbb R$ with $\int_S\rho_c\,dS=1$. The counting function $\mu_c(U)=\int_U\rho_c\,dS$ is the fraction of the system in $U$, with $\mu_c(S)=1$.
--   2. **State variables** (Def. 2): a single variable is a map $S\to\mathbb R$; a complete set is an invertible map $S\to\mathbb R^n$.
--   3. **Unit system** (Def. 6): a change of units acts on each unit variable independently ($\hat q^i$ depends only on $q^i$).
--   4. **Degree of freedom** (Def. 9): the area measure $dS^i=dq^i\,dp_i$ of a canonical pair.
--   5. **Independent degrees of freedom** (Def. 10): the product measure $dS=\prod_i dS^i$.
--   6. **Deterministic and reversible evolution** (Def. 13): density conservation, encoded as the divergence-free condition on the evolution vector field.
--
--   **Formalization Note.** Densities are normalized (the source drops the denominator implicitly). "Differentiable" is taken as $C^1$. Density conservation is encoded via the Liouville equivalence with the divergence-free condition. The Poisson bracket (Def. 11) reuses the published `RelPartMech_coordinates` definition.
-- source:
--   Cosper 2022, From Two Assumptions to Hamilton's Mechanics, Definitions (1),(2),(6),(9),(10),(13). https://github.com/assumptionsofphysics/thesis-ClassicalMechanics

import Mathlib

open MeasureTheory
open scoped BigOperators

namespace TwoAssumptions

/-- **Infinitesimal reducibility (Definition 1).** The whole-system states `C` reduce to
particle states `S`: a measure `dS` on `S` and, for each whole state `c`, a normalized
nonnegative integrable density `ρ c : S → ℝ`. The counting function `counting h c U`
gives the fraction of the system found in `U`, and `counting h c Set.univ = 1`. -/
structure InfinitesimallyReducible (C S : Type*) [MeasurableSpace S] where
  dS : Measure S
  ρ : C → S → ℝ
  ρ_nonneg : ∀ c s, 0 ≤ ρ c s
  ρ_integrable : ∀ c, Integrable (ρ c) dS
  ρ_normalized : ∀ c, ∫ s, ρ c s ∂dS = 1

/-- The counting function `μ(U)`: the fraction of the system found within the states `U`. -/
noncomputable def counting {C S : Type*} [MeasurableSpace S]
    (h : InfinitesimallyReducible C S) (c : C) (U : Set S) : ℝ :=
  ∫ s in U, h.ρ c s ∂h.dS

/-- **State variable (Definition 2).** A single numerical quantity assigned to each state. -/
def StateVariable (S : Type*) := S → ℝ

/-- **Complete set of state variables (Definition 2).** An invertible labeling
`ξ^a : S → ℝ^n` identifying each state with a unique tuple of `n` numbers. -/
def CompleteStateVariables (S : Type*) (n : ℕ) := S ≃ (Fin n → ℝ)

/-- **Unit system / change of units (Definition 6).** A change of the `n` unit variables
in which each `q̂^i` depends only on `q^i` (unit variables are independent of one another):
the derivative of component `i` in any other unit direction `j ≠ i` vanishes. -/
def IsUnitChange {n : ℕ} (g : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ i j, i ≠ j → ∀ q, fderiv ℝ (fun q' => g q' i) q (Pi.single j 1) = 0

/-- **Degree of freedom (Definition 9).** The state-counting measure of one canonical pair
`(q^i, p_i)` is the area `dS^i = dq^i dp_i` (Lebesgue measure on the plane). -/
noncomputable def dofMeasure : Measure (ℝ × ℝ) := MeasureTheory.volume

/-- **Independent degrees of freedom (Definition 10).** For `n` independent degrees of
freedom the total state-counting measure is the product `dS = ∏_i dS^i`, the volume on
`(ℝ × ℝ)^n`. -/
noncomputable def stateCountingMeasure (n : ℕ) : Measure (Fin n → ℝ × ℝ) :=
  MeasureTheory.volume

/-- **Deterministic and reversible evolution (Definition 13).** The density of states is
conserved along the evolution. For a `C¹` evolution vector field `S` this is the
divergence-free (Liouville) condition `∑_i ∂S^i/∂x^i = 0`, equivalent to the flow
preserving the state-counting volume; uniqueness of the evolution is automatic for a
`C¹` field. -/
def IsDetRev {m : ℕ} (S : (Fin m → ℝ) → (Fin m → ℝ)) : Prop :=
  ∀ x, ∑ i, fderiv ℝ (fun y => S y i) x (Pi.single i 1) = 0

end TwoAssumptions


