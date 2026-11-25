-- Prove2me | Definitions.Def_MondererShapley_Examples
-- name    : MondererShapley_Examples
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:07:38.449065+00:00
-- url     : https://prove2.me/theorems/36241f80-1ae8-4789-9b44-730ca6face42
-- title:
--   Examples
-- statement:
--   Definitions and structural lemmas for Examples, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/monderer-shapley-potential-lean; see pinned Apache-2.0 LICENSE)'s pinned Monderer-Shapley exact potential games characterization development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Examples.lean

module
public import Definitions.Def_MondererShapley_Solution
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Theorems.Thm_Potential_exactPotential_fourCycle
public import Theorems.Thm_Potential_fourCycle_exists_pureNash
public import Theorems.Thm_Potential_monderer_shapley_characterization
public import Theorems.Thm_Potential_monderer_shapley_fourCycle

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Potential.Examples
def coordination : Payoff (fun _ : Bool => Bool) :=
  fun _ s => if s false = s true then 1 else 0
def coordinationPotential (s : Bool → Bool) : ℝ :=
  if s false = s true then 1 else 0
theorem coordination_exact : ExactPotential coordination coordinationPotential := by
  intro s i a
  rfl
example : FourCycle coordination :=
  exactPotential_fourCycle coordination coordinationPotential coordination_exact
example : ∃ s, PureNash coordination s :=
  fourCycle_exists_pureNash coordination
    (exactPotential_fourCycle coordination coordinationPotential coordination_exact)
def matchingPennies : Payoff (fun _ : Bool => Bool) := fun i s =>
  if i then (if s false = s true then 0 else 1)
  else (if s false = s true then 1 else 0)
theorem matchingPennies_not_fourCycle : ¬ FourCycle matchingPennies := by
  intro h
  have hc := h (fun _ => false) false true (by decide) true true
  norm_num [matchingPennies, Function.update] at hc
example : ¬ ∃ P, ExactPotential matchingPennies P := by
  intro h
  exact matchingPennies_not_fourCycle ((monderer_shapley_fourCycle matchingPennies).mp h)
def polynomialGame : Payoff (fun _ : Bool => ℝ) := fun i s =>
  s false * s true + if i then (s true)^2 else (s false)^2
def polynomialPotential (s : Bool → ℝ) : ℝ :=
  s false * s true + (s false)^2 + (s true)^2
theorem polynomial_exact : ExactPotential polynomialGame polynomialPotential := by
  intro s i a
  cases i <;> simp [polynomialGame, polynomialPotential, Function.update] <;> ring
example : FourCycle polynomialGame :=
  exactPotential_fourCycle polynomialGame polynomialPotential polynomial_exact
example : SimpleFourCycleProperty polynomialGame :=
  (monderer_shapley_characterization polynomialGame).2.2.1.mp
    ⟨polynomialPotential, polynomial_exact⟩
def UnequalAction : Bool → Type := fun i => if i then Fin 3 else Fin 2
instance unequal_fintype (i : Bool) : Fintype (UnequalAction i) := by
  cases i <;> dsimp [UnequalAction] <;> infer_instance
instance unequal_nonempty (i : Bool) : Nonempty (UnequalAction i) := by
  cases i <;> dsimp [UnequalAction] <;> infer_instance
def unequalPotential (s : Profile UnequalAction) : ℝ :=
  (s false).val + (s true).val
def unequalGame : Payoff UnequalAction := fun _ => unequalPotential
example : ∃ s, PureNash unequalGame s := by
  apply fourCycle_exists_pureNash unequalGame
  exact exactPotential_fourCycle unequalGame unequalPotential (fun _ _ _ => rfl)
example : ∃ s : Empty → Bool, PureNash (fun _ _ => (0 : ℝ)) s := by
  apply fourCycle_exists_pureNash
  intro s i
  cases i
example : FourCycle (fun (_ : Bool) (_ : Bool → Unit) => (0 : ℝ)) := by
  intro s i j hij a b
  ring
def unboundedGame : Payoff (fun _ : Unit => ℝ) := fun _ s => s ()
example : ExactPotential unboundedGame (fun s => s ()) := by
  intro s i a
  rfl
end Potential.Examples


