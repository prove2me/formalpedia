-- Prove2me | Definitions.Def_AME125_Defs
-- name    : AME125_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:58:31.001346+00:00
-- url     : https://prove2.me/theorems/862a615a-cbf6-4210-8466-0ff87ee19e14
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Zayn Blore (zblore/fc-ame-12-5; definitions and statement reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and source headers)'s pinned Existence of a twelve-party absolutely maximally entangled state in local dimension five (AME(12,5)) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean

module
public import Mathlib
set_option autoImplicit false
@[expose] public section
@[expose] public section
open scoped BigOperators
namespace OpenQuantumProblem35
abbrev Config (n d : ℕ) := Fin n → Fin d
abbrev StateVector (n d : ℕ) := EuclideanSpace ℂ (Config n d)
abbrev mkStateVector {n d : ℕ} (ψ : Config n d → ℂ) : StateVector n d :=
  WithLp.toLp 2 ψ
instance {n d : ℕ} : CoeFun (StateVector n d) (fun _ => Config n d → ℂ) where
  coe ψ := ψ.ofLp
def IsNormalized {n d : ℕ} (ψ : StateVector n d) : Prop :=
  ‖ψ‖ = 1
def permuteConfig {n d : ℕ} (π : Equiv.Perm (Fin n)) (x : Config n d) : Config n d :=
  fun i => x (π i)
def permuteState {n d : ℕ} (π : Equiv.Perm (Fin n)) (ψ : StateVector n d) : StateVector n d :=
  mkStateVector fun x => ψ (permuteConfig π x)
def combineFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) : Config n d :=
  fun i =>
    if hi : i.1 < m then
      x ⟨i.1, hi⟩
    else
      y ⟨i.1 - m, by
        have him : m ≤ i.1 := Nat.le_of_not_gt hi
        exact Nat.sub_lt_sub_right him i.2⟩
def leftIndex {m n : ℕ} (hm : m ≤ n) (i : Fin m) : Fin n :=
  ⟨i.1, lt_of_lt_of_le i.2 hm⟩
def rightIndex {m n : ℕ} (hm : m ≤ n) (i : Fin (n - m)) : Fin n :=
  ⟨m + i.1, by omega⟩
noncomputable def reducedDensityFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n) (ψ : StateVector n d) :
    Matrix (Config m d) (Config m d) ℂ :=
  fun x y =>
    ∑ z : Config (n - m) d,
      ψ (combineFirst (n := n) (d := d) m hm x z) *
        star (ψ (combineFirst (n := n) (d := d) m hm y z))
noncomputable def maximallyMixed (m d : ℕ) :
    Matrix (Config m d) (Config m d) ℂ :=
  ((Fintype.card (Config m d) : ℂ)⁻¹) •
    (1 : Matrix (Config m d) (Config m d) ℂ)
def HasMaximallyMixedFirstReduction {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (ψ : StateVector n d) : Prop :=
  reducedDensityFirst (n := n) (d := d) m hm ψ = maximallyMixed m d
def IsAME {n d : ℕ} (ψ : StateVector n d) : Prop :=
  IsNormalized ψ ∧
    ∀ π : Equiv.Perm (Fin n),
      HasMaximallyMixedFirstReduction (n := n) (d := d)
        (n / 2) (Nat.div_le_self n 2) (permuteState π ψ)
def ExistsAME (n d : ℕ) : Prop :=
  ∃ ψ : StateVector n d, IsAME (n := n) (d := d) ψ
noncomputable def uniformCoeff (d : ℕ) : ℂ :=
  (Real.sqrt ((d : ℝ)⁻¹) : ℂ)
def IsConstantConfig {n d : ℕ} (x : Config n d) : Prop :=
  ∀ i j, x i = x j
instance {n d : ℕ} : DecidablePred (@IsConstantConfig n d) := by
  intro x
  unfold IsConstantConfig
  infer_instance
def constantConfig {m d : ℕ} (a : Fin d) : Config m d :=
  fun _ => a
noncomputable def diagonalState (n d : ℕ) : StateVector n d :=
  mkStateVector fun x => if IsConstantConfig x then uniformCoeff d else 0
noncomputable abbrev bellState (d : ℕ) : StateVector 2 d :=
  diagonalState 2 d
noncomputable abbrev ghzState (d : ℕ) : StateVector 3 d :=
  diagonalState 3 d
noncomputable abbrev ghzState4 (d : ℕ) : StateVector 4 d :=
  diagonalState 4 d
def constantCompletion {n d : ℕ} (x : Config 1 d) : Config (n - 1) d :=
  constantConfig (m := n - 1) (d := d) (x 0)
end OpenQuantumProblem35


