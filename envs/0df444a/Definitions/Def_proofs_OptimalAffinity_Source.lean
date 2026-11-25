-- Prove2me | Definitions.Def_proofs_OptimalAffinity_Source
-- name    : proofs_OptimalAffinity_Source
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T20:52:42.064535+00:00
-- url     : https://prove2.me/theorems/458b51e4-557a-5b14-97aa-47a984fb9b24
-- title:
--   Source
-- statement:
--   Definitions and structural lemmas for Source, from mmislan (mmislan/palomar-p004-optimal-affinity-counterexample; see pinned Apache-2.0 LICENSE and README.md)'s pinned A two-reaction counterexample to the gross-amplification affinity bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Source.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace OptimalAffinity
abbrev Reaction := Fin 2
structure Network where
  xReactant : Reaction → ℕ
  yReactant : Reaction → ℕ
  xProduct : Reaction → ℕ
  yProduct : Reaction → ℕ
  kPlus : Reaction → ℝ
  kMinus : Reaction → ℝ
def forwardFlux (N : Network) (r : Reaction) (x y : ℝ) : ℝ :=
  N.kPlus r * x ^ N.xReactant r * y ^ N.yReactant r
def reverseFlux (N : Network) (r : Reaction) (x y : ℝ) : ℝ :=
  N.kMinus r * x ^ N.xProduct r * y ^ N.yProduct r
def netFlux (N : Network) (r : Reaction) (x y : ℝ) : ℝ :=
  forwardFlux N r x y - reverseFlux N r x y
def netX (N : Network) (r : Reaction) : ℤ :=
  (N.xProduct r : ℤ) - N.xReactant r
def netY (N : Network) (r : Reaction) : ℤ :=
  (N.yProduct r : ℤ) - N.yReactant r
def determinant (N : Network) : ℤ :=
  netX N 0 * netY N 1 - netX N 1 * netY N 0
def alpha (N : Network) : ℕ := N.xReactant 0 + N.xReactant 1
def beta (N : Network) : ℕ := N.xProduct 0 + N.xProduct 1
def yInput (N : Network) : ℕ := N.yReactant 0 + N.yReactant 1
def yOutput (N : Network) : ℕ := N.yProduct 0 + N.yProduct 1
def UnitProductionMode (N : Network) : Prop :=
  netX N 0 + netX N 1 = 1 ∧ netY N 0 + netY N 1 = 0
def DetailedBalanceExists (N : Network) : Prop :=
  ∃ x y : ℝ, 0 < x ∧ 0 < y ∧
    ∀ r : Reaction, forwardFlux N r x y = reverseFlux N r x y
def SourceValid (N : Network) : Prop :=
  (∀ r : Reaction, 0 < N.kPlus r ∧ 0 < N.kMinus r) ∧
  determinant N ≠ 0 ∧
  UnitProductionMode N ∧
  0 < alpha N ∧ alpha N < beta N ∧
  yInput N = yOutput N ∧
  DetailedBalanceExists N
def YSteady (N : Network) (x y : ℝ) : Prop :=
  (netY N 0 : ℝ) * netFlux N 0 x y +
    (netY N 1 : ℝ) * netFlux N 1 x y = 0
def productionCurrent (N : Network) (x y : ℝ) : ℝ := netFlux N 0 x y
def IsUniqueGlobalMaximum (N : Network) (xStar yStar : ℝ) : Prop :=
  0 < xStar ∧ 0 < yStar ∧ YSteady N xStar yStar ∧
  (∀ x y : ℝ, 0 < x → 0 < y → YSteady N x y →
    productionCurrent N x y ≤ productionCurrent N xStar yStar) ∧
  (∀ x y : ℝ, 0 < x → 0 < y → YSteady N x y →
    productionCurrent N x y = productionCurrent N xStar yStar →
    x = xStar ∧ y = yStar)
noncomputable def affinityExp (N : Network) (x y : ℝ) : ℝ :=
  (forwardFlux N 0 x y / reverseFlux N 0 x y) *
  (forwardFlux N 1 x y / reverseFlux N 1 x y)
noncomputable def seedRatio (N : Network) : ℝ := (beta N : ℝ) / alpha N
def HasCatalyticReaction (N : Network) : Prop :=
  ∃ r : Reaction, 0 < N.yReactant r ∧ 0 < N.yProduct r
structure EmbeddingMasses where
  x : ℕ
  y : ℕ
  f1 : ℕ
  w1 : ℕ
  f2 : ℕ
  w2 : ℕ
def PositiveMassConservingEmbedding (m : EmbeddingMasses) : Prop :=
  0 < m.x ∧ 0 < m.y ∧ 0 < m.f1 ∧ 0 < m.w1 ∧ 0 < m.f2 ∧ 0 < m.w2 ∧
  m.f1 + m.x = m.y + m.w1 ∧
  m.f2 + 2 * m.y = 2 * m.x + m.y + m.w2
def oa2x2 : Network where
  xReactant := ![1, 0]
  yReactant := ![0, 2]
  xProduct := ![0, 2]
  yProduct := ![1, 1]
  kPlus := ![3, 7]
  kMinus := ![2, 6]
def oa2x2Masses : EmbeddingMasses where
  x := 1
  y := 1
  f1 := 1
  w1 := 1
  f2 := 2
  w2 := 1
end OptimalAffinity


