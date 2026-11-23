-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_IsStrictDom
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_IsStrictDom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:25:56.625086+00:00
-- url     : https://prove2.me/theorems/0031601b-a4e0-4dc1-b7d7-99759adc9138
-- title:
--   Is Strict Dom
-- statement:
--   Definitions and structural lemmas for Is Strict Dom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/IsStrictDom.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_BasePsiLeviLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y MeasureTheory Topology
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def Rel (X : Data E r) (x x' : X.dom) : Prop :=
  ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, (x' : Frame X.Ψ r) = lact γ (rmul (x : Frame X.Ψ r) b)
def Yq (X : Data E r) : Type := Quot (Rel X)
instance instTopYq (X : Data E r) : TopologicalSpace (Yq X) :=
  inferInstanceAs (TopologicalSpace (Quot (Rel X)))
instance instMeasYq (X : Data E r) : MeasurableSpace (Yq X) := borel (Yq X)
instance instBorelYq (X : Data E r) : BorelSpace (Yq X) := ⟨rfl⟩
def q (X : Data E r) : X.dom → Yq X := Quot.mk _
abbrev Ent (X : Data E r) : Type := X.Ψ × {p : Fin r × Fin r // p.2 < p.1}
def nd (X : Data E r) : ℕ := Fintype.card (Ent X)
def nmat (X : Data E r) (z : V (nd X)) : Frame X.Ψ r := fun τ a b =>
  if h : b < a then z ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, b), h⟩⟩) else if a = b then 1 else 0
def cpt (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) : Frame X.Ψ r := rmul x0 (nmat X z)
def kapW (X : Data E r) : Wt X.Ψ r := fun _ a => 2 * (a : ℤ) - ((r : ℤ) - 1)
def IsStrictDom (X : Data E r) (la : Wt X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, (∀ i j : Fin r, i < j → (j : ℕ) < X.p0 → la τ j < la τ i) ∧
    (∀ i j : Fin r, X.p0 ≤ (i : ℕ) → i < j → la τ j < la τ i) ∧
    (∀ i j : Fin r, (i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → la τ i < la τ j)
variable (X : Data E r) [T2Space (Yq X)] [SecondCountableTopology (Yq X)]
def secOf (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)) (P : Frame X.Ψ r → ℂ) :
    X.dom → Yq X → ℂ :=
  fun i y => P (cpt X i.1 (A.chart i y))
def lift (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)) (y : Yq X) : Frame X.Ψ r :=
  cpt X (A.pick y).1 (A.chart (A.pick y) y)
def la1Y (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)) (y : Yq X) : ℝ := X.la1 (lift X A y)
def vanY (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)) (la : Wt X.Ψ r) (c : ℝ)
    (s : X.dom → Yq X → ℂ) : Prop :=
  ∃ P ∈ X.SSgt la c, ∀ i y, y ∈ (A.chart i).source → s i y = secOf X A P i y
def Fits (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)) : Prop :=
  (∀ i : X.dom, q X i ∈ (A.chart i).source ∧ A.chart i (q X i) = 0 ∧
    ∀ z ∈ (A.chart i).target, ∃ h : cpt X i.1 z ∈ X.dom, (A.chart i).symm z = q X ⟨_, h⟩) ∧
  A.kap = kapW X ∧
  (∀ la P, X.IsSec la P → A.IsSec la (secOf X A P)) ∧
  (∀ la s, A.IsSec la s → ∃ P, X.IsSec la P ∧ ∀ i y, y ∈ (A.chart i).source → s i y = secOf X A P i y) ∧
  ∀ la P, X.IsSec la P → ∀ x : X.dom, A.nsq la (secOf X A P) (q X x) = X.pnorm la P x ^ 2
end
end ReciprocityTheory.ChartRestriction.G.AR.Inst


