-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_QuotientIsHausdorff
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_QuotientIsHausdorff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:53.736806+00:00
-- url     : https://prove2.me/theorems/c909b40a-ba15-4544-8d8e-e49d7d0b824e
-- title:
--   Quotient Is Hausdorff
-- statement:
--   Definitions and structural lemmas for Quotient Is Hausdorff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/QuotientIsHausdorff.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_IsStrictDom
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def PropDisc {r : ℕ} (X : Data E r) : Prop :=
  ∀ x ∈ X.dom, ∀ x' ∈ X.dom, ∃ U ∈ 𝓝 x, ∃ U' ∈ 𝓝 x',
    {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r, lact γ u = rmul u' b}.Finite
def GGConnStatement : Prop := ∀ (r : ℕ) (X : Data E r), IsConnected X.dom
def YConnStatement : Prop := ∀ (r : ℕ) (X : Data E r), ConnectedSpace (Yq X)
def QuotientIsHausdorff : Prop := ∀ (r : ℕ) (X : Data E r), PropDisc X → T2Space (Yq X)
def YSCStatement : Prop := ∀ (r : ℕ) (X : Data E r), SecondCountableTopology (Yq X)
def AtlasStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) [T2Space (Yq X)] [SecondCountableTopology (Yq X)], PropDisc X →
    (∀ γ ∈ X.Γ, X.χ (kapW X) γ = 1) →
    ∃ A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r), Fits X A
def CurvStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) [T2Space (Yq X)] [SecondCountableTopology (Yq X)]
    (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)), Fits X A → ∀ la : Wt X.Ψ r,
    (X.IsDominant la → A.Pos la fun _ => 0) ∧
    (IsStrictDom X la → ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < A.leviAt i (A.ph la i) y ξ)
def LineBundleFirstBound : Prop :=
  ∀ (r : ℕ) (X : Data E r) [T2Space (Yq X)] [SecondCountableTopology (Yq X)]
    (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)), 0 < r → Fits X A → PropDisc X →
    Continuous (la1Y X A) ∧ (∀ y, 0 < la1Y X A y) ∧
      ∀ ε : ℝ, 0 < ε → IsCompact {y | ε ≤ la1Y X A y}
def DecStatement {r : ℕ} (X : Data E r) : Prop :=
  ∀ (la : Wt X.Ψ r) (c : ℝ), ∀ P ∈ X.SSgt la c, ∃ C : ℝ, ∀ x ∈ X.dom,
    X.pnorm la P x ^ 2 ≤ C * Real.exp (-(2 * Real.pi * c) / X.la1 x ^ 2)
def GapStatement {r : ℕ} (X : Data E r) : Prop :=
  ∀ (la : Wt X.Ψ r), ∀ P ∈ X.SSgt la 0, ∃ c : ℝ, 0 < c ∧ P ∈ X.SSgt la c
variable {r : ℕ} (X : Data E r) [T2Space (Yq X)] [SecondCountableTopology (Yq X)]
def cfwY (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)) (ps : Yq X → ℝ) (a : ℝ) : Prop :=
  (∃ C A' : ℝ, ∀ y, ps y ≤ C + A' * Real.log (1 + 1 / la1Y X A y)) ∧
  ∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ C A' : ℝ, ∀ y, ∀ ξ : Fin r → E, X.IsIso ξ →
    (∀ τ, 1 ≤ X.tt ξ (lift X A y) τ) →
    ps y ≤ C + A' * Real.log (1 + 1 / la1Y X A y) -
      8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ (lift X A y) τ
def CfStatement (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)) : Prop :=
  ∀ (G L : Wt X.Ψ r) (N : ℕ) (w : Fin N → X.dom → Yq X → ℂ) (F : X.dom → Yq X → ℂ)
    (ps : Yq X → ℝ) (a η : ℝ),
    (∀ k, A.IsSec L (w k)) → (∀ k, Bdd A L (w k)) → (∀ k, vanY X A L 0 (w k)) →
    (∀ y, ∃ k, w k (A.pick y) y ≠ 0) → 0 < η → 0 ≤ a → A.IsSec G F → cfwY X A ps a →
    ∫⁻ y, ENNReal.ofReal (A.nsq G F y * Real.exp (-ps y) * A.sqn L w y ^ (-η)) ∂A.mu < ⊤ →
    Bdd A G F ∧ vanY X A G 0 F ∧ vanY X A G a F
omit [T2Space (Yq X)] [SecondCountableTopology (Yq X)] in

def CuspInstStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) [T2Space (Yq X)] [SecondCountableTopology (Yq X)]
    (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)), 0 < r → Fits X A → PropDisc X →
    A.mu Set.univ < ⊤ → DecStatement X → GapStatement X → CfStatement X A →
    ∃ C : Cusp A, C.la1 = la1Y X A ∧ C.van = vanY X A ∧ C.kd = 2 * Real.pi ∧ C.cfw = cfwY X A
omit [T2Space (Yq X)] [SecondCountableTopology (Yq X)] in

def FlatStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) [T2Space (Yq X)] [SecondCountableTopology (Yq X)]
    (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)), Fits X A → ∀ (C : Cusp A) (Xa : ArchIn A C),
    ∃ (w0 : X.dom → Yq X → ℂ) (s : Fin (nd X) → X.dom → Yq X → ℂ) (De : MvPolynomial (Fin (nd X)) ℂ)
      (thp : X.dom → Yq X → ℂ) (h1 : A.IsSec Xa.Fp thp) (h2 : Bdd A Xa.Fp thp)
      (h3 : C.van Xa.Fp 0 thp) (h4 : ∃ y, thp (A.pick y) y ≠ 0),
      FlatDatum A C { Xa with thp := thp, thp_sec := h1, thp_bdd := h2, thp_van := h3, thp_ne := h4 }
        w0 s De
end
end ReciprocityTheory.ChartRestriction.G.AR.Inst


