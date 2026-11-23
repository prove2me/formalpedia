-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_Bridge
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_Bridge
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:16.188936+00:00
-- url     : https://prove2.me/theorems/d9e24f83-98b2-4e28-9314-74b3746a4261
-- title:
--   Bridge
-- statement:
--   Definitions and structural lemmas for Bridge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/Bridge.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
noncomputable section
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
  {E : Type} [Field E] [NumberField E] [IsCMField E]
structure Reading (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ) where

  Rg : Subring (A c)
  w_mem : ∀ j, d.w j c ∈ Rg
  rd : Rg →+* (Frame X.Ψ r → ℂ)

  WE : AddSubgroup WT
  wL_mem : d.wL ∈ WE
  wt : WE →+ Wt X.Ψ r

  Gen : Set (Frame X.Ψ r)
  Gen_sub : Gen ⊆ X.dom
  Gen_dense : X.dom ⊆ closure Gen
  pt : Frame X.Ψ r → (Ω c →+* ℂ)
  pt_mem : ∀ x ∈ Gen, pt x ∈ PT (Ω := Ω c) sg
  pt_onto : ∀ P ∈ PT (Ω := Ω c) sg, ∃ x ∈ Gen, pt x = P

  w_nz : ∀ x ∈ X.dom, ∃ j, rd ⟨d.w j c, w_mem j⟩ x ≠ 0
  sec : ∀ G (hG : G ∈ WE), ∀ f (hf : f ∈ Rg), f ∈ 𝒜 c G → X.IsSec (wt ⟨G, hG⟩) (rd ⟨f, hf⟩)
  inj : ∀ G, ∀ f (hf : f ∈ Rg), f ∈ 𝒜 c G → (∀ x ∈ X.dom, rd ⟨f, hf⟩ x = 0) → f = 0
  norm : ∀ G (hG : G ∈ WE), ∀ f (hf : f ∈ Rg), f ∈ 𝒜 c G → ∀ x ∈ Gen,
    X.pnorm (wt ⟨G, hG⟩) (rd ⟨f, hf⟩) x = d.nrm c G f (pt x)
  ratio_rd : ∀ G, ∀ f (hf : f ∈ Rg) g (hg : g ∈ Rg), f ∈ 𝒜 c G → g ∈ 𝒜 c G → g ≠ 0 → ∀ x ∈ Gen,
    rd ⟨f, hf⟩ x = pt x (ratio (Ω := Ω c) f g) * rd ⟨g, hg⟩ x

  Gen_inv : ∀ x ∈ Gen, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ Gen ∧ pt (lact γ (rmul x b)) = pt x
  orbit_inj : ∀ x ∈ Gen, ∀ x' ∈ Gen, pt x = pt x' → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x' = lact γ (rmul x b)

  Gen_max : ∀ x ∈ X.dom, ∀ P ∈ PT (Ω := Ω c) sg,
    (∀ G ∈ WE, ∀ f (hf : f ∈ Rg) g (hg : g ∈ Rg), f ∈ 𝒜 c G → g ∈ 𝒜 c G → g ≠ 0 →
      rd ⟨f, hf⟩ x = P (ratio (Ω := Ω c) f g) * rd ⟨g, hg⟩ x) → x ∈ Gen ∧ pt x = P

  bir : ∀ a : Ω c, ∃ (G : WT) (f p : A c), f ∈ Rg ∧ p ∈ Rg ∧ f ∈ 𝒜 c G ∧ p ∈ 𝒜 c G ∧ p ≠ 0 ∧
    p ∈ Algebra.adjoin K (Set.range fun j => d.w j c) ∧ a = ratio (Ω := Ω c) f p

  coordAt : ∀ x ∈ Gen, ∃ (j0 : Fin (d.N + 1)) (jj : Fin (nd X) → Fin (d.N + 1)),
    rd ⟨d.w j0 c, w_mem j0⟩ x ≠ 0 ∧
    (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      rd ⟨d.w (jj k) c, w_mem (jj k)⟩ (cpt X x z) / rd ⟨d.w j0 c, w_mem j0⟩ (cpt X x z) : V (nd X))) 0).det ≠ 0
structure BeData (d : Data K ι Ω WT A) (c : ι) {r : ℕ} {X : FD.Data E r} {sg : K →+* ℂ}
    (R : Reading (𝒜 := 𝒜) d c X sg) where
  k : ℕ
  be : A c
  be_mem : be ∈ R.Rg
  be_in : be ∈ 𝒜 c (k • d.wL)
  be_ne : be ≠ 0
  w_pos : ∀ x ∈ X.dom, 0 < ∑ j, X.pnorm (R.wt ⟨d.wL, R.wL_mem⟩) (R.rd ⟨d.w j c, R.w_mem j⟩) x ^ 2
  be1 : ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (R.wt ⟨k • d.wL, R.WE.nsmul_mem R.wL_mem k⟩) (R.rd ⟨be, be_mem⟩) x ≤
    C * (∑ j, X.pnorm (R.wt ⟨d.wL, R.wL_mem⟩) (R.rd ⟨d.w j c, R.w_mem j⟩) x ^ 2) ^ ((k : ℝ) / 2)
  be2 : ∀ δ : ℝ, 0 < δ → ∃ Cs : Set (Frame X.Ψ r), IsCompact Cs ∧ Cs ⊆ X.dom ∧
    ∀ x ∈ X.dom, δ * (∑ j, X.pnorm (R.wt ⟨d.wL, R.wL_mem⟩) (R.rd ⟨d.w j c, R.w_mem j⟩) x ^ 2) ^ ((k : ℝ) / 2) ≤
      X.pnorm (R.wt ⟨k • d.wL, R.WE.nsmul_mem R.wL_mem k⟩) (R.rd ⟨be, be_mem⟩) x →
      ∃ y ∈ Cs, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul y b)
def SgGeneric {D N : ℕ} (sg : K →+* ℂ) (t : TVar D N → ℂ) : Prop :=
  ∀ Q : MvPolynomial (TVar D N) K, Q ≠ 0 → MvPolynomial.eval₂ sg t Q ≠ 0
def FlatOfAlgStatement : Prop :=
  ∀ (d : Data K ι Ω WT A), d.AxW 𝒜 → ∀ (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ)
    (R : Reading (𝒜 := 𝒜) d c X sg) (Xa : ArchInM X) (hD : nd X = d.D)
    (e : Fin Xa.N ≃ Fin (d.N + 1)) (t : TVar d.D d.N → ℂ) (Bd : BeData (𝒜 := 𝒜) d c R),
    Xa.L = R.wt ⟨d.wL, R.wL_mem⟩ → (∀ k, Xa.w k = R.rd ⟨d.w (e k) c, R.w_mem _⟩) → SgGeneric sg t →
    IntegralStatement (K := K) (ι := ι) (Ω := Ω) (WT := WT) (A := A) (𝒜 := 𝒜) →
    NormStatement (K := K) (ι := ι) (Ω := Ω) (WT := WT) (A := A) (𝒜 := 𝒜) →
    d.S1 → Algebra.IsSeparable (d.KT c) (OmS (Ω c) d.D d.N) → PropDisc X →
    ∃ Fl : FlatM X Xa,
      (∀ x, Fl.w0 x = ∑ j, t (0, j) * R.rd ⟨d.w j c, R.w_mem j⟩ x) ∧
      ∀ i x, Fl.s i x = ∑ j, t ((Fin.cast hD i).succ, j) * R.rd ⟨d.w j c, R.w_mem j⟩ x
def w0R (d : Data K ι Ω WT A) (c : ι) {r : ℕ} {X : FD.Data E r} {sg : K →+* ℂ}
    (R : Reading (𝒜 := 𝒜) d c X sg) (t : TVar d.D d.N → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∑ j, t (0, j) * R.rd ⟨d.w j c, R.w_mem j⟩ x
def sR (d : Data K ι Ω WT A) (c : ι) {r : ℕ} {X : FD.Data E r} {sg : K →+* ℂ}
    (R : Reading (𝒜 := 𝒜) d c X sg) (t : TVar d.D d.N → ℂ) (hD : nd X = d.D) (i : Fin (nd X))
    (x : Frame X.Ψ r) : ℂ :=
  ∑ j, t ((Fin.cast hD i).succ, j) * R.rd ⟨d.w j c, R.w_mem j⟩ x
def FlatHyp (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ)
    (R : Reading (𝒜 := 𝒜) d c X sg) (Xa : ArchInM X) (hD : nd X = d.D)
    (e : Fin Xa.N ≃ Fin (d.N + 1)) (t : TVar d.D d.N → ℂ) : Prop :=
  d.AxW 𝒜 ∧ Xa.L = R.wt ⟨d.wL, R.wL_mem⟩ ∧ (∀ k, Xa.w k = R.rd ⟨d.w (e k) c, R.w_mem _⟩) ∧ SgGeneric sg t ∧
    d.S1 ∧ Algebra.IsSeparable (d.KT c) (OmS (Ω c) d.D d.N) ∧ PropDisc X
def SPointsStatement : Prop :=
  ∀ (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ)
    (R : Reading (𝒜 := 𝒜) d c X sg) (Xa : ArchInM X) (hD : nd X = d.D)
    (e : Fin Xa.N ≃ Fin (d.N + 1)) (t : TVar d.D d.N → ℂ), FlatHyp d c X sg R Xa hD e t →
    IntegralStatement (K := K) (ι := ι) (Ω := Ω) (WT := WT) (A := A) (𝒜 := 𝒜) →
    ∃ (δ : ℕ) (xs : Fin δ → Frame X.Ψ r), (∀ j, xs j ∈ R.Gen) ∧
      (∀ x ∈ X.dom, (∀ i, sR d c R t hD i x = 0) ↔
        ∃ j, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (xs j) b)) ∧
      (∀ j j', ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, xs j' = lact γ (rmul (xs j) b) → j = j') ∧
      ∀ j, w0R d c R t (xs j) ≠ 0
def SCoordStatement : Prop :=
  ∀ (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ)
    (R : Reading (𝒜 := 𝒜) d c X sg) (Xa : ArchInM X) (hD : nd X = d.D)
    (e : Fin Xa.N ≃ Fin (d.N + 1)) (t : TVar d.D d.N → ℂ), FlatHyp d c X sg R Xa hD e t →
    ∀ x ∈ R.Gen, (∀ i, sR d c R t hD i x = 0) → w0R d c R t x ≠ 0 →
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun i =>
        sR d c R t hD i (cpt X x z) / w0R d c R t (cpt X x z) : V (nd X))) 0).det ≠ 0
def WLeStatement : Prop :=
  ∀ (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ)
    (R : Reading (𝒜 := 𝒜) d c X sg) (Xa : ArchInM X) (hD : nd X = d.D)
    (e : Fin Xa.N ≃ Fin (d.N + 1)) (t : TVar d.D d.N → ℂ), FlatHyp d c X sg R Xa hD e t →
    IntegralStatement (K := K) (ι := ι) (Ω := Ω) (WT := WT) (A := A) (𝒜 := 𝒜) →
    ∃ Kc : ℝ, ∀ x ∈ X.dom, ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤
      Kc * (X.pnorm Xa.L (w0R d c R t) x ^ 2 + ∑ i, X.pnorm Xa.L (sR d c R t hD i) x ^ 2)
def WLeSStatement : Prop :=
  ∀ (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ)
    (R : Reading (𝒜 := 𝒜) d c X sg) (Xa : ArchInM X) (hD : nd X = d.D)
    (e : Fin Xa.N ≃ Fin (d.N + 1)) (t : TVar d.D d.N → ℂ), FlatHyp d c X sg R Xa hD e t →
    IntegralStatement (K := K) (ι := ι) (Ω := Ω) (WT := WT) (A := A) (𝒜 := 𝒜) →
    NormStatement (K := K) (ι := ι) (Ω := Ω) (WT := WT) (A := A) (𝒜 := 𝒜) → PropDisc X →
    BeData (𝒜 := 𝒜) d c R →
    ∀ U : Set (Frame X.Ψ r), IsOpen U →
      (∀ x ∈ X.dom, (∀ i, sR d c R t hD i x = 0) → x ∈ U) →
      (∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U) →
      ∃ Kc : ℝ, ∀ x ∈ X.dom, x ∉ U →
        ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤ Kc * ∑ i, X.pnorm Xa.L (sR d c R t hD i) x ^ 2
def SSgtLinStatement : Prop :=
  ∀ (r : ℕ) (X : FD.Data E r) (la : Wt X.Ψ r) (c : ℝ) {ι' : Type} (s : Finset ι') (a : ι' → ℂ)
    (P : ι' → Frame X.Ψ r → ℂ), (∀ i ∈ s, P i ∈ X.SSgt la c) →
    (fun x => ∑ i ∈ s, a i * P i x) ∈ X.SSgt la c
end
end ReciprocityTheory.ChartRestriction.G.AR.Up


