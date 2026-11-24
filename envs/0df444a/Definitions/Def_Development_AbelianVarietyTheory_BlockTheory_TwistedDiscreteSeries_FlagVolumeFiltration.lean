-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FlagVolumeFiltration
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FlagVolumeFiltration
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:02:13.100409+00:00
-- url     : https://prove2.me/theorems/91f416f6-93f6-4593-b87d-b35d9a65fae5
-- title:
--   Flag Volume Filtration
-- statement:
--   Definitions and structural lemmas for Flag Volume Filtration, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/FlagVolumeFiltration.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Theorems.Thm_GlobalTheory_LatPair_inX_mem_gluedLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise NNReal ENNReal
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair
section Objects
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ}
variable (k n) in

def flagSub (c i : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) where
  carrier := {y | ∀ l : Fin c, i ≤ l.val → y (Sum.inr l) = 0}
  zero_mem' _ _ := rfl
  add_mem' h h' l hl := by simp [h l hl, h' l hl]
  smul_mem' s y h l hl := by simp [h l hl]
def latStep (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) := L ⊓ flagSub k n c i
def interX (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : Submodule 𝒪[k] (n → k) := L.comap (inX k n c)
def qStep (q : Unif k) (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : ℕ) : Set (n ⊕ Fin c → k) :=
  {y | q.inv • y ∈ latStep L i}
def IsDepthOne (q : Unif k) (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : Prop :=
  ∀ i : Fin c, (fun y : n ⊕ Fin c → k => y (Sum.inr i)) '' (latStep L (i.val + 1) : Set (n ⊕ Fin c → k)) =
    {t : k | (q.1 : k) * t ∈ 𝒪[k]}
def flagIn (c i : ℕ) (y : n ⊕ Fin i → k) : n ⊕ Fin c → k :=
  Sum.elim (fun r => y (Sum.inl r)) fun l => if h : l.val < i then y (Sum.inr ⟨l.val, h⟩) else 0
def refLat (c : ℕ) (L : Submodule 𝒪[k] (n → k)) : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
  L.map (inX k n c) ⊔ Submodule.span 𝒪[k] {y | ∃ i, 1 ≤ i ∧ i ≤ c ∧ y = avec k n c i}
variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
def stabN (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : Subgroup (GL (n ⊕ Fin c) k) := N k n c 1 ⊓ latStab L
def InCoset (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) (h₀ h : GL (n ⊕ Fin c) k) : Prop :=
  ∃ r ∈ R k n c 1, ∃ κ ∈ latStab L₀, h = r * h₀ * κ
def IsTheta {M' M : Type} [AddCommGroup M'] [Module ℂ M'] [AddCommGroup M] [Module ℂ M] (μ : kˣ →* ℂˣ)
    (π' : Representation ℂ (GL n' k) M') (π : Representation ℂ (GL n k) M)
    (θ : M' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] M) : Prop :=
  ∀ (g : GL n' k) (h : GL n k) (v : M') (Ψ Ψ' : SB (Matrix n n' k)), Ψ'.1 = om μ g h Ψ.1 →
    θ (π' g v) Ψ' = π h (θ v Ψ)
def DiesOnRam (P : Pair k n') (Ξ : Matrix n n' k → ℂ) : Prop :=
  ∃ hΞ : Ξ ∈ SB (Matrix n n' k),
    ∀ (M' M : Type) [AddCommGroup M'] [Module ℂ M'] [AddCommGroup M] [Module ℂ M] (μ : kˣ →* ℂˣ), IsUnram μ →
      ∀ (π' : Representation ℂ (GL n' k) M') (π : Representation ℂ (GL n k) M)
        (θ : M' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] M), IsTheta μ π' π θ →
        ∀ φ ∈ EqForm π', φ ∈ Mram k n' M' → θ (φ P) ⟨Ξ, hΞ⟩ = 0
variable [MeasurableSpace k] [BorelSpace k]
def volStep (ν : Measure k) (q : Unif k) (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : ℕ) : ℝ≥0∞ :=
  (Measure.pi fun _ : n ⊕ Fin i => ν) {y | flagIn c i y ∈ qStep q L i}
def volAll (ν : Measure k) (q : Unif k) (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : ℝ :=
  ∏ i ∈ Finset.Icc 1 c, (volStep ν q L i).toReal
def volStabN (ν : Measure k) (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : ℝ≥0∞ :=
  volN ν n c 1 {u | (u : GL (n ⊕ Fin c) k) ∈ latStab L}
def unf (ψ : AddChar k Circle) (ν : Measure k) (q : Unif k) (P : Pair k n')
    (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : Matrix n n' k → ℂ :=
  opE ψ ν 1 (latInd (gluedS q (c + 1) P.ker P.vec) L)
end Objects
section Statements
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (q : Unif k)
def DatumTranslate : Prop :=
  ∀ (μ : kˣ →* ℂˣ) (P : Pair k n') (L'₀ : Submodule 𝒪[k] (n' ⊕ Fin (c + 1) → k)) [L'₀.IsLattice k]
    (L₀ L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k] (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k),
    h' • L'₀ = gluedS q (c + 1) P.ker P.vec → h • L₀ = L → ∀ x,
      latInd (gluedS q (c + 1) P.ker P.vec) L x =
        (((μ (GeneralLinearGroup.det h'))⁻¹ : ℂˣ) : ℂ) * (μ (GeneralLinearGroup.det h) : ℂ) *
          ((nabs k (GeneralLinearGroup.det h') ^ (-((Fintype.card n : ℝ) + c) / 2) : ℝ) : ℂ) *
          ((nabs k (GeneralLinearGroup.det h) ^ (((Fintype.card n' : ℝ) + c + 1) / 2) : ℝ) : ℂ) *
          om μ h' h (latInd L'₀ L₀) x
def StabGlued : Prop :=
  ∀ P : Pair k n,
    (∀ i j : Fin c, j.val = i.val + 1 →
      (fun u : GL (n ⊕ Fin c) k => u.val (Sum.inr i) (Sum.inr j)) ''
        (stabN (gluedS q c P.ker P.vec) : Set (GL (n ⊕ Fin c) k)) = (𝒪[k] : Set k)) ∧
    R k n c 1 ⊓ latStab (gluedS q c P.ker P.vec) =
      stabN (gluedS q c P.ker P.vec) ⊔ (MulAction.stabilizer (GL n k) P).map (embX c) ∧
    Disjoint (stabN (gluedS q c P.ker P.vec)) ((MulAction.stabilizer (GL n k) P).map (embX c)) ∧
    ∀ g ∈ MulAction.stabilizer (GL n k) P, ∀ u ∈ stabN (gluedS q c P.ker P.vec),
      embX c g * u * (embX c g)⁻¹ ∈ stabN (gluedS q c P.ker P.vec)
def NormalForm : Prop :=
  ∀ (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L.IsLattice k], IsDepthOne q L →
    ∃ η : n → k, (∃ u ∈ N k n c 1, L = u • gluedS q c (interX L) η) ∧
      ∀ η' : n → k, (∃ u ∈ N k n c 1, L = u • gluedS q c (interX L) η') → η' - η ∈ interX L
def OneOrbit : Prop :=
  (∀ (L₁ L₂ : Submodule 𝒪[k] (n → k)) (f₁ f₂ : n → k), IsGlue L₁ f₁ → IsGlue L₂ f₂ →
    ∃ g : GL n k, g • L₁ = L₂ ∧ g • f₁ - f₂ ∈ L₂) ∧
  ∀ (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k] (Q : Pair k n) (h₀ : GL (n ⊕ Fin c) k),
    h₀ • L₀ = gluedS q c Q.ker Q.vec → ∀ h : GL (n ⊕ Fin c) k,
      (∃ u ∈ N k n c 1, ∃ (L'' : Submodule 𝒪[k] (n → k)) (f'' : n → k), IsGlue L'' f'' ∧
        h • L₀ = u • gluedS q c L'' f'') ↔ InCoset L₀ h₀ h
def StabCoords : Prop :=
  ∀ Q : Pair k n, Set.BijOn
    (fun (u : GL (n ⊕ Fin c) k) (i : Fin c) => u.val *ᵥ avec k n c (i.val + 1) - avec k n c (i.val + 1))
    (stabN (gluedS q c Q.ker Q.vec) : Set (GL (n ⊕ Fin c) k))
    {y | ∀ i : Fin c, (i.val = 0 → y i = 0) ∧ (1 ≤ i.val → y i ∈ qStep q (gluedS q c Q.ker Q.vec) i.val)}
def DetValuations : Prop :=
  ∀ (P : Pair k n') (Q : Pair k n) (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k),
    h' • refLat (c + 1) P.lat = gluedS q (c + 1) P.ker P.vec → h • refLat c Q.lat = gluedS q c Q.ker Q.vec →
      valuation k (h'.val.det) = valuation k (q.inv ^ c) ∧ valuation k (h.val.det) = valuation k (q.inv ^ (c - 1)) ∧
      ∀ μ : kˣ →* ℂˣ, IsUnram μ →
        μ (GeneralLinearGroup.det h') * (μ (GeneralLinearGroup.det h))⁻¹ = (μ q.unit)⁻¹
variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
def Vanishing : Prop :=
  ∀ (P : Pair k n') (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L.IsLattice k], ¬ IsDepthOne q L → unf ψ ν q P L = 0
open Classical in

def NormalValue : Prop :=
  ∀ (P : Pair k n') (L'' : Submodule 𝒪[k] (n → k)) [L''.IsLattice k] (η : n → k),
    (∀ i ∈ Finset.Icc 1 c, volStep ν q (gluedS q c L'' η) i ≠ 0 ∧ volStep ν q (gluedS q c L'' η) i ≠ ∞) ∧
    (∀ x : Matrix n n' k, unf ψ ν q P (gluedS q c L'' η) x = (volAll ν q (gluedS q c L'' η) : ℂ) *
      if (∀ y ∈ P.ker, x *ᵥ y ∈ L'') ∧ x *ᵥ P.vec - η ∈ L'' then 1 else 0) ∧
    (q.1 • η ∉ L'' → unf ψ ν q P (gluedS q c L'' η) = 0)
def SplitCase : Prop :=
  ∀ (P : Pair k n') (L'' : Submodule 𝒪[k] (n → k)) [L''.IsLattice k] (η : n → k), η ∈ L'' →
    (∀ x : Matrix n n' k, unf ψ ν q P (gluedS q c L'' η) x =
      (volAll ν q (gluedS q c L'' η) : ℂ) * latInd P.lat L'' x) ∧
    (∀ g ∈ latStab P.lat, ∀ x : Matrix n n' k,
      unf ψ ν q P (gluedS q c L'' η) (x * g.val) = unf ψ ν q P (gluedS q c L'' η) x) ∧
    DiesOnRam P (unf ψ ν q P (gluedS q c L'' η))
def GluedCase : Prop :=
  ∀ (P : Pair k n') (L'' : Submodule 𝒪[k] (n → k)) [L''.IsLattice k] (f'' : n → k), f'' ∉ L'' → q.1 • f'' ∈ L'' →
    ∃ Q : Pair k n, Q.lat = L'' ⊔ Submodule.span 𝒪[k] {f''} ∧ Q.HasVal f'' 1 ∧ Q.ker = L'' ∧
      gluedS q c L'' f'' = gluedS q c Q.ker Q.vec ∧
      ∀ x : Matrix n n' k, unf ψ ν q P (gluedS q c L'' f'') x =
        (volAll ν q (gluedS q c L'' f'') : ℂ) * phiOne P Q x
def OneCoset : Prop :=
  ∀ (P : Pair k n') (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k] (Q : Pair k n) (h₀ : GL (n ⊕ Fin c) k),
    h₀ • L₀ = gluedS q c Q.ker Q.vec → ∀ h : GL (n ⊕ Fin c) k, ¬ InCoset L₀ h₀ h →
      DiesOnRam P (unf ψ ν q P (h • L₀))
def Volumes : Prop :=
  ∀ Q : Pair k n,
    ∏ i ∈ Finset.Ico 1 c, volStep ν q (gluedS q c Q.ker Q.vec) i = volStabN ν (gluedS q c Q.ker Q.vec) ∧
    volStabN ν (gluedS q c Q.ker Q.vec) ≠ 0 ∧ volStabN ν (gluedS q c Q.ker Q.vec) ≠ ∞ ∧
    volAll ν q (gluedS q c Q.ker Q.vec) / (volStabN ν (gluedS q c Q.ker Q.vec)).toReal =
      (volStep ν q (gluedS q c Q.ker Q.vec) c).toReal ∧
    (IsSelfDual ψ ν → ∃ e : ℤ, (volStep ν q (gluedS q c Q.ker Q.vec) c).toReal = (resCard k : ℝ) ^ e)
def CosetWeight : Prop :=
  ∀ (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure]
    (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k], μG (latStab L₀ : Set (GL (n ⊕ Fin c) k)) = 1 →
    ∀ (Q : Pair k n) (h₀ : GL (n ⊕ Fin c) k), h₀ • L₀ = gluedS q c Q.ker Q.vec →
      (μX (MulAction.stabilizer (GL n k) Q : Set (GL n k)) ≠ 0 ∧
        μX (MulAction.stabilizer (GL n k) Q : Set (GL n k)) ≠ ∞) ∧
      ∀ f : GL (n ⊕ Fin c) k → ℂ,
        (∀ (g : GL n k), ∀ u ∈ N k n c 1, ∀ h, ∀ κ ∈ latStab L₀, f (embX c g * u * h * κ) =
          ((nabs k (GeneralLinearGroup.det g) ^ ((c : ℝ) - 1) : ℝ) : ℂ) * f h) →
        (∀ h, ¬ InCoset L₀ h₀ h → f h = 0) → ∀ z : ℂ, IsQuotInt ν μX μG 1 f z ↔
          z = f h₀ / (((volStabN ν (gluedS q c Q.ker Q.vec)).toReal : ℂ) *
            ((μX (MulAction.stabilizer (GL n k) Q : Set (GL n k))).toReal : ℂ))
def UnfoldedIntegral : Prop :=
  ∀ (M' M A : Type) [AddCommGroup M'] [Module ℂ M'] [AddCommGroup M] [Module ℂ M] [AddCommGroup A] [Module ℂ A]
    (μ : kˣ →* ℂˣ), IsUnram μ →
    ∀ (π' : Representation ℂ (GL n' k) M') (π : Representation ℂ (GL n k) M)
      (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (θ : M' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] M), IsTheta μ π' π θ →
    ∀ b : M →ₗ[ℂ] A →ₗ[ℂ] ℂ, IsPos ψ 1 π σ b →
    ∀ (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure]
      (L'₀ : Submodule 𝒪[k] (n' ⊕ Fin (c + 1) → k)) [L'₀.IsLattice k]
      (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k], μG (latStab L₀ : Set (GL (n ⊕ Fin c) k)) = 1 →
    ∀ (F : sphVecs σ L₀) (P : Pair k n') (Q : Pair k n) (h' : GL (n' ⊕ Fin (c + 1)) k) (h₀ : GL (n ⊕ Fin c) k),
      h' • L'₀ = gluedS q (c + 1) P.ker P.vec → h₀ • L₀ = gluedS q c Q.ker Q.vec →
    ∀ φ ∈ EqForm π', φ ∈ Mram k n' M' →
      ∃ (hE : ∀ h : GL (n ⊕ Fin c) k, opE ψ ν 1 (om μ h' h (latInd L'₀ L₀)) ∈ SB (Matrix n n' k))
        (h₁ : phiOne P Q ∈ SB (Matrix n n' k)), ∀ z : ℂ,
        IsQuotInt ν μX μG 1 (fun h => b (θ (φ P) ⟨_, hE h⟩) (σ h F)) z ↔
          z = (μ (GeneralLinearGroup.det h') : ℂ) * (((μ (GeneralLinearGroup.det h₀))⁻¹ : ℂˣ) : ℂ) *
            ((nabs k (GeneralLinearGroup.det h') ^ (((Fintype.card n : ℝ) + c) / 2) : ℝ) : ℂ) *
            ((nabs k (GeneralLinearGroup.det h₀) ^ (-((Fintype.card n' : ℝ) + c + 1) / 2) : ℝ) : ℂ) *
            ((volStep ν q (gluedS q c Q.ker Q.vec) c).toReal : ℂ) /
            ((μX (MulAction.stabilizer (GL n k) Q : Set (GL n k))).toReal : ℂ) *
            b (θ (φ P) ⟨_, h₁⟩) (vecAt σ F (gluedS q c Q.ker Q.vec))
end Statements
def Statement : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (c : ℕ), 1 ≤ c → ∀ (q : Unif k) (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ν : Measure k, ν.IsAddHaarMeasure →
      DatumTranslate k n n' c q ∧ StabGlued k n c q ∧ StabGlued k n' (c + 1) q ∧
      Vanishing k n n' c q ψ ν ∧ NormalForm k n c q ∧ NormalValue k n n' c q ψ ν ∧ SplitCase k n n' c q ψ ν ∧
      GluedCase k n n' c q ψ ν ∧
      (OneOrbit k n c q ∧ OneCoset k n n' c q ψ ν ∧ StabCoords k n c q ∧ Volumes k n c q ψ ν ∧
        CosetWeight k n c q ν) ∧
      UnfoldedIntegral k n n' c q ψ ν ∧ DetValuations k n n' c q
section Examples
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} {c : ℕ}
example (hc : 1 ≤ c) (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (η : n → k) : interX (gluedS q c L η) = L := by
  ext x
  rw [← gluedLat_one]
  exact inX_mem_gluedLat le_rfl hc
example (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : latStep L c = L := by
  refine inf_eq_left.2 fun y _ l hl => ?_
  exact absurd l.2 (by omega)
example (i : ℕ) (y : n ⊕ Fin i → k) : flagIn c i y ∈ flagSub k n c i := fun l hl => by
  simp [flagIn, not_lt.2 hl]
example [Fintype n] [DecidableEq n] (g : GL n k) (x : n → k) : g • x = g.val *ᵥ x := rfl
end Examples
end GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration


