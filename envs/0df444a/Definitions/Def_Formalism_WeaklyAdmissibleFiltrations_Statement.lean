-- Prove2me | Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
-- name    : Formalism_WeaklyAdmissibleFiltrations_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:51.848841+00:00
-- url     : https://prove2.me/theorems/9c862895-a49c-49b4-821a-d0da6407e817
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/Statement.lean

import Mathlib
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.WeaklyAdmissibleFiltrations
open Module TensorProduct
structure FilPhi (LL : Type) [Field LL] (D : Type) [AddCommGroup D] [Module LL D]
    (n : ℕ) (Emb : Type) [Fintype Emb] where
  letter : Emb → ZMod n
  e : ℕ
  fiber : ∀ i : ZMod n, (Finset.univ.filter fun τ => letter τ = i).card = e
  Dl : ZMod n → Submodule LL D
  internal : DirectSum.IsInternal Dl
  φ : D ≃ₗ[LL] D
  φ_Dl : ∀ i, (Dl i).map (φ : D →ₗ[LL] D) = Dl (i + 1)
  Fil : Emb → ℤ → Submodule LL D
  Fil_le : ∀ τ a, Fil τ a ≤ Dl (letter τ)
  Fil_anti : ∀ τ a, Fil τ (a + 1) ≤ Fil τ a
  lo : ℤ
  hi : ℤ
  lo_le : lo ≤ hi
  Fil_lo : ∀ τ a, a ≤ lo → Fil τ a = Dl (letter τ)
  Fil_hi : ∀ τ a, hi ≤ a → Fil τ a = ⊥
namespace FilPhi
variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb] (F : FilPhi LL D n Emb)
def IsJump (τ : Emb) (a : ℤ) : Prop := F.Fil τ (a + 1) ≠ F.Fil τ a
def JumpsIn (τ : Emb) (S : Set ℤ) : Prop := ∀ a, F.IsJump τ a → a ∈ S
def mult (D' : Submodule LL D) (τ : Emb) (a : ℤ) : ℤ :=
  (finrank LL ↥(F.Fil τ a ⊓ D') : ℤ) - (finrank LL ↥(F.Fil τ (a + 1) ⊓ D') : ℤ)
def tHw (D' : Submodule LL D) (l h : ℤ) : ℤ :=
  ∑ τ, ∑ a ∈ Finset.Ico l h, a * F.mult D' τ a
def tH (D' : Submodule LL D) : ℤ := F.tHw D' F.lo F.hi
def IsSub (D' : Submodule LL D) : Prop :=
  (∀ x ∈ D', F.φ x ∈ D') ∧ D' = ⨆ i, (D' ⊓ F.Dl i)
def φres (D' : Submodule LL D) (h : ∀ x ∈ D', F.φ x ∈ D') : ↥D' →ₗ[LL] ↥D' :=
  (F.φ : D →ₗ[LL] D).restrict h
def NewtonAbove (v : AddValuation LL (WithTop ℚ)) (D' : Submodule LL D)
    (h : ∀ x ∈ D', F.φ x ∈ D') : Prop :=
  (((F.tH D' : ℚ)) : WithTop ℚ) ≤ F.e • v (LinearMap.det (F.φres D' h))
def WeaklyAdmissible (v : AddValuation LL (WithTop ℚ)) : Prop :=
  (((F.tH ⊤ : ℚ)) : WithTop ℚ) = F.e • v (LinearMap.det (F.φ : D →ₗ[LL] D)) ∧
    ∀ D' : Submodule LL D, ∀ h : F.IsSub D', F.NewtonAbove v D' h.1
end FilPhi
namespace FilPhi
variable {LL : Type} [Field LL] {D D' : Type} [AddCommGroup D] [Module LL D] [AddCommGroup D']
  [Module LL D'] {n : ℕ} {Emb : Type} [Fintype Emb]
structure Iso (F : FilPhi LL D n Emb) (F' : FilPhi LL D' n Emb) where
  e : D ≃ₗ[LL] D'
  letter : ∀ τ, F.letter τ = F'.letter τ
  Dl : ∀ i, (F.Dl i).map (e : D →ₗ[LL] D') = F'.Dl i
  φ : ∀ x, e (F.φ x) = F'.φ (e x)
  Fil : ∀ τ a, (F.Fil τ a).map (e : D →ₗ[LL] D') = F'.Fil τ a
end FilPhi
structure PeriodData (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] where
  p : ℕ
  hp : p.Prime
  finK₀ : FiniteDimensional Qp K₀
  finK : FiniteDimensional Qp K
  σ : K₀ →ₐ[Qp] K₀
  σ_bij : Function.Bijective σ
  actB : G →* (B ≃ₐ[K₀] B)
  invB : ∀ b : B, (∀ g, actB g b = b) → ∃ c : K₀, algebraMap K₀ B c = b
  φ : B →ₐ[Qp] B
  φ_inj : Function.Injective φ
  φ_K₀ : ∀ c : K₀, φ (algebraMap K₀ B c) = algebraMap K₀ B (σ c)
  φ_comm : ∀ g b, φ (actB g b) = actB g (φ b)
  actdR : G →* (BdR ≃ₐ[K] BdR)
  invdR : ∀ b : BdR, (∀ g, actdR g b = b) → ∃ c : K, algebraMap K BdR c = b
  ι : B →ₐ[K₀] BdR
  ι_inj : Function.Injective ι
  ι_comm : ∀ g b, ι (actB g b) = actdR g (ι b)
  Fil : ℤ → Submodule K BdR
  Fil_anti : ∀ a, Fil (a + 1) ≤ Fil a
  one_mem : (1 : BdR) ∈ Fil 0
  Fil_mul : ∀ a b x y, x ∈ Fil a → y ∈ Fil b → x * y ∈ Fil (a + b)
  Fil_exh : ∀ x, ∃ a, x ∈ Fil a
  Fil_sep : ∀ x, (∀ a, x ∈ Fil a) → x = 0
  Fil_G : ∀ g a x, x ∈ Fil a → actdR g x ∈ Fil a
  χ : G →* Qpˣ
  t : B
  t_unit : IsUnit t
  t_act : ∀ g, actB g t = ((χ g : Qpˣ) : Qp) • t
  t_φ : φ t = (p : Qp) • t
  mem_filtration_one : ι t ∈ Fil 1
  not_mem_filtration_two : ι t ∉ Fil 2
  fund : ∀ b : B, φ b = b → ι b ∈ Fil 0 → ∃ c : Qp, algebraMap Qp B c = b
section Galois
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)
def actVB (g : G) : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B :=
  AlgebraTensorModule.map (ρ g) (((PD.actB g).toAlgHom.toLinearMap).restrictScalars Qp)
def actVdR (g : G) : V ⊗[Qp] BdR →ₗ[LL] V ⊗[Qp] BdR :=
  AlgebraTensorModule.map (ρ g) (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp)
def Dcris : Submodule LL (V ⊗[Qp] B) :=
  ⨅ g : G, LinearMap.ker (actVB PD ρ g - LinearMap.id)
def DdR : Submodule LL (V ⊗[Qp] BdR) :=
  ⨅ g : G, LinearMap.ker (actVdR PD ρ g - LinearMap.id)
def mulVB (c : K₀) : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp (algebraMap K₀ B c))
def mulVdR (c : K) : V ⊗[Qp] BdR →ₗ[LL] V ⊗[Qp] BdR :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp (algebraMap K BdR c))
def DcrisL (τ₀ : K₀ →ₐ[Qp] LL) : Submodule LL (V ⊗[Qp] B) :=
  Dcris PD ρ ⊓ ⨅ c : K₀, LinearMap.ker (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c - τ₀ c • LinearMap.id)
def DdRE (τ : K →ₐ[Qp] LL) : Submodule LL (V ⊗[Qp] BdR) :=
  DdR PD ρ ⊓ ⨅ c : K, LinearMap.ker (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c - τ c • LinearMap.id)
def FilV (a : ℤ) : Submodule LL (V ⊗[Qp] BdR) :=
  LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
    ((PD.Fil a).restrictScalars Qp).subtype)
def FildR (τ : K →ₐ[Qp] LL) (a : ℤ) : Submodule LL (V ⊗[Qp] BdR) :=
  DdRE PD ρ τ ⊓ FilV PD (LL := LL) (V := V) a
def IsJumpV (τ : K →ₐ[Qp] LL) (a : ℤ) : Prop := FildR PD ρ τ (a + 1) ≠ FildR PD ρ τ a
def JumpsInV (τ : K →ₐ[Qp] LL) (S : Set ℤ) : Prop := ∀ a, IsJumpV PD ρ τ a → a ∈ S
def ιV : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] BdR :=
  AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (PD.ι.toLinearMap.restrictScalars Qp)
def FilCris (a : ℤ) : Submodule LL (V ⊗[Qp] B) :=
  Dcris PD ρ ⊓ (FilV PD (LL := LL) (V := V) a).comap (ιV PD (LL := LL) (V := V))
def φVB : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B :=
  AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) PD.φ.toLinearMap
def IsCrys : Prop := finrank LL ↥(Dcris PD ρ) = finrank Qp K₀ * finrank LL V
variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
def continuousCocycles : Submodule LL (G → V) where
  carrier := {c | Continuous c ∧ ∀ g h, c (g * h) = c g + ρ g (c h)}
  zero_mem' := ⟨continuous_const, fun g h => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨ha.add hb, fun g h => ?_⟩
    simp only [Pi.add_apply, ha', hb', map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨ha.const_smul c, fun g h => ?_⟩
    simp only [Pi.smul_apply, ha', map_smul, smul_add]
def cob : V →ₗ[LL] (G → V) := LinearMap.pi fun g => ρ g - LinearMap.id
def B1 : Submodule LL (G → V) := LinearMap.range (cob ρ)
def finiteCocycles : Submodule LL (G → V) where
  carrier := {c | c ∈ continuousCocycles ρ ∧ ∃ x : V ⊗[Qp] B, ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, 0, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, x, hx⟩ ⟨hb, y, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, x + y, fun g => ?_⟩
    simp only [Pi.add_apply, add_tmul, hx, hy, map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, x, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, c • x, fun g => ?_⟩
    simp only [Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl
end Galois
section Lattice
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    (ρ : Representation LL G V)
structure Lattice where
  T : Submodule O V
  stable : ∀ g, ∀ x ∈ T, ρ g x ∈ T
  fg : T.FG
  free : Module.Free O T
  span : Submodule.span LL (T : Set V) = ⊤
variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
variable {ρ}
def latticeCocycles (L : Lattice (O := O) ρ) : Submodule O (G → V) :=
  (continuousCocycles ρ).restrictScalars O ⊓ Submodule.pi Set.univ (fun _ => L.T)
def latticeCoboundaries (L : Lattice (O := O) ρ) : Submodule O (G → V) :=
  L.T.map ((cob ρ).restrictScalars O)
abbrev LatticeCohomology (L : Lattice (O := O) ρ) : Type := ↥(latticeCocycles L) ⧸ (latticeCoboundaries L).comap (latticeCocycles L).subtype
def latticeFiniteCocycles (L : Lattice (O := O) ρ) : Submodule O (G → V) :=
  latticeCocycles L ⊓ (finiteCocycles PD ρ).restrictScalars O
def latticeFiniteCohomology (L : Lattice (O := O) ρ) : Submodule O (LatticeCohomology L) :=
  ((latticeFiniteCocycles PD L).comap (latticeCocycles L).subtype).map (Submodule.mkQ _)
section Map
variable {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
structure LatHom (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') where
  f : V →ₗ[LL] V'
  equiv : ∀ g x, f (ρ g x) = ρ' g (f x)
  cont : Continuous f
  T_le : ∀ x ∈ L.T, f x ∈ L'.T
variable {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L')
def LatHom.post : (G → V) →ₗ[O] (G → V') := LinearMap.compLeft (F.f.restrictScalars O) G
def LatHom.ImF : Submodule O (G → V') := (latticeFiniteCocycles PD L).map F.post ⊔ latticeCoboundaries L'
def LatHom.col : ℕ∞ :=
  Module.length O (↥(latticeFiniteCocycles PD L') ⧸ (F.ImF PD).comap (latticeFiniteCocycles PD L').subtype)
def LatHom.LiftF (e : ℕ) : Prop :=
  ∀ c ∈ latticeFiniteCocycles PD L', ((PD.p : O) ^ e) • c ∈ F.ImF PD
theorem LatHom.post_Z1T (c : G → V) (hc : c ∈ latticeCocycles L) : F.post c ∈ latticeCocycles L' := by
  obtain ⟨hc1, hc2⟩ := Submodule.mem_inf.mp hc
  have hz : Continuous c ∧ ∀ g h, c (g * h) = c g + ρ g (c h) :=
    (Submodule.restrictScalars_mem _ _ _).mp hc1
  have hT : ∀ g, c g ∈ L.T := fun g => (Submodule.mem_pi.mp hc2) g (Set.mem_univ g)
  have hp : F.post c = fun g => F.f (c g) := rfl
  refine Submodule.mem_inf.mpr ⟨(Submodule.restrictScalars_mem _ _ _).mpr ?_,
    Submodule.mem_pi.mpr fun g _ => ?_⟩
  · show Continuous (F.post c) ∧ ∀ g h, F.post c (g * h) = F.post c g + ρ' g (F.post c h)
    rw [hp]
    refine ⟨F.cont.comp hz.1, fun g h => ?_⟩
    show F.f (c (g * h)) = F.f (c g) + ρ' g (F.f (c h))
    rw [hz.2, map_add, F.equiv]
  · rw [hp]
    exact F.T_le _ (hT g)
theorem LatHom.post_B1T (c : G → V) (hc : c ∈ latticeCoboundaries L) : F.post c ∈ latticeCoboundaries L' := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hc
  refine Submodule.mem_map.mpr ⟨F.f x, F.T_le x hx, ?_⟩
  funext g
  show ρ' g (F.f x) - F.f x = F.f (ρ g x - x)
  rw [map_sub, F.equiv]
def LatHom.H1map : LatticeCohomology L →ₗ[O] LatticeCohomology L' :=
  Submodule.mapQ _ _ (F.post.restrict fun c hc => F.post_Z1T c hc) (fun c hc => F.post_B1T c hc)
def LatHom.Onto : Prop := ∀ y ∈ L'.T, ∃ x ∈ L.T, F.f x = y
end Map
end Lattice
section Rational
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)
def H0V : Submodule LL V := ⨅ g : G, LinearMap.ker (ρ g - LinearMap.id)
variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
abbrev H1V : Type := ↥(continuousCocycles ρ) ⧸ (B1 ρ).comap (continuousCocycles ρ).subtype
abbrev FiniteCohomology : Type := ↥(finiteCocycles PD ρ) ⧸ (B1 ρ).comap (finiteCocycles PD ρ).subtype
end Rational
section AutomorphicFormsHyp
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    (LL : Type) [Field LL] [Algebra Qp LL]
def FontaineLe : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V),
    finrank LL ↥(Dcris PD ρ) ≤ finrank Qp K₀ * finrank LL V
variable [TopologicalSpace G]
def Splits [Fintype (K →ₐ[Qp] LL)] : Prop :=
  FiniteDimensional Qp LL ∧ Fintype.card (K →ₐ[Qp] LL) = finrank Qp K
def BlochKatoDim [TopologicalSpace LL] [Fintype (K →ₐ[Qp] LL)] : Prop :=
  Splits LL (K := K) (Qp := Qp) →
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] [TopologicalSpace V] [IsModuleTopology LL V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul LL V] (ρ : Representation LL G V),
    (∀ x, Continuous fun g => ρ g x) → IsCrys PD ρ →
    (finrank LL (FiniteCohomology PD ρ) : ℤ) = finrank LL ↥(H0V ρ) +
      ∑ τ : K →ₐ[Qp] LL, ((finrank LL ↥(DdRE PD ρ τ) : ℤ) - finrank LL ↥(FildR PD ρ τ 0))
end AutomorphicFormsHyp
section WachLink
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V}
    [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
def WachLink (L : Lattice (O := O) ρ) {A D : Type} [CommRing A] [Algebra O A] [AddCommGroup D]
    [Module A D] [Module O D] [IsScalarTower O A D] {Bw : Formalism.CoboundaryTransfers.Base O A} {M : ℕ}
    (W : Formalism.CoboundaryTransfers.WachMod Bw M D) (cl : W.Z1 →ₗ[O] LatticeCohomology L) : Prop :=
  Formalism.CoboundaryTransfers.HerrIso W cl ∧ Formalism.CoboundaryTransfers.HfIsZf W cl (latticeFiniteCohomology PD L)
def GoodCoeffs [TopologicalSpace LL] [Fintype (K →ₐ[Qp] LL)] : Prop :=
  Splits LL (K := K) (Qp := Qp) ∧ IsModuleTopology LL V ∧
    ∃ hO : IsDomain O, @IsDiscreteValuationRing O _ hO ∧ IsFractionRing O LL
def BergerWach [TopologicalSpace LL] [Fintype (K →ₐ[Qp] LL)] (L : Lattice (O := O) ρ) (M h : ℕ) :
    Prop :=
  Function.Bijective (algebraMap K₀ K) → PD.p ≠ 2 →
    GoodCoeffs (K := K) (Qp := Qp) (LL := LL) (O := O) (V := V) → IsCrys PD ρ →
    (∀ τ : K →ₐ[Qp] LL, JumpsInV PD ρ τ (Set.Icc (-(M : ℤ)) h)) →
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (D : Type) (_ : AddCommGroup D)
      (_ : Module A D) (_ : Module O D) (_ : IsScalarTower O A D)
      (Bw : Formalism.CoboundaryTransfers.Base O A) (W : Formalism.CoboundaryTransfers.WachMod Bw M D) (cl : W.Z1 →ₗ[O] LatticeCohomology L),
      Bw.p = PD.p ∧ Bw.QLin ∧ Bw.GammaModX ∧ Bw.PhiX (PD.p - 1) ∧ W.HeightLower h ∧
        WachLink PD L W cl
def BergerWachSES [TopologicalSpace LL] [Fintype (K →ₐ[Qp] LL)] {V' : Type} [AddCommGroup V']
    [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] [Module O V'] [IsScalarTower O LL V']
    {ρ' : Representation LL G V'} [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L') (M h : ℕ) : Prop :=
  Function.Bijective (algebraMap K₀ K) → PD.p ≠ 2 →
    GoodCoeffs (K := K) (Qp := Qp) (LL := LL) (O := O) (V := V) → IsModuleTopology LL V' →
    IsCrys PD ρ → IsCrys PD ρ' → F.Onto →
    (∀ τ : K →ₐ[Qp] LL, JumpsInV PD ρ τ (Set.Icc (-(M : ℤ)) h)) →
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (D₀ D₁ D₂ : Type)
      (_ : AddCommGroup D₀) (_ : Module A D₀) (_ : Module O D₀) (_ : IsScalarTower O A D₀)
      (_ : AddCommGroup D₁) (_ : Module A D₁) (_ : Module O D₁) (_ : IsScalarTower O A D₁)
      (_ : AddCommGroup D₂) (_ : Module A D₂) (_ : Module O D₂) (_ : IsScalarTower O A D₂)
      (Bw : Formalism.CoboundaryTransfers.Base O A) (W₀ : Formalism.CoboundaryTransfers.WachMod Bw M D₀) (W₁ : Formalism.CoboundaryTransfers.WachMod Bw M D₁)
      (W₂ : Formalism.CoboundaryTransfers.WachMod Bw M D₂) (S : Formalism.CoboundaryTransfers.SES W₀ W₁ W₂)
      (cl₁ : W₁.Z1 →ₗ[O] LatticeCohomology L) (cl₂ : W₂.Z1 →ₗ[O] LatticeCohomology L'),
      Bw.p = PD.p ∧ Bw.QLin ∧ Bw.GammaModX ∧ Bw.PhiX (PD.p - 1) ∧ W₁.HeightLower h ∧
        W₂.HeightLower h ∧ WachLink PD L W₁ cl₁ ∧ WachLink PD L' W₂ cl₂ ∧ S.Surj ∧
        ∀ (pr : W₁.Z1) (pr' : W₂.Z1), (pr' : D₂ × D₂) = S.π.f2 pr → F.H1map (cl₁ pr) = cl₂ pr'
end WachLink
section CF
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {n : ℕ} [NeZero n]
def IsDcrisFilPhi {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (emb : ZMod n → (K₀ →ₐ[Qp] LL))
    (F : FilPhi LL ↥(Dcris PD ρ) n (ZMod n)) : Prop :=
  (∀ τ, F.letter τ = τ) ∧
    (∀ i, F.Dl i = (DcrisL PD ρ (emb i)).comap (Dcris PD ρ).subtype) ∧
    (∀ x, ((F.φ x : ↥(Dcris PD ρ)) : V ⊗[Qp] B) = φVB PD (LL := LL) (V := V) (x : V ⊗[Qp] B)) ∧
    (∀ τ a, F.Fil τ a = (FilCris PD ρ a ⊓ DcrisL PD ρ (emb τ)).comap (Dcris PD ρ).subtype)
variable (LL)
def Letters (v : AddValuation LL (WithTop ℚ)) (emb : ZMod n → (K₀ →ₐ[Qp] LL)) : Prop :=
  Function.Bijective (algebraMap K₀ K) ∧ FiniteDimensional Qp LL ∧ n = finrank Qp K₀ ∧
    Function.Bijective emb ∧ (∀ i, (emb (i + 1)).comp PD.σ = emb i) ∧ v (PD.p : LL) = 1
def FontaineWA (v : AddValuation LL (WithTop ℚ)) (emb : ZMod n → (K₀ →ₐ[Qp] LL)) : Prop :=
  Letters PD LL v emb →
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V), IsCrys PD ρ →
    ∃ F : FilPhi LL ↥(Dcris PD ρ) n (ZMod n), IsDcrisFilPhi PD ρ emb F ∧ F.WeaklyAdmissible v
def ColmezFontaine [TopologicalSpace G] [TopologicalSpace LL] (v : AddValuation LL (WithTop ℚ))
    (emb : ZMod n → (K₀ →ₐ[Qp] LL)) : Prop :=
  Letters PD LL v emb →
  ∀ (D : Type) [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
    (F : FilPhi LL D n (ZMod n)), (∀ τ, F.letter τ = τ) → F.WeaklyAdmissible v →
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module LL V) (_ : Module Qp V)
      (_ : IsScalarTower Qp LL V) (_ : FiniteDimensional LL V) (_ : TopologicalSpace V)
      (_ : IsModuleTopology LL V)
      (ρ : Representation LL G V) (F' : FilPhi LL ↥(Dcris PD ρ) n (ZMod n)),
      (∀ x, Continuous fun g => ρ g x) ∧ IsCrys PD ρ ∧ IsDcrisFilPhi PD ρ emb F' ∧
        Nonempty (FilPhi.Iso F F')
end CF
section Ops
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}
def multV (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) : ℤ :=
  (finrank LL ↥(FildR PD ρ τ a) : ℤ) - finrank LL ↥(FildR PD ρ τ (a + 1))
def lenOl : ℕ∞ := Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O)})
def IsSESLat {V₀ : Type} [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]
    [Module O V₀] [IsScalarTower O LL V₀] {ρ₀ : Representation LL G V₀}
    [TopologicalSpace V₀] [TopologicalSpace V] [TopologicalSpace V']
    {L₀ : Lattice (O := O) ρ₀} {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'}
    (ι : LatHom L₀ L) (π : LatHom L L') : Prop :=
  Function.Injective ι.f ∧ Function.Surjective π.f ∧ π.Onto ∧
    (∀ x, π.f x = 0 ↔ ∃ y, ι.f y = x) ∧ (∀ y, ι.f y ∈ L.T → y ∈ L₀.T)
def charRep (χ : G →* LLˣ) : Representation LL G LL where
  toFun g := ((χ g : LLˣ) : LL) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_comm]
def IsTwist (χ : G →* LLˣ) (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') : Prop :=
  ∃ e : V ≃ₗ[LL] V', (∀ g x, ρ' g (e x) = ((χ g : LLˣ) : LL) • e (ρ g x)) ∧
    L.T.map ((e : V →ₗ[LL] V').restrictScalars O) = L'.T
def IsDualLat (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (P : V →ₗ[LL] V' →ₗ[LL] LL) :
    Prop :=
  (∀ g x y, P (ρ g x) (ρ' g y) = P x y) ∧ (∀ x, (∀ y, P x y = 0) → x = 0) ∧
    (∀ y, (∀ x, P x y = 0) → y = 0) ∧ finrank LL V = finrank LL V' ∧
    ∀ y, y ∈ L'.T ↔ ∀ x ∈ L.T, ∃ a : O, P x y = algebraMap O LL a
variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
def Z1ur (ρ : Representation LL G V) (I : Subgroup G) : Submodule LL (G → V) where
  carrier := {c | c ∈ continuousCocycles ρ ∧ ∃ x : V, ∀ g ∈ I, c g = ρ g x - x}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, 0, fun g _ => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, x, hx⟩ ⟨hb, y, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, x + y, fun g hg => ?_⟩
    simp only [Pi.add_apply, hx g hg, hy g hg, map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, x, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, c • x, fun g hg => ?_⟩
    simp only [Pi.smul_apply, hx g hg, map_smul, smul_sub]
variable {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L')
theorem LatHom.post_Z1fT (c : G → V) (hc : c ∈ latticeFiniteCocycles PD L) : F.post c ∈ latticeFiniteCocycles PD L' := by
  obtain ⟨hcT, hcf⟩ := Submodule.mem_inf.mp hc
  refine Submodule.mem_inf.mpr ⟨F.post_Z1T c hcT, ?_⟩
  have hf : c ∈ continuousCocycles ρ ∧ ∃ x : V ⊗[Qp] B, ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x := hcf
  obtain ⟨-, x, hx⟩ := hf
  have hz' : F.post c ∈ continuousCocycles ρ' :=
    (Submodule.restrictScalars_mem _ _ _).mp (Submodule.mem_inf.mp (F.post_Z1T c hcT)).1
  let M : V ⊗[Qp] B →ₗ[LL] V' ⊗[Qp] B := AlgebraTensorModule.map F.f LinearMap.id
  have hcomm : ∀ g y, M (actVB PD ρ g y) = actVB PD ρ' g (M y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, M, AlgebraTensorModule.map_tmul, F.equiv]
    | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]
  show F.post c ∈ continuousCocycles ρ' ∧ ∃ x : V' ⊗[Qp] B, ∀ g, F.post c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ' g x - x
  refine ⟨hz', M x, fun g => ?_⟩
  have h := congrArg M (hx g)
  rw [map_sub, hcomm] at h
  rw [← h]
  simp [M, AlgebraTensorModule.map_tmul, LatHom.post]
theorem LatHom.H1map_H1fT (x : LatticeCohomology L) (hx : x ∈ latticeFiniteCohomology PD L) : F.H1map x ∈ latticeFiniteCohomology PD L' := by
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hx
  refine Submodule.mem_map.mpr ⟨⟨F.post c, F.post_Z1T (c : G → V) c.2⟩,
    Submodule.mem_comap.mpr (F.post_Z1fT PD (c : G → V) (Submodule.mem_comap.mp hc)), ?_⟩
  rfl
def LatHom.H1fmap : ↥(latticeFiniteCohomology PD L) →ₗ[O] ↥(latticeFiniteCohomology PD L') :=
  F.H1map.restrict fun x hx => F.H1map_H1fT PD x hx
def LatHom.ColLe (b : ℚ) : Prop :=
  ∃ m k : ℕ, F.col PD = m ∧ lenOl PD (O := O) = k ∧ (m : ℚ) ≤ b * k
end Ops
section Published2
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul LL V]
def FiniteCohomologyGeneratorsBound [TopologicalSpace LL] [Fintype (K →ₐ[Qp] LL)] (L : Lattice (O := O) ρ) : Prop :=
  GoodCoeffs (K := K) (Qp := Qp) (LL := LL) (O := O) (V := V) → IsCrys PD ρ →
    (∀ x, Continuous fun g => ρ g x) →
    ∃ s : Finset (LatticeCohomology L), Submodule.span O (s : Set (LatticeCohomology L)) = latticeFiniteCohomology PD L ∧
      (s.card : ℤ) ≤ finrank LL ↥(H0V ρ) + finrank LL V +
        ∑ τ : K →ₐ[Qp] LL, ((finrank LL ↥(DdRE PD ρ τ) : ℤ) - finrank LL ↥(FildR PD ρ τ 0))
def UnrTriv [TopologicalSpace LL] [IsTopologicalRing LL] (I : Subgroup G) : Prop :=
  finiteCocycles PD (1 : Representation LL G LL) = Z1ur (1 : Representation LL G LL) I
end Published2
end Formalism.WeaklyAdmissibleFiltrations


