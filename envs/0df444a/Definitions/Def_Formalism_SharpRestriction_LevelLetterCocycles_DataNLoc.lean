-- Prove2me | Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
-- name    : Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:11.926471+00:00
-- url     : https://prove2.me/theorems/b88b9095-932c-418f-b098-a59624c88648
-- title:
--   Data NLoc
-- statement:
--   Definitions and structural lemmas for Data NLoc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/DataNLoc.lean

import Mathlib
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementPC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions
open Formalism.WeaklyAdmissibleFiltrations PowerSeries TensorProduct
structure LocLat (G : Type) [Group G] [TopologicalSpace G] (Qp LL O : Type) [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] where
  V : Type
  [acg : AddCommGroup V]
  [modLL : Module LL V]
  [modQp : Module Qp V]
  [towQp : IsScalarTower Qp LL V]
  [modO : Module O V]
  [towO : IsScalarTower O LL V]
  [top : TopologicalSpace V]
  [cadd : ContinuousAdd V]
  [csmul : ContinuousConstSMul LL V]
  [mtop : IsModuleTopology LL V]
  [fdim : FiniteDimensional LL V]
  ρ : Representation LL G V

  cont : ∀ x : V, Continuous fun g => ρ g x
  L : Lattice (O := O) ρ
attribute [instance] LocLat.acg LocLat.modLL LocLat.modQp LocLat.towQp LocLat.top LocLat.cadd LocLat.csmul
  LocLat.mtop LocLat.fdim
attribute [instance high] LocLat.modO LocLat.towO
instance (priority := high) LocLat.modFun {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type}
    [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) {X : Type} : Module O (X → T.V) :=
  Pi.module _ _ _
instance (priority := high) LocLat.modSubFun {G : Type} [Group G] [TopologicalSpace G]
    {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
    [TopologicalSpace LL] (T : LocLat G Qp LL O) {X : Type} (S : Submodule O (X → T.V)) :
    Module O ↥S :=
  Submodule.module S
instance (priority := high) LocLat.modT {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (T : LocLat G Qp LL O) :
    Module O ↥T.L.T :=
  Submodule.module _
abbrev LetA (O : Type) [CommRing O] (n : ℕ) : Type := ZMod n → PowerSeries O
section Rings
variable {O : Type} [CommRing O] {n : ℕ}
def letE (i : ZMod n) : LetA O n := Pi.single i 1
def letπ : LetA O n := fun _ => PowerSeries.X
def letφ (φ₀ : PowerSeries O →ₐ[O] PowerSeries O) : LetA O n →ₐ[O] LetA O n :=
  AlgHom.pi fun i => φ₀.comp (Pi.evalAlgHom O (fun _ : ZMod n => PowerSeries O) (i - 1))
def letγ (g₀ : PowerSeries O →ₐ[O] PowerSeries O) : LetA O n →ₐ[O] LetA O n :=
  AlgHom.pi fun i => g₀.comp (Pi.evalAlgHom O (fun _ : ZMod n => PowerSeries O) i)
end Rings
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
def resLat {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) (H : Subgroup G) : Lattice (O := O) (T.ρ.comp H.subtype) where
  T := T.L.T
  stable := fun g x hx => T.L.stable g x hx
  fg := T.L.fg
  free := T.L.free
  span := T.L.span
def latId {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) : LatHom T.L T.L where
  f := LinearMap.id
  equiv := fun _ _ => rfl
  cont := continuous_id
  T_le := fun _ hx => hx
def latComp {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {T T' T'' : LocLat G Qp LL O} (g : LatHom T'.L T''.L) (f : LatHom T.L T'.L) :
    LatHom T.L T''.L where
  f := g.f.comp f.f
  equiv := fun a x => by simp [f.equiv, g.equiv]
  cont := g.cont.comp f.cont
  T_le := fun x hx => g.T_le _ (f.T_le x hx)
def latAdd {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {T T' : LocLat G Qp LL O} (f g : LatHom T.L T'.L) : LatHom T.L T'.L where
  f := f.f + g.f
  equiv := fun a x => by simp [f.equiv, g.equiv]
  cont := f.cont.add g.cont
  T_le := fun x hx => T'.L.T.add_mem (f.T_le x hx) (g.T_le x hx)
def latSmul {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) (c : O) : LatHom T.L T.L where
  f := algebraMap O LL c • LinearMap.id
  equiv := fun a x => by simp
  cont := continuous_const_smul _
  T_le := fun x hx => by
    change algebraMap O LL c • x ∈ T.L.T
    rw [algebraMap_smul]
    exact T.L.T.smul_mem c hx
def resHom {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (H : Subgroup G) :
    LatHom (resLat T H) (resLat T' H) where
  f := f.f
  equiv := fun a x => f.equiv a x
  cont := f.cont
  T_le := f.T_le
section Res
variable {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
  (T : LocLat G Qp LL O) (H : Subgroup G)
def resFun : (G → T.V) →ₗ[O] (↥H → T.V) := LinearMap.funLeft O T.V (Subtype.val : ↥H → G)
theorem resFun_Z1T (c : G → T.V) (hc : c ∈ latticeCocycles T.L) : resFun T H c ∈ latticeCocycles (resLat T H) := by
  obtain ⟨⟨hcont, hcoc⟩, hT⟩ := hc
  refine ⟨⟨hcont.comp continuous_subtype_val, fun g h => ?_⟩, ?_⟩
  · simp only [resFun, LinearMap.funLeft_apply, Subgroup.coe_mul, hcoc]
    rfl
  · intro g _
    exact hT (g : G) (Set.mem_univ _)
theorem resFun_B1T (c : G → T.V) (hc : c ∈ latticeCoboundaries T.L) : resFun T H c ∈ latticeCoboundaries (resLat T H) := by
  obtain ⟨x, hx, rfl⟩ := hc
  exact ⟨x, hx, by funext g; rfl⟩
def resH1 : LatticeCohomology T.L →ₗ[O] LatticeCohomology (resLat T H) :=
  Submodule.mapQ _ _
    (((resFun T H).comp (latticeCocycles T.L).subtype).codRestrict (latticeCocycles (resLat T H))
      (fun c => resFun_Z1T T H c c.2))
    (by
      intro c hc
      simp only [Submodule.mem_comap, Submodule.subtype_apply] at hc ⊢
      exact resFun_B1T T H c hc)
end Res
def herrCocycles {O D : Type} [CommRing O] [AddCommGroup D] [Module O D] (γ φ : D →ₗ[O] D) :
    Submodule O (D × D) :=
  LinearMap.ker ((γ - LinearMap.id).coprod (-(φ - LinearMap.id)))
def herrZ1Δ {O D ι : Type} [CommRing O] [AddCommGroup D] [Module O D] (γ φ : D →ₗ[O] D)
    (S : Finset ι) (δ : ι → D →ₗ[O] D) : Submodule O (D × D) :=
  herrCocycles γ φ ⊓ ⨅ d ∈ S, LinearMap.ker (LinearMap.prodMap (δ d) (δ d) - LinearMap.id)
set_option maxHeartbeats 1000000 in

structure LocWach (PD : PeriodData G Qp K₀ K B BdR) (LL O : Type) [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] (v : AddValuation LL (WithTop ℚ)) (n : ℕ) where

  emb : ZMod n → (K₀ →ₐ[Qp] LL)
  emb_bij : Function.Bijective emb
  emb_σ : ∀ i, (emb (i + 1)).comp PD.σ = emb i
  n_eq : n = Module.finrank Qp K₀
  v_l : v (PD.p : LL) = 1

  s : ℕ
  s_pos : 1 ≤ s
  s_two : PD.p = 2 → 2 ≤ s

  φ₀ : PowerSeries O →ₐ[O] PowerSeries O
  q₀ : PowerSeries O
  q₀_def : PowerSeries.X * q₀ = (1 + PowerSeries.X) ^ PD.p - 1
  φ₀_X : φ₀ PowerSeries.X = PowerSeries.X * q₀

  Gam : Type
  [gamGrp : CommGroup Gam]
  resΓ : G →* Gam
  resΓ_onto : Function.Surjective resΓ
  χΓ : Gam →* Oˣ
  χΓ_res : ∀ g, algebraMap O LL (χΓ (resΓ g) : O) = algebraMap Qp LL (PD.χ g : Qp)

  χΓ_inj : Function.Injective χΓ

  γ₀ : Gam →* (PowerSeries O →ₐ[O] PowerSeries O)
  γ₀_comm : ∀ g a, φ₀ (γ₀ g a) = γ₀ g (φ₀ a)
  γ₀_X : ∀ g, PowerSeries.constantCoeff (γ₀ g PowerSeries.X) = 0 ∧
    PowerSeries.coeff 1 (γ₀ g PowerSeries.X) = (χΓ g : O)

  gam : Gam
  gam_gen : v (algebraMap O LL (χΓ gam : O) - 1) = (s : WithTop ℚ)

  DelF : Finset Gam
  DelF_def : ∀ g, g ∈ DelF ↔ ∃ k : ℕ, 0 < k ∧ g ^ k = 1

  gamK : Gam
  gamK_gen : ∀ g : Gam, v (algebraMap O LL ((χΓ gamK : O) ^ DelF.card) - 1) ≤
    v (algebraMap O LL ((χΓ g : O) ^ DelF.card) - 1)

  gamK_eq : (∀ g : Gam, v (algebraMap O LL ((χΓ gam : O) ^ DelF.card) - 1) ≤
    v (algebraMap O LL ((χΓ g : O) ^ DelF.card) - 1)) → gamK = gam
  gamK_eq_one : s = 1 → PD.p ≠ 2 → gamK = gam

  GKs : Subgroup G
  GKs_def : ∀ g, g ∈ GKs ↔ (s : WithTop ℚ) ≤ v (algebraMap Qp LL (PD.χ g : Qp) - 1)

  EE : Type
  [eeRing : CommRing EE]
  [eeAlgA : Algebra (LetA O n) EE]
  [eeAlgO : Algebra O EE]
  [eeTow : IsScalarTower O (LetA O n) EE]
  EE_inj : Function.Injective (algebraMap (LetA O n) EE)
  EE_π : IsUnit (algebraMap (LetA O n) EE letπ)
  EE_complete : IsAdicComplete (Ideal.span {((PD.p : ℕ) : EE)}) EE
  EE_dense : ∀ (x : EE) (k : ℕ), ∃ (a : LetA O n) (m : ℕ),
    x * algebraMap (LetA O n) EE (letπ ^ m) - algebraMap (LetA O n) EE a ∈
      Ideal.span {((PD.p : ℕ) : EE) ^ k}
  EE_sat : ∀ (a : LetA O n) (k : ℕ),
    algebraMap (LetA O n) EE a ∈ Ideal.span {((PD.p : ℕ) : EE) ^ k} →
      ∃ b : LetA O n, a = ((PD.p : ℕ) : LetA O n) ^ k * b
  φE : EE →ₐ[O] EE
  φE_ext : ∀ a, φE (algebraMap (LetA O n) EE a) = algebraMap (LetA O n) EE (letφ φ₀ a)
  γE : Gam →* (EE →ₐ[O] EE)
  γE_ext : ∀ g a, γE g (algebraMap (LetA O n) EE a) = algebraMap (LetA O n) EE (letγ (γ₀ g) a)

  DD : LocLat G Qp LL O → Type
  [ddAcg : ∀ T, AddCommGroup (DD T)]
  [ddModE : ∀ T, Module EE (DD T)]
  [ddModA : ∀ T, Module (LetA O n) (DD T)]
  [ddModO : ∀ T, Module O (DD T)]
  [ddTowA : ∀ T, IsScalarTower (LetA O n) EE (DD T)]
  [ddTowO : ∀ T, IsScalarTower O (LetA O n) (DD T)]
  φD : ∀ T, DD T →ₗ[O] DD T
  φD_smul : ∀ T (e : EE) (x : DD T), φD T (e • x) = φE e • φD T x
  γD : ∀ T, Gam → (DD T →ₗ[O] DD T)
  γD_smul : ∀ T g (e : EE) (x : DD T), γD T g (e • x) = γE g e • γD T g x
  γD_one : ∀ T x, γD T 1 x = x
  γD_mul : ∀ T g h x, γD T (g * h) x = γD T g (γD T h x)
  φγ_comm : ∀ T g x, φD T (γD T g x) = γD T g (φD T x)

  DD_free : ∀ T, Module.Free EE (DD T) ∧ Module.finrank EE (DD T) = Module.finrank O ↥T.L.T

  N : ∀ T, Submodule (LetA O n) (DD T)
  N_base : ∀ T, IsCrys PD T.ρ → IsBaseChange EE ((N T).subtype)

  N_φ : ∀ T, ∀ x ∈ N T, ∃ k : ℕ,
    ((letφ (n := n) φ₀ ^ (s - 1)) (fun _ => q₀)) ^ k • φD T x ∈ N T
  N_φinv : ∀ T, ∀ y ∈ N T, ∃ k : ℕ, ((letφ (n := n) φ₀ ^ (s - 1)) (fun _ => q₀)) ^ k • y ∈
    Submodule.span (LetA O n) (φD T '' (N T : Set (DD T)))

  N_fg : ∀ T, (N T).FG

  N_Γ : ∀ T (g : Gam), ∀ x ∈ N T, γD T g x ∈ N T

  N_π : ∀ T (g : Gam), ∀ x ∈ N T, ∃ y ∈ N T, γD T g x - x = (letπ : LetA O n) • y

  map : ∀ {T T' : LocLat G Qp LL O}, LatHom T.L T'.L → (DD T →ₗ[EE] DD T')
  map_φ : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) x, map f (φD T x) = φD T' (map f x)
  map_γ : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) g x, map f (γD T g x) = γD T' g (map f x)
  map_N : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ x ∈ N T, map f x ∈ N T'
  map_id : ∀ T x, map (latId T) x = x
  map_comp : ∀ {T T' T'' : LocLat G Qp LL O} (g : LatHom T'.L T''.L) (f : LatHom T.L T'.L) x,
    map (latComp g f) x = map g (map f x)

  map_latAdd : ∀ {T T' : LocLat G Qp LL O} (f g : LatHom T.L T'.L) x, map (latAdd f g) x = map f x + map g x
  map_latSmul : ∀ (T : LocLat G Qp LL O) (c : O) x, map (latSmul T c) x = c • x

  cl : ∀ T, ↥(herrCocycles (γD T gam) (φD T)) →ₗ[O]
    LatticeCohomology (resLat T GKs)

  lev : ZMod n → LL → (LetA O n →ₐ[O] PowerSeries LL)
  lev_letter : ∀ i ζ a, a i = 0 → lev i ζ a = 0
  lev_π : ∀ i (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∃ E : PowerSeries LL, PowerSeries.constantCoeff E = 1 ∧
    PowerSeries.derivative LL E = E ∧ 1 + lev i ζ letπ = PowerSeries.C ζ * E

  lev_cont : ∀ (i : ZMod n) (ζ : LL) (a : LetA O n) (k r : ℕ), ∃ m₀ : ℕ, ∀ m ≥ m₀, (r : WithTop ℚ) ≤
    v (PowerSeries.coeff k (lev i ζ a) -
      PowerSeries.coeff k (lev i ζ (fun j => ((PowerSeries.trunc m (a j) : Polynomial O) : PowerSeries O))))

  cmp : ∀ T : LocLat G Qp LL O, ↥(N T) →+ T.V ⊗[Qp] B
  cmp_smul : ∀ (T : LocLat G Qp LL O) (c : O) (x : ↥(N T)), cmp T (c • x) = algebraMap O LL c • cmp T x
  cmp_π : ∀ (T : LocLat G Qp LL O) (x : ↥(N T)), cmp T ((letπ : LetA O n) • x) = 0
  cmp_mem : ∀ (T : LocLat G Qp LL O) (x : ↥(N T)), cmp T x ∈ Dcris PD T.ρ
  cmp_letter : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (x : ↥(N T)), cmp T ((letE i : LetA O n) • x) ∈ DcrisL PD T.ρ (emb i)

  cmp_map : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ (x : ↥(N T)) (hx : map f (x : DD T) ∈ N T'),
    cmp T' ⟨map f (x : DD T), hx⟩ = AlgebraTensorModule.map f.f (LinearMap.id : B →ₗ[Qp] B) (cmp T x)

  levN : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(N T) →+ (ℤ → T.V ⊗[Qp] BdR)
  levN_supp : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) x, ∃ m : ℤ, ∀ k < m, levN T i ζ x k = 0
  levN_smul : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (a : LetA O n) (x : ↥(N T)) (k : ℤ),
    levN T i ζ (a • x) k = ∑ᶠ j : ℕ, PowerSeries.coeff j (lev i ζ a) • levN T i ζ x (k - j)

  levN_map : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ (i : ZMod n) (ζ : LL) (x : ↥(N T))
    (hx : map f (x : DD T) ∈ N T') (k : ℤ),
    levN T' i ζ ⟨map f (x : DD T), hx⟩ k = AlgebraTensorModule.map f.f (LinearMap.id : BdR →ₗ[Qp] BdR) (levN T i ζ x k)

  clK : ∀ T : LocLat G Qp LL O, ↥(herrZ1Δ (γD T gamK) (φD T) DelF (γD T)) →ₗ[O] LatticeCohomology T.L

  one : LocLat G Qp LL O
  one_triv : ∀ g x, one.ρ g x = x
  one_line : ∃ e : one.V, e ≠ 0 ∧ one.L.T = Submodule.span O {e}
attribute [instance] LocWach.gamGrp LocWach.eeRing LocWach.eeAlgA LocWach.eeAlgO LocWach.eeTow
  LocWach.ddAcg LocWach.ddModE LocWach.ddModA LocWach.ddModO LocWach.ddTowA LocWach.ddTowO
namespace LocWach
variable {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
instance towOE (T : LocLat G Qp LL O) : IsScalarTower O W.EE (W.DD T) :=
  ⟨fun c e x => by
    rw [← algebraMap_smul (LetA O n) c (e • x), ← algebraMap_smul W.EE (algebraMap O (LetA O n) c) (e • x),
      smul_smul, Algebra.smul_def c e, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]⟩
def φA : LetA O n →ₐ[O] LetA O n := letφ W.φ₀
def γA (g : W.Gam) : LetA O n →ₐ[O] LetA O n := letγ (W.γ₀ g)
def q : LetA O n := fun _ => W.q₀
def X : LetA O n := (W.φA ^ (W.s - 1)) letπ
def Q : LetA O n := (W.φA ^ (W.s - 1)) W.q
def lvl (j : ℕ) : LetA O n := (W.φA ^ j) W.q
def Nl (T : LocLat G Qp LL O) (i : ZMod n) : Submodule (LetA O n) (W.DD T) :=
  (W.N T).map ((letE i : LetA O n) • LinearMap.id)
def φpull (T : LocLat G Qp LL O) : Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T)))
def InvN (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) : Prop :=
  ∃ k : ℕ, a ^ k • x ∈ W.N T
def γ (T : LocLat G Qp LL O) : W.DD T →ₗ[O] W.DD T := W.γD T W.gam
def π₀₁ : PowerSeries O :=
  1 - ((PD.p : ℕ) : PowerSeries O) + ∑ δ ∈ W.DelF, W.γ₀ δ (1 + PowerSeries.X)
def π₀ : LetA O n := fun _ => W.π₀₁
def AΔ : Subalgebra O (LetA O n) where
  carrier := {a | ∀ δ ∈ W.DelF, W.γA δ a = a}
  mul_mem' := by
    intro a b ha hb δ hδ
    rw [map_mul, ha δ hδ, hb δ hδ]
  add_mem' := by
    intro a b ha hb δ hδ
    rw [map_add, ha δ hδ, hb δ hδ]
  algebraMap_mem' := by
    intro r δ _
    exact AlgHom.commutes _ r
def NΔ (T : LocLat G Qp LL O) : Submodule O (W.DD T) where
  carrier := {x | x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x}
  zero_mem' := ⟨(W.N T).zero_mem, fun δ _ => map_zero _⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨(W.N T).add_mem ha hb, fun δ hδ => by rw [map_add, ha' δ hδ, hb' δ hδ]⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨?_, fun δ hδ => by rw [map_smul, ha' δ hδ]⟩
    rw [← algebraMap_smul (LetA O n) c a]
    exact (W.N T).smul_mem _ ha
theorem φA_π : W.φA letπ = letπ * W.q := by
  funext i
  simp [φA, letφ, letπ, q, W.φ₀_X]
theorem φA_γA (g : W.Gam) (a : LetA O n) : W.φA (W.γA g a) = W.γA g (W.φA a) := by
  funext i
  simp [φA, γA, letφ, letγ, W.γ₀_comm]
theorem φA_X : W.φA W.X = W.X * W.Q := by
  have h : W.φA * W.φA ^ (W.s - 1) = W.φA ^ (W.s - 1) * W.φA := (pow_mul_comm' _ _).symm
  have := congrArg (fun f : LetA O n →ₐ[O] LetA O n => f letπ) h
  simp only [AlgHom.mul_apply] at this
  rw [X, this, φA_π, map_mul]
  rfl
def base : Formalism.CoboundaryTransfers.Base O (LetA O n) where
  p := PD.p
  hp := PD.hp
  φ := W.φA
  γ := W.γA W.gam
  X := W.X
  Q := W.Q
  comm := fun a => W.φA_γA W.gam a
  φX := ⟨W.Q, W.φA_X⟩
def divisibleCocycles (T : LocLat G Qp LL O) : Submodule O (W.DD T × W.DD T) :=
  herrCocycles (W.γ T) (W.φD T)
def wachCocyclesDelta (T : LocLat G Qp LL O) : Submodule O (W.DD T × W.DD T) :=
  herrZ1Δ (W.γD T W.gamK) (W.φD T) W.DelF (W.γD T)
def ClNat : Prop :=
  ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (pr : ↥(W.divisibleCocycles T)) (pr' : ↥(W.divisibleCocycles T')),
    (pr' : W.DD T' × W.DD T') = (W.map f (pr : W.DD T × W.DD T).1, W.map f (pr : W.DD T × W.DD T).2) →
      (LatHom.H1map (resHom f W.GKs) (W.cl T pr) : LatticeCohomology (resLat T' W.GKs)) = W.cl T' pr'
def ClKNat : Prop :=
  ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (pr : ↥(W.wachCocyclesDelta T)) (pr' : ↥(W.wachCocyclesDelta T')),
    (pr' : W.DD T' × W.DD T') = (W.map f (pr : W.DD T × W.DD T).1, W.map f (pr : W.DD T × W.DD T).2) →
      (LatHom.H1map f (W.clK T pr) : LatticeCohomology T'.L) = W.clK T' pr'
def wachOf (T : LocLat G Qp LL O) (M : ℕ)
    (hX : ∀ x : W.DD T, W.X • x = 0 → x = 0)
    (hQ : Function.Bijective (fun x : W.DD T => W.Q • x))
    (hφN : ∀ x ∈ W.N T, W.Q ^ M • W.φD T x ∈ W.N T)
    (hγN : ∀ x ∈ W.N T, ∃ x' ∈ W.N T, W.γ T x - x = W.X • x')
    (hγQN : ∀ y : W.DD T, W.Q ^ M • y ∈ W.N T →
      ∃ y' : W.DD T, W.Q ^ M • y' ∈ W.N T ∧ W.γ T y - y = W.X • y') :
    Formalism.CoboundaryTransfers.WachMod W.base M (W.DD T) where
  N := W.N T
  φ := W.φD T
  γ := W.γ T
  φ_smul := fun a x => by
    have := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
    rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
    exact this
  γ_smul := fun a x => by
    have := W.γD_smul T W.gam (algebraMap (LetA O n) W.EE a) x
    rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
    exact this
  comm := fun x => W.φγ_comm T W.gam x
  X_inj := hX
  Q_bij := hQ
  φ_N := hφN
  γ_N := hγN
  γ_QN := hγQN
end LocWach
section Fam
namespace Loc
variable (l : ℕ) [Fact l.Prime]
abbrev Om : Type := PadicAlgCl l
abbrev GQ : Type := Om l ≃ₐ[ℚ_[l]] Om l
def MaximalUnramifiedExtension : IntermediateField ℚ_[l] (Om l) :=
  IntermediateField.adjoin ℚ_[l] {x | ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ^ m = 1}
abbrev FinExt : Type := {K : IntermediateField ℚ_[l] (Om l) // FiniteDimensional ℚ_[l] K}
variable {l}
def K0 (K : FinExt l) : IntermediateField ℚ_[l] (Om l) := K.1 ⊓ MaximalUnramifiedExtension l
def GK (K : FinExt l) : Subgroup (GQ l) := K.1.fixingSubgroup
def IK (K : FinExt l) : Subgroup ↥(GK K) :=
  Subgroup.closure {σ | ∀ x : Om l, ‖x‖ ≤ 1 → ‖(σ : GQ l) x - x‖ < 1}
def Ks (K : FinExt l) (s : ℕ) : IntermediateField ℚ_[l] (Om l) :=
  K0 K ⊔ IntermediateField.adjoin ℚ_[l] {x | x ^ (l ^ s) = 1}
def OL (LL : FinExt l) : Subalgebra ℤ_[l] ↥LL.1 := integralClosure ℤ_[l] ↥LL.1
def Good (K : FinExt l) (s : ℕ) (LL : FinExt l) : Prop :=
  1 ≤ s ∧ (l = 2 → 2 ≤ s) ∧ K.1 ≤ Ks K s ∧
    ∀ τ : ↥(Ks K s) →ₐ[ℚ_[l]] Om l, ∀ x, τ x ∈ LL.1
def CaseA (K : FinExt l) (LL : FinExt l) : Prop := K.1 ≤ MaximalUnramifiedExtension l ∧ l ≠ 2 ∧ Good K 1 LL
instance maxUnramifiedAlgebra (K : FinExt l) : Algebra ↥(K0 K) ↥K.1 :=
  (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toAlgebra
instance maxUnramifiedScalarTower (K : FinExt l) : IsScalarTower ℚ_[l] ↥(K0 K) ↥K.1 :=
  IsScalarTower.of_algebraMap_eq fun x => by
    apply Subtype.ext
    rfl
def zlA (LL : FinExt l) (n : ℕ) : PowerSeries ℤ_[l] →+* LetA ↥(OL LL) n :=
  RingHom.pi fun _ => PowerSeries.map (algebraMap ℤ_[l] ↥(OL LL))
end Loc
open Loc
variable {l : ℕ} [Fact l.Prime]
structure LocRings (l : ℕ) [Fact l.Prime] where
  B : Type
  BdR : Type
  [rB : CommRing B]
  [rdR : CommRing BdR]
  [aQB : Algebra ℚ_[l] B]
  [aUB : Algebra ↥(MaximalUnramifiedExtension l) B]
  [tUB : IsScalarTower ℚ_[l] ↥(MaximalUnramifiedExtension l) B]
  [aOdR : Algebra (Om l) BdR]
  [aQdR : Algebra ℚ_[l] BdR]
  [tQdR : IsScalarTower ℚ_[l] (Om l) BdR]
attribute [instance] LocRings.rB LocRings.rdR LocRings.aQB LocRings.aUB LocRings.tUB LocRings.aOdR
  LocRings.aQdR LocRings.tQdR
instance maxUnramifiedCrisAlgebra (R : LocRings l) (K : FinExt l) : Algebra ↥(K0 K) R.B :=
  ((algebraMap ↥(MaximalUnramifiedExtension l) R.B).comp
    (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)).toRingHom).toAlgebra
instance maxUnramifiedCrisTower (R : LocRings l) (K : FinExt l) : IsScalarTower ℚ_[l] ↥(K0 K) R.B :=
  IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap ℚ_[l] R.B x = algebraMap ↥(MaximalUnramifiedExtension l) R.B (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) x)
    exact IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) R.B x
instance maxUnramifiedDeRhamTower (R : LocRings l) (K : FinExt l) : IsScalarTower ↥(K0 K) ↥K.1 R.BdR :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
structure LocPrime (l : ℕ) [Fact l.Prime] where
  R : LocRings l
  PD : ∀ K : FinExt l, PeriodData ↥(GK K) ℚ_[l] ↥(K0 K) ↥K.1 R.B R.BdR
  actQ : GQ l →* (R.B ≃ₐ[ℚ_[l]] R.B)
  actQdR : GQ l →* (R.BdR ≃ₐ[ℚ_[l]] R.BdR)
  φB : R.B →ₐ[ℚ_[l]] R.B
  ιB : R.B →ₐ[ℚ_[l]] R.BdR
  tB : R.B
  χQ : GQ l →* ℚ_[l]ˣ
  PD_p : ∀ K : FinExt l, (PD K).p = l
  PD_actB : ∀ (K : FinExt l) (g : ↥(GK K)) b, (PD K).actB g b = actQ (g : GQ l) b
  PD_actdR : ∀ (K : FinExt l) (g : ↥(GK K)) b, (PD K).actdR g b = actQdR (g : GQ l) b
  PD_φ : ∀ (K : FinExt l) b, (PD K).φ b = φB b
  PD_ι : ∀ (K : FinExt l) b, (PD K).ι b = ιB b
  period_datum_t_eq : ∀ K : FinExt l, (PD K).t = tB
  PD_χ : ∀ (K : FinExt l) (g : ↥(GK K)), (((PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = χQ (g : GQ l)
  PD_Fil : ∀ (K K' : FinExt l) a, (((PD K).Fil a : Submodule ↥K.1 R.BdR) : Set R.BdR) = ((PD K').Fil a : Set R.BdR)

  actQ_Kur : ∀ (g : GQ l) (c c' : ↥(MaximalUnramifiedExtension l)), g (c : Om l) = (c' : Om l) →
    actQ g (algebraMap ↥(MaximalUnramifiedExtension l) R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) R.B c'
  actQdR_Om : ∀ (g : GQ l) (x : Om l), actQdR g (algebraMap (Om l) R.BdR x) = algebraMap (Om l) R.BdR (g x)

  PD_σ : ∀ (K : FinExt l) (x : ↥(K0 K)), ‖((x : ↥(K0 K)) : Om l)‖ ≤ 1 →
    ‖((((PD K).σ x : ↥(K0 K))) : Om l) - ((x : ↥(K0 K)) : Om l) ^ l‖ < 1

  χQ_cyc : ∀ (g : GQ l) (m : ℕ) (ζ : Om l), ζ ^ (l ^ m) = 1 →
    ∃ a : ℕ, ‖(χQ g : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ∧ g ζ = ζ ^ a

  ζQ : ℕ → Om l
  ζQ_zero : ζQ 0 = 1
  ζQ_succ : ∀ m, ζQ (m + 1) ^ l = ζQ m
  ζQ_one : ζQ 1 ≠ 1

  v : ∀ LL : FinExt l, AddValuation ↥LL.1 (WithTop ℚ)
  v_l : ∀ LL : FinExt l, v LL (l : ↥LL.1) = 1
  v_O : ∀ (LL : FinExt l) (x : ↥LL.1), 0 ≤ v LL x ↔ x ∈ OL LL
abbrev LocTheory : Type 1 := ∀ (l : ℕ) [Fact l.Prime], LocPrime l
end Fam
section Bridge
open Loc
variable {l : ℕ} [Fact l.Prime]
structure LocBridge (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω]
    (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] where
  Kw : FinExt l
  j : Ω →+* Om l
  j_E : ∀ x : E, j (algebraMap E Ω x) ∈ Kw.1
  j_dense : (Kw.1 : Set (Om l)) ⊆ closure (Set.range fun x : E => j (algebraMap E Ω x))
  e : ↥Gw ≃* ↥(GK Kw)
  e_cont : Continuous e
  e_symm_cont : Continuous e.symm
  e_comm : ∀ (g : ↥Gw) (x : Ω), ((e g : ↥(GK Kw)) : GQ l) (j x) = j ((g : Ω ≃ₐ[E] Ω) x)
  LL : FinExt l

  LL_split : ∀ (τ : ↥Kw.1 →ₐ[ℚ_[l]] Om l) (x : ↥Kw.1), τ x ∈ LL.1
  eO : O ≃+* ↥(OL LL)

  eO_alg : ∀ z : ℤ_[l], eO (algebraMap ℤ_[l] O z) = algebraMap ℤ_[l] ↥(OL LL) z
  eO_cont : Continuous eO
  eO_symm_cont : Continuous eO.symm
end Bridge
section PullPD
variable {G H : Type} [Group G] [Group H] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
def pullPD (PD : PeriodData G Qp K₀ K B BdR) (f : H →* G) (hf : Function.Surjective f) :
    PeriodData H Qp K₀ K B BdR where
  p := PD.p
  hp := PD.hp
  finK₀ := PD.finK₀
  finK := PD.finK
  σ := PD.σ
  σ_bij := PD.σ_bij
  actB := PD.actB.comp f
  invB := fun b hb => PD.invB b fun g => by
    obtain ⟨h, rfl⟩ := hf g
    exact hb h
  φ := PD.φ
  φ_inj := PD.φ_inj
  φ_K₀ := PD.φ_K₀
  φ_comm := fun h b => PD.φ_comm (f h) b
  actdR := PD.actdR.comp f
  invdR := fun b hb => PD.invdR b fun g => by
    obtain ⟨h, rfl⟩ := hf g
    exact hb h
  ι := PD.ι
  ι_inj := PD.ι_inj
  ι_comm := fun h b => PD.ι_comm (f h) b
  Fil := PD.Fil
  Fil_anti := PD.Fil_anti
  one_mem := PD.one_mem
  Fil_mul := PD.Fil_mul
  Fil_exh := PD.Fil_exh
  Fil_sep := PD.Fil_sep
  Fil_G := fun h a x hx => PD.Fil_G (f h) a x hx
  χ := PD.χ.comp f
  t := PD.t
  t_unit := PD.t_unit
  t_act := fun h => PD.t_act (f h)
  t_φ := PD.t_φ
  mem_filtration_one := PD.mem_filtration_one
  not_mem_filtration_two := PD.not_mem_filtration_two
  fund := PD.fund
end PullPD
section PC
open Loc
variable {l : ℕ} [Fact l.Prime]
def GKin {K K' : FinExt l} (_h : K.1 ≤ K'.1) : Subgroup ↥(GK K) := (GK K').subgroupOf (GK K)
def GKinEquiv {K K' : FinExt l} (h : K.1 ≤ K'.1) : ↥(GKin h) ≃* ↥(GK K') :=
  Subgroup.subgroupOfEquivOfLe (fun g hg => by
    intro x
    exact hg ⟨x.1, h x.2⟩)
def pc (P : LocPrime l) {K K' : FinExt l} (h : K.1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') :
    PotCrysData ↥(GK K) ℚ_[l] ↥(K0 K) ↥K.1 ↥(K0 K') ↥K'.1 P.R.B P.R.BdR where
  H := GKin h
  normal := hN
  finiteIndex := hF
  PD := P.PD K
  PD' := pullPD (P.PD K') (GKinEquiv h).toMonoidHom (GKinEquiv h).surjective
  actB_eq := fun x b => by
    change (P.PD K').actB (GKinEquiv h x) b = (P.PD K).actB (x : ↥(GK K)) b
    rw [P.PD_actB, P.PD_actB]
    rfl
  actdR_eq := fun x b => by
    change (P.PD K').actdR (GKinEquiv h x) b = (P.PD K).actdR (x : ↥(GK K)) b
    rw [P.PD_actdR, P.PD_actdR]
    rfl
  φ_eq := fun b => by
    change (P.PD K').φ b = (P.PD K).φ b
    rw [P.PD_φ, P.PD_φ]
  ι_eq := fun b => by
    change (P.PD K').ι b = (P.PD K).ι b
    rw [P.PD_ι, P.PD_ι]
  Fil_eq := fun a => P.PD_Fil K' K a
  p_eq := by
    change (P.PD K').p = (P.PD K).p
    rw [P.PD_p, P.PD_p]
  t_eq := by
    change (P.PD K').t = (P.PD K).t
    rw [P.period_datum_t_eq, P.period_datum_t_eq]
  χ_eq := fun x => by
    apply Units.ext
    change (((P.PD K').χ (GKinEquiv h x) : ℚ_[l]ˣ) : ℚ_[l]) = (((P.PD K).χ (x : ↥(GK K)) : ℚ_[l]ˣ) : ℚ_[l])
    rw [P.PD_χ, P.PD_χ]
    rfl
  stableK₀' := hS
end PC
section BridgeDefs
open Loc
variable {l : ℕ} [Fact l.Prime]
theorem GK_le {K K' : FinExt l} (h : K.1 ≤ K'.1) : GK K' ≤ GK K := fun _ hg x => hg ⟨x.1, h x.2⟩
namespace LocBridge
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
def toLL : O →+* ↥Bw.LL.1 := (algebraMap ↥(OL Bw.LL) ↥Bw.LL.1).comp Bw.eO.toRingHom
def rep {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O) :
    Representation ↥Bw.LL.1 ↥(GK Bw.Kw) (Fin m → ↥Bw.LL.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥Bw.LL.1 ≃ₐ[↥Bw.LL.1] _) : _ →* _).comp
    ((Units.coeHom _).comp ((Matrix.GeneralLinearGroup.map Bw.toLL).comp
      (r.comp Bw.e.symm.toMonoidHom)))
def IsCrysW (P : LocPrime l) {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O) : Prop :=
  IsCrys (P.PD Bw.Kw) (Bw.rep r)
def IsJumpW (P : LocPrime l) {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O)
    (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1) (a : ℤ) : Prop :=
  IsJumpV (P.PD Bw.Kw) (Bw.rep r) τ a
def IsdRW (P : LocPrime l) {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O) : Prop :=
  Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r)) = Module.finrank ℚ_[l] ↥Bw.Kw.1 * m
def IsPotCrysW (P : LocPrime l) {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O) : Prop :=
  ∃ (K' : FinExt l) (h : Bw.Kw.1 ≤ K'.1),
    IsCrys (P.PD K') ((Bw.rep r).comp (Subgroup.inclusion (GK_le h)))
end LocBridge
end BridgeDefs
end Formalism.BasicNotions
namespace Formalism.BasicNotions
open Loc NNReal
namespace Loc
variable (l : ℕ) [Fact l.Prime]
theorem OC_l_not_unit : ¬ IsUnit ((l : ℕ) : PadicComplexInt l) := by
  intro h
  have h1 := ((PadicComplexInt.integers l).isUnit_iff_valuation_eq_one).mp h
  have h2 : (PadicComplex.valued l).v
      (algebraMap (PadicComplexInt l) (PadicComplex l) ((l : ℕ) : PadicComplexInt l))
      = 1 / (l : ℝ≥0) := by
    rw [map_natCast]
    exact PadicComplex.valuation_p l
  rw [h1] at h2
  have hl : (2 : ℝ≥0) ≤ (l : ℝ≥0) := by exact_mod_cast (Fact.out : l.Prime).two_le
  have : (1 : ℝ≥0) / (l : ℝ≥0) < 1 := by
    rw [div_lt_one (by positivity)]
    exact lt_of_lt_of_le (by norm_num) hl
  exact absurd h2 (ne_of_gt this)
instance factOC : Fact (¬ IsUnit ((l : ℕ) : PadicComplexInt l)) := ⟨OC_l_not_unit l⟩
abbrev OC : Type := ↥(PadicComplexInt l)
abbrev OCb : Type := PreTilt (OC l) l
abbrev Ainf : Type := WittVector l (OCb l)
instance domOCb : IsDomain (OCb l) :=
  PreTilt.isDomain (PadicComplex l) (PadicComplex.valued l).v (OC l) (PadicComplexInt.integers l) l
abbrev Cb : Type := FractionRing (OCb l)
instance charCb : CharP (Cb l) l := charP_of_injective_algebraMap' (OCb l) l
abbrev WCb : Type := WittVector l (Cb l)
def inclW : Ainf l →+* WCb l := WittVector.map (algebraMap (OCb l) (Cb l))
def autCb (g : OCb l ≃+* OCb l) : Cb l ≃+* Cb l :=
  IsLocalization.ringEquivOfRingEquiv (M := nonZeroDivisors (OCb l)) (T := nonZeroDivisors (OCb l))
    (Cb l) (Cb l) g (MulEquivClass.map_nonZeroDivisors g)
end Loc
structure LocAinf (l : ℕ) [Fact l.Prime] (P : LocPrime l) where

  actC : GQ l →* (PadicComplex l ≃+* PadicComplex l)
  actC_ext : ∀ (g : GQ l) (x : Om l), actC g (x : PadicComplex l) = ((g x : Om l) : PadicComplex l)
  actC_norm : ∀ (g : GQ l) (y : PadicComplex l), ‖actC g y‖ = ‖y‖

  actT : GQ l →* (OCb l ≃+* OCb l)
  actT_coeff : ∀ (g : GQ l) (x : OCb l) (n : ℕ) (y : OC l),
    PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y →
      ∃ y' : OC l, (y' : PadicComplex l) = actC g (y : PadicComplex l) ∧
        PreTilt.coeff n (actT g x) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y'

  ζ : ℕ → OC l
  ζ_zero : ζ 0 = 1
  ζ_succ : ∀ n, ζ (n + 1) ^ l = ζ n
  ζ_one : ζ 1 ≠ 1

  ε : OCb l
  ε_coeff : ∀ n, PreTilt.coeff n ε = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (ζ n)

  ιA : Ainf l →+* P.R.B
  ιA_inj : Function.Injective ιA
  ιA_act : ∀ (g : GQ l) (a : Ainf l),
    ιA (WittVector.map (actT g : OCb l ≃+* OCb l).toRingHom a) = P.actQ g (ιA a)
  ιA_φ : ∀ a : Ainf l, ιA (WittVector.frobenius a) = P.φB (ιA a)

  ζ_eq : ∀ m, ((ζ m : OC l) : PadicComplex l) = ((P.ζQ m : Om l) : PadicComplex l)

  ainf_image_mem_filtration_zero : ∀ (K : FinExt l) (a : Ainf l), P.ιB (ιA a) ∈ (P.PD K).Fil 0
  ainf_image_mem_filtration_one_iff : ∀ (K : FinExt l) (a : Ainf l), P.ιB (ιA a) ∈ (P.PD K).Fil 1 ↔
    ∃ b : Ainf l, a = (∑ i ∈ Finset.range l,
      (WittVector.teichmuller l ((frobeniusEquiv (OCb l) l).symm ε)) ^ i) * b

  ιA_teich : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → ∀ xb : OCb l,
    (∀ k : ℕ, ∃ y : OC l, (y : PadicComplex l) ^ (l ^ k) = ((c : Om l) : PadicComplex l) ∧ y ^ m = 1 ∧
      PreTilt.coeff k xb = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) →
    ιA (WittVector.teichmuller l xb) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c
namespace LocAinf
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
def actW (g : GQ l) : Ainf l →+* Ainf l := WittVector.map (AI.actT g).toRingHom
def actWCb (g : GQ l) : WCb l →+* WCb l := WittVector.map (autCb l (AI.actT g)).toRingHom
def εroot (s : ℕ) : OCb l := ((frobeniusEquiv (OCb l) l).symm)^[s] AI.ε
def μ : Ainf l := WittVector.teichmuller l AI.ε - 1
def ε1 : OCb l := (frobeniusEquiv (OCb l) l).symm AI.ε
def π₁ : Ainf l := WittVector.teichmuller l AI.ε1 - 1
def ξ : Ainf l := ∑ i ∈ Finset.range l, (WittVector.teichmuller l AI.ε1) ^ i
end LocAinf
end Formalism.BasicNotions
namespace Formalism.BasicNotions
open Loc
namespace Loc
variable (l : ℕ) [Fact l.Prime]
def zlW (R : Type) [CommRing R] [CharP R l] : ℤ_[l] →+* WittVector l R :=
  (WittVector.map (ZMod.castHom (dvd_refl l) R)).comp (WittVector.equiv l).symm.toRingHom
instance algZlWCb : Algebra ℤ_[l] (WCb l) := (zlW l (Cb l)).toAlgebra
instance algZlAinf : Algebra ℤ_[l] (Ainf l) := (zlW l (OCb l)).toAlgebra
example : algebraMap ℤ_[l] (WCb l) ((l : ℕ) : ℤ_[l]) = ((l : ℕ) : WCb l) := map_natCast _ _
theorem map_zlW {R S : Type} [CommRing R] [CommRing S] [CharP R l] [CharP S l] (f : R →+* S)
    (x : ℤ_[l]) : WittVector.map f (zlW l R x) = zlW l S x := by
  simp only [zlW, RingHom.comp_apply]
  ext n
  rw [WittVector.map_coeff, WittVector.map_coeff, WittVector.map_coeff]
  exact congrArg (fun φ : ZMod l →+* S => φ (((WittVector.equiv l).symm.toRingHom x).coeff n))
    (RingHom.ext_zmod (f.comp (ZMod.castHom (dvd_refl l) R)) (ZMod.castHom (dvd_refl l) S))
def inclWA : Ainf l →ₐ[ℤ_[l]] WCb l where
  toRingHom := inclW l
  commutes' := fun x => map_zlW l (algebraMap (OCb l) (Cb l)) x
def AinfSub : Subalgebra ℤ_[l] (WCb l) := (inclWA l).range
def mapEquivW {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    WittVector l R ≃+* WittVector l S :=
  RingEquiv.ofRingHom (WittVector.map e.toRingHom) (WittVector.map e.symm.toRingHom)
    (by
      ext x n
      simp [WittVector.map_coeff])
    (by
      ext x n
      simp [WittVector.map_coeff])
def mapAlgEquivW {R S : Type} [CommRing R] [CommRing S] [CharP R l] [CharP S l] (e : R ≃+* S) :
    @AlgEquiv ℤ_[l] (WittVector l R) (WittVector l S) _ _ _ (zlW l R).toAlgebra (zlW l S).toAlgebra :=
  @AlgEquiv.ofRingEquiv ℤ_[l] (WittVector l R) (WittVector l S) _ _ _ (zlW l R).toAlgebra
    (zlW l S).toAlgebra (mapEquivW l e) (fun x => map_zlW l e.toRingHom x)
theorem autCb_alg (g : OCb l ≃+* OCb l) (x : OCb l) :
    autCb l g (algebraMap (OCb l) (Cb l) x) = algebraMap (OCb l) (Cb l) (g x) := by
  unfold autCb
  erw [IsLocalization.ringEquivOfRingEquiv_eq]
theorem autCb_one : autCb l (1 : OCb l ≃+* OCb l) = 1 := by
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors (OCb l))
  ext x
  change autCb l 1 (algebraMap (OCb l) (Cb l) x) = algebraMap (OCb l) (Cb l) x
  rw [autCb_alg]
  rfl
theorem autCb_mul (g h : OCb l ≃+* OCb l) : autCb l (g * h) = autCb l g * autCb l h := by
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors (OCb l))
  ext x
  change autCb l (g * h) (algebraMap (OCb l) (Cb l) x) =
    autCb l g (autCb l h (algebraMap (OCb l) (Cb l) x))
  rw [autCb_alg, autCb_alg, autCb_alg]
  rfl
end Loc
namespace LocAinf
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
def actWHom : GQ l →* (Ainf l ≃ₐ[ℤ_[l]] Ainf l) where
  toFun g := mapAlgEquivW l (AI.actT g)
  map_one' := by
    ext x n
    simp [mapAlgEquivW, mapEquivW, WittVector.map_coeff]
  map_mul' g h := by
    ext x n
    simp [mapAlgEquivW, mapEquivW, WittVector.map_coeff]
def actWCbHom : GQ l →* (WCb l ≃ₐ[ℤ_[l]] WCb l) where
  toFun g := mapAlgEquivW l (autCb l (AI.actT g))
  map_one' := by
    ext x n
    simp [mapAlgEquivW, mapEquivW, WittVector.map_coeff, autCb_one]
  map_mul' g h := by
    ext x n
    simp [mapAlgEquivW, mapEquivW, WittVector.map_coeff, autCb_mul]
end LocAinf
end Formalism.BasicNotions
namespace Formalism.BasicNotions
open Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
def LocLat.actT {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (T : LocLat G Qp LL O) (g : G) :
    ↥T.L.T →ₗ[O] ↥T.L.T :=
  ((T.ρ g).restrictScalars O).restrict (fun x hx => T.L.stable g x hx)
section Generic
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
abbrev TW (R : Type) [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) : Type := R ⊗[O] ↥T.L.T
def TWmap {R : Type} [CommRing R] [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G Qp LL O) :
    TW R T →ₗ[O] TW R T :=
  TensorProduct.map f.toLinearMap LinearMap.id
def TWact {R : Type} [CommRing R] [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (g : G) :
    TW R T →ₗ[O] TW R T :=
  TensorProduct.map f.toLinearMap (T.actT g)
structure EtTie (W : LocWach PD LL O v n) (RA RW : Type) [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] (inclR : RA →ₐ[O] RW) (φR : RW →ₐ[O] RW) (gR : G → (RW →ₐ[O] RW)) (πA : RA) where

  io : LetA O n →ₐ[O] RA
  io_π : io letπ = πA

  ioE : W.EE →ₐ[O] RW
  ioE_ext : ∀ a, ioE (algebraMap (LetA O n) W.EE a) = inclR (io a)

  jD : ∀ T, W.DD T →ₗ[O] TW RW T
  jD_smul : ∀ T (e : W.EE) x, jD T (e • x) = ioE e • jD T x
  jD_φ : ∀ T x, jD T (W.φD T x) = TWmap φR T (jD T x)
  jD_act : ∀ T (g : G) x, jD T (W.γD T (W.resΓ g) x) = TWact (gR g) T g (jD T x)
  jD_inj : ∀ T, Function.Injective (jD T)
  jD_span : ∀ T, Submodule.span RW (Set.range (jD T)) = ⊤

  jD_map : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (x : W.DD T),
    jD T' (W.map f x) = TensorProduct.map (LinearMap.id : RW →ₗ[O] RW)
      ((f.f.restrictScalars O).restrict f.T_le) (jD T x)

  clK_res : W.gamK = W.gam → ∀ T (pr : ↥(W.wachCocyclesDelta T)) (pr' : ↥(W.divisibleCocycles T)),
    (pr' : W.DD T × W.DD T) = (pr : W.DD T × W.DD T) → resH1 T W.GKs (W.clK T pr) = W.cl T pr'

  one_e : ∃ (e : W.DD W.one) (e₀ : ↥W.one.L.T), Submodule.span O {e₀} = ⊤ ∧
    jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧ W.N W.one = Submodule.span (LetA O n) {e}

  cl_def : ∀ T (pr : ↥(W.divisibleCocycles T)) (b : TW RW T),
    TWmap φR T b - b = jD T (pr : W.DD T × W.DD T).1 →
    ∃ c : ↥(latticeCocycles (resLat T W.GKs)), Submodule.Quotient.mk c = W.cl T pr ∧
      ∀ (g : ↥W.GKs) (t : ↥T.L.T), (t : T.V) = (c : ↥W.GKs → T.V) g →
        (W.resΓ (g : G) = 1 → (1 : RW) ⊗ₜ[O] t = -(TWact (gR g) T (g : G) b - b)) ∧
        (W.resΓ (g : G) = W.gam →
          (1 : RW) ⊗ₜ[O] t = jD T (pr : W.DD T × W.DD T).2 - (TWact (gR g) T (g : G) b - b))

  clK_def : (PD.p = 2 → W.DelF = {1}) → ∀ T (pr : ↥(W.wachCocyclesDelta T)) (b : TW RW T),
    TWmap φR T b - b = jD T (pr : W.DD T × W.DD T).1 →
    ∃ c : ↥(latticeCocycles T.L), Submodule.Quotient.mk c = W.clK T pr ∧
      ∀ (g : G) (t : ↥T.L.T), (t : T.V) = (c : G → T.V) g →
        (W.resΓ g ∈ W.DelF → (1 : RW) ⊗ₜ[O] t = -(TWact (gR g) T g b - b)) ∧
        (W.resΓ g = W.gamK →
          (1 : RW) ⊗ₜ[O] t = jD T (pr : W.DD T × W.DD T).2 - (TWact (gR g) T g b - b))
end Generic
namespace Loc
variable {l : ℕ} [Fact l.Prime]
abbrev RW (LL : FinExt l) : Type := ↥(OL LL) ⊗[ℤ_[l]] WCb l
abbrev RA (LL : FinExt l) : Type := ↥(OL LL) ⊗[ℤ_[l]] Ainf l
def inclR (LL : FinExt l) : RA LL →ₐ[↥(OL LL)] RW LL :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (inclWA l)
def frobW (l : ℕ) [Fact l.Prime] : WCb l →ₐ[ℤ_[l]] WCb l where
  toRingHom := WittVector.map (frobenius (Cb l) l)
  commutes' := fun x => map_zlW l _ x
def φRW (LL : FinExt l) : RW LL →ₐ[↥(OL LL)] RW LL :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (frobW l)
def IsTiltOf (x : Om l) (m : ℕ) (xb : OCb l) : Prop :=
  ∀ k : ℕ, ∃ y : OC l, (y : PadicComplex l) ^ (l ^ k) = (x : PadicComplex l) ∧ y ^ m = 1 ∧
    PreTilt.coeff k xb = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y
end Loc
variable {l : ℕ} [Fact l.Prime]
def LocAinf.gRW {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l) :
    RW LL →ₐ[↥(OL LL)] RW LL :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (AI.actWCbHom g).toAlgHom
structure EtSit (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (_h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) where
  tie : EtTie W (RA LL) (RW LL) (inclR LL) (φRW LL)
    (fun g : ↥(GK K) => AI.gRW LL (g : GQ l))
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1))

  inertia_action_on_roots : ∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → ∀ xb : OCb l,
    IsTiltOf (c : Om l) m xb → ∀ o : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL),
    (∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = W.emb i c) →
      tie.io (fun i => PowerSeries.C (o i)) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l xb
end Formalism.BasicNotions
namespace Formalism.BasicNotions
open Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
section Generic
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
def mulVR (T : LocLat G Qp LL O) (b : BdR) : T.V ⊗[Qp] BdR →ₗ[LL] T.V ⊗[Qp] BdR :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp b)
def compKer (T : LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR) : Submodule LL (T.V ⊗[Qp] BdR) :=
  Submodule.span LL {z | ∃ (c : LL) (y : T.V ⊗[Qp] BdR), z = c • y - mulVR T (ι c) y}
def TWincl {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G Qp LL O) : TW R T →ₗ[O] TW R' T :=
  TensorProduct.map f.toLinearMap LinearMap.id
variable {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
structure CmpTie (W : LocWach PD LL O v n) {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    (E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA) (ιdR : Ai →+* BdR) (p1 : Ai) (tS zS : BdR) where

  levB : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(W.N T) →+ (ℤ → T.V ⊗[Qp] B)
  levB_mem : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
    levB T i ζ x k ∈ DcrisL PD T.ρ (W.emb i)
  levB_supp : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)),
    ∃ m : ℤ, ∀ k < m, levB T i ζ x k = 0

  levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
    W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (levB T i ζ x k)

  cmp_eq : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (x : ↥(W.N T)),
    W.cmp T ((letE i : LetA O n) • x) = levB T i 1 x 0

  levB_φ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL),
    (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
    (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
    levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
      ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
        (((PD.p : LL) ^ (k - (j : ℤ))) •
          φVB PD (LL := LL) (V := T.V) (levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ))))

  levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
    IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
    ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
    levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • levB T i ζ' x k

  lev_Γ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
    IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
    ζ' = ζ ^ a → ∀ f : LetA O n,
    W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f)
  lev_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
    W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f)

  βdR : ∀ T : LocLat G Qp LL O, TW (O ⊗[Zl] Ai) T →+ T.V ⊗[Qp] BdR
  βdR_tmul : ∀ (T : LocLat G Qp LL O) (a : O) (w : Ai) (t : ↥T.L.T),
    βdR T ((a ⊗ₜ[Zl] w) ⊗ₜ[O] t) = ((a • t : ↥T.L.T) : T.V) ⊗ₜ[Qp] ιdR w

  levN_dR : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL) (ι : LL →ₐ[Qp] BdR),
    (∀ c : K₀, ι (W.emb i c) = algebraMap K₀ BdR c) → ι ζ = zS →
    ∀ (x : ↥(W.N T)) (k : ℕ) (y : TW (O ⊗[Zl] Ai) T),
    TWincl inclR T y = (inclR ((1 : O) ⊗ₜ[Zl] p1)) ^ k • E.jD T (x : W.DD T) →
    ∀ a : ℕ, (∀ r : ℤ, r < -(a : ℤ) → W.levN T i ζ x r = 0) →
    ∃ c : ℤ, ∀ M : ℕ,
      mulVR T (tS ^ a) (βdR T y) - mulVR T (ιdR p1 ^ k)
        (∑ r ∈ Finset.range M, mulVR T (tS ^ r) (W.levN T i ζ x ((r : ℤ) - (a : ℤ)))) ∈
      compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) ((M : ℤ) - c)
end Generic
variable {l : ℕ} [Fact l.Prime]
structure CmpSit (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) where
  tie : CmpTie W E.tie (P.ιB.toRingHom.comp AI.ιA) AI.π₁
    ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) (algebraMap (Om l) P.R.BdR (P.ζQ s))

  tB_ε : P.ιB (AI.ιA AI.μ) - P.ιB P.tB ∈ (P.PD K).Fil 2

  π₁_inv : ∃ u ∈ (P.PD K).Fil 0, P.ιB (AI.ιA AI.π₁) * u = 1
structure LocHW (l : ℕ) [Fact l.Prime] (P : LocPrime l) where

  W : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL →
    LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))
  W_s : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), (W K s LL h).s = s

  W_proj : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
    @Module.Projective (PowerSeries ℤ_[l]) _ ↥((W K s LL h).N T) _
      (Module.compHom _ (zlA LL (Module.finrank ℚ_[l] ↥(K0 K))))
structure LocFon (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P) where
  E : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), EtSit P AI K s LL h (H.W K s LL h)
structure LocCmpT (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) where
  C : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), CmpSit P AI K s LL h (F.E K s LL h)
abbrev HWOf (L : LocTheory) : Type 1 := ∀ (l : ℕ) [Fact l.Prime], LocHW l (L l)
abbrev FonOf (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)) (H : HWOf L) : Type 1 :=
  ∀ (l : ℕ) [Fact l.Prime], LocFon l (L l) (A l) (H l)
abbrev CmpOf (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)) (H : HWOf L)
    (F : FonOf L A H) : Type 1 :=
  ∀ (l : ℕ) [Fact l.Prime], LocCmpT l (L l) (A l) (H l) (F l)
def LocHW.IsPt {P : LocPrime l} (H : LocHW l P) {K : FinExt l} {s : ℕ} {LL : FinExt l}
    (h : Good K s LL) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1)
    (τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1) : Prop :=
  (∀ (x : ↥(K0 K)) (y : ↥(Ks K s)), (y : Om l) = (x : Om l) → τ y = (H.W K s LL h).emb i x) ∧
    ∀ y : ↥(Ks K s), (y : Om l) = P.ζQ s → τ y = ζ
end Formalism.BasicNotions


