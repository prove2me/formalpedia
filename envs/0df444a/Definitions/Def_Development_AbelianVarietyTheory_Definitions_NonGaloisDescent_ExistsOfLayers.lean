-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsOfLayers
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsOfLayers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:54.703306+00:00
-- url     : https://prove2.me/theorems/b1ac85fd-6393-4f0d-98dc-627d3f9514e2
-- title:
--   Exists Of Layers
-- statement:
--   Definitions and structural lemmas for Exists Of Layers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsOfLayers.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HWL
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
section Generic
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
structure WGam (PD : PeriodData G Qp K₀ K B BdR) (LL O : Type) [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] (v : AddValuation LL (WithTop ℚ)) (n s : ℕ) where
  emb : ZMod n → (K₀ →ₐ[Qp] LL)
  emb_bij : Function.Bijective emb
  emb_σ : ∀ i, (emb (i + 1)).comp PD.σ = emb i
  n_eq : n = Module.finrank Qp K₀
  v_l : v (PD.p : LL) = 1
  s_pos : 1 ≤ s
  s_two : PD.p = 2 → 2 ≤ s
  Gam : Type
  [gamGrp : CommGroup Gam]
  resΓ : G →* Gam
  resΓ_onto : Function.Surjective resΓ
  χΓ : Gam →* Oˣ
  χΓ_res : ∀ g, algebraMap O LL (χΓ (resΓ g) : O) = algebraMap Qp LL (PD.χ g : Qp)
  χΓ_inj : Function.Injective χΓ
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
  one : LocLat G Qp LL O
  one_triv : ∀ g x, one.ρ g x = x
  one_line : ∃ e : one.V, e ≠ 0 ∧ one.L.T = Submodule.span O {e}
attribute [instance] WGam.gamGrp
variable {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
structure WSer (Γ : WGam PD LL O v n s) where
  φ₀ : PowerSeries O →ₐ[O] PowerSeries O
  q₀ : PowerSeries O
  q₀_def : PowerSeries.X * q₀ = (1 + PowerSeries.X) ^ PD.p - 1
  φ₀_X : φ₀ PowerSeries.X = PowerSeries.X * q₀
  γ₀ : Γ.Gam →* (PowerSeries O →ₐ[O] PowerSeries O)
  γ₀_comm : ∀ g a, φ₀ (γ₀ g a) = γ₀ g (φ₀ a)
  γ₀_X : ∀ g, PowerSeries.constantCoeff (γ₀ g PowerSeries.X) = 0 ∧
    PowerSeries.coeff 1 (γ₀ g PowerSeries.X) = (Γ.χΓ g : O)
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
  γE : Γ.Gam →* (EE →ₐ[O] EE)
  γE_ext : ∀ g a, γE g (algebraMap (LetA O n) EE a) = algebraMap (LetA O n) EE (letγ (γ₀ g) a)
  lev : ZMod n → LL → (LetA O n →ₐ[O] PowerSeries LL)
  lev_letter : ∀ i ζ a, a i = 0 → lev i ζ a = 0
  lev_π : ∀ i (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∃ E : PowerSeries LL, PowerSeries.constantCoeff E = 1 ∧
    PowerSeries.derivative LL E = E ∧ 1 + lev i ζ letπ = PowerSeries.C ζ * E
  lev_cont : ∀ (i : ZMod n) (ζ : LL) (a : LetA O n) (k r : ℕ), ∃ m₀ : ℕ, ∀ m ≥ m₀, (r : WithTop ℚ) ≤
    v (PowerSeries.coeff k (lev i ζ a) -
      PowerSeries.coeff k (lev i ζ (fun j => ((PowerSeries.trunc m (a j) : Polynomial O) : PowerSeries O))))
  lev_Γ : ∀ (g : Γ.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
    IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (Γ.χΓ g : O) - (a : LL)) →
    ζ' = ζ ^ a → ∀ f : LetA O n,
    lev i ζ (letγ (γ₀ g) f) = PowerSeries.rescale (algebraMap O LL (Γ.χΓ g : O)) (lev i ζ' f)
  lev_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
    lev i ζ (letφ φ₀ f) = PowerSeries.rescale (PD.p : LL) (lev (i - 1) (ζ ^ PD.p) f)
  lev_junk : ∀ (i : ZMod n) (ζ : LL), ¬ (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → lev i ζ = lev i 1
attribute [instance] WSer.eeRing WSer.eeAlgA WSer.eeAlgO WSer.eeTow
variable {Γ : WGam PD LL O v n s}
def WSer.Q (R : WSer Γ) : LetA O n := (letφ (n := n) R.φ₀ ^ (s - 1)) (fun _ => R.q₀)
structure WIo (R : WSer Γ) (RA RW : Type) [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] (inclR : RA →ₐ[O] RW) (φR : RW →ₐ[O] RW) (gR : G → (RW →ₐ[O] RW)) (πA : RA) where
  io : LetA O n →ₐ[O] RA
  io_π : io letπ = πA
  ioE : R.EE →ₐ[O] RW
  ioE_ext : ∀ a, ioE (algebraMap (LetA O n) R.EE a) = inclR (io a)
  ioE_φ : ∀ e, ioE (R.φE e) = φR (ioE e)
  ioE_γ : ∀ (g : G) e, ioE (R.γE (Γ.resΓ g) e) = gR g (ioE e)
variable {R : WSer Γ}
section Et
variable {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
set_option maxHeartbeats 1000000 in

structure WEt (I : WIo R RA RW inclR φR gR πA) where
  DD : LocLat G Qp LL O → Type
  [ddAcg : ∀ T, AddCommGroup (DD T)]
  [ddModE : ∀ T, Module R.EE (DD T)]
  [ddModA : ∀ T, Module (LetA O n) (DD T)]
  [ddModO : ∀ T, Module O (DD T)]
  [ddTowA : ∀ T, IsScalarTower (LetA O n) R.EE (DD T)]
  [ddTowO : ∀ T, IsScalarTower O (LetA O n) (DD T)]
  φD : ∀ T, DD T →ₗ[O] DD T
  φD_smul : ∀ T (e : R.EE) (x : DD T), φD T (e • x) = R.φE e • φD T x
  γD : ∀ T, Γ.Gam → (DD T →ₗ[O] DD T)
  γD_smul : ∀ T g (e : R.EE) (x : DD T), γD T g (e • x) = R.γE g e • γD T g x
  γD_one : ∀ T x, γD T 1 x = x
  γD_mul : ∀ T g h x, γD T (g * h) x = γD T g (γD T h x)
  φγ_comm : ∀ T g x, φD T (γD T g x) = γD T g (φD T x)
  DD_free : ∀ T, Module.Free R.EE (DD T) ∧ Module.finrank R.EE (DD T) = Module.finrank O ↥T.L.T
  map : ∀ {T T' : LocLat G Qp LL O}, LatHom T.L T'.L → (DD T →ₗ[R.EE] DD T')
  map_φ : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) x, map f (φD T x) = φD T' (map f x)
  map_γ : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) g x, map f (γD T g x) = γD T' g (map f x)
  map_id : ∀ T x, map (latId T) x = x
  map_comp : ∀ {T T' T'' : LocLat G Qp LL O} (g : LatHom T'.L T''.L) (f : LatHom T.L T'.L) x,
    map (latComp g f) x = map g (map f x)
  map_latAdd : ∀ {T T' : LocLat G Qp LL O} (f g : LatHom T.L T'.L) x, map (latAdd f g) x = map f x + map g x
  map_latSmul : ∀ (T : LocLat G Qp LL O) (c : O) x, map (latSmul T c) x = c • x
  jD : ∀ T, DD T →ₗ[O] TW RW T
  jD_smul : ∀ T (e : R.EE) x, jD T (e • x) = I.ioE e • jD T x
  jD_φ : ∀ T x, jD T (φD T x) = TWmap φR T (jD T x)
  jD_act : ∀ T (g : G) x, jD T (γD T (Γ.resΓ g) x) = TWact (gR g) T g (jD T x)
  jD_inj : ∀ T, Function.Injective (jD T)
  jD_span : ∀ T, Submodule.span RW (Set.range (jD T)) = ⊤
  jD_map : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (x : DD T),
    jD T' (map f x) = TensorProduct.map (LinearMap.id : RW →ₗ[O] RW)
      ((f.f.restrictScalars O).restrict f.T_le) (jD T x)
attribute [instance] WEt.ddAcg WEt.ddModE WEt.ddModA WEt.ddModO WEt.ddTowA WEt.ddTowO
variable {I : WIo R RA RW inclR φR gR πA}
set_option maxHeartbeats 1000000 in

structure WN (E : WEt I) {Zl : Type} [CommRing Zl] (zl : PowerSeries Zl →+* LetA O n) where
  N : ∀ T, Submodule (LetA O n) (E.DD T)
  N_base : ∀ T, IsCrys PD T.ρ → IsBaseChange R.EE ((N T).subtype)
  N_φ : ∀ T, ∀ x ∈ N T, ∃ k : ℕ,
    ((letφ (n := n) R.φ₀ ^ (s - 1)) (fun _ => R.q₀)) ^ k • E.φD T x ∈ N T
  N_φinv : ∀ T, ∀ y ∈ N T, ∃ k : ℕ, ((letφ (n := n) R.φ₀ ^ (s - 1)) (fun _ => R.q₀)) ^ k • y ∈
    Submodule.span (LetA O n) (E.φD T '' (N T : Set (E.DD T)))
  N_fg : ∀ T, (N T).FG
  N_Γ : ∀ T (g : Γ.Gam), ∀ x ∈ N T, E.γD T g x ∈ N T
  N_π : ∀ T (g : Γ.Gam), ∀ x ∈ N T, ∃ y ∈ N T, E.γD T g x - x = (letπ : LetA O n) • y
  map_N : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ x ∈ N T, E.map f x ∈ N T'
  one_e : ∃ (e : E.DD Γ.one) (e₀ : ↥Γ.one.L.T), Submodule.span O {e₀} = ⊤ ∧
    E.jD Γ.one e = (1 : RW) ⊗ₜ[O] e₀ ∧ N Γ.one = Submodule.span (LetA O n) {e}
  N_proj : ∀ T, @Module.Projective (PowerSeries Zl) _ ↥(N T) _ (Module.compHom _ zl)
  N_junk : ∀ T, ¬ IsCrys PD T.ρ → N T = ⊥
set_option maxHeartbeats 1000000 in

structure WCl (E : WEt I) where
  cl : ∀ T, ↥(herrCocycles (E.γD T Γ.gam) (E.φD T)) →ₗ[O]
    LatticeCohomology (resLat T Γ.GKs)
  clK : ∀ T : LocLat G Qp LL O, ↥(herrZ1Δ (E.γD T Γ.gamK) (E.φD T) Γ.DelF (E.γD T)) →ₗ[O] LatticeCohomology T.L
  clK_res : Γ.gamK = Γ.gam → ∀ T (pr : ↥(herrZ1Δ (E.γD T Γ.gamK) (E.φD T) Γ.DelF (E.γD T))) (pr' : ↥(herrCocycles (E.γD T Γ.gam) (E.φD T))),
    (pr' : E.DD T × E.DD T) = (pr : E.DD T × E.DD T) → resH1 T Γ.GKs (clK T pr) = cl T pr'
  cl_def : ∀ T (pr : ↥(herrCocycles (E.γD T Γ.gam) (E.φD T))) (b : TW RW T),
    TWmap φR T b - b = E.jD T (pr : E.DD T × E.DD T).1 →
    ∃ c : ↥(latticeCocycles (resLat T Γ.GKs)), Submodule.Quotient.mk c = cl T pr ∧
      ∀ (g : ↥Γ.GKs) (t : ↥T.L.T), (t : T.V) = (c : ↥Γ.GKs → T.V) g →
        (Γ.resΓ (g : G) = 1 → (1 : RW) ⊗ₜ[O] t = -(TWact (gR g) T (g : G) b - b)) ∧
        (Γ.resΓ (g : G) = Γ.gam →
          (1 : RW) ⊗ₜ[O] t = E.jD T (pr : E.DD T × E.DD T).2 - (TWact (gR g) T (g : G) b - b))
  clK_def : (PD.p = 2 → Γ.DelF = {1}) → ∀ T (pr : ↥(herrZ1Δ (E.γD T Γ.gamK) (E.φD T) Γ.DelF (E.γD T))) (b : TW RW T),
    TWmap φR T b - b = E.jD T (pr : E.DD T × E.DD T).1 →
    ∃ c : ↥(latticeCocycles T.L), Submodule.Quotient.mk c = clK T pr ∧
      ∀ (g : G) (t : ↥T.L.T), (t : T.V) = (c : G → T.V) g →
        (Γ.resΓ g ∈ Γ.DelF → (1 : RW) ⊗ₜ[O] t = -(TWact (gR g) T g b - b)) ∧
        (Γ.resΓ g = Γ.gamK →
          (1 : RW) ⊗ₜ[O] t = E.jD T (pr : E.DD T × E.DD T).2 - (TWact (gR g) T g b - b))
end Et
section Cmp
variable {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n}
set_option maxHeartbeats 2000000 in

structure WCmp (Mo : WN E zl) (ιdR : Ai →+* BdR) (p1 : Ai) (tS zS : BdR) where
  cmp : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B
  cmp_smul : ∀ (T : LocLat G Qp LL O) (c : O) (x : ↥(Mo.N T)), cmp T (c • x) = algebraMap O LL c • cmp T x
  cmp_π : ∀ (T : LocLat G Qp LL O) (x : ↥(Mo.N T)), cmp T ((letπ : LetA O n) • x) = 0
  cmp_mem : ∀ (T : LocLat G Qp LL O) (x : ↥(Mo.N T)), cmp T x ∈ Dcris PD T.ρ
  cmp_letter : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (x : ↥(Mo.N T)), cmp T ((letE i : LetA O n) • x) ∈ DcrisL PD T.ρ (Γ.emb i)
  cmp_map : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ (x : ↥(Mo.N T)) (hx : E.map f (x : E.DD T) ∈ Mo.N T'),
    cmp T' ⟨E.map f (x : E.DD T), hx⟩ = AlgebraTensorModule.map f.f (LinearMap.id : B →ₗ[Qp] B) (cmp T x)
  levN : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(Mo.N T) →+ (ℤ → T.V ⊗[Qp] BdR)
  levN_supp : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) x, ∃ m : ℤ, ∀ k < m, levN T i ζ x k = 0
  levN_smul : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (a : LetA O n) (x : ↥(Mo.N T)) (k : ℤ),
    levN T i ζ (a • x) k = ∑ᶠ j : ℕ, PowerSeries.coeff j (R.lev i ζ a) • levN T i ζ x (k - j)
  levN_map : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T))
    (hx : E.map f (x : E.DD T) ∈ Mo.N T') (k : ℤ),
    levN T' i ζ ⟨E.map f (x : E.DD T), hx⟩ k = AlgebraTensorModule.map f.f (LinearMap.id : BdR →ₗ[Qp] BdR) (levN T i ζ x k)
  levB : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(Mo.N T) →+ (ℤ → T.V ⊗[Qp] B)
  levB_mem : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (k : ℤ),
    levB T i ζ x k ∈ DcrisL PD T.ρ (Γ.emb i)
  levB_supp : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)),
    ∃ m : ℤ, ∀ k < m, levB T i ζ x k = 0
  levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (k : ℤ),
    levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (levB T i ζ x k)
  cmp_eq : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (x : ↥(Mo.N T)),
    cmp T ((letE i : LetA O n) • x) = levB T i 1 x 0
  levB_φ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL),
    (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(Mo.N T)) (m : ℕ)
    (hx : R.Q ^ m • E.φD T (x : E.DD T) ∈ Mo.N T) (k : ℤ),
    levB T i ζ ⟨R.Q ^ m • E.φD T (x : E.DD T), hx⟩ k =
      ∑ᶠ j : ℕ, PowerSeries.coeff j (R.lev i ζ (R.Q ^ m)) •
        (((PD.p : LL) ^ (k - (j : ℤ))) •
          φVB PD (LL := LL) (V := T.V) (levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ))))
  levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : Γ.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
    IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (Γ.χΓ g : O) - (a : LL)) →
    ζ' = ζ ^ a → ∀ (x : ↥(Mo.N T)) (hx : E.γD T g (x : E.DD T) ∈ Mo.N T) (k : ℤ),
    levB T i ζ ⟨E.γD T g (x : E.DD T), hx⟩ k = (algebraMap O LL (Γ.χΓ g : O)) ^ k • levB T i ζ' x k
  βdR : ∀ T : LocLat G Qp LL O, TW (O ⊗[Zl] Ai) T →+ T.V ⊗[Qp] BdR
  βdR_tmul : ∀ (T : LocLat G Qp LL O) (a : O) (w : Ai) (t : ↥T.L.T),
    βdR T ((a ⊗ₜ[Zl] w) ⊗ₜ[O] t) = ((a • t : ↥T.L.T) : T.V) ⊗ₜ[Qp] ιdR w
  levN_dR : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL) (ι : LL →ₐ[Qp] BdR),
    (∀ c : K₀, ι (Γ.emb i c) = algebraMap K₀ BdR c) → ι ζ = zS →
    ∀ (x : ↥(Mo.N T)) (k : ℕ) (y : TW (O ⊗[Zl] Ai) T),
    TWincl inclR T y = (inclR ((1 : O) ⊗ₜ[Zl] p1)) ^ k • E.jD T (x : E.DD T) →
    ∀ a : ℕ, (∀ r : ℤ, r < -(a : ℤ) → levN T i ζ x r = 0) →
    ∃ c : ℤ, ∀ M : ℕ,
      mulVR T (tS ^ a) (βdR T y) - mulVR T (ιdR p1 ^ k)
        (∑ r ∈ Finset.range M, mulVR T (tS ^ r) (levN T i ζ x ((r : ℤ) - (a : ℤ)))) ∈
      compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) ((M : ℤ) - c)
variable {Mo : WN E zl} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
set_option maxHeartbeats 2000000 in

def toWach (Cl : WCl E) (Cm : WCmp Mo ιdR p1 tS zS) : LocWach PD LL O v n :=
  { Γ, R, E, Mo, Cl, Cm with s := s }
set_option maxHeartbeats 2000000 in

def toEt (Cl : WCl E) (Cm : WCmp Mo ιdR p1 tS zS) :
    EtTie (toWach Cl Cm) (O ⊗[Zl] Ai) RW inclR φR gR πA :=
  { I, E, Mo, Cl with }
set_option maxHeartbeats 2000000 in

def toCmp (Cl : WCl E) (Cm : WCmp Mo ιdR p1 tS zS) :
    CmpTie (toWach Cl Cm) (toEt Cl Cm) ιdR p1 tS zS :=
  { R, Cm with }
end Cmp
end Generic
section Concrete
variable {l : ℕ} [Fact l.Prime]
abbrev GamS (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) : Type 1 :=
  WGam (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)) s
variable {P : LocPrime l} {K : FinExt l} {s : ℕ} {LL : FinExt l} {Γ : GamS P K s LL}
abbrev IoS (AI : LocAinf l P) (R : WSer Γ) : Type :=
  WIo R (RA LL) (RW LL) (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l))
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1))
def IoW {AI : LocAinf l P} {R : WSer Γ} (I : IoS AI R) : Prop :=
  ∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → ∀ xb : OCb l,
    IsTiltOf (c : Om l) m xb → ∀ o : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL),
    (∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = Γ.emb i c) →
      I.io (fun i => PowerSeries.C (o i)) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l xb
abbrev NS {AI : LocAinf l P} {R : WSer Γ} {I : IoS AI R} (E : WEt I) : Type 1 :=
  WN E (zlA LL (Module.finrank ℚ_[l] ↥(K0 K)))
abbrev CmpS {AI : LocAinf l P} {R : WSer Γ} {I : IoS AI R} {E : WEt I} (Mo : NS E) : Type 1 :=
  WCmp Mo (P.ιB.toRingHom.comp AI.ιA) AI.π₁
    ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) (algebraMap (Om l) P.R.BdR (P.ζQ s))
structure Layers (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) where
  Γ : GamS P K s LL
  R : WSer Γ
  I : IoS AI R
  ioW : IoW I
  E : WEt I
  Mo : NS E
  Cl : WCl E
  Cm : CmpS Mo
end Concrete
end GlobalTheory.HWL


