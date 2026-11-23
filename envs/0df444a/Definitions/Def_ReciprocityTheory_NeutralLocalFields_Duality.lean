-- Prove2me | Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
-- name    : ReciprocityTheory_NeutralLocalFields_Duality
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:18.723735+00:00
-- url     : https://prove2.me/theorems/85fecedc-2085-45dd-b939-44a4dbc694ed
-- title:
--   Duality
-- statement:
--   Definitions and structural lemmas for Duality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Duality.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
namespace Neutral.B1
section CohA
set_option linter.unusedVariables false
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
section ContMaps
variable (R M)
def contMaps (X : Type*) [TopologicalSpace X] : Submodule R (X → M) where
  carrier := {f | Continuous f}
  zero_mem' := continuous_const
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.const_smul c
variable {R M}
end ContMaps
def ContAction (rho : Representation R G M) : Prop :=
  Continuous (fun p : G × M => rho p.1 p.2)
variable (rho : Representation R G M)
def H0 : Submodule R M := rho.invariants
theorem mem_riemannRochSpace_iff_regularAt_everywhere (m : M) : m ∈ H0 rho ↔ ∀ g, rho g m = m := Iff.rfl
def Z1 : Submodule R (G → M) where
  carrier := {f | Continuous f ∧ ∀ g h, f (g * h) = f g + rho g (f h)}
  zero_mem' := ⟨continuous_const, fun g h => by simp⟩
  add_mem' := fun {f f'} hf hf' => ⟨hf.1.add hf'.1, fun g h => by
    simp only [Pi.add_apply, hf.2, hf'.2, map_add]; abel⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, fun g h => by
    simp only [Pi.smul_apply, hf.2, map_smul, smul_add]⟩
def d0 : M →ₗ[R] (G → M) := LinearMap.pi fun g => rho g - LinearMap.id
@[simp] theorem amitsur_d0_apply (m : M) (g : G) : d0 rho m g = rho g m - m := rfl
def Bd1 : Submodule R (G → M) := LinearMap.range (d0 rho)
theorem mem_contCoboundaries1 (f : G → M) : f ∈ Bd1 rho ↔ ∃ m, ∀ g, f g = rho g m - m := by
  constructor
  · rintro ⟨m, rfl⟩; exact ⟨m, fun g => rfl⟩
  · rintro ⟨m, hm⟩; exact ⟨m, funext fun g => (hm g).symm⟩
abbrev H1 := Z1 rho ⧸ (Bd1 rho).comap (Z1 rho).subtype
def Z2 : Submodule R (G × G → M) where
  carrier := {f | Continuous f ∧
    ∀ g h k, rho g (f (h, k)) - f (g * h, k) + f (g, h * k) - f (g, h) = 0}
  zero_mem' := ⟨continuous_const, fun g h k => by simp⟩
  add_mem' := fun {f f'} hf hf' => ⟨hf.1.add hf'.1, fun g h k => by
    have e1 := hf.2 g h k; have e2 := hf'.2 g h k
    simp only [Pi.add_apply, map_add]
    calc _ = (rho g (f (h, k)) - f (g * h, k) + f (g, h * k) - f (g, h)) +
          (rho g (f' (h, k)) - f' (g * h, k) + f' (g, h * k) - f' (g, h)) := by abel
      _ = 0 := by rw [e1, e2, add_zero]⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, fun g h k => by
    have e := hf.2 g h k
    simp only [Pi.smul_apply, map_smul]
    rw [← smul_sub, ← smul_add, ← smul_sub, e, smul_zero]⟩
def d1 : (G → M) →ₗ[R] (G × G → M) where
  toFun c p := rho p.1 (c p.2) - c (p.1 * p.2) + c p.1
  map_add' c c' := by
    funext p; simp only [Pi.add_apply, map_add]; abel
  map_smul' r c := by
    funext p; simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub, smul_add]
@[simp] theorem d1_apply (c : G → M) (g h : G) :
    d1 rho c (g, h) = rho g (c h) - c (g * h) + c g := rfl
def Bd2 : Submodule R (G × G → M) := (contMaps R M G).map (d1 rho)
theorem mem_contCoboundaries2 (f : G × G → M) :
    f ∈ Bd2 rho ↔ ∃ c : G → M, Continuous c ∧ d1 rho c = f := Iff.rfl
abbrev H2 := Z2 rho ⧸ (Bd2 rho).comap (Z2 rho).subtype
def Cn (rho : Representation R G M) (n : ℕ) : Submodule R ((Fin n → G) → M) := contMaps R M (Fin n → G)
def dn (n : ℕ) : ((Fin n → G) → M) →ₗ[R] ((Fin (n + 1) → G) → M) where
  toFun f g := rho (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
    (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)
  map_add' f f' := by
    funext g
    simp [Finset.sum_add_distrib, add_add_add_comm]
  map_smul' r f := by
    funext g
    simp [Finset.smul_sum, ← smul_assoc, mul_comm r]
theorem dn_apply (n : ℕ) (f : (Fin n → G) → M) (g : Fin (n + 1) → G) :
    dn rho n f g = rho (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := rfl
def Zn (n : ℕ) : Submodule R ((Fin n → G) → M) := Cn rho n ⊓ LinearMap.ker (dn rho n)
def Bn : (n : ℕ) → Submodule R ((Fin n → G) → M)
  | 0 => ⊥
  | n + 1 => (Cn rho n).map (dn rho n)
abbrev Hn (n : ℕ) := Zn rho n ⧸ (Bn rho n).comap (Zn rho n).subtype
section Restriction
variable {H : Type*} [Group H] [TopologicalSpace H] (phi : H →* G)
def resH0 : H0 rho →ₗ[R] H0 (rho.comp phi) :=
  Submodule.inclusion fun _ hm h => hm (phi h)
variable (hphi : Continuous phi)
include hphi
def restrictCocycles1 : Z1 rho →ₗ[R] Z1 (rho.comp phi) where
  toFun f := ⟨f.1 ∘ phi, f.2.1.comp hphi, fun g h => by
    simp only [Function.comp_apply, map_mul, MonoidHom.coe_comp]
    exact f.2.2 _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp] theorem restrictCocycles1_apply (f : Z1 rho) (h : H) : (restrictCocycles1 rho phi hphi f).1 h = f.1 (phi h) := rfl
def resH1 : H1 rho →ₗ[R] H1 (rho.comp phi) :=
  Submodule.mapQ _ _ (restrictCocycles1 rho phi hphi) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_contCoboundaries1 rho _).1 hf
    exact (mem_contCoboundaries1 _ _).2 ⟨m, fun h => hm (phi h)⟩
def restrictCocycles2 : Z2 rho →ₗ[R] Z2 (rho.comp phi) where
  toFun f := ⟨fun p => f.1 (phi p.1, phi p.2), f.2.1.comp (hphi.prodMap hphi), fun g h k => by
    simp only [map_mul, MonoidHom.coe_comp, Function.comp_apply]
    exact f.2.2 _ _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp] theorem restrictCocycles2_apply (f : Z2 rho) (g h : H) :
    (restrictCocycles2 rho phi hphi f).1 (g, h) = f.1 (phi g, phi h) := rfl
def resH2 : H2 rho →ₗ[R] H2 (rho.comp phi) :=
  Submodule.mapQ _ _ (restrictCocycles2 rho phi hphi) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (mem_contCoboundaries2 rho _).1 hf
    refine (mem_contCoboundaries2 _ _).2 ⟨c ∘ phi, hc.comp hphi, ?_⟩
    funext p
    have e := congrFun hcf (phi p.1, phi p.2)
    simp only [Submodule.coe_subtype] at e
    change _ = f.1 (phi p.1, phi p.2)
    rw [← e]
    simp [d1]
end Restriction
section Map
variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
  (hequiv : ∀ g m, u (rho g m) = rho' g (u m))
include hu hequiv
def cocycles1MapOfEquivariant : Z1 rho →ₗ[R] Z1 rho' where
  toFun f := ⟨u ∘ f.1, hu.comp f.2.1, fun g h => by
    simp only [Function.comp_apply, f.2.2 g h, map_add, hequiv]⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)
def mapH1 : H1 rho →ₗ[R] H1 rho' :=
  Submodule.mapQ _ _ (cocycles1MapOfEquivariant rho rho' u hu hequiv) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_contCoboundaries1 rho _).1 hf
    refine (mem_contCoboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
    have e := hm g
    simp only [Submodule.coe_subtype] at e
    change u (f.1 g) = _
    rw [e, map_sub, hequiv]
def cocycles2Map : Z2 rho →ₗ[R] Z2 rho' where
  toFun f := ⟨u ∘ f.1, hu.comp f.2.1, fun g h k => by
    simp only [Function.comp_apply, ← hequiv, ← map_sub, ← map_add, f.2.2 g h k, map_zero]⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)
def mapH2 : H2 rho →ₗ[R] H2 rho' :=
  Submodule.mapQ _ _ (cocycles2Map rho rho' u hu hequiv) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (mem_contCoboundaries2 rho _).1 hf
    refine (mem_contCoboundaries2 _ _).2 ⟨u ∘ c, hu.comp hc, ?_⟩
    funext p
    have e := congrFun hcf p
    simp only [Submodule.coe_subtype] at e
    change _ = u (f.1 p)
    rw [← e]
    simp [d1, hequiv]
end Map
section Pair
variable {G' : Type*} [Group G'] [TopologicalSpace G']
  {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho' : Representation R G' M') (phi : G' →* G) (hphi : Continuous phi)
  (u : M →ₗ[R] M') (hu : Continuous u) (hcompat : ∀ g m, u (rho (phi g) m) = rho' g (u m))
include hphi hu hcompat
def compatiblePairCocycles1 : Z1 rho →ₗ[R] Z1 rho' where
  toFun f := ⟨fun g => u (f.1 (phi g)), hu.comp (f.2.1.comp hphi), fun g h => by
    simp only [map_mul, f.2.2, map_add, hcompat]⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)
@[simp] theorem compatiblePairCocycles1_apply (f : Z1 rho) (g : G') :
    (compatiblePairCocycles1 rho rho' phi hphi u hu hcompat f).1 g = u (f.1 (phi g)) := rfl
def pairH1DecompositionMap : H1 rho →ₗ[R] H1 rho' :=
  Submodule.mapQ _ _ (compatiblePairCocycles1 rho rho' phi hphi u hu hcompat) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_contCoboundaries1 rho _).1 hf
    refine (mem_contCoboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
    have e := hm (phi g)
    simp only [Submodule.coe_subtype] at e
    change u (f.1 (phi g)) = _
    rw [e, map_sub, hcompat]
def compatiblePairCocycles2 : Z2 rho →ₗ[R] Z2 rho' where
  toFun f := ⟨fun p => u (f.1 (phi p.1, phi p.2)), hu.comp (f.2.1.comp (hphi.prodMap hphi)),
    fun g h k => by
      have e := congrArg u (f.2.2 (phi g) (phi h) (phi k))
      simp only [map_sub, map_add, map_zero, hcompat] at e
      simpa only [map_mul] using e⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)
@[simp] theorem compatiblePairCocycles2_apply (f : Z2 rho) (g h : G') :
    (compatiblePairCocycles2 rho rho' phi hphi u hu hcompat f).1 (g, h) = u (f.1 (phi g, phi h)) := rfl
def compatiblePairH2 : H2 rho →ₗ[R] H2 rho' :=
  Submodule.mapQ _ _ (compatiblePairCocycles2 rho rho' phi hphi u hu hcompat) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (mem_contCoboundaries2 rho _).1 hf
    refine (mem_contCoboundaries2 _ _).2 ⟨fun g => u (c (phi g)), hu.comp (hc.comp hphi), ?_⟩
    funext p
    have e := congrFun hcf (phi p.1, phi p.2)
    simp only [Submodule.coe_subtype] at e
    change _ = u (f.1 (phi p.1, phi p.2))
    rw [← e]
    simp [d1, hcompat]
end Pair
section MapPair
variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
  (hequiv : ∀ g m, u (rho g m) = rho' g (u m))
end MapPair
section RestrictionN
variable {H : Type*} [Group H] [TopologicalSpace H] (phi : H →* G)
theorem contractNth_map {n : ℕ} (j : Fin (n + 1)) (g : Fin (n + 1) → H) :
    (fun k => phi (Fin.contractNth j (· * ·) g k)) =
      Fin.contractNth j (· * ·) (fun k => phi (g k)) := by
  funext k
  rcases lt_trichotomy (k : ℕ) j with h | h | h
  · simp only [Fin.contractNth_apply_of_lt _ _ _ _ h]
  · simp only [Fin.contractNth_apply_of_eq _ _ _ _ h, map_mul]
  · simp only [Fin.contractNth_apply_of_gt _ _ _ _ h]
theorem dn_comp (n : ℕ) (f : (Fin n → G) → M) (g : Fin (n + 1) → H) :
    dn (rho.comp phi) n (fun x => f fun i => phi (x i)) g = dn rho n f (fun i => phi (g i)) := by
  simp only [dn_apply, MonoidHom.coe_comp, Function.comp_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [contractNth_map]
variable (hphi : Continuous phi)
include hphi
theorem continuous_comp_tuple (n : ℕ) {f : (Fin n → G) → M} (hf : Continuous f) :
    Continuous (fun x : Fin n → H => f fun i => phi (x i)) :=
  hf.comp (continuous_pi fun i => hphi.comp (continuous_apply i))
def resZn (n : ℕ) : Zn rho n →ₗ[R] Zn (rho.comp phi) n where
  toFun f := ⟨fun x => f.1 fun i => phi (x i), by
    obtain ⟨hc, hk⟩ := Submodule.mem_inf.1 f.2
    refine Submodule.mem_inf.2 ⟨continuous_comp_tuple phi hphi n hc, LinearMap.mem_ker.2 ?_⟩
    funext g
    rw [dn_comp]
    exact congrFun (LinearMap.mem_ker.1 hk) _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp] theorem resZn_apply (n : ℕ) (f : Zn rho n) (x : Fin n → H) :
    (resZn rho phi hphi n f).1 x = f.1 fun i => phi (x i) := rfl
def resHn (n : ℕ) : Hn rho n →ₗ[R] Hn (rho.comp phi) n :=
  Submodule.mapQ _ _ (resZn rho phi hphi n) fun f hf => by
    rw [Submodule.mem_comap, Submodule.coe_subtype] at hf
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.coe_subtype]
    cases n with
    | zero =>
      have h0 : f.1 = 0 := (Submodule.mem_bot R).1 hf
      show (resZn rho phi hphi 0 f).1 ∈ (⊥ : Submodule R _)
      rw [Submodule.mem_bot]
      funext x
      simp [h0]
    | succ n =>
      obtain ⟨c, hc, hcf⟩ := Submodule.mem_map.1 hf
      refine Submodule.mem_map.2 ⟨fun x => c fun i => phi (x i),
        continuous_comp_tuple phi hphi n hc, ?_⟩
      funext g
      rw [dn_comp, hcf]
      rfl
end RestrictionN
section Tate
def normEnd [Finite G] : Module.End R M := ∑ᶠ g : G, rho g
def normSub [Finite G] : Submodule R (H0 rho) := (LinearMap.range (normEnd rho)).comap (H0 rho).subtype
abbrev tateH0 [Finite G] := H0 rho ⧸ normSub rho
end Tate
end
end CohA
section Coh
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (rho : Representation R G M)
section Cup
variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  {P : Type*} [AddCommGroup P] [Module R P] [TopologicalSpace P]
  [IsTopologicalAddGroup P] [ContinuousConstSMul R P]
  (rho' : Representation R G M') (rhoP : Representation R G P)
  (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
  (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
section CupZ11
include hb hbe
def cupCocycleZ1Z1 (hrho' : ContAction rho') : Z1 rho →ₗ[R] Z1 rho' →ₗ[R] Z2 rhoP :=
  LinearMap.mk₂ R
    (fun x y => ⟨fun p => b (x.1 p.1) (rho' p.1 (y.1 p.2)),
      hb.comp ((x.2.1.comp continuous_fst).prodMk
        (hrho'.comp (continuous_fst.prodMk (y.2.1.comp continuous_snd)))),
      fun g h k => by
        have hx := x.2.2 g h
        have hy := y.2.2 h k
        dsimp only
        rw [← hbe, hx, hy, map_mul, Module.End.mul_apply]
        simp only [map_add, LinearMap.add_apply]
        abel⟩)
    (fun x x' y => Subtype.ext (funext fun p => by simp))
    (fun r x y => Subtype.ext (funext fun p => by simp))
    (fun x y y' => Subtype.ext (funext fun p => by simp))
    (fun r x y => Subtype.ext (funext fun p => by simp))
@[simp] theorem cupCocycleZ1Z1_apply (hrho' : ContAction rho') (x : Z1 rho) (y : Z1 rho') (g h : G) :
    (cupCocycleZ1Z1 rho rho' rhoP b hb hbe hrho' x y).1 (g, h) = b (x.1 g) (rho' g (y.1 h)) := rfl
def cupProductH1H1 (hrho' : ContAction rho') : H1 rho →ₗ[R] H1 rho' →ₗ[R] H2 rhoP :=
  LinearMap.liftQ₂ _ _ ((cupCocycleZ1Z1 rho rho' rhoP b hb hbe hrho').compr₂ (Submodule.mkQ _))
    (fun x hx => by
      obtain ⟨m, hm⟩ := (mem_contCoboundaries1 rho _).1 hx
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun y => ?_
      rw [LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      refine (mem_contCoboundaries2 _ _).2 ⟨fun h => b m (y.1 h), hb.comp (continuous_const.prodMk y.2.1), ?_⟩
      funext p
      obtain ⟨g, h⟩ := p
      have e := hm g
      simp only [Submodule.coe_subtype] at e
      simp only [d1_apply, Submodule.coe_subtype, cupCocycleZ1Z1_apply, e, ← hbe, y.2.2 g h, map_add,
        map_sub, LinearMap.sub_apply]
      abel)
    (fun y hy => by
      obtain ⟨m, hm⟩ := (mem_contCoboundaries1 rho' _).1 hy
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.flip_apply, LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      refine (mem_contCoboundaries2 _ _).2 ⟨fun g => -b (x.1 g) (rho' g m),
        (hb.comp (x.2.1.prodMk (hrho'.comp (continuous_id.prodMk continuous_const)))).neg, ?_⟩
      funext p
      obtain ⟨g, h⟩ := p
      have e := hm h
      simp only [Submodule.coe_subtype] at e
      simp only [d1_apply, Submodule.coe_subtype, cupCocycleZ1Z1_apply, e, map_neg, ← hbe, x.2.2 g h,
        map_mul, Module.End.mul_apply, map_add, map_sub, LinearMap.add_apply]
      abel)
end CupZ11
include hb hbe
def cupCocycleH0Z2 : H0 rho →ₗ[R] Z2 rho' →ₗ[R] Z2 rhoP :=
  LinearMap.mk₂ R
    (fun m f => ⟨fun p => b m.1 (f.1 p), hb.comp (continuous_const.prodMk f.2.1),
      fun g h k => by
        have e := congrArg (b m.1) (f.2.2 g h k)
        simp only [map_sub, map_add, map_zero] at e
        rw [← hbe, (mem_riemannRochSpace_iff_regularAt_everywhere rho m.1).1 m.2 g]
        exact e⟩)
    (fun m m' f => Subtype.ext (funext fun p => by simp))
    (fun r m f => Subtype.ext (funext fun p => by simp))
    (fun m f f' => Subtype.ext (funext fun p => by simp))
    (fun r m f => Subtype.ext (funext fun p => by simp))
@[simp] theorem cupCocycleH0Z2_apply (m : H0 rho) (f : Z2 rho') (p : G × G) :
    (cupCocycleH0Z2 rho rho' rhoP b hb hbe m f).1 p = b m.1 (f.1 p) := rfl
def cupProductH0H2 : H0 rho →ₗ[R] H2 rho' →ₗ[R] H2 rhoP :=
  (Submodule.liftQ _ ((cupCocycleH0Z2 rho rho' rhoP b hb hbe).compr₂ (Submodule.mkQ _)).flip
    (fun f hf => by
      obtain ⟨c, hc, hcf⟩ := (mem_contCoboundaries2 rho' _).1 hf
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun m => ?_
      rw [LinearMap.flip_apply, LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      refine (mem_contCoboundaries2 _ _).2 ⟨fun g => b m.1 (c g), hb.comp (continuous_const.prodMk hc), ?_⟩
      funext p
      obtain ⟨g, h⟩ := p
      have e := congrFun hcf (g, h)
      simp only [Submodule.coe_subtype] at e
      simp only [d1_apply, Submodule.coe_subtype, cupCocycleH0Z2_apply, ← e, ← hbe,
        (mem_riemannRochSpace_iff_regularAt_everywhere rho m.1).1 m.2 g, map_add, map_sub])).flip
def cupCocycleZ2H0 : Z2 rho →ₗ[R] H0 rho' →ₗ[R] Z2 rhoP :=
  LinearMap.mk₂ R
    (fun f m => ⟨fun p => b (f.1 p) m.1, hb.comp (f.2.1.prodMk continuous_const),
      fun g h k => by
        have e := congrArg (b.flip m.1) (f.2.2 g h k)
        simp only [map_sub, map_add, map_zero, LinearMap.flip_apply] at e
        rw [← (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2 g, hbe, (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2 g] at e
        exact e⟩)
    (fun f f' m => Subtype.ext (funext fun p => by simp))
    (fun r f m => Subtype.ext (funext fun p => by simp))
    (fun f m m' => Subtype.ext (funext fun p => by simp))
    (fun r f m => Subtype.ext (funext fun p => by simp))
@[simp] theorem cupCocycleZ2H0_apply (f : Z2 rho) (m : H0 rho') (p : G × G) :
    (cupCocycleZ2H0 rho rho' rhoP b hb hbe f m).1 p = b (f.1 p) m.1 := rfl
def cupProductH2H0 : H2 rho →ₗ[R] H0 rho' →ₗ[R] H2 rhoP :=
  Submodule.liftQ _ ((cupCocycleZ2H0 rho rho' rhoP b hb hbe).compr₂ (Submodule.mkQ _))
    (fun f hf => by
      obtain ⟨c, hc, hcf⟩ := (mem_contCoboundaries2 rho _).1 hf
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun m => ?_
      rw [LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      refine (mem_contCoboundaries2 _ _).2 ⟨fun g => b (c g) m.1, hb.comp (hc.prodMk continuous_const), ?_⟩
      funext p
      obtain ⟨g, h⟩ := p
      have e := congrFun hcf (g, h)
      simp only [Submodule.coe_subtype] at e
      have hm := (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2 g
      simp only [d1_apply, Submodule.coe_subtype, cupCocycleZ2H0_apply, ← e, map_add, map_sub,
        LinearMap.add_apply, LinearMap.sub_apply]
      rw [← hbe, hm])
end Cup
section Local
variable {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  (phi : ∀ i, D i →* G) (hphi : ∀ i, Continuous (phi i))
abbrev LocCond := ∀ i, Submodule R (H1 (rho.comp (phi i)))
def Sel (L : LocCond rho phi) : Submodule R (H1 rho) :=
  ⨅ i, (L i).comap (resH1 rho (phi i) (hphi i))
def Sha1 : Submodule R (H1 rho) := ⨅ i, LinearMap.ker (resH1 rho (phi i) (hphi i))
def Sha2 : Submodule R (H2 rho) := ⨅ i, LinearMap.ker (resH2 rho (phi i) (hphi i))
end Local
section Inertia
variable {D : Type*} [Group D] [TopologicalSpace D] (rhoD : Representation R D M)
  (J : Subgroup D)
def H1ur : Submodule R (H1 rhoD) :=
  LinearMap.ker (resH1 rhoD J.subtype continuous_subtype_val)
end Inertia
end
end Coh
section NatCoh
variable {R : Type*} [CommRing R] {G : Type*} [Group G] [TopologicalSpace G]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho : Representation R G M) (rho' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
  (hequiv : ∀ g m, u (rho g m) = rho' g (u m))
theorem resH1_comp_mapH1 {H : Type*} [Group H] [TopologicalSpace H] (phi : H →* G)
    (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (mapH1 rho rho' u hu hequiv x) =
      mapH1 (rho.comp phi) (rho'.comp phi) u hu (fun g m => hequiv (phi g) m)
        (resH1 rho phi hphi x) := by
  induction x using Submodule.Quotient.induction_on with
  | H f => rfl
theorem resH2_comp_mapH2 {H : Type*} [Group H] [TopologicalSpace H] (phi : H →* G)
    (hphi : Continuous phi) (x : H2 rho) :
    resH2 rho' phi hphi (mapH2 rho rho' u hu hequiv x) =
      mapH2 (rho.comp phi) (rho'.comp phi) u hu (fun g m => hequiv (phi g) m)
        (resH2 rho phi hphi x) := by
  induction x using Submodule.Quotient.induction_on with
  | H f => rfl
variable {I : Type*} {Dl : I → Type*} [∀ i, Group (Dl i)] [∀ i, TopologicalSpace (Dl i)]
  (phis : ∀ i, Dl i →* G) (hphis : ∀ i, Continuous (phis i))
def shaMap1 : Sha1 rho phis hphis →ₗ[R] Sha1 rho' phis hphis :=
  (mapH1 rho rho' u hu hequiv).restrict fun x hx => by
    simp only [Sha1, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    intro i
    rw [resH1_comp_mapH1, hx i, map_zero]
def shaMap2 : Sha2 rho phis hphis →ₗ[R] Sha2 rho' phis hphis :=
  (mapH2 rho rho' u hu hequiv).restrict fun x hx => by
    simp only [Sha2, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    intro i
    rw [resH2_comp_mapH2, hx i, map_zero]
end NatCoh
instance (priority := 100) continuousConstSMul_of_discrete {R M : Type*} [SMul R M]
    [TopologicalSpace M] [DiscreteTopology M] : ContinuousConstSMul R M :=
  ⟨fun _ => continuous_of_discreteTopology⟩
section Coeff
variable {R : Type*} [CommRing R] {Γ : Type*} [Group Γ]
  {M : Type*} [AddCommGroup M] [Module R M]
def charRep (χ : Γ →* Rˣ) : Representation R Γ R where
  toFun g := ((χ g : Rˣ) : R) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_comm]
@[simp] theorem charRep_apply (χ : Γ →* Rˣ) (g : Γ) (x : R) :
    charRep χ g x = ((χ g : Rˣ) : R) * x := rfl
variable (R M) in

def TDual := Module.Dual R M
instance : AddCommGroup (TDual R M) := inferInstanceAs (AddCommGroup (Module.Dual R M))
instance : Module R (TDual R M) := inferInstanceAs (Module R (Module.Dual R M))
instance : TopologicalSpace (TDual R M) := ⊥
instance : DiscreteTopology (TDual R M) := ⟨rfl⟩
instance : FunLike (TDual R M) M R := inferInstanceAs (FunLike (M →ₗ[R] R) M R)
def TDual.mk (φ : M →ₗ[R] R) : TDual R M := φ
@[simp] theorem TDual.mk_apply (φ : M →ₗ[R] R) (m : M) : TDual.mk φ m = φ m := rfl
@[simp] theorem TDual.add_apply (φ ψ : TDual R M) (m : M) : (φ + ψ) m = φ m + ψ m := rfl
@[simp] theorem TDual.smul_apply (c : R) (φ : TDual R M) (m : M) : (c • φ) m = c * φ m := rfl
@[ext] theorem TDual.ext {φ ψ : TDual R M} (h : ∀ m, φ m = ψ m) : φ = ψ := LinearMap.ext h
def twDual (χ : Γ →* Rˣ) (rho : Representation R Γ M) : Representation R Γ (TDual R M) where
  toFun g :=
    { toFun := fun φ => TDual.mk (((χ g : Rˣ) : R) • ((φ : M →ₗ[R] R) ∘ₗ rho g⁻¹))
      map_add' := fun φ ψ => by
        ext m
        show ((χ g : Rˣ) : R) * (φ (rho g⁻¹ m) + ψ (rho g⁻¹ m)) =
          ((χ g : Rˣ) : R) * φ (rho g⁻¹ m) + ((χ g : Rˣ) : R) * ψ (rho g⁻¹ m)
        ring
      map_smul' := fun c φ => by
        ext m
        show ((χ g : Rˣ) : R) * (c * φ (rho g⁻¹ m)) = c * (((χ g : Rˣ) : R) * φ (rho g⁻¹ m))
        ring }
  map_one' := by ext φ m; simp; rfl
  map_mul' g h := by
    ext φ m
    show _ * φ (rho (g * h)⁻¹ m) = _ * (_ * φ (rho h⁻¹ (rho g⁻¹ m)))
    rw [mul_inv_rev, map_mul rho, Module.End.mul_apply, map_mul χ, Units.val_mul, mul_assoc]
@[simp] theorem twDual_apply (χ : Γ →* Rˣ) (rho : Representation R Γ M) (g : Γ) (φ : TDual R M)
    (m : M) : twDual χ rho g φ m = ((χ g : Rˣ) : R) * φ (rho g⁻¹ m) := rfl
def evalPair : M →ₗ[R] TDual R M →ₗ[R] R := LinearMap.applyₗ
@[simp] theorem evalPair_apply (m : M) (φ : TDual R M) : evalPair m φ = φ m := rfl
theorem evalPair_equiv (χ : Γ →* Rˣ) (rho : Representation R Γ M) (g : Γ) (m : M)
    (φ : TDual R M) : evalPair (rho g m) (twDual χ rho g φ) = charRep χ g (evalPair m φ) := by
  simp only [evalPair_apply, twDual_apply, charRep_apply]
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
def tdualMap {M' : Type*} [AddCommGroup M'] [Module R M'] (u : M →ₗ[R] M') :
    TDual R M' →ₗ[R] TDual R M :=
  u.dualMap
@[simp] theorem tdualMap_apply {M' : Type*} [AddCommGroup M'] [Module R M'] (u : M →ₗ[R] M')
    (φ : TDual R M') (m : M) : tdualMap u φ m = φ (u m) := rfl
theorem tdualMap_equiv (χ : Γ →* Rˣ) {M' : Type*} [AddCommGroup M'] [Module R M']
    (rho : Representation R Γ M) (rho' : Representation R Γ M') (u : M →ₗ[R] M')
    (hequiv : ∀ g m, u (rho g m) = rho' g (u m)) (g : Γ) (φ : TDual R M') :
    tdualMap u (twDual χ rho' g φ) = twDual χ rho g (tdualMap u φ) := by
  ext m
  simp only [tdualMap_apply, twDual_apply, hequiv]
end Coeff
section Cup
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]
theorem ContAction.comp' [TopologicalSpace Γ] {D : Type*} [Group D] [TopologicalSpace D]
    {rho : Representation R Γ M} (h : ContAction rho) {φ : D →* Γ} (hφ : Continuous φ) :
    ContAction (rho.comp φ) :=
  h.comp ((hφ.comp continuous_fst).prodMk continuous_snd)
variable {D : Type*} [Group D] [TopologicalSpace D]
  (χ : Γ →* Rˣ) (rho : Representation R Γ M) (φ : D →* Γ)
def cupH0H2TwistedDual : H0 (rho.comp φ) →ₗ[R] H2 ((twDual χ rho).comp φ) →ₗ[R] H2 ((charRep χ).comp φ) :=
  cupProductH0H2 (rho.comp φ) ((twDual χ rho).comp φ) ((charRep χ).comp φ) evalPair
    continuous_of_discreteTopology (fun g x y => evalPair_equiv χ rho (φ g) x y)
def cup20 : H2 (rho.comp φ) →ₗ[R] H0 ((twDual χ rho).comp φ) →ₗ[R] H2 ((charRep χ).comp φ) :=
  cupProductH2H0 (rho.comp φ) ((twDual χ rho).comp φ) ((charRep χ).comp φ) evalPair
    continuous_of_discreteTopology (fun g x y => evalPair_equiv χ rho (φ g) x y)
def cupH1H1TwistedDual (hrho : ContAction (rho.comp φ)) :
    H1 ((twDual χ rho).comp φ) →ₗ[R] H1 (rho.comp φ) →ₗ[R] H2 ((charRep χ).comp φ) :=
  cupProductH1H1 ((twDual χ rho).comp φ) (rho.comp φ) ((charRep χ).comp φ) evalPair.flip
    continuous_of_discreteTopology (fun g y x => evalPair_equiv χ rho (φ g) x y) hrho
def perpCond {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
    (phi : ∀ i, D i →* Γ) (hrho : ∀ i, ContAction (rho.comp (phi i)))
    (L : ∀ i, Submodule R (H1 (rho.comp (phi i)))) :
    ∀ i, Submodule R (H1 ((twDual χ rho).comp (phi i))) :=
  fun i => ⨅ x ∈ L i, LinearMap.ker ((cupH1H1TwistedDual χ rho (phi i) (hrho i)).flip x)
end Cup
section NatMaps
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] [TopologicalSpace Γ] (χ : Γ →* Rˣ)
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
  (rho : Representation R Γ M) (rho' : Representation R Γ M') (u : M →ₗ[R] M')
  (hequiv : ∀ g m, u (rho g m) = rho' g (u m))
def mapH1OfEquivariant : H1 rho →ₗ[R] H1 rho' := mapH1 rho rho' u continuous_of_discreteTopology hequiv
def mapH2OfEquivariant : H2 rho →ₗ[R] H2 rho' := mapH2 rho rho' u continuous_of_discreteTopology hequiv
def mapH1TwistedDual : H1 (twDual χ rho') →ₗ[R] H1 (twDual χ rho) :=
  mapH1 (twDual χ rho') (twDual χ rho) (tdualMap u) continuous_of_discreteTopology
    (tdualMap_equiv χ rho rho' u hequiv)
def mapH2TwistedDual : H2 (twDual χ rho') →ₗ[R] H2 (twDual χ rho) :=
  mapH2 (twDual χ rho') (twDual χ rho) (tdualMap u) continuous_of_discreteTopology
    (tdualMap_equiv χ rho rho' u hequiv)
variable {I : Type*} {Dl : I → Type*} [∀ i, Group (Dl i)] [∀ i, TopologicalSpace (Dl i)]
  (phis : ∀ i, Dl i →* Γ) (hphis : ∀ i, Continuous (phis i))
def natSha1 : Sha1 rho phis hphis →ₗ[R] Sha1 rho' phis hphis :=
  shaMap1 rho rho' u continuous_of_discreteTopology hequiv phis hphis
def natSha2d : Sha2 (twDual χ rho') phis hphis →ₗ[R] Sha2 (twDual χ rho) phis hphis :=
  shaMap2 (twDual χ rho') (twDual χ rho) (tdualMap u) continuous_of_discreteTopology
    (tdualMap_equiv χ rho rho' u hequiv) phis hphis
end NatMaps
section Cyc
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed L] [CharZero L]
  (n : ℕ) [NeZero n]
def cycN : (L ≃ₐ[K] L) →* (ZMod n)ˣ :=
  (modularCyclotomicCharacter L (HasEnoughRootsOfUnity.natCard_rootsOfUnity L n)).comp
    (MulSemiringAction.toRingAut (L ≃ₐ[K] L) L)
end Cyc
section Local
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
abbrev GK : Type := PadicAlgCl p ≃ₐ[K] PadicAlgCl p
def inertiaSet : Set (GK p K) := {σ | ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1}
def inertiaK : Subgroup (GK p K) := Subgroup.closure (inertiaSet p K)
abbrev cycK (n : ℕ) [NeZero n] : GK p K →* (ZMod n)ˣ := cycN K (PadicAlgCl p) n
variable {p K}
def unrK {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R (GK p K) M) :
    Submodule R (H1 rho) :=
  H1ur rho (inertiaK p K)
variable (p) in

def KbarMult : Type := Additive (PadicAlgCl p)ˣ
instance : AddCommGroup (KbarMult p) := inferInstanceAs (AddCommGroup (Additive (PadicAlgCl p)ˣ))
instance : TopologicalSpace (KbarMult p) := ⊥
instance : DiscreteTopology (KbarMult p) := ⟨rfl⟩
variable (p K) in

def kbarRep : Representation ℤ (GK p K) (KbarMult p) where
  toFun σ := AddMonoidHom.toIntLinearMap
    (MonoidHom.toAdditive (Units.map (σ : PadicAlgCl p →* PadicAlgCl p)))
  map_one' := by
    apply LinearMap.ext; intro x
    apply Units.ext
    rfl
  map_mul' σ τ := by
    apply LinearMap.ext; intro x
    apply Units.ext
    rfl
abbrev QZ : Type := ℚ ⧸ (Int.castAddHom ℚ).range
end Local
def LocalCohomologyFinite : Prop := ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
  FiniteDimensional ℚ_[p] K → ∀ (n : ℕ) [NeZero n] (M : Type) [AddCommGroup M]
  [Module (ZMod n) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GK p K) M), ContAction rho →
    Finite (H0 rho) ∧ Finite (H1 rho) ∧ Finite (H2 rho) ∧ ∀ i, 3 ≤ i → Subsingleton (Hn rho i)
def LocalInvariantIsomorphism : Prop := ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
  FiniteDimensional ℚ_[p] K →
    Nonempty (H2 (kbarRep p K) ≃ₗ[ℤ] QZ) ∧
    ∀ (n : ℕ) [NeZero n], Nonempty (H2 (charRep (cycK p K n)) ≃ₗ[ZMod n] ZMod n)
def NeutralFieldTateDuality : Prop := ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
  FiniteDimensional ℚ_[p] K → ∀ (n : ℕ) [NeZero n] (M : Type) [AddCommGroup M]
  [Module (ZMod n) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GK p K) M) (hrho : ContAction rho),
    Function.Bijective (cupH0H2TwistedDual (cycK p K n) rho (MonoidHom.id _)) ∧
    Function.Bijective (cupH0H2TwistedDual (cycK p K n) rho (MonoidHom.id _)).flip ∧
    Function.Bijective (cupH1H1TwistedDual (cycK p K n) rho (MonoidHom.id _) (hrho.comp' continuous_id)) ∧
    Function.Bijective (cupH1H1TwistedDual (cycK p K n) rho (MonoidHom.id _) (hrho.comp' continuous_id)).flip ∧
    Function.Bijective (cup20 (cycK p K n) rho (MonoidHom.id _)) ∧
    Function.Bijective (cup20 (cycK p K n) rho (MonoidHom.id _)).flip
def UnramifiedClassesOrthogonal : Prop := ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
  FiniteDimensional ℚ_[p] K → ∀ (n : ℕ) [NeZero n] (M : Type) [AddCommGroup M]
  [Module (ZMod n) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GK p K) M) (hrho : ContAction rho), ¬ p ∣ n →
  (∀ σ ∈ inertiaK p K, ∀ m, rho σ m = m) →
    (∀ y : H1 (twDual (cycK p K n) rho),
      y ∈ unrK (twDual (cycK p K n) rho) ↔
        ∀ x ∈ unrK rho, cupH1H1TwistedDual (cycK p K n) rho (MonoidHom.id _) (hrho.comp' continuous_id) y x = 0) ∧
    (∀ x : H1 rho,
      x ∈ unrK rho ↔
        ∀ y ∈ unrK (twDual (cycK p K n) rho),
          cupH1H1TwistedDual (cycK p K n) rho (MonoidHom.id _) (hrho.comp' continuous_id) y x = 0)
def LocalEulerCharacteristic : Prop := ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
  FiniteDimensional ℚ_[p] K → ∀ (n : ℕ) [NeZero n] (M : Type) [AddCommGroup M]
  [Module (ZMod n) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GK p K) M), ContAction rho →
    Nat.card (H1 rho) =
      Nat.card (H0 rho) * Nat.card (H2 rho) *
        p ^ (Module.finrank ℚ_[p] K * padicValNat p (Nat.card M))
section Global
abbrev G (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] := Ω ≃ₐ[F] Ω
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
def IsPlaceOver (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal
variable (F) in

abbrev Dec (A : ValuationSubring Ω) : Subgroup (G F Ω) := A.decompositionSubgroup F
def Inertia (A : ValuationSubring Ω) : Set (G F Ω) :=
  {σ | σ ∈ Dec F A ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1}
variable (F) in

def DecInf (j : Ω →+* ℂ) : Subgroup (G F Ω) where
  carrier := {σ | (∀ x, j (σ x) = j x) ∨ ∀ x, j (σ x) = starRingEnd ℂ (j x)}
  one_mem' := Or.inl fun x => rfl
  mul_mem' := by
    rintro σ τ (hσ | hσ) (hτ | hτ)
    · exact Or.inl fun x => by simp only [AlgEquiv.mul_apply, hσ, hτ]
    · exact Or.inr fun x => by simp only [AlgEquiv.mul_apply, hσ, hτ]
    · exact Or.inr fun x => by simp only [AlgEquiv.mul_apply, hσ, hτ]
    · exact Or.inl fun x => by simp only [AlgEquiv.mul_apply, hσ, hτ, Complex.conj_conj]
  inv_mem' := by
    rintro σ (hσ | hσ)
    · refine Or.inl fun x => ?_
      have := hσ (σ⁻¹ x)
      rw [show σ (σ⁻¹ x) = x from by simp] at this
      exact this.symm
    · refine Or.inr fun x => ?_
      have := hσ (σ⁻¹ x)
      rw [show σ (σ⁻¹ x) = x from by simp] at this
      rw [this, Complex.conj_conj]
theorem mem_DecInf (j : Ω →+* ℂ) (σ : G F Ω) :
    σ ∈ DecInf F j ↔ (∀ x, j (σ x) = j x) ∨ ∀ x, j (σ x) = starRingEnd ℂ (j x) := Iff.rfl
instance finite_DecInf (j : Ω →+* ℂ) : Finite (DecInf F j) := by
  classical
  refine Finite.of_injective (fun σ : DecInf F j => decide (∀ x, j (σ.1 x) = j x)) ?_
  intro σ τ h
  have hiff : (∀ x, j (σ.1 x) = j x) ↔ ∀ x, j (τ.1 x) = j x := by simpa using h
  have hσ := (mem_DecInf j σ.1).1 σ.2
  have hτ := (mem_DecInf j τ.1).1 τ.2
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply j.injective
  by_cases h1 : ∀ x, j (σ.1 x) = j x
  · rw [h1 x, hiff.1 h1 x]
  · have h2 : ¬ ∀ x, j (τ.1 x) = j x := fun h' => h1 (hiff.2 h')
    rw [hσ.resolve_left h1 x, hτ.resolve_left h2 x]
section unram
variable (S : Set (HeightOneSpectrum (𝓞 F)))
variable (Ω) in

def NS : Subgroup (G F Ω) :=
  (Subgroup.normalClosure
    (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v}, Inertia (F := F) A)
    ).topologicalClosure
instance normal_NS : (NS Ω S).Normal := by
  unfold NS; exact Subgroup.is_normal_topologicalClosure _
variable (Ω) in

abbrev GS := G F Ω ⧸ NS Ω S
variable (Ω) in

def toGS : G F Ω →* GS Ω S := QuotientGroup.mk' (NS Ω S)
variable (Ω) in
theorem continuous_toGS : Continuous (toGS Ω S) := QuotientGroup.continuous_mk
end unram
variable (F Ω) in

def cycG [IsAlgClosure F Ω] (n : ℕ) [NeZero n] : G F Ω →* (ZMod n)ˣ :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  cycN F Ω n
variable (F Ω) in

structure GData [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n] where

  A : S → ValuationSubring Ω
  hA : ∀ v, IsPlaceOver (A v) v.1

  J : InfinitePlace F → (Ω →+* ℂ)
  hJ : ∀ w, InfinitePlace.mk ((J w).comp (algebraMap F Ω)) = w

  chi : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod n)ˣ
  hchi : chi.comp (toGS Ω _) = cycG F Ω n
variable [IsAlgClosure F Ω] {S : Finset (HeightOneSpectrum (𝓞 F))} {n : ℕ} [NeZero n]
def locGrp (D : GData F Ω S n) : S ⊕ InfinitePlace F → Subgroup (G F Ω) :=
  Sum.elim (fun v => Dec F (D.A v)) (fun w => DecInf F (D.J w))
def locHom (D : GData F Ω S n) (i : S ⊕ InfinitePlace F) :
    locGrp D i →* GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) :=
  (toGS Ω _).comp (locGrp D i).subtype
theorem continuous_locHom (D : GData F Ω S n) (i : S ⊕ InfinitePlace F) :
    Continuous (locHom D i) :=
  (continuous_toGS Ω _).comp continuous_subtype_val
abbrev locF (D : GData F Ω S n) (v : S) := locHom D (Sum.inl v)
theorem continuous_locF (D : GData F Ω S n) (v : S) : Continuous (locF D v) :=
  continuous_locHom D _
abbrev locI (D : GData F Ω S n) (w : InfinitePlace F) := locHom D (Sum.inr w)
instance finite_locGrp_inr (D : GData F Ω S n) (w : InfinitePlace F) :
    Finite (locGrp D (Sum.inr w)) :=
  inferInstanceAs (Finite (DecInf F (D.J w)))
end Global
section PTMaps
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {S : Finset (HeightOneSpectrum (𝓞 F))} {n : ℕ} [NeZero n] (D : GData F Ω S n)
  {M : Type} [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
def PTCase (F : Type) [Field F] [NumberField F] (n : ℕ) : Prop :=
  Odd n ∨ InfinitePlace.nrRealPlaces F = 0
def Recip (inv : ∀ v : S, H2 ((charRep D.chi).comp (locF D v)) →ₗ[ZMod n] ZMod n) : Prop :=
  ∀ c : H2 (charRep D.chi),
    ∑ v : S, inv v (resH2 (charRep D.chi) (locF D v) (continuous_locF D v) c) = 0
def localizationH0 (h : H0 rho) : ∀ v : S, H0 (rho.comp (locF D v)) :=
  fun v => resH0 rho (locF D v) h
def localizationH1 (h : H1 rho) : ∀ v : S, H1 (rho.comp (locF D v)) :=
  fun v => resH1 rho (locF D v) (continuous_locF D v) h
def localizationH2 (h : H2 rho) : ∀ v : S, H2 (rho.comp (locF D v)) :=
  fun v => resH2 rho (locF D v) (continuous_locF D v) h
variable (inv : ∀ v : S, H2 ((charRep D.chi).comp (locF D v)) →ₗ[ZMod n] ZMod n)
def poitouTateH0Dual (x : ∀ v : S, H0 (rho.comp (locF D v))) (y : H2 (twDual D.chi rho)) : ZMod n :=
  ∑ v : S, inv v (cupH0H2TwistedDual D.chi rho (locF D v) (x v)
    (resH2 (twDual D.chi rho) (locF D v) (continuous_locF D v) y))
def poitouTateH1Dual (hrho : ContAction rho) (x : ∀ v : S, H1 (rho.comp (locF D v)))
    (y : H1 (twDual D.chi rho)) : ZMod n :=
  ∑ v : S, inv v (cupH1H1TwistedDual D.chi rho (locF D v) (hrho.comp' (continuous_locF D v))
    (resH1 (twDual D.chi rho) (locF D v) (continuous_locF D v) y) (x v))
def poitouTateH2Dual (x : ∀ v : S, H2 (rho.comp (locF D v))) (y : H0 (twDual D.chi rho)) : ZMod n :=
  ∑ v : S, inv v (cup20 D.chi rho (locF D v) (x v) (resH0 (twDual D.chi rho) (locF D v) y))
end PTMaps
section PTMapsAll
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {S : Finset (HeightOneSpectrum (𝓞 F))} {n : ℕ} [NeZero n] (D : GData F Ω S n)
  {M : Type} [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
def IsInvFamily
    (inv : ∀ i : S ⊕ InfinitePlace F, H2 ((charRep D.chi).comp (locHom D i)) →ₗ[ZMod n] ZMod n) :
    Prop :=
  (∀ v : S, Function.Bijective (inv (Sum.inl v))) ∧
  (∀ w : InfinitePlace F, Function.Injective (inv (Sum.inr w)) ∧
    Nat.card (LinearMap.range (inv (Sum.inr w))) ≤ 2) ∧
  ∀ c : H2 (charRep D.chi),
    ∑ i, inv i (resH2 (charRep D.chi) (locHom D i) (continuous_locHom D i) c) = 0
abbrev P0 := (∀ v : S, H0 (rho.comp (locF D v))) × (∀ w : InfinitePlace F, tateH0 (rho.comp (locI D w)))
def localizationH0AllPlaces (h : H0 rho) : P0 D rho :=
  (localizationH0 D rho h, fun w => Submodule.Quotient.mk (resH0 rho (locI D w) h))
def toP0 (x : (∀ v : S, H0 (rho.comp (locF D v))) × (∀ w : InfinitePlace F, H0 (rho.comp (locI D w)))) :
    P0 D rho :=
  (x.1, fun w => Submodule.Quotient.mk (x.2 w))
variable (inv : ∀ i : S ⊕ InfinitePlace F, H2 ((charRep D.chi).comp (locHom D i)) →ₗ[ZMod n] ZMod n)
def poitouTateH0DualAllPlaces (x : (∀ v : S, H0 (rho.comp (locF D v))) × (∀ w : InfinitePlace F, H0 (rho.comp (locI D w))))
    (y : H2 (twDual D.chi rho)) : ZMod n :=
  (∑ v : S, inv (Sum.inl v) (cupH0H2TwistedDual D.chi rho (locF D v) (x.1 v)
    (resH2 (twDual D.chi rho) (locF D v) (continuous_locF D v) y))) +
  ∑ w : InfinitePlace F, inv (Sum.inr w) (cupH0H2TwistedDual D.chi rho (locI D w) (x.2 w)
    (resH2 (twDual D.chi rho) (locI D w) (continuous_locHom D _) y))
def localizationH1AllPlaces (h : H1 rho) : ∀ i : S ⊕ InfinitePlace F, H1 (rho.comp (locHom D i)) :=
  fun i => resH1 rho (locHom D i) (continuous_locHom D i) h
def localizationH2AllPlaces (h : H2 rho) : ∀ i : S ⊕ InfinitePlace F, H2 (rho.comp (locHom D i)) :=
  fun i => resH2 rho (locHom D i) (continuous_locHom D i) h
def poitouTateH1DualAllPlaces (hrho : ContAction rho) (x : ∀ i : S ⊕ InfinitePlace F, H1 (rho.comp (locHom D i)))
    (y : H1 (twDual D.chi rho)) : ZMod n :=
  ∑ i, inv i (cupH1H1TwistedDual D.chi rho (locHom D i) (hrho.comp' (continuous_locHom D i))
    (resH1 (twDual D.chi rho) (locHom D i) (continuous_locHom D i) y) (x i))
def poitouTateH2DualAllPlaces (x : ∀ i : S ⊕ InfinitePlace F, H2 (rho.comp (locHom D i)))
    (y : H0 (twDual D.chi rho)) : ZMod n :=
  ∑ i, inv i (cup20 D.chi rho (locHom D i) (x i) (resH0 (twDual D.chi rho) (locHom D i) y))
end PTMapsAll
section PTFam
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {S : Finset (HeightOneSpectrum (𝓞 F))} {n : ℕ} [NeZero n] (D : GData F Ω S n)
abbrev Delta0Fam : Type 1 := ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M]
  [DiscreteTopology M] (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
  Module.Dual (ZMod n) (H2 (twDual D.chi rho)) →ₗ[ZMod n] H1 rho
abbrev Delta1Fam : Type 1 := ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M]
  [DiscreteTopology M] (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
  Module.Dual (ZMod n) (H1 (twDual D.chi rho)) →ₗ[ZMod n] H2 rho
abbrev ShaFam : Type 1 := ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M]
  [DiscreteTopology M] (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
  Sha1 rho (locHom D) (continuous_locHom D) →ₗ[ZMod n]
    Module.Dual (ZMod n) (Sha2 (twDual D.chi rho) (locHom D) (continuous_locHom D))
def PTNatural (δ0 : Delta0Fam D) (δ1 : Delta1Fam D) : Prop :=
  ∀ (M M' : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] [AddCommGroup M'] [Module (ZMod n) M'] [Finite M'] [TopologicalSpace M']
    [DiscreteTopology M']
    (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (rho' : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M'),
    ContAction rho → ContAction rho' →
    ∀ (u : M →ₗ[ZMod n] M') (hequiv : ∀ g m, u (rho g m) = rho' g (u m)),
      (δ0 M' rho').comp (mapH2TwistedDual D.chi rho rho' u hequiv).dualMap =
          (mapH1OfEquivariant rho rho' u hequiv).comp (δ0 M rho) ∧
        (δ1 M' rho').comp (mapH1TwistedDual D.chi rho rho' u hequiv).dualMap =
          (mapH2OfEquivariant rho rho' u hequiv).comp (δ1 M rho)
variable {M : Type} [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
  (hrho : ContAction rho)
def PTExact
    (inv : ∀ i : S ⊕ InfinitePlace F, H2 ((charRep D.chi).comp (locHom D i)) →ₗ[ZMod n] ZMod n)
    (δ0 : Module.Dual (ZMod n) (H2 (twDual D.chi rho)) →ₗ[ZMod n] H1 rho)
    (δ1 : Module.Dual (ZMod n) (H1 (twDual D.chi rho)) →ₗ[ZMod n] H2 rho) : Prop :=
  Function.Injective (localizationH0AllPlaces D rho) ∧
  (∀ x, (∀ y, poitouTateH0DualAllPlaces D rho inv x y = 0) ↔ ∃ h, localizationH0AllPlaces D rho h = toP0 D rho x) ∧
  (∀ f, δ0 f = 0 ↔ ∃ x, ∀ y, f y = poitouTateH0DualAllPlaces D rho inv x y) ∧
  (∀ h, localizationH1AllPlaces D rho h = 0 ↔ ∃ f, δ0 f = h) ∧
  (∀ x, (∀ y, poitouTateH1DualAllPlaces D rho inv hrho x y = 0) ↔ ∃ h, localizationH1AllPlaces D rho h = x) ∧
  (∀ f, δ1 f = 0 ↔ ∃ x, ∀ y, f y = poitouTateH1DualAllPlaces D rho inv hrho x y) ∧
  (∀ h, localizationH2AllPlaces D rho h = 0 ↔ ∃ f, δ1 f = h) ∧
  (∀ x, (∀ y, poitouTateH2DualAllPlaces D rho inv x y = 0) ↔ ∃ h, localizationH2AllPlaces D rho h = x) ∧
  (∀ f : Module.Dual (ZMod n) (H0 (twDual D.chi rho)), ∃ x, ∀ y, f y = poitouTateH2DualAllPlaces D rho inv x y)
def PTExactOdd (inv : ∀ v : S, H2 ((charRep D.chi).comp (locF D v)) →ₗ[ZMod n] ZMod n)
    (δ0 : Module.Dual (ZMod n) (H2 (twDual D.chi rho)) →ₗ[ZMod n] H1 rho)
    (δ1 : Module.Dual (ZMod n) (H1 (twDual D.chi rho)) →ₗ[ZMod n] H2 rho) : Prop :=
  Function.Injective (localizationH0 D rho) ∧
  (∀ x, (∀ y, poitouTateH0Dual D rho inv x y = 0) ↔ ∃ h, localizationH0 D rho h = x) ∧
  (∀ f, δ0 f = 0 ↔ ∃ x, ∀ y, f y = poitouTateH0Dual D rho inv x y) ∧
  (∀ h, localizationH1 D rho h = 0 ↔ ∃ f, δ0 f = h) ∧
  (∀ x, (∀ y, poitouTateH1Dual D rho inv hrho x y = 0) ↔ ∃ h, localizationH1 D rho h = x) ∧
  (∀ f, δ1 f = 0 ↔ ∃ x, ∀ y, f y = poitouTateH1Dual D rho inv hrho x y) ∧
  (∀ h, localizationH2 D rho h = 0 ↔ ∃ f, δ1 f = h) ∧
  (∀ x, (∀ y, poitouTateH2Dual D rho inv x y = 0) ↔ ∃ h, localizationH2 D rho h = x) ∧
  (∀ f : Module.Dual (ZMod n) (H0 (twDual D.chi rho)), ∃ x, ∀ y, f y = poitouTateH2Dual D rho inv x y)
end PTFam
def PoitouTateDataExists : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n],
  (∀ v : HeightOneSpectrum (𝓞 F), ((n : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) →
    Nonempty (GData F Ω S n)
def GlobalEulerCharacteristic : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n],
  (∀ v : HeightOneSpectrum (𝓞 F), ((n : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) →
  ∀ (D : GData F Ω S n) (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
  [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), ContAction rho →
    Finite (H0 rho) ∧ Finite (H1 rho) ∧ Finite (H2 rho) ∧
    Nat.card (H1 rho) * ∏ w : InfinitePlace F, Nat.card (H0 (rho.comp (locHom D (Sum.inr w)))) =
      Nat.card (H0 rho) * Nat.card (H2 rho) * Nat.card M ^ Module.finrank ℚ F
def GlobalCohomologyVanishesAbove : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n],
  (∀ v : HeightOneSpectrum (𝓞 F), ((n : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) → PTCase F n →
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
  [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), ContAction rho →
    ∀ i, 3 ≤ i → Subsingleton (Hn rho i)
def TateShafarevichDuality : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n],
  (∀ v : HeightOneSpectrum (𝓞 F), ((n : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) →
  ∀ D : GData F Ω S n, ∃ ι : ShaFam D,
    (∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M]
      (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), ContAction rho →
        Finite (Sha1 rho (locHom D) (continuous_locHom D)) ∧ Function.Bijective (ι M rho)) ∧
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M] (M' : Type) [AddCommGroup M'] [Module (ZMod n) M'] [Finite M']
    [TopologicalSpace M'] [DiscreteTopology M']
      (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
      (rho' : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M'),
      ContAction rho → ContAction rho' →
      ∀ (u : M →ₗ[ZMod n] M') (hequiv : ∀ g m, u (rho g m) = rho' g (u m)),
        (ι M' rho').comp (natSha1 rho rho' u hequiv (locHom D) (continuous_locHom D)) =
          (natSha2d D.chi rho rho' u hequiv (locHom D) (continuous_locHom D)).dualMap.comp (ι M rho)
def LocalInvariantsFinitePlaces : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n],
  (∀ v : HeightOneSpectrum (𝓞 F), ((n : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) → PTCase F n →
  ∀ D : GData F Ω S n, ∃ inv : ∀ v : S, H2 ((charRep D.chi).comp (locF D v)) ≃ₗ[ZMod n] ZMod n,
    Recip D (fun v => (inv v).toLinearMap)
def PoitouTateSequenceFinitePlaces : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n],
  (∀ v : HeightOneSpectrum (𝓞 F), ((n : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) → PTCase F n →
  ∀ (D : GData F Ω S n) (inv : ∀ v : S, H2 ((charRep D.chi).comp (locF D v)) ≃ₗ[ZMod n] ZMod n),
  Recip D (fun v => (inv v).toLinearMap) →
  ∃ (δ0 : Delta0Fam D) (δ1 : Delta1Fam D),
    (∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M]
      (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
      (hrho : ContAction rho),
        PTExactOdd D rho hrho (fun v => (inv v).toLinearMap) (δ0 M rho) (δ1 M rho)) ∧
    PTNatural D δ0 δ1
def GlobalCohomologyRealPlaces : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n],
  (∀ v : HeightOneSpectrum (𝓞 F), ((n : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) →
  ∀ (D : GData F Ω S n) (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
  [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), ContAction rho →
    ∀ i, 3 ≤ i → Function.Bijective (fun c : Hn rho i =>
      fun w : {w : InfinitePlace F // w.IsReal} =>
        resHn rho (locI D w.1) (continuous_locHom D _) i c)
def LocalInvariantsAllPlaces : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n],
  (∀ v : HeightOneSpectrum (𝓞 F), ((n : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) →
  ∀ D : GData F Ω S n, ∃ inv : ∀ i : S ⊕ InfinitePlace F,
      H2 ((charRep D.chi).comp (locHom D i)) →ₗ[ZMod n] ZMod n, IsInvFamily D inv
def PoitouTateSequence : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n],
  (∀ v : HeightOneSpectrum (𝓞 F), ((n : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) →
  ∀ (D : GData F Ω S n)
  (inv : ∀ i : S ⊕ InfinitePlace F, H2 ((charRep D.chi).comp (locHom D i)) →ₗ[ZMod n] ZMod n),
  IsInvFamily D inv →
  ∃ (δ0 : Delta0Fam D) (δ1 : Delta1Fam D),
    (∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M]
      (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
      (hrho : ContAction rho), PTExact D rho hrho inv (δ0 M rho) (δ1 M rho)) ∧
    PTNatural D δ0 δ1
def SelmerGroupFormula : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n],
  (∀ v : HeightOneSpectrum (𝓞 F), ((n : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) →
  ∀ (D : GData F Ω S n) (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
  [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
  (hrho : ContAction rho)
  (L : ∀ i : S ⊕ InfinitePlace F, Submodule (ZMod n) (H1 (rho.comp (locHom D i)))),
    Finite (Sel rho (locHom D) (continuous_locHom D) L) ∧
    Finite (Sel (twDual D.chi rho) (locHom D) (continuous_locHom D)
      (perpCond D.chi rho (locHom D) (fun i => hrho.comp' (continuous_locHom D i)) L)) ∧
    Nat.card (Sel rho (locHom D) (continuous_locHom D) L) * Nat.card (H0 (twDual D.chi rho)) *
        ∏ i, Nat.card (H0 (rho.comp (locHom D i))) =
      Nat.card (Sel (twDual D.chi rho) (locHom D) (continuous_locHom D)
          (perpCond D.chi rho (locHom D) (fun i => hrho.comp' (continuous_locHom D i)) L)) *
        Nat.card (H0 rho) * ∏ i, Nat.card (L i)
section LubinTate
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
def intK : Subring (PadicAlgCl p) where
  carrier := {x | x ∈ K ∧ ‖x‖ ≤ 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨K.mul_mem ha hb, ?_⟩
    rw [norm_mul]
    exact mul_le_one₀ ha' (norm_nonneg _) hb'
  one_mem' := ⟨K.one_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨K.add_mem ha hb, (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha' hb')⟩
  zero_mem' := ⟨K.zero_mem, by simp⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨K.neg_mem ha, by rwa [norm_neg]⟩
abbrev OK : Type := intK p K
variable {p K}
def IsUnif (π : OK p K) : Prop :=
  ‖(π : PadicAlgCl p)‖ < 1 ∧ ∀ x : OK p K, ‖(x : PadicAlgCl p)‖ < 1 → ∃ y : OK p K, x = π * y
def resCard (π : OK p K) : ℕ := Nat.card (OK p K ⧸ Ideal.span {π})
def IsLTSeries (π : OK p K) (f : PowerSeries (OK p K)) : Prop :=
  PowerSeries.constantCoeff f = 0 ∧ PowerSeries.coeff 1 f = π ∧
    ∀ k, PowerSeries.coeff k (f - PowerSeries.X ^ resCard π) ∈ Ideal.span {π}
end LubinTate
section FGL
variable {R : Type} [CommRing R]
def IsFGL1 (F : MvPowerSeries (Fin 2) R) : Prop :=
  MvPowerSeries.constantCoeff F = 0 ∧
  MvPowerSeries.coeff (Finsupp.single 0 1) F = 1 ∧
  MvPowerSeries.coeff (Finsupp.single 1 1) F = 1 ∧
  MvPowerSeries.subst (fun i : Fin 2 => if i = 0 then (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R)
    else 0) F = MvPowerSeries.X 0 ∧
  MvPowerSeries.subst (fun i : Fin 2 => if i = 0 then
      MvPowerSeries.subst (fun j : Fin 2 => (MvPowerSeries.X (Fin.castSucc j) :
        MvPowerSeries (Fin 3) R)) F
    else MvPowerSeries.X 2) F =
  MvPowerSeries.subst (fun i : Fin 2 => if i = 0 then (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R)
    else MvPowerSeries.subst (fun j : Fin 2 => (MvPowerSeries.X j.succ :
        MvPowerSeries (Fin 3) R)) F) F ∧
  MvPowerSeries.subst (fun i : Fin 2 => (MvPowerSeries.X (Fin.rev i) : MvPowerSeries (Fin 2) R)) F = F
def atX (g : PowerSeries R) : MvPowerSeries (Fin 2) R := PowerSeries.subst (MvPowerSeries.X 0) g
def atY (g : PowerSeries R) : MvPowerSeries (Fin 2) R := PowerSeries.subst (MvPowerSeries.X 1) g
def IsFGHom (F F' : MvPowerSeries (Fin 2) R) (g : PowerSeries R) : Prop :=
  PowerSeries.subst F g =
    MvPowerSeries.subst (fun i : Fin 2 => if i = 0 then atX g else atY g) F'
end FGL
def LubinTateFormalGroupUnique : Prop := ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
  FiniteDimensional ℚ_[p] K → ∀ π : OK p K, IsUnif π → ∀ f : PowerSeries (OK p K), IsLTSeries π f →
    ∃! F : MvPowerSeries (Fin 2) (OK p K), IsFGL1 F ∧ IsFGHom F F f
def LubinTateEndomorphisms : Prop := ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
  FiniteDimensional ℚ_[p] K → ∀ π : OK p K, IsUnif π → ∀ f : PowerSeries (OK p K), IsLTSeries π f →
    (∀ a : OK p K, ∃! g : PowerSeries (OK p K), PowerSeries.constantCoeff g = 0 ∧
      PowerSeries.coeff 1 g = a ∧ PowerSeries.subst g f = PowerSeries.subst f g) ∧
    ∀ (F : MvPowerSeries (Fin 2) (OK p K)) (g : PowerSeries (OK p K)), IsFGL1 F → IsFGHom F F f →
      PowerSeries.constantCoeff g = 0 → PowerSeries.subst g f = PowerSeries.subst f g →
        IsFGHom F F g
def LubinTateIsomorphism : Prop := ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
  FiniteDimensional ℚ_[p] K → ∀ π : OK p K, IsUnif π → ∀ f g : PowerSeries (OK p K),
  IsLTSeries π f → IsLTSeries π g →
    ∃ θ : PowerSeries (OK p K), PowerSeries.constantCoeff θ = 0 ∧ PowerSeries.coeff 1 θ = 1 ∧
      PowerSeries.subst θ g = PowerSeries.subst f θ ∧
      ∀ Ff Fg : MvPowerSeries (Fin 2) (OK p K), IsFGL1 Ff → IsFGHom Ff Ff f →
        IsFGL1 Fg → IsFGHom Fg Fg g → IsFGHom Ff Fg θ
section Division
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
def ltPoly (π : OK p K) : Polynomial (PadicAlgCl p) :=
  Polynomial.X ^ resCard π + Polynomial.C (π : PadicAlgCl p) * Polynomial.X
def divPts (π : OK p K) (n : ℕ) : Set (PadicAlgCl p) :=
  {x | ((fun P : Polynomial (PadicAlgCl p) => P.comp (ltPoly π))^[n] Polynomial.X).eval x = 0}
def ltExt (π : OK p K) (n : ℕ) : IntermediateField K (PadicAlgCl p) :=
  IntermediateField.adjoin K (divPts π n)
end Division
def LubinTateExtensionStructure : Prop := ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
  FiniteDimensional ℚ_[p] K → ∀ π : OK p K, IsUnif π → ∀ n : ℕ, 1 ≤ n →
    Nat.card (divPts π n) = resCard π ^ n ∧
    FiniteDimensional K (ltExt π n) ∧
    Module.finrank K (ltExt π n) = (resCard π - 1) * resCard π ^ (n - 1) ∧
    IsGalois K (ltExt π n) ∧
    Nonempty ((ltExt π n ≃ₐ[K] ltExt π n) ≃* (OK p K ⧸ Ideal.span {π ^ n})ˣ) ∧
    ∀ x ∈ divPts π n \ divPts π (n - 1),
      ‖x‖ ^ ((resCard π - 1) * resCard π ^ (n - 1)) = ‖(π : PadicAlgCl p)‖
section LTRecip
open ValuativeRel
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
def ltPolyBar (π : K) : Polynomial (AlgebraicClosure K) :=
  Polynomial.X ^ Nat.card 𝓀[K] + Polynomial.C (algebraMap K (AlgebraicClosure K) π) * Polynomial.X
def divPtsBar (π : K) : Set (AlgebraicClosure K) :=
  {x | ∃ m : ℕ, ((fun P : Polynomial (AlgebraicClosure K) => P.comp (ltPolyBar K π))^[m]
    Polynomial.X).eval x = 0}
def rootsPrimeToResChar : Set (AlgebraicClosure K) :=
  {ζ | ∃ m : ℕ, 0 < m ∧ ¬ ringChar 𝓀[K] ∣ m ∧ ζ ^ m = 1}
def ltUrComp (π : K) : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K (divPtsBar K π ∪ rootsPrimeToResChar K)
end LTRecip
open ValuativeRel in

def LubinTateReciprocity : Prop := ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (Art : Kˣ →* Field.absoluteGaloisGroupAbelianization K),
  IsLocalArtinMap K Art → ∀ π : Kˣ, IsUniformiser K (π : K) →
    (∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, toAb K g = Art π →
      ∀ x ∈ divPtsBar K (π : K), g x = x) ∧
    (∀ L : IntermediateField K (AlgebraicClosure K), IsFiniteAbelian K L → L ≤ ltUrComp K (π : K)) ∧
    (∀ x ∈ ltUrComp K (π : K), ∃ L : IntermediateField K (AlgebraicClosure K),
      IsFiniteAbelian K L ∧ x ∈ L)
section Hecke
variable (K : Type) [Field K] [NumberField K]
variable {K}
def infComp (x : Ideles K) (v : InfinitePlace K) : v.Completion := (x : AdeleRing (𝓞 K) K).1 v
def finComp (x : Ideles K) (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K :=
  (x : AdeleRing (𝓞 K) K).2 v
def embC (σ : K →+* ℂ) : (InfinitePlace.mk σ).Completion →+* ℂ := by
  classical
  exact if σ = (InfinitePlace.mk σ).embedding then InfinitePlace.Completion.extensionEmbedding _
    else (starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _)
def IsAlgHecke (χ : Ideles K →* ℂˣ) (n : (K →+* ℂ) → ℤ) : Prop :=
  Continuous χ ∧ (∀ a : Kˣ, χ (diagUnits K a) = 1) ∧
  ∀ x : Ideles K, (∀ v, finComp x v = 1) →
    (∀ σ : K →+* ℂ, (InfinitePlace.mk σ).IsReal → 0 < (embC σ (infComp x (InfinitePlace.mk σ))).re) →
      (χ x : ℂ) = ∏ σ : K →+* ℂ, (embC σ (infComp x (InfinitePlace.mk σ))) ^ n σ
end Hecke
def AlgebraicHeckeCharacterPAdic : Prop := ∀ (K : Type) [Field K] [NumberField K] (χ : Ideles K →* ℂˣ)
  (n : (K →+* ℂ) → ℤ), IsAlgHecke χ n →
  ∃ E : Subfield ℂ, FiniteDimensional ℚ E ∧
    (∀ x : Ideles K, (∀ v, infComp x v = 1) → (χ x : ℂ) ∈ E) ∧
    ∀ (l : ℕ) [Fact l.Prime] (ι : E →+* PadicAlgCl l),
      ∃! ψ : Ideles K →* (PadicAlgCl l)ˣ, Continuous ψ ∧ (∀ a : Kˣ, ψ (diagUnits K a) = 1) ∧
        ∀ x : Ideles K, (∀ v, infComp x v = 1) →
          (∀ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal → finComp x v = 1) →
            ∃ h : (χ x : ℂ) ∈ E, (ψ x : PadicAlgCl l) = ι ⟨(χ x : ℂ), h⟩
theorem contAction_trivial {R G M : Type*} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] :
    ContAction (Representation.trivial R G M) :=
  continuous_snd
example (p : ℕ) [Fact p.Prime] : FiniteDimensional ℚ_[p] (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) :=
  inferInstance
example (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (j : Ω →+* ℂ) : Finite (DecInf F j) ∧ DiscreteTopology (DecInf F j) :=
  ⟨inferInstance, inferInstance⟩
example (F : Type) [Field F] [NumberField F] : PTCase F 1 := Or.inl odd_one
example (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n] :
    ContAction (Representation.trivial (ZMod n) (GK p K) (ZMod n)) :=
  contAction_trivial
end Neutral.B1


