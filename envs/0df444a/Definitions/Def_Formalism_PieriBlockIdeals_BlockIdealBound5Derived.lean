-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
-- name    : Formalism_PieriBlockIdeals_BlockIdealBound5Derived
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:02.791711+00:00
-- url     : https://prove2.me/theorems/5924df3d-ab7d-485a-8f7d-ce18b84b32ed
-- title:
--   Block Ideal Bound5 Derived
-- statement:
--   Definitions and structural lemmas for Block Ideal Bound5 Derived, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/BlockIdealBound5Derived.lean

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_PieriBlockIdeals_StatementC
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWAssembled
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial CategoryTheory CategoryTheory.Limits
namespace Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
def nablaWtR (R : Type) [CommRing R] (r : ℕ) (ν μ : Fin r → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin r) R) :=
  dualWeyl R r r ν ⊓ weightedHomogeneousSubmodule R (rowW r r) μ
def ExpLeRing : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ),
    (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) → ExpLe l r ν μ e →
    ∀ x ∈ nablaWtR R r ν μ, (l : R) ^ e • x ∈ weyl R r r le_rfl ν
def ExpLeRingComp : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ),
    (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) → ExpLe l r ν μ e →
    ∀ x ∈ dualWeyl R r r ν, weightedHomogeneousComponent (rowW r r) μ x ∈ dualWeyl R r r ν ∧
      (l : R) ^ e • weightedHomogeneousComponent (rowW r r) μ x ∈ weyl R r r le_rfl ν
def DepthNonneg : Prop :=
  ∀ (r c : ℕ) (ν μ : Fin r → ℕ), Antitone ν → nablaWt r ν μ ≠ ⊥ →
    ∑ a, μ a = ∑ a, ν a ∧ 0 ≤ depth2 (res r (varpi c)) ν μ
def ApplicationWindow : Prop :=
  LemmaDLastGraded → ∀ (l k j t q h : ℕ) (lam : ℕ → ℕ) (xm xp : ℤ), l.Prime → 1 ≤ t →
    (∀ a b, a ≤ b → b < k + j + t + q → lam b ≤ lam a) →
    (∀ a, k + j ≤ a → a < k + j + t → lam a = lam (k + j)) →
    lam 0 + (k + j + t + q) ≤ h + lam (k + j + t + q - 1) + 1 → h < l ^ 2 →
    (∀ a, a < k → xm ≤ UN (k + j + t + q) lam a ∧ UN (k + j + t + q) lam a ≤ xp) →
    (∀ a, k ≤ a → a < k + j → UN (k + j + t + q) lam a < xm) →
    UN (k + j + t + q) lam (k + j) < xm → xm ≤ xp → xp - UN (k + j + t + q) lam (k + j) ≤ (h : ℤ) →
    ∀ ecl : ℕ, (∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ ecl) →
      ∀ I : ℕ, ExpUpTo l (k + j + t + q) lam (varpi (k + j)) (I : ℤ)
        ⌊cPrime l k j t q h ecl xm xp (UN (k + j + t + q) lam (k + j)) (I : ℝ)⌋₊
def chainB {O : Type} [CommRing O] {ι : Type} [DecidableEq ι] {Nb : ι → Type} [∀ τ, AddCommGroup (Nb τ)]
    [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)) (s : Finset ι) : ∀ τ, Submodule O (Nb τ) :=
  fun τ => if τ ∈ s then ⊤ else B τ
def atFactor {O : Type} [CommRing O] {ι : Type} [DecidableEq ι] {Nb : ι → Type} [∀ τ, AddCommGroup (Nb τ)]
    [∀ τ, Module O (Nb τ)] (τ : ι) (p : Nb τ →ₗ[O] Nb τ) : (⨂[O] τ, Nb τ) →ₗ[O] (⨂[O] τ, Nb τ) :=
  PiTensorProduct.map (Function.update (fun _ => LinearMap.id) τ p)
def AtFactorTprod : Prop :=
  ∀ (O : Type) [CommRing O] (ι : Type) [Fintype ι] [DecidableEq ι] (Nb : ι → Type)
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (τ : ι) (p : Nb τ →ₗ[O] Nb τ) (x : ∀ τ, Nb τ),
    atFactor τ p (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ (p (x τ)))
def TensorWeightKill : Prop :=
  ∀ (O : Type) [CommRing O] (ι : Type) [Fintype ι] [DecidableEq ι] (Nb : ι → Type)
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)) (s : Finset ι) (a : ι)
    (p : Nb a →ₗ[O] Nb a) (l : O) (c : ℕ), a ∉ s → (∀ x, l ^ c • p x ∈ B a) →
    ∀ y ∈ tensSub (chainB B (insert a s)), l ^ c • atFactor a p y ∈ tensSub (chainB B s)
def ChainEnds : Prop :=
  ∀ (O : Type) [CommRing O] (ι : Type) [Fintype ι] [DecidableEq ι] (Nb : ι → Type)
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)),
    tensSub (chainB B ∅) = tensSub B ∧ tensSub (chainB B Finset.univ) = ⊤
def ChainMono : Prop :=
  ∀ (O : Type) [CommRing O] (ι : Type) [Fintype ι] [DecidableEq ι] (Nb : ι → Type)
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)) (s s' : Finset ι),
    s ⊆ s' → tensSub (chainB B s) ≤ tensSub (chainB B s')
def TensorProjKill : Prop :=
  ∀ (R : Type) [CommRing R] (P X P' : Type) [AddCommGroup P] [Module R P] [AddCommGroup X] [Module R X]
    [AddCommGroup P'] [Module R P'] (p : X →ₗ[R] X) (l : R) (c : ℕ), (∀ x : X, l ^ c • p x = 0) →
    ∀ z : P ⊗[R] (X ⊗[R] P'),
      l ^ c • TensorProduct.map LinearMap.id (TensorProduct.map p LinearMap.id) z = 0
def scaleSub {O : Type} [CommRing O] (A : Type) [Ring A] [Algebra O A] (V : Type) [AddCommGroup V]
    [Module O V] [Module A V] [IsScalarTower O A V] (c : O) : Submodule A V where
  carrier := {x | ∃ y : V, x = c • y}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩; exact ⟨y + z, by rw [smul_add]⟩
  smul_mem' := by rintro a _ ⟨y, rfl⟩; exact ⟨a • y, by rw [smul_comm]⟩
def IsSubquot (A : Type) [Ring A] (V G : Type) [AddCommGroup V] [Module A V] [AddCommGroup G]
    [Module A G] : Prop :=
  ∃ (E : Submodule A V) (ψ : E →ₗ[A] G), Function.Surjective ψ
def PowQuotient : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (V : Type) [AddCommGroup V]
    [Module O V] [Module A V] [IsScalarTower O A V] (ϖ : O) (a : ℕ),
    ∃ φ : (V ⧸ scaleSub A V ϖ) →ₗ[A]
        (scaleSub A V (ϖ ^ a) ⧸ (scaleSub A V (ϖ ^ (a + 1))).comap (scaleSub A V (ϖ ^ a)).subtype),
      (∀ v : V, φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk ⟨ϖ ^ a • v, v, rfl⟩) ∧
      Function.Surjective φ ∧ ((∀ v : V, ϖ • v = 0 → v = 0) → Function.Injective φ)
def SimpleSubquotOfPower : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (V : Type) [AddCommGroup V]
    [Module O V] [Module A V] [IsScalarTower O A V] (ϖ : O) (n : ℕ) (F F' : Submodule A V),
    F ≤ F' → scaleSub A V (ϖ ^ n) ≤ F → IsSimpleModule A (F' ⧸ F.comap F'.subtype) →
    IsSubquot A (V ⧸ scaleSub A V ϖ) (F' ⧸ F.comap F'.subtype)
def SubquotIso : Prop :=
  ∀ (A : Type) [Ring A] (V G G' : Type) [AddCommGroup V] [Module A V] [AddCommGroup G] [Module A G]
    [AddCommGroup G'] [Module A G'], Nonempty (G ≃ₗ[A] G') → IsSubquot A V G → IsSubquot A V G'
def repOf (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    {K : Subgroup G} (jK : K →* A) (W : Type) [AddCommGroup W] [Module O W] [Module A W]
    [IsScalarTower O A W] : Representation O K W :=
  ((Algebra.lsmul O O W : A →ₐ[O] Module.End O W) : A →* Module.End O W).comp jK
abbrev Forms (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) (W : Type) [AddCommGroup W] [Module O W]
    [Module A W] [IsScalarTower O A W] : Submodule O (G → W) :=
  AMFK O Γ K (repOf O jK W)
def RepOfApply : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (G : Type) [Group G] (K : Subgroup G)
    (jK : K →* A) (W : Type) [AddCommGroup W] [Module O W] [Module A W] [IsScalarTower O A W]
    (κ : K) (w : W), repOf O jK W κ w = jK κ • w
def HeckeStable (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) (T : Type) [CommRing T] (V : Type)
    [AddCommGroup V] [Module O V] [Module A V] [IsScalarTower O A V] [Module T (Forms O Γ jK V)] :
    Prop :=
  ∀ (U : Submodule A V) (t : T) (f : Forms O Γ jK V), (∀ g, (f : G → V) g ∈ U) →
    ∀ g, ((t • f : Forms O Γ jK V) : G → V) g ∈ U
def HeckeNat (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) (T : Type) [CommRing T] (V W : Type)
    [AddCommGroup V] [Module O V] [Module A V] [IsScalarTower O A V] [AddCommGroup W] [Module O W]
    [Module A W] [IsScalarTower O A W] [Module T (Forms O Γ jK V)] [Module T (Forms O Γ jK W)] :
    Prop :=
  ∀ (U : Submodule A V) (ψ : U →ₗ[A] W) (t : T) (f : Forms O Γ jK V) (φ : Forms O Γ jK W)
    (hf : ∀ g, (f : G → V) g ∈ U) (hf' : ∀ g, ((t • f : Forms O Γ jK V) : G → V) g ∈ U),
    (∀ g, (φ : G → W) g = ψ ⟨(f : G → V) g, hf g⟩) →
    ∀ g, ((t • φ : Forms O Γ jK W) : G → W) g = ψ ⟨((t • f : Forms O Γ jK V) : G → V) g, hf' g⟩
def FormsStep : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (G : Type) [Group G] (Γ K : Subgroup G)
    (jK : K →* A) (T : Type) [CommRing T] (V W : Type) [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [AddCommGroup W] [Module O W] [Module A W] [IsScalarTower O A W]
    [Module T (Forms O Γ jK V)] [Module T (Forms O Γ jK W)] (S : Submonoid T)
    (F F' : Submodule A V) (ψ : F' →ₗ[A] W),
    HeckeStable O Γ jK T V → HeckeNat O Γ jK T V W → (∀ x : F', ψ x = 0 → (x : V) ∈ F) →
    Subsingleton (LocalizedModule S (Forms O Γ jK W)) →
    ∀ f : Forms O Γ jK V, (∀ g, (f : G → V) g ∈ F') →
      ∃ s ∈ S, ∀ g, ((s • f : Forms O Γ jK V) : G → V) g ∈ F
def FormsDevissage : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (G : Type) [Group G] (Γ K : Subgroup G)
    (jK : K →* A) (T : Type) [CommRing T] (V : Type) [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module T (Forms O Γ jK V)] (S : Submonoid T) (D₀ : Submodule O V)
    (D E : Submodule A V), IsNoetherian O V → IsArtinian O (V ⧸ D₀) → D₀ ≤ D.restrictScalars O →
    D ≤ E →
    (∀ F F' : Submodule A V, D ≤ F → F ⋖ F' → F' ≤ E →
      ∀ f : Forms O Γ jK V, (∀ g, (f : G → V) g ∈ F') →
        ∃ s ∈ S, ∀ g, ((s • f : Forms O Γ jK V) : G → V) g ∈ F) →
    ∀ f : Forms O Γ jK V, (∀ g, (f : G → V) g ∈ E) →
      ∃ s ∈ S, ∀ g, ((s • f : Forms O Γ jK V) : G → V) g ∈ D
def cTau {ι : Type} [DecidableEq ι] (T2 : Finset ι) (ex c' : ι → ℕ) (τ : ι) : ℕ :=
  if τ ∈ T2 then min (ex τ) (c' τ) else ex τ
def TheoremWCore : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (G : Type) [Group G] (Γ K : Subgroup G)
    (jK : K →* A) (ι : Type) [Fintype ι] [DecidableEq ι] (Nb : ι → Type) [∀ τ, AddCommGroup (Nb τ)]
    [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)) [Module A (⨂[O] τ, Nb τ)]
    [IsScalarTower O A (⨂[O] τ, Nb τ)] (T : Type) [CommRing T] [Algebra O T]
    [Module T (Forms O Γ jK (⨂[O] τ, Nb τ))] [IsScalarTower O T (Forms O Γ jK (⨂[O] τ, Nb τ))]
    (S : Submonoid T) (l ϖ : O) (n₀ : ℕ) (ω : Type) (pr : ∀ τ, ω → Nb τ →ₗ[O] Nb τ) (e : ι → ω → A)
    (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)] [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)]
    [∀ μ, IsScalarTower O A (L μ)] [∀ μ, Module T (Forms O Γ jK (L μ))]
    (hwt : Λ → ι → ω) (depth : ι → ω → ℤ) (i : ι → ℤ) (T2 : Finset ι) (ex c' : ι → ℕ),
    IsNoetherian O (⨂[O] τ, Nb τ) → IsArtinian O ((⨂[O] τ, Nb τ) ⧸ tensSub B) → l ∣ ϖ ^ n₀ →
    (∀ (s : Finset ι) (a : A), ∀ x ∈ tensSub (chainB B s), a • x ∈ tensSub (chainB B s)) →
    (∀ τ w (x : ⨂[O] τ, Nb τ), e τ w • x = atFactor τ (pr τ w) x) →
    HeckeStable O Γ jK T (⨂[O] τ, Nb τ) → (∀ μ, HeckeNat O Γ jK T (⨂[O] τ, Nb τ) (L μ)) →
    (∀ (Gm : Type) [AddCommGroup Gm] [Module A Gm], IsSimpleModule A Gm →
      IsSubquot A ((⨂[O] τ, Nb τ) ⧸ scaleSub A (⨂[O] τ, Nb τ) ϖ) Gm → ∃ μ, Nonempty (Gm ≃ₗ[A] L μ)) →
    (∀ μ τ, ∃ z : L μ, e τ (hwt μ τ) • z ≠ 0) →
    (∀ μ, IsSubquot A ((⨂[O] τ, Nb τ) ⧸ scaleSub A (⨂[O] τ, Nb τ) ϖ) (L μ) →
      ¬ Subsingleton (LocalizedModule S (Forms O Γ jK (L μ))) → ∀ τ ∈ T2, depth τ (hwt μ τ) ≤ i τ) →
    (∀ τ, LatIncl l (B τ) (ex τ)) →
    (∀ τ ∈ T2, ∀ w, depth τ w ≤ i τ → ∀ x : Nb τ, l ^ c' τ • pr τ w x ∈ B τ) →
    ∀ y : LocalizedModule S (Forms O Γ jK (⨂[O] τ, Nb τ)),
      (algebraMap O T l) ^ (∑ τ, cTau T2 ex c' τ) • y ∈
        locSet S {x : Forms O Γ jK (⨂[O] τ, Nb τ) |
          (x : G → ⨂[O] τ, Nb τ) ∈ formsIn Γ K (repOf O jK (⨂[O] τ, Nb τ)) (tensSub B)}
abbrev NablaT (O : Type) [CommRing O] (N : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) : Type :=
  ⨂[O] τ : ι, dualWeyl O N N (res N (lam τ))
def deltaIn (O : Type) [CommRing O] (N : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) (τ : ι) :
    Submodule O (dualWeyl O N N (res N (lam τ))) :=
  (weyl O N N le_rfl (res N (lam τ))).comap (dualWeyl O N N (res N (lam τ))).subtype
def depthAt (N k : ℕ) {ι : Type} (j : ι → ℕ) (lam : ι → ℕ → ℕ) (τ : ι) (w : Fin N → ℕ) : ℤ :=
  depth2 (res N (varpi (k + j τ))) (res N (lam τ)) w
def cFloor (l N k t h : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) (j q : ι → ℕ) (xm xp : ι → ℤ) (ecl i : ι → ℕ)
    (τ : ι) : ℕ :=
  ⌊cPrime l k (j τ) t (q τ) h (ecl τ) (xm τ) (xp τ) (UN N (lam τ) (k + j τ)) (i τ : ℝ)⌋₊
structure Shape (N k j t q h : ℕ) (lam : ℕ → ℕ) (xm xp : ℤ) : Prop where
  what₂ : k + j + t + q = N
  anti : ∀ a b, a ≤ b → b < N → lam b ≤ lam a
  block : ∀ a, k + j ≤ a → a < k + j + t → lam a = lam (k + j)
  spread : lam 0 + N ≤ h + lam (N - 1) + 1
  cloud : ∀ a, a < k → xm ≤ UN N lam a ∧ UN N lam a ≤ xp
  lows : ∀ a, k ≤ a → a < k + j → UN N lam a < xm
  above : UN N lam (k + j) < xm
  le : xm ≤ xp
  top : xp - UN N lam (k + j) ≤ (h : ℤ)
def TopInputs (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) {ι : Type} [DecidableEq ι] (l N k t h : ℕ)
    (lam : ι → ℕ → ℕ) (T2 : Finset ι) (j q : ι → ℕ) (xm xp : ι → ℤ) (ecl ex i : ι → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] (T : Type) [CommRing T]
    [Module T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin N → ℕ) → A) {Λ : Type} (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin N → ℕ) : Prop :=
  l.Prime ∧ (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : O)) ∧ Finite (O ⧸ Ideal.span {(l : O)}) ∧
  (l : O) ∣ ϖ ^ n₀ ∧ h < l ^ 2 ∧ 1 ≤ t ∧
  (∀ τ ∈ T2, Shape N k (j τ) t (q τ) h (lam τ) (xm τ) (xp τ)) ∧
  (∀ τ ∈ T2, ∀ μ : Fin k → ℕ, ExpLe l k (res k (lam τ)) μ (ecl τ)) ∧
  (∀ τ, LA.InclZ N N le_rfl (res N (lam τ)) l (ex τ)) ∧
  (∀ (s : Finset ι) (a : A), ∀ x ∈ tensSub (chainB (deltaIn O N lam) s),
    a • x ∈ tensSub (chainB (deltaIn O N lam) s)) ∧
  (∀ τ w (x : ∀ τ, dualWeyl O N N (res N (lam τ))) (y : dualWeyl O N N (res N (lam τ))),
    (y : MvPolynomial (Fin N × Fin N) O) =
      weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O) →
    e τ w • PiTensorProduct.tprod O x = PiTensorProduct.tprod O (Function.update x τ y)) ∧
  HeckeStable O Γ jK T (NablaT O N lam) ∧ (∀ μ, HeckeNat O Γ jK T (NablaT O N lam) (L μ)) ∧
  (∀ (Gm : Type) [AddCommGroup Gm] [Module A Gm], IsSimpleModule A Gm →
    IsSubquot A (NablaT O N lam ⧸ scaleSub A (NablaT O N lam) ϖ) Gm → ∃ μ, Nonempty (Gm ≃ₗ[A] L μ)) ∧
  (∀ μ τ, ∃ z : L μ, e τ (hwt μ τ) • z ≠ 0) ∧
  (∀ μ, IsSubquot A (NablaT O N lam ⧸ scaleSub A (NablaT O N lam) ϖ) (L μ) →
    ¬ Subsingleton (LocalizedModule S (Forms O Γ jK (L μ))) →
    ∀ τ ∈ T2, depthAt N k j lam τ (hwt μ τ) ≤ (i τ : ℤ))
def TopIncl (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) {ι : Type} (l N : ℕ) (lam : ι → ℕ → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] {T : Type} [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (J : ℕ) : Prop :=
  ∀ y : LocalizedModule S (Forms O Γ jK (NablaT O N lam)),
    (algebraMap O T (l : O)) ^ J • y ∈
      locSet S {x : Forms O Γ jK (NablaT O N lam) |
        (x : G → NablaT O N lam) ∈ formsIn Γ K (repOf O jK (NablaT O N lam)) (tensSub (deltaIn O N lam))}
def TheoremWTop : Prop :=
  LemmaDLastGraded →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (A : Type) [Ring A] [Algebra O A]
    (G : Type) [Group G] (Γ K : Subgroup G) (jK : K →* A) (ι : Type) [Fintype ι] [DecidableEq ι]
    (l N k t h : ℕ) (lam : ι → ℕ → ℕ) (T2 : Finset ι) (j q : ι → ℕ) (xm xp : ι → ℤ) (ecl ex i : ι → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] (T : Type) [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O N lam))]
    [IsScalarTower O T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin N → ℕ) → A) (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin N → ℕ),
    TopInputs O A Γ jK l N k t h lam T2 j q xm xp ecl ex i T S ϖ n₀ e L hwt →
    TopIncl O Γ jK l N lam S (∑ τ, cTau T2 ex (cFloor l N k t h lam j q xm xp ecl i) τ) ∧
    sInf {J : ℕ | TopIncl O Γ jK l N lam S J} ≤
      ∑ τ, cTau T2 ex (cFloor l N k t h lam j q xm xp ecl i) τ
open Formalism.RankGapBounds.ChebyshevFactorialBounds in

def CPrimeLeCW5 : Prop :=
  ∀ (ι : Type) (D : Data ι) (τ : ι) (l : ℕ), l.Prime → τ ∈ D.T2 → D.Params →
    cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ) (D.depth τ l : ℝ) ≤
      Cor.coefficientBoundTau D τ l
def LogPlusVsMax : Prop :=
  ∀ (l h : ℕ) (i : ℝ), 1 ≤ h → h < l → 0 < i →
    (i / (l : ℝ)) * max 0 (1 + Real.log ((h : ℝ) / (l : ℝ))) <
      (i / (l : ℝ)) * (1 + Real.posLog ((h : ℝ) / (l : ℝ)))
open Formalism.RankGapBounds.ChebyshevFactorialBounds in

def JointEstimate : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι), D.Params →
    (∀ l : ℕ, l.Prime → l ∉ D.Exc → D.lJ < (l : ℝ) → D.h + D.Nr < l ^ 2 → D.Nr + 1 < l →
      D.t + 2 * D.kap l < l →
      D.J l ≤ ∑ τ, cTau D.T2 (fun τ => D.ex τ l) (fun τ =>
        ⌊cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ)
          (D.depth τ l : ℝ)⌋₊) τ) →
    Cor.BlockIdealBound5 D
open Formalism.RankGapBounds.ChebyshevFactorialBounds in

def BlockIdealAt : Prop :=
  LemmaDLastGraded →
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι) (l : ℕ)
    (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (A : Type) [Ring A] [Algebra O A]
    (G : Type) [Group G] (Γ K : Subgroup G) (jK : K →* A) (lam : ι → ℕ → ℕ)
    [Module A (NablaT O D.Nr lam)] [IsScalarTower O A (NablaT O D.Nr lam)] (T : Type) [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O D.Nr lam))]
    [IsScalarTower O T (Forms O Γ jK (NablaT O D.Nr lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin D.Nr → ℕ) → A) (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin D.Nr → ℕ),
    D.Params →
    TopInputs O A Γ jK l D.Nr D.k D.t D.h lam D.T2 D.j D.q D.xlo D.xhi (fun τ => D.ecl τ l)
      (fun τ => D.ex τ l) (fun τ => D.depth τ l) T S ϖ n₀ e L hwt →
    (∀ τ ∈ D.T2, D.maxB τ = UN D.Nr (lam τ) (D.k + D.j τ)) →
    D.J l ≤ sInf {J : ℕ | TopIncl O Γ jK l D.Nr lam S J} →
    (D.J l : ℝ) ≤ ∑ τ, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (Cor.coefficientBoundTau D τ l) else (D.ex τ l : ℝ))
def WeightSpacePrimePowerBoundOverDomain : Prop :=
  LemmaDLastGraded → ∀ (R : Type) [CommRing R] [IsDomain R] (l N k j t q h : ℕ) (lam : ℕ → ℕ)
    (xm xp : ℤ) (ecl : ℕ), l.Prime → (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) → h < l ^ 2 → 1 ≤ t →
    Shape N k j t q h lam xm xp → (∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ ecl) →
    ∀ (I : ℕ) (w : Fin N → ℕ), depth2 (res N (varpi (k + j))) (res N lam) w ≤ (I : ℤ) →
      ∀ x ∈ nablaWtR R N (res N lam) w,
        (l : R) ^ ⌊cPrime l k j t q h ecl xm xp (UN N lam (k + j)) (I : ℝ)⌋₊ • x ∈
          weyl R N N le_rfl (res N lam)
def ExpLeOfInclZ : Prop :=
  ∀ (r : ℕ) (ν μ : Fin r → ℕ) (l e : ℕ), LA.InclZ r r le_rfl ν l e → ExpLe l r ν μ e
def ExactExponentsFit : Prop :=
  ∀ (l N k : ℕ) (lam : ℕ → ℕ), l.Prime → Antitone (res N lam) → Antitone (res k lam) →
    LA.InclZ N N le_rfl (res N lam) l (LA.exZ N N le_rfl (res N lam) l) ∧
      ∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ (LA.exZ k k le_rfl (res k lam) l)
def TopInclMono : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (G : Type) [Group G] (Γ K : Subgroup G)
    (jK : K →* A) (ι : Type) (l N : ℕ) (lam : ι → ℕ → ℕ) [Module A (NablaT O N lam)]
    [IsScalarTower O A (NablaT O N lam)] (T : Type) [CommRing T] [Algebra O T]
    [Module T (Forms O Γ jK (NablaT O N lam))] [IsScalarTower O T (Forms O Γ jK (NablaT O N lam))]
    (S : Submonoid T) (J J' : ℕ), J ≤ J' → TopIncl O Γ jK l N lam S J → TopIncl O Γ jK l N lam S J'
def cFloorCoarse (l N k t h : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) (j q : ι → ℕ) (xm xp : ι → ℤ)
    (ecl i : ι → ℕ) (τ : ι) : ℕ :=
  ⌊cCoarse l k (j τ) t (q τ) h N (ecl τ) (xm τ) (xp τ) (UN N (lam τ) (k + j τ)) (i τ : ℝ)⌋₊
def TheoremWTopCoarse : Prop :=
  LemmaDLastGraded →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (A : Type) [Ring A] [Algebra O A]
    (G : Type) [Group G] (Γ K : Subgroup G) (jK : K →* A) (ι : Type) [Fintype ι] [DecidableEq ι]
    (l N k t h : ℕ) (lam : ι → ℕ → ℕ) (T2 : Finset ι) (j q : ι → ℕ) (xm xp : ι → ℤ) (ecl ex i : ι → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] (T : Type) [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O N lam))]
    [IsScalarTower O T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin N → ℕ) → A) (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin N → ℕ),
    TopInputs O A Γ jK l N k t h lam T2 j q xm xp ecl ex i T S ϖ n₀ e L hwt →
    TopIncl O Γ jK l N lam S (∑ τ, cTau T2 ex (cFloorCoarse l N k t h lam j q xm xp ecl i) τ)
open Formalism.RankGapBounds.ChebyshevFactorialBounds in

def BlockIdealBound5Derived : Prop :=
  LemmaDLastGraded →
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι), D.Params →
    (∀ l : ℕ, l.Prime → l ∉ D.Exc → D.lJ < (l : ℝ) → D.h + D.Nr < l ^ 2 → D.Nr + 1 < l →
      D.t + 2 * D.kap l < l →
      ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsNoetherianRing O) (A : Type) (_ : Ring A)
        (_ : Algebra O A) (G : Type) (_ : Group G) (Γ K : Subgroup G) (jK : K →* A) (lam : ι → ℕ → ℕ)
        (_ : Module A (NablaT O D.Nr lam)) (_ : IsScalarTower O A (NablaT O D.Nr lam)) (T : Type)
        (_ : CommRing T) (_ : Algebra O T) (_ : Module T (Forms O Γ jK (NablaT O D.Nr lam)))
        (_ : IsScalarTower O T (Forms O Γ jK (NablaT O D.Nr lam))) (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
        (e : ι → (Fin D.Nr → ℕ) → A) (Λ : Type) (L : Λ → Type) (_ : ∀ μ, AddCommGroup (L μ))
        (_ : ∀ μ, Module O (L μ)) (_ : ∀ μ, Module A (L μ)) (_ : ∀ μ, IsScalarTower O A (L μ))
        (_ : ∀ μ, Module T (Forms O Γ jK (L μ))) (hwt : Λ → ι → Fin D.Nr → ℕ),
        TopInputs O A Γ jK l D.Nr D.k D.t D.h lam D.T2 D.j D.q D.xlo D.xhi (fun τ => D.ecl τ l)
          (fun τ => D.ex τ l) (fun τ => D.depth τ l) T S ϖ n₀ e L hwt ∧
        (∀ τ ∈ D.T2, D.maxB τ = UN D.Nr (lam τ) (D.k + D.j τ)) ∧
        D.J l ≤ sInf {J : ℕ | TopIncl O Γ jK l D.Nr lam S J}) →
    Cor.BlockIdealBound5 D
def DepthAsU : Prop :=
  ∀ (N c : ℕ) (lam : ℕ → ℕ) (w : Fin N → ℕ),
    depth2 (res N (varpi c)) (res N lam) w =
      ∑ a ∈ Finset.univ.filter (fun a : Fin N => (a : ℕ) < c),
        (UN N lam a - ((w a : ℤ) + (N : ℤ) - 1 - ((a : ℕ) : ℤ)))
def WEDepth : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (k j t q l h : ℕ) (F : Type) [Field F] [CharP F l]
    (W : WData ι t (k + j + t + q) F) (U U' : ι → Fin (k + j + t + q) → ℤ) (bot cst : ι → ℤ)
    (kap : ι → Fin t → ℤ) (c : ι → ℕ) (τ : ι) (lam : ℕ → ℕ) (w : Fin (k + j + t + q) → ℕ),
    l.Prime → t + 2 * (h / (l - 1)) < l →
    WProps W σ l U' bot kap c →
    (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ (h : ℤ)) →
    (∀ i (s : Fin t), 0 ≤ (l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s ∧
      (l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s ≤ (h : ℤ)) →
    (∀ i, StrictAnti (U i)) → (∀ i, StrictAnti (U' i)) →
    (∀ i (s : Fin t), ∃ a, U i a = bot i + ((s : ℕ) : ℤ)) →
    (∀ i, (∏ a, (Polynomial.X + Polynomial.C (((U i a + cst i : ℤ)) : F))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' i a + cst i : ℤ)) : F))) →
    (∀ a, 0 ≤ U τ a) → (∀ a, 0 ≤ U' τ a ∧ U' τ a ≤ (h : ℤ)) → ∑ a, U τ a = ∑ a, U' τ a →
    (∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
      U τ a = bot τ + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)) →
    (c τ : ℤ) = ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)),
      U' τ a →
    (∀ a, U τ a = UN (k + j + t + q) lam a) →
    (∀ a, U' τ a = (w a : ℤ) + ((k + j + t + q : ℕ) : ℤ) - 1 - ((a : ℕ) : ℤ)) →
    depth2 (res (k + j + t + q) (varpi (k + j))) (res (k + j + t + q) lam) w ≤
      ((q * h + (l * mwCount l (bot (σ τ)) t (h / (l - 1)) (Finset.univ.image (U (σ τ))) +
        mwCount l (bot τ) t (h / (l - 1)) (Finset.univ.image (U τ))) * (t + 2 * (h / (l - 1))) : ℕ) : ℤ)
def FilteredMap : Prop :=
  ∀ (C D : Type 1) [Category.{0} C] [Category.{0} D] [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (P : C → Prop) (P' : D → Prop),
    (∀ X, P X → P' (F.obj X)) → ∀ Y, Filtered P Y → Filtered P' (F.obj Y)
def FilteredExt : Prop :=
  ∀ (C : Type 1) [Category.{0} C] [Abelian C] (P : C → Prop) (S : ShortComplex C), S.ShortExact →
    Filtered P S.X₁ → Filtered P S.X₃ → Filtered P S.X₂
def FilteredTrans : Prop :=
  ∀ (C : Type 1) [Category.{0} C] [Abelian C] (P : C → Prop) (Y : C),
    Filtered (Filtered P) Y → Filtered P Y
def FilteredMapFiltered : Prop :=
  ∀ (C D : Type 1) [Category.{0} C] [Category.{0} D] [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (P : C → Prop) (P' : D → Prop),
    (∀ X, P X → Filtered P' (F.obj X)) → ∀ Y, Filtered P Y → Filtered P' (F.obj Y)
end Formalism.CohomologicalDescent.DepthNonnegative


