-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PatchingModules_PatchedSupportCompletions
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_PatchingModules_PatchedSupportCompletions
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T17:01:25.808979+00:00
-- url     : https://prove2.me/theorems/60644d8e-d811-48ae-a0f9-0254c572e54d
-- title:
--   Patched Support Completions
-- statement:
--   Definitions and structural lemmas for Patched Support Completions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/PatchingModules/PatchedSupportCompletions.lean

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PatchingModules_ThetaCoefficientMapEq
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_AlgebraTools_IsCplAtSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools
namespace UpperTheory.V.Pa
class IsCoef (l : outParam ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop where
  complete : IsAdicComplete (maximalIdeal O) O
  finite : Finite (ResidueField O)
  char : CharP (ResidueField O) l
def S4 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0), T.ProL → Nonempty (Lim T)
def CohLim : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (x : NP G0.frame n) (k : Kap x)
    (al : Fin T.q → Fin n → x.A) (D0 : ℕ), l ≠ 2 → T.ProL → T.Eig x al → T.B1 k D0 → T.B2 k →
    K1 Λ.h k D0 ∧ K2 Λ.h k ∧ K3 Λ.h k
section S5
variable {Λ R σ : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing R] (s : MvPowerSeries σ Λ →+* R)
def kjIdeal (Λ σ : Type) [CommRing Λ] [IsLocalRing Λ] (k j : ℕ) : Ideal (MvPowerSeries σ Λ) :=
  Ideal.span (Set.range MvPowerSeries.X) ^ k ⊔ (maximalIdeal Λ ^ j).map (MvPowerSeries.C : Λ →+* MvPowerSeries σ Λ)
structure PatchedSupportCompletions (ii : Ideal R) (ann : Ideal R) {ι : Type} (q : ι → Ideal R) (d : ℕ) : Type 1 where
  B : ι → Type
  [ring : ∀ i, CommRing (B i)]
  [loc : ∀ i, IsLocalRing (B i)]
  [alg : ∀ i, Algebra (R ⧸ ii) (B i)]
  cpl : ∀ i, IsCplAt (R ⧸ ii) ((q i).map (Ideal.Quotient.mk ii)) (B i)
  S : ∀ i, Ideal (B i)
  dim : ∀ i, ∀ P ∈ (S i).minimalPrimes, (d : WithBot ℕ∞) ≤ ringKrullDim (B i ⧸ P)
  fib : ∀ i (Q : Ideal (B i)), Q.IsPrime → (∀ a, algebraMap (R ⧸ ii) (B i) (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q) →
    (S i ≤ Q ↔ ann ≤ (Q.comap (algebraMap (R ⧸ ii) (B i))).comap (Ideal.Quotient.mk ii))
  move : ∀ i i' (Z Q : Ideal (B i)), Z.IsPrime → Q.IsPrime → S i ≤ Z → Z ≤ Q →
    (∀ a, algebraMap (R ⧸ ii) (B i) (Ideal.Quotient.mk ii (s (MvPowerSeries.X a))) ∈ Q) →
    (Q.comap (algebraMap (R ⧸ ii) (B i))).comap (Ideal.Quotient.mk ii) ≤ q i' →
    ∃ Z' : Ideal (B i'), Z'.IsPrime ∧ S i' ≤ Z' ∧
      Z'.comap (algebraMap (R ⧸ ii) (B i')) = Z.comap (algebraMap (R ⧸ ii) (B i))
attribute [instance] PatchedSupportCompletions.ring PatchedSupportCompletions.loc PatchedSupportCompletions.alg
end S5
def S5 : Prop :=
  ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ]
    [Finite (ResidueField Λ)] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Fintype σ]
    (s : MvPowerSeries σ Λ →+* R) (U : Ultrafilter ℕ) (f : R) (ii : Ideal R)
    (M : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)]
    (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Free Λ X] [Module.Finite Λ X],
    (U : Filter ℕ) ≤ atTop →
    (∀ (a : Λ) (x : X), a • x = s (MvPowerSeries.C a) • x) → (∀ a (x : X), s (MvPowerSeries.X a) • x = 0) →
    (∀ k j, ∀ᶠ N in U, ∃ (r : ℕ) (e : (M N ⧸ ((kjIdeal Λ σ k j).map s • ⊤ : Submodule R (M N))) ≃+
      (Fin r → MvPowerSeries σ Λ ⧸ kjIdeal Λ σ k j)), ∀ a m, e (s a • m) = a • e m) →
    (∀ j, ∀ᶠ N in U, ∃ (φ : (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) →ₗ[R]
        (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N))))
      (ψ : (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N))) →ₗ[R]
        (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))),
      (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) →
    (∃ (e : ℕ) (Gs : Set R), Ideal.span Gs = ii ∧ ∀ r ∈ Gs, ∀ j, ∀ᶠ N in U, ∃ a : R,
      (f * r) ^ e - a ∈ maximalIdeal R ^ j ∧ ∀ m : M N, a • m = 0) →
    ∀ (ι : Type) (q : ι → Ideal R) (d : ℕ), (∀ i, (q i).IsPrime ∧ ii ≤ q i ∧ f ∉ q i ∧ ∀ a, s (MvPowerSeries.X a) ∈ q i) →
    (∀ i, ∃ (La : Type) (_ : CommRing La) (_ : IsLocalRing La) (_ : Algebra Λ La),
      IsCplAt Λ ((q i).comap (s.comp MvPowerSeries.C)) La ∧ IsRegularLocalRing La ∧ ringKrullDim La = d) →
    Nonempty (PatchedSupportCompletions s ii (Module.annihilator R X) q (d + Fintype.card σ))
section URep
variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) {n : ℕ} (x : NP G0.frame n)
  {B : Type} [CommRing B] [IsLocalRing B] (D : GDet n B G.G₀) (I : Set (MonoidAlgebra B G.G₀))
  (Bh : Type) [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] (rF : Bh →+* FractionRing x.A) (e : G.G₀ →* Bˣ)
structure URep : Type 1 where
  AA : Type
  [ring : CommRing AA]
  [alg : Algebra Bh AA]
  [algB : Algebra B AA]
  [tower : IsScalarTower B Bh AA]
  fin : Module.Finite Bh AA
  inj : Function.Injective (algebraMap Bh AA)
  N : Submodule Bh AA
  compl : _root_.IsCompl (1 : Submodule Bh AA) N
  mul_mem : ∀ a ∈ N, ∀ b ∈ N, ∃ c ∈ maximalIdeal Bh, a * b = algebraMap Bh AA c
  typeI : x.a = n → N = ⊥
  vr : G.G₀ →* Matrix (Fin n) (Fin n) AA
  span : Submodule.span Bh (Set.range vr) = blkMat n x.a (1 : Submodule Bh AA) N
  det : D.map (algebraMap B AA) = GDet.ofRep vr
  form : ∀ g, (vr g)ᵀ * vr (G.frame.conj g) = algebraMap B AA (e g ^ (1 - (n : ℤ)) : Bˣ) • (1 : Matrix (Fin n) (Fin n) AA)
  red : ∀ g i j (b : Bh), vr g i j - algebraMap Bh AA b ∈ N → rF b = algebraMap x.A _ (mat x.ρ (h.p₀ g) i j)
  kills : ∀ z ∈ I, GDet.repAlg vr AA (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B AA) z) = 0
  thick : ∀ Q : Ideal Bh, Q.IsPrime → NonSS I (algebraMap B Bh) Q → Module.annihilator Bh N ≤ Q
  P : Submodule B (Matrix (Fin n) (Fin n) AA)
  ker_le_span_sub_sup_map : P.FG
  vr_mem : ∀ g, vr g ∈ P
  cont : ∀ j : ℕ, ∃ V : OpenNormalSubgroup G.G₀, ∀ g, ∀ v ∈ V, vr (g * v) - vr g ∈ maximalIdeal B ^ j • P
attribute [instance] URep.ring URep.alg URep.algB URep.tower
end URep
section Oo
variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) {n : ℕ} (x : NP G0.frame n)
  {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n}
  {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B)
structure OoPt where
  fg : ∃ s : Finset G.Γ, (Subgroup.closure (s : Set G.Γ)).topologicalClosure = ⊤
  Ip : ∀ w, r.Ip w = G.frame.Iu w
  surj : Function.Surjective (algebraMap O x.K)
  q : ℕ
  ph : Fin q → G.G₀
  ta : Fin q → G.G₀
  comm : ∀ j, ph j * ta j = ta j * ph j
  p_ta : ∀ j, h.p₀ (ta j) = 1
  U : Fin q → Fin n → B
  y : Fin q → Fin n → B
  s : B
  q1 : ∀ j g, u.D.tr (MonoidAlgebra.single g 1 * q1El (ph j) (U j)) = 0
  q2 : ∀ j i g, u.D.tr (MonoidAlgebra.single g 1 * q2El (ph j) (ta j) (U j) i (y j i)) = 0
  gen : GenBy O (pairVals u ∪ {b | ∃ j i, b = U j i ∨ b = y j i} ∪ {s})
  f : B →ₐ[O] x.A
  maps : u.Maps f.toRingHom (GDet.ofRep (mat (x.ρ.comp h.p₀))) x.ψ
  f_s : f s = x.t
  f_y : ∀ j i, f (y j i) = 0
  f_U : ∀ j, Function.Injective fun i => f (U j i)
  eig : ∀ j, (mat x.ρ (h.p₀ (ph j))).charpoly = ∏ i, (Polynomial.X - Polynomial.C (f (U j i)))
variable {h x u}
def OoPt.ker (P : OoPt h x u) : Set (MonoidAlgebra B G.G₀) :=
  {z | z ∈ u.D.chBar (pairGens u ∪ qGens (O := O) (F := G.frame) P.ph P.ta P.U P.y)}
end Oo
def S6 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K]
    (r : Resid G.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (P : OoPt h x u)
    (Bh : Type) [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] (rF : Bh →+* FractionRing x.A), l ≠ 2 →
    IsCplAt B (RingHom.ker P.f) Bh → (∀ b, rF (algebraMap B Bh b) = algebraMap x.A _ (P.f b)) →
    RingHom.ker rF = maximalIdeal Bh → Nonempty (URep h x u.D P.ker Bh rF (G.frame.eps O B))
def GalOut : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K]
    (r : Resid G.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (P : OoPt h x u)
    (Bh : Type) [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] (D0 : ℕ), l ≠ 2 →
    IsCplAt B (RingHom.ker P.f) Bh → K1 h k D0 → K2 h k → K3 h k →
    ∀ Z Q : Ideal Bh, Z.IsPrime → Q.IsPrime → DiscSt (u.D.map (algebraMap B Bh)) Z →
      ((1 + D0 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (Bh ⧸ Z) →
      DiscSt (u.D.map (algebraMap B Bh)) Q ∨ NonSS P.ker (algebraMap B Bh) Q → Z ≤ Q
section Chain
variable {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} (T : TWGrp G0) {n : ℕ}
  {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {r : Resid G0.frame O n}
  {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B)
structure Pt (D0 : ℕ) : Type 1 where
  x : NP G0.frame n
  [alg : Algebra O x.K]
  k : Kap x
  al : Fin T.q → Fin n → x.A
  eig : T.Eig x al
  b1 : T.B1 k D0
  b2 : T.B2 k
  f : B →ₐ[O] x.A
  maps : u.Maps f.toRingHom (GDet.ofRep (mat x.ρ)) x.ψ
attribute [instance] Pt.alg
def Adapted : Prop :=
  (∀ g : G0.G₀, (g : G0.Γ) ∈ T.H → ∀ i, r.chib i g = 1) ∧ ∀ w, r.Ip w = G0.frame.Iu w
def ChainConcl (J : Ideal B) {h : ℕ} (p : Fin (h + 1) → Ideal B) : Prop :=
  ∀ e : Fin h → Ideal B,
    (∀ i, (e i).IsPrime ∧ NonSS (augmentationIdealKernel u) (RingHom.id B) (e i) ∧ e i ≤ p i.castSucc ∧ e i ≤ p i.succ) →
    (∃ q₁ : Ideal B, q₁.IsPrime ∧ DiscSt u.D q₁ ∧ J ≤ q₁ ∧ q₁ ≤ p 0) →
    ∀ q : Ideal B, q.IsPrime → q ≤ p (Fin.last h) → StOrTh u q → J ≤ q
end Chain
def Core : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O]
    (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ)
    (A : TWAut u J Unit D T), l ≠ 2 → T.ProL → Adapted T (r := r) →
    GenBy O (pairVals u ∪ {A.b.lam (MvPowerSeries.X (.inl ()))}) →
    ∀ (h : ℕ) (x : Fin (h + 1) → Pt T u (D + n * T.q)),
      (∀ i, Function.Surjective (algebraMap O (x i).x.K) ∧ (x i).f (A.b.lam (MvPowerSeries.X (.inl ()))) = (x i).x.t) →
      ChainConcl u J fun i => RingHom.ker (x i).f
def CoreBC : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O]
    (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ)
    (_A : TWAut u J Empty D T), l ≠ 2 → T.ProL → Adapted T (r := r) → GenBy O (pairVals u) →
    ∀ (h : ℕ) (x : Fin (h + 1) → Pt T u (D + n * T.q)), (∀ i, Nat.card (x i).x.K = Nat.card (x 0).x.K) →
      ChainConcl u J fun i => RingHom.ker (x i).f
def Raw : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O]
    (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ)
    (_A : TWAut u J Empty D T), l ≠ 2 → Adapted T (r := r) → GenBy O (pairVals u) →
    ∀ (h : ℕ) (x : Fin (h + 1) → Pt T u (D + n * T.q)), (∀ i, Nat.card (x i).x.K = Nat.card (x 0).x.K) →
      ChainConcl u J fun i => RingHom.ker (x i).f
def Detection : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x), l ≠ 2 →
    (∃ g : F.G₀, PadicInt.toZMod ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) →
    ∀ S : Set F.G₀, S ⊆ F.G' → (F.G' : Set F.G₀) ⊆ closure S → Detects k S
def NP.Ext {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A) : Prop :=
  Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ x'.ρ = pushRep j x.ρ ∧ x'.a = x.a ∧ ∀ v i, x'.ψ v i = pushCh j (x.ψ v i)
def Choice : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n h : ℕ) (x : Fin (h + 1) → NP F n), l ≠ 2 → PhiCond F.Γ l →
    (∃ g : F.G₀, PadicInt.toZMod ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) → (∀ i, (x i).N3) →
    ∃ (q : ℕ) (sg : Fin q → F.G₀) (x' : Fin (h + 1) → NP F n) (j : ∀ i, (x i).A →+* (x' i).A) (k : ∀ i, Kap (x' i))
      (al : ∀ i, Fin q → Fin n → (x' i).A), (∀ a, sg a ∈ F.G') ∧ (∀ i, (x i).Ext (x' i) (j i)) ∧
      (∀ i, Nat.card (x' i).K = Nat.card (x' 0).K) ∧ (∀ i, Detects (k i) (Set.range sg)) ∧
      ∀ i a, Function.Injective (al i a) ∧
        (mat (x' i).ρ (sg a)).charpoly = ∏ b, (Polynomial.X - Polynomial.C (al i a b))
end UpperTheory.V.Pa


