-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PatchingModules_ThetaCoefficientMapEq
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_PatchingModules_ThetaCoefficientMapEq
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:50:51.613381+00:00
-- url     : https://prove2.me/theorems/3b6fb2a2-3753-5b0e-a8a4-2ee1e318ad04
-- title:
--   Theta Coefficient Map Eq
-- statement:
--   Definitions and structural lemmas for Theta Coefficient Map Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/PatchingModules/ThetaCoefficientMapEq.lean

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PatchingModules_PairedDualFirstOrderDualMatrixSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W
open scoped TensorProduct
namespace UpperTheory.V.Pa
variable {l : ℕ} [Fact l.Prime] {L : Loc}
abbrev HomL (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (H : Subgroup Γ) : Type :=
  {φ : H →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set H)}
structure TWGrp (G0 : Glob l L) : Type 1 where
  q : ℕ
  H : OpenNormalSubgroup G0.Γ
  H_η : ∀ g ∈ H, G0.η g = 1
  H_ε : ∀ g ∈ H, PadicInt.toZMod ((G0.ε g : ℤ_[l]ˣ) : ℤ_[l]) = 1
  GN : ℕ → Glob l L
  h : ∀ N, (GN N).Hom G0
  sg : Fin q → G0.G₀
  sg_mem : ∀ j, sg j ∈ G0.frame.G'
  Nq : ℕ → Fin q → ℕ
  Nq_mod : ∀ N j, Nq N j ≡ 1 [MOD l ^ N]
  ph : ∀ N, Fin q → (GN N).G₀
  ta : ∀ N, Fin q → (GN N).G₀
  ph_lim : ∀ (V : OpenNormalSubgroup G0.Γ) j, PL l H.toSubgroup ≤ V.toSubgroup → ∀ᶠ N in atTop, (h N).p (ph N j) * (sg j : G0.Γ)⁻¹ ∈ V
  ph_H : ∀ N j, (h N).p (ph N j) * (sg j : G0.Γ)⁻¹ ∈ H
  ta_ker : ∀ N j, (h N).p (ta N j) = 1
  tame : ∀ N j, (((ta N j ^ Nq N j)⁻¹ * ((ph N j)⁻¹ * ta N j * ph N j) : (GN N).G₀) : (GN N).Γ) ∈
    PL l (H.toSubgroup.comap (h N).p)
  ker_le : ∀ N, (h N).p.ker ≤ (Subgroup.normalClosure (Set.range fun j => (ta N j : (GN N).Γ)) ⊔
    PL l (H.toSubgroup.comap (h N).p)).topologicalClosure
  hb : ℕ
  fin0 : Finite (HomL l H.toSubgroup)
  finN : ∀ N, Finite (HomL l (H.toSubgroup.comap (h N).p)) ∧ Nat.card (HomL l (H.toSubgroup.comap (h N).p)) ≤ hb
  phiV : ∀ v, PhiCond (L.Gv v) l
  phiU : ∀ u, PhiCond (L.Gu u) l
namespace TWGrp
variable {G0 : Glob l L} (T : TWGrp G0)
def ProL : Prop := PL l T.H.toSubgroup = ⊥ ∧ ∀ N, PL l (T.H.toSubgroup.comap (T.h N).p) = ⊥
variable {n : ℕ} (x : NP G0.frame n)
def Eig (al : Fin T.q → Fin n → x.A) : Prop :=
  ∀ j, Function.Injective (al j) ∧ (mat x.ρ (T.sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))
variable {x} (k : Kap x)
def B1 (D0 : ℕ) : Prop :=
  ∃ C : ℕ, ∀ m, ∀ᶠ N in atTop, (Sel1 (T.h N) (x.Am m) k).Finite ∧
    (Sel1 (T.h N) (x.Am m) k).ncard ≤ (Bd1 (T.h N) (x.Am m) k).ncard * Nat.card x.K ^ (m * D0 + C)
def B2 : Prop :=
  ∃ C : ℕ, ∀ m, ∀ᶠ N in atTop, ∀ z : Fin (k.g + 1) → Fin k.g → (T.GN N).G₀ → Matrix (Fin n) (Fin n) (x.Am m),
    (∀ i j, z i j ∈ SelP (T.h N) x (x.Am m)) → ∃ c : Fin (k.g + 1) → x.A, (∃ i, IsUnit (c i)) ∧
      ∃ Ψ ∈ Sel2 (T.h N) (x.Am m) k, ∀ j γ a b, (Ψ γ a b).ep' j = (x.t ^ C • ∑ i, c i • z i j γ) a b
end TWGrp
section Oo
variable {G G0 : Glob l L} (h : G.Hom G0) {n : ℕ} {x : NP G0.frame n} (k : Kap x)
def K1 (D0 : ℕ) : Prop :=
  ∀ (e : ℕ) (z : Fin e → G.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)), (∀ i, z i ∈ Sel1 h x.A k) →
    (∀ c : Fin e → x.A, ∑ i, c i • z i ∈ Bd1 h x.A k → c = 0) → e ≤ D0
def K2 : Prop :=
  ∀ z : Fin (k.g + 1) → Fin k.g → G.G₀ → Matrix (Fin n) (Fin n) x.A, (∀ i j, z i j ∈ SelP h x x.A) →
    ∃ c : Fin (k.g + 1) → x.A, c ≠ 0 ∧ ∃ Ψ ∈ Sel2 h x.A k, ∀ j γ a b, (Ψ γ a b).ep' j = (∑ i, c i • z i j γ) a b
def K3 : Prop :=
  ∀ z ∈ SelM h x x.A, ∃ (s : ℕ) (c : Fin k.g → x.A), (x.t ^ s • z - ∑ j, c j • fun γ => k.κ j (h.p₀ γ)) ∈ BdM h x x.A
end Oo
section Q
variable {R G : Type} [CommRing R] [Group G] {n : ℕ}
def q1El (ph : G) (u : Fin n → R) : MonoidAlgebra R G :=
  (List.ofFn fun i => MonoidAlgebra.single ph (1 : R) - MonoidAlgebra.single 1 (u i)).prod
def q2El (ph ta : G) (u : Fin n → R) (i : Fin n) (y : R) : MonoidAlgebra R G :=
  (List.ofFn fun k => if k = i then 1 else MonoidAlgebra.single ph (1 : R) - MonoidAlgebra.single 1 (u k)).prod *
    (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 y)
def fEl {q : ℕ} (Nq : Fin q → ℕ) (u : Fin q → Fin n → R) : R :=
  ∏ j, ∏ i, ∏ i' ∈ Finset.univ.erase i, (u j i - u j i') * (u j i - (Nq j : R) * u j i')
def spIdeal {q : ℕ} (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) : Ideal (MvPowerSeries (Fin q × Fin n) R) :=
  Ideal.span {z | ∃ j k, z = ((∏ i, (Polynomial.X - Polynomial.C (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i)))) -
    (P j).map (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R)).coeff k}
def Sp {q : ℕ} (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) : Type :=
  MvPowerSeries (Fin q × Fin n) R ⧸ spIdeal P ut
instance {q : ℕ} (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) : CommRing (Sp P ut) :=
  inferInstanceAs (CommRing (MvPowerSeries (Fin q × Fin n) R ⧸ spIdeal P ut))
instance {q : ℕ} (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) {A : Type} [CommRing A] [Algebra A R] :
    Algebra A (Sp P ut) :=
  inferInstanceAs (Algebra A (MvPowerSeries (Fin q × Fin n) R ⧸ spIdeal P ut))
instance {q : ℕ} (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) {A : Type} [CommRing A] [Algebra A R] :
    IsScalarTower A R (Sp P ut) :=
  inferInstanceAs (IsScalarTower A R (MvPowerSeries (Fin q × Fin n) R ⧸ spIdeal P ut))
def Sp.mk {q : ℕ} (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) : MvPowerSeries (Fin q × Fin n) R →ₐ[R] Sp P ut :=
  Ideal.Quotient.mkₐ R (spIdeal P ut)
def Sp.u {q : ℕ} (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) (j : Fin q) (i : Fin n) : Sp P ut :=
  Sp.mk P ut (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i))
def delIdeal (l : ℕ) (R : Type) [CommRing R] {q : ℕ} (n : ℕ) (a : Fin q → ℕ) : Ideal (MvPowerSeries (Fin q × Fin n) R) :=
  Ideal.span (Set.range fun p : Fin q × Fin n => (1 + MvPowerSeries.X p) ^ l ^ a p.1 - 1)
end Q
section Gens
variable {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n}
  {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B)
def pairGens : Set (MonoidAlgebra B F.G₀) :=
  {z | ∃ v g, z = F.oEl v (u.ψ v) g ∨ z = F.star O B n (F.oEl v (u.ψ v) g)} ∪
    {z | ∃ w, ∃ g ∈ r.Ip w, z = MonoidAlgebra.single g 1 - 1 ∨ z = F.star O B n (MonoidAlgebra.single g 1) - 1}
def qGens {q : ℕ} (ph ta : Fin q → F.G₀) (U y : Fin q → Fin n → B) : Set (MonoidAlgebra B F.G₀) :=
  {z | ∃ j, z = q1El (ph j) (U j) ∨ z = F.star O B n (q1El (ph j) (U j))} ∪
    {z | ∃ j i, z = q2El (ph j) (ta j) (U j) i (y j i) ∨ z = F.star O B n (q2El (ph j) (ta j) (U j) i (y j i))}
def pairVals : Set B :=
  {b | ∃ i g, b = u.D.lam i (MonoidAlgebra.single g 1)} ∪ {b | ∃ v i g, b = ((u.ψ v i g : Bˣ) : B)}
def augmentationIdealKernel : Set (MonoidAlgebra B F.G₀) := {z | z ∈ u.D.chBar (pairGens u)}
def StOrTh (q : Ideal B) : Prop := DiscSt u.D q ∨ NonSS (augmentationIdealKernel u) (RingHom.id B) q
end Gens
structure WtVars (L : Loc) (O : Type) (n D : ℕ) where
  v : Fin D → L.Vl
  i : Fin D → Fin n
  γ : ∀ k, L.Gv (v k)
  c : Fin D → O
section Aut
abbrev abelian₂ (O : Type) [CommRing O] (σ : Type) (D : ℕ) : Type := MvPowerSeries (σ ⊕ Fin D) O
abbrev Sinf (O : Type) [CommRing O] (σ : Type) (D q n : ℕ) : Type := MvPowerSeries (Fin q × Fin n) (abelian₂ O σ D)
variable {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid G0.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B)
  (σ : Type) (D : ℕ)
structure TWBase : Type 1 where
  wt : WtVars L O n D
  wt_res : ∀ k, residue O (wt.c k) * (r.psib (wt.v k) (wt.i k) (wt.γ k) : ResidueField O) = 1
  lam : abelian₂ O σ D →ₐ[O] B
  segmentWeightExponent : ∀ k, lam (MvPowerSeries.X (.inr k)) = algebraMap O B (wt.c k) * (u.ψ (wt.v k) (wt.i k) (wt.γ k) : B) - 1
  M : Type
  [addM : AddCommGroup M]
  [modB : Module B M]
  [modL : Module (abelian₂ O σ D) M]
  smul_lam : ∀ (a : abelian₂ O σ D) (m : M), a • m = lam a • m
  free : Module.Free (abelian₂ O σ D) M
  fin : Module.Finite (abelian₂ O σ D) M
  supp : ∀ p : Ideal B, p.IsPrime → (Module.annihilator B M ≤ p ↔ J ≤ p)
attribute [instance] TWBase.addM TWBase.modB TWBase.modL
abbrev SpAt {q : ℕ} (g : Fin q → G0.G₀) (ut : Fin q → Fin n → O) : Type :=
  Sp (fun j => u.D.chi (MonoidAlgebra.single (g j) 1)) fun j i => algebraMap O B (ut j i)
variable {u J σ D} (b : TWBase u J σ D) {G : Glob l L} (h : G.Hom G0) {q : ℕ} (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀)
  (ut : Fin q → Fin n → O)
structure TWRing (N : ℕ) : Type 1 where
  rN : Resid G.frame O n
  compat : Glob.Compat h rN r
  R : Type
  [ring : CommRing R]
  [alg : Algebra O R]
  [co : IsCO O R]
  p : Pair rN R
  s : Sinf O σ D q n →ₐ[O] R
  s_w : ∀ k, s (MvPowerSeries.C (MvPowerSeries.X (.inr k))) =
    algebraMap O R (b.wt.c k) * (p.ψ (b.wt.v k) (b.wt.i k) (b.wt.γ k) : R) - 1
  U : Fin q → Fin n → R
  U_res : ∀ j i, U j i - algebraMap O R (ut j i) ∈ maximalIdeal R
  M : Type
  [add : AddCommGroup M]
  [mod : Module R M]
  a : Fin q → ℕ
  le_a : ∀ j, N ≤ a j
  rk : ℕ
  e : M ≃+ (Fin rk → Sinf O σ D q n ⧸ delIdeal l (abelian₂ O σ D) n a)
  e_smul : ∀ z m, e (s z • m) = z • e m
attribute [instance] TWRing.ring TWRing.alg TWRing.co TWRing.add TWRing.mod
variable {b h ut} {N : ℕ} (A : TWRing b h ut N)
abbrev TWRing.X : Type := A.M ⧸ (Ideal.span (Set.range fun p => A.s (MvPowerSeries.X p)) • ⊤ : Submodule A.R A.M)
structure TWMaps (ex : ℕ) where
  θ : A.R →ₐ[O] SpAt u (fun j => h.p₀ (ph j)) ut
  θ_pair : A.p.Maps θ.toRingHom ((u.D.comap h.p₀).map (algebraMap B _)) fun v i => pushCh (algebraMap B _) (u.ψ v i)
  theta_coefficientMap_eq : ∀ z, θ (A.s z) = algebraMap B _ (b.lam (MvPowerSeries.constantCoeff z))
  θ_U : ∀ j i, θ (A.U j i) = Sp.u _ _ j i
  φ : SpAt u (fun j => h.p₀ (ph j)) ut ⊗[B] b.M →+ A.X
  ψ : A.X →+ SpAt u (fun j => h.p₀ (ph j)) ut ⊗[B] b.M
  φ_smul : ∀ (t : A.R) z, φ (θ t • z) = t • φ z
  ψ_smul : ∀ (t : A.R) z, ψ (t • z) = θ t • ψ z
  φψ : ∀ z, φ (ψ z) = fEl Nq A.U • z
  ψφ : ∀ z, ψ (φ z) = θ (fEl Nq A.U) • z
  rel1 : ∀ j (g : G.G₀) (m : A.M), (fEl Nq A.U * A.p.D.tr (MonoidAlgebra.single g 1 * q1El (ph j) (A.U j))) ^ ex • m = 0
  rel2 : ∀ j i (g : G.G₀) (m : A.M), (fEl Nq A.U *
    A.p.D.tr (MonoidAlgebra.single g 1 * q2El (ph j) (ta j) (A.U j) i (A.s (MvPowerSeries.X (j, i))))) ^ ex • m = 0
variable (u J σ D) in

structure TWAut (T : TWGrp G0) : Type 1 where
  b : TWBase u J σ D
  ut : Fin T.q → Fin n → O
  ut_res : ∀ j i, residue O (ut j i) = r.chib i (T.sg j)
  A : ∀ N, TWRing b (T.h N) ut N
  ex : ℕ
  m : ∀ N, TWMaps (T.Nq N) (T.ph N) (T.ta N) (A N) ex
end Aut
section Det
variable {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X]
def epsD (g : F.Γ) : DD X k.g := algebraMap x.A (DD X k.g) (algebraMap ℤ_[l] x.A (F.ε g : ℤ_[l]))
def TwZ : Set (F.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) :=
  {z | (∀ g, z g ∈ pairedDualFirstOrderDualMatrixSpace n x.A X k.g x.a) ∧ (∀ i j, AdicCont (Ideal.span {algebraMap x.A (DD X k.g) x.t}) fun g => z g i j) ∧
    (∀ g h, z (g * h) = z g + epsD k X g • (k.ρ1 X g * z h * k.ρ1 X g⁻¹)) ∧
    ∀ g, z (F.conj g) = -(epsD k X F.c • (z g)ᵀ)}
def TwB : Set (F.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) :=
  {z | ∃ Y ∈ pairedDualFirstOrderDualMatrixSpace n x.A X k.g x.a, -(epsD k X F.c • Yᵀ) = Y ∧
    z = fun g : F.G₀ => epsD k X g • (k.ρ1 X g * Y * k.ρ1 X g⁻¹) - Y}
def ell (σ : F.G₀) (z : F.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) : X := (z σ * k.ρ1 X σ).trace.eta
def Detects (S : Set F.G₀) : Prop :=
  ∀ z ∈ TwZ k x.A, (∀ σ ∈ S, ell k x.A σ z = 0) → ∃ s : ℕ, x.t ^ s • z ∈ TwB k x.A
end Det
def Close {Ph A B : Type} [Group Ph] [Group A] [Group B] (π : Ph →* A) (π' : Ph →* B) (V : Subgroup Ph) (a : A) (b : B) : Prop :=
  ∃ g g', π g = a ∧ π' g' = b ∧ g⁻¹ * g' ∈ V
structure Lim {G0 : Glob l L} (T : TWGrp G0) : Type 1 where
  Ph : Type
  [grp : Group Ph]
  [top : TopologicalSpace Ph]
  [tgrp : IsTopologicalGroup Ph]
  [cpt : CompactSpace Ph]
  [tdisc : TotallyDisconnectedSpace Ph]
  fg : ∃ s : Finset Ph, (Subgroup.closure (s : Set Ph)).topologicalClosure = ⊤
  U : Ultrafilter ℕ
  U_le : (U : Filter ℕ) ≤ atTop
  π : ∀ N, Ph →* (T.GN N).Γ
  π_cont : ∀ N, Continuous (π N)
  π_surj : ∀ N, Function.Surjective (π N)
  G : Glob l L
  h : G.Hom G0
  πo : Ph →* G.Γ
  πo_cont : Continuous πo
  πo_surj : Function.Surjective πo
  modH : ∀ N g, (T.h N).p (π N g) * (h.p (πo g))⁻¹ ∈ T.H
  ct : Ph
  ct_N : ∀ N, π N ct = (T.GN N).c
  ct_o : πo ct = G.c
  ker_lim : ∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in U, (π N).ker ⊔ V.toSubgroup = πo.ker ⊔ V.toSubgroup
  p_lim : ∀ V : OpenNormalSubgroup G0.Γ, ∀ᶠ N in U, ∀ g, (T.h N).p (π N g) * (h.p (πo g))⁻¹ ∈ V
  φ_lim : ∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in U, ∀ v g, Close (π N) πo V.toSubgroup ((T.GN N).φ v g) (G.φ v g)
  φu_lim : ∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in U, ∀ w g, Close (π N) πo V.toSubgroup ((T.GN N).φu w g) (G.φu w g)
  ph : Fin T.q → G.G₀
  ta : Fin T.q → G.G₀
  ph_lim : ∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in U, ∀ j, Close (π N) πo V.toSubgroup (T.ph N j) (ph j)
  ta_lim : ∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in U, ∀ j, Close (π N) πo V.toSubgroup (T.ta N j) (ta j)
  comm : ∀ j, ph j * ta j = ta j * ph j
  p_ph : ∀ j, h.p₀ (ph j) = T.sg j
  p_ta : ∀ j, h.p₀ (ta j) = 1
attribute [instance] Lim.grp Lim.top Lim.tgrp Lim.cpt Lim.tdisc
end UpperTheory.V.Pa


