-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:51.291548+00:00
-- url     : https://prove2.me/theorems/6382117e-cff0-4658-842b-f33b5467b520
-- title:
--   Projection Surjective
-- statement:
--   Definitions and structural lemmas for Projection Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ProjectionSurjective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing Matrix
namespace GlobalTheory.Pat
structure Point {Φ : Frame} (G : PolGp Φ) where
  a : ℕ
  a_pos : 0 < a
  a_le : a ≤ Φ.n
  r : G.Γ →* Matrix (Fin Φ.n) (Fin Φ.n) Φ.A
  cont : ∀ i j, ContM Φ.A (fun g => r g i j)
  block : ∀ g (i j : Fin Φ.n), ¬ ((i : ℕ) < a ↔ (j : ℕ) < a) → r g i j = 0
  pol : ∀ g, r (G.sig g) * (r g)ᵀ = Φ.jA ((G.mu g : Φ.Oˣ) : Φ.O) • (1 : Matrix (Fin Φ.n) (Fin Φ.n) Φ.A)
  triv : ∀ u g, r (G.iu u g) = 1
  psi : ∀ v, Fin Φ.n → (Φ.Gv v →* Φ.Aˣ)
  P : Φ.Vl → GL (Fin Φ.n) Φ.A
  P_block : ∀ v (j : Fin Φ.n), (∀ i : Fin Φ.n, (i : ℕ) < a → (P v : Matrix (Fin Φ.n) (Fin Φ.n) Φ.A) i j = 0) ∨
    (∀ i : Fin Φ.n, ¬ (i : ℕ) < a → (P v : Matrix (Fin Φ.n) (Fin Φ.n) Φ.A) i j = 0)
  tri : ∀ v g (i j : Fin Φ.n), j < i →
    ((((P v)⁻¹ : GL (Fin Φ.n) Φ.A) : Matrix (Fin Φ.n) (Fin Φ.n) Φ.A) * r (G.iv v g) *
      (P v : Matrix (Fin Φ.n) (Fin Φ.n) Φ.A)) i j = 0
  diag : ∀ v g (i : Fin Φ.n),
    ((((P v)⁻¹ : GL (Fin Φ.n) Φ.A) : Matrix (Fin Φ.n) (Fin Φ.n) Φ.A) * r (G.iv v g) *
      (P v : Matrix (Fin Φ.n) (Fin Φ.n) Φ.A)) i i = ((psi v i g : Φ.Aˣ) : Φ.A)
  psi_inj : ∀ v, Function.Injective (psi v)
  span : ∀ X : Matrix (Fin Φ.n) (Fin Φ.n) Φ.F,
    (∀ i j : Fin Φ.n, ¬ ((i : ℕ) < a ↔ (j : ℕ) < a) → X i j = 0) →
    X ∈ Submodule.span Φ.F (Set.range fun g => (r g).map (algebraMap Φ.A Φ.F))
def IsPtMap {Φ : Frame} {G : PolGp Φ} (R : Pair G) (x : Point G) (φ : R.B →+* Φ.A) : Prop :=
  IsLocalHom φ ∧ φ.comp R.j = Φ.jA ∧
    R.D.map φ = GDet.ofRep x.r ∧
    ∀ v i g, φ ((R.psi v i g : R.Bˣ) : R.B) = ((x.psi v i g : Φ.Aˣ) : Φ.A)
section Selmer
variable {Φ : Frame} {Gb : PolGp Φ} (x : Point Gb) {G : PolGp Φ} (p : Mor G Gb)
  (R : Type) [CommRing R] [Algebra Φ.A R]
abbrev Mat (Φ : Frame) (R : Type) : Type := Matrix (Fin Φ.n) (Fin Φ.n) R
def act (g : G.Γ) (X : Mat Φ R) : Mat Φ R :=
  (x.r (p.p g)).map (algebraMap Φ.A R) * X * (x.r (p.p g⁻¹)).map (algebraMap Φ.A R)
def cob (Y : Mat Φ R) : G.Γ → Mat Φ R := fun g => act x p R g Y - Y
def cobSub : Submodule R (G.Γ → Mat Φ R) := Submodule.span R (Set.range (cob x p R))
variable {R}
def IsPlus (X : Mat Φ R) : Prop := ∀ i j : Fin Φ.n, ¬ ((i : ℕ) < x.a ↔ (j : ℕ) < x.a) → X i j = 0
def IsMinus (X : Mat Φ R) : Prop := ∀ i j : Fin Φ.n, ((i : ℕ) < x.a ↔ (j : ℕ) < x.a) → X i j = 0
def inFlag (v : Φ.Vl) (X : Mat Φ R) : Mat Φ R :=
  (((x.P v)⁻¹ : GL (Fin Φ.n) Φ.A) : Mat Φ Φ.A).map (algebraMap Φ.A R) * X *
    (x.P v : Mat Φ Φ.A).map (algebraMap Φ.A R)
def InB (v : Φ.Vl) (X : Mat Φ R) : Prop := ∀ i j : Fin Φ.n, j < i → inFlag x v X i j = 0
def PolTriv (f : G.Γ → Mat Φ R) : Prop :=
  (∀ g, f (G.sig g) = -(f g)ᵀ) ∧ ∀ u g, f (G.iu u g) = 0
def IsCoc (f : G.Γ → Mat Φ R) : Prop := ∀ g h, f (g * h) = f g + act x p R g (f h)
def SelP (al : G.Γ → Mat Φ R) (Y : Φ.Vl → Mat Φ R) : Prop :=
  IsCoc x p al ∧ PolTriv al ∧ (∀ g, IsPlus x (al g)) ∧ (∀ v, IsPlus x (Y v)) ∧
  (∀ v g, InB x v (al (G.iv v g) - cob x p R (Y v) (G.iv v g))) ∧
  ∀ v, ∀ g ∈ Φ.Mu v, ∀ i, inFlag x v (al (G.iv v g) - cob x p R (Y v) (G.iv v g)) i i = 0
def SelM (ka : G.Γ → Mat Φ R) (Y : Φ.Vl → Mat Φ R) : Prop :=
  IsCoc x p ka ∧ PolTriv ka ∧ (∀ g, IsMinus x (ka g)) ∧ (∀ v, IsMinus x (Y v)) ∧
  ∀ v g, InB x v (ka (G.iv v g) - cob x p R (Y v) (G.iv v g))
def LocConst (f : G.Γ → Mat Φ R) : Prop := IsLocallyConstant f
def BddCont (f : G.Γ → Mat Φ Φ.F) : Prop :=
  ∃ (s : ℕ) (f' : G.Γ → Mat Φ Φ.A), (∀ i j, ContM Φ.A (fun g => f' g i j)) ∧
    ∀ g, (f' g).map (algebraMap Φ.A Φ.F) = (algebraMap Φ.A Φ.F PowerSeries.X) ^ s • f g
end Selmer
structure Kap {Φ : Frame} {Gb : PolGp Φ} (x : Point Gb) where
  g : ℕ
  kap : Fin g → Gb.Γ → Mat Φ Φ.A
  Y : Fin g → Φ.Vl → Mat Φ Φ.A
  cont : ∀ j a b, ContM Φ.A (fun h => kap j h a b)
  sel : ∀ j, SelM x (Mor.id Gb) (kap j) (Y j)
  indep : ∀ (c : Fin g → Φ.F) (Z : Mat Φ Φ.F),
    (∀ h, ∑ j, c j • (kap j h).map (algebraMap Φ.A Φ.F) = cob x (Mor.id Gb) Φ.F Z h) → c = 0
section Sel2
variable {Φ : Frame} {Gb : PolGp Φ} {x : Point Gb} (K : Kap x) {G : PolGp Φ} (p : Mor G Gb)
  {R : Type} [CommRing R] [Algebra Φ.A R]
def br (X Y : Mat Φ R) : Mat Φ R := X * Y - Y * X
def Kap.at (R : Type) [CommRing R] [Algebra Φ.A R] (j : Fin K.g) (g : G.Γ) : Mat Φ R :=
  (K.kap j (p.p g)).map (algebraMap Φ.A R)
def Kap.Spans : Prop :=
  ∀ (ka : G.Γ → Mat Φ Φ.F) (Y : Φ.Vl → Mat Φ Φ.F), BddCont ka → SelM x p ka Y →
    ∃ (c : Fin K.g → Φ.F) (Z : Mat Φ Φ.F), IsMinus x Z ∧ Zᵀ = -Z ∧
      ∀ g, ka g = ∑ j, c j • K.at p Φ.F j g + cob x p Φ.F Z g
def Sel2 (be : G.Γ → Mat Φ R) (Y0 : Φ.Vl → Mat Φ R) (al : Fin K.g → G.Γ → Mat Φ R)
    (Y : Fin K.g → Φ.Vl → Mat Φ R) : Prop :=
  (∀ j, SelP x p (al j) (Y j)) ∧ PolTriv be ∧ (∀ g, IsMinus x (be g)) ∧ (∀ v, IsMinus x (Y0 v)) ∧
  (∀ g h, be (g * h) = be g + act x p R g (be h) + ∑ j, br (K.at p R j g) (act x p R g (al j h))) ∧
  ∀ v g, InB x v (be (G.iv v g) - cob x p R (Y0 v) (G.iv v g) -
    ∑ j, br (K.at p R j (G.iv v g)) (act x p R (G.iv v g) (Y j v)) +
    ∑ j, br ((K.Y j v).map (algebraMap Φ.A R)) (al j (G.iv v g) - cob x p R (Y j v) (G.iv v g)))
def SelF (d : ℕ) : Prop :=
  ∃ z : (G.Γ → Mat Φ Φ.F) →ₗ[Φ.F] Matrix (Fin K.g) (Fin K.g) Φ.F,
    (∀ T : Submodule Φ.F (G.Γ → Mat Φ Φ.F), Module.Finite Φ.F T →
      (∀ al ∈ T, BddCont al ∧ (∃ Y, SelP x p al Y) ∧ z al = 0) → T ⊓ cobSub x p Φ.F = ⊥ →
      Module.finrank Φ.F T + K.g ^ 2 ≤ d) ∧
    ∀ be Y0 (al : Fin K.g → G.Γ → Mat Φ Φ.F) Y, BddCont be → (∀ j, BddCont (al j)) →
      Sel2 K p be Y0 al Y → ∀ i, ∑ j, z (al j) i j = 0
end Sel2
def Frame.red (Φ : Frame) (m : ℕ) : Φ.Am (m + 1) →+* Φ.Am m :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ m)))
def SelLev {Φ : Frame} {Gb : PolGp Φ} {x : Point Gb} (K : Kap x) (G : ℕ → PolGp Φ)
    (p : ∀ N, Mor (G N) Gb) (d : ℕ) : Prop :=
  ∃ (C : ℕ) (z : ∀ N m : ℕ, ((G N).Γ → Mat Φ (Φ.Am m)) → (Φ.Vl → Mat Φ (Φ.Am m)) →
      Matrix (Fin K.g) (Fin K.g) (Φ.Am m)),
    ∀ N m : ℕ, m ≤ N →
      (∀ (c c' : Φ.Am m) al Y al' Y', LocConst al → LocConst al' → SelP x (p N) al Y → SelP x (p N) al' Y' →
        z N m (c • al + c' • al') (c • Y + c' • Y') = c • z N m al Y + c' • z N m al' Y') ∧
      (∀ al Y Y', LocConst al → SelP x (p N) al Y → SelP x (p N) al Y' → (∀ v, InB x v (Y v - Y' v)) →
        z N m al Y = z N m al Y') ∧
      (m + 1 ≤ N → ∀ al Y, LocConst al → SelP x (p N) al Y →
        z N m (fun g => (al g).map (Φ.red m)) (fun v => (Y v).map (Φ.red m)) =
          (z N (m + 1) al Y).map (Φ.red m)) ∧
      (∀ T : Submodule (Φ.Am m) (((G N).Γ → Mat Φ (Φ.Am m)) × (Φ.Vl → Mat Φ (Φ.Am m))),
        (∀ y ∈ T, LocConst y.1 ∧ SelP x (p N) y.1 y.2 ∧ z N m y.1 y.2 = 0) →
        Module.length (Φ.Am m) ↥((T.map (LinearMap.fst _ _ _)).map (cobSub x (p N) (Φ.Am m)).mkQ) +
          (m * K.g ^ 2 : ℕ) ≤ (m * d + C : ℕ)) ∧
      ∀ be Y0 (al : Fin K.g → (G N).Γ → Mat Φ (Φ.Am m)) Y, LocConst be → (∀ j, LocConst (al j)) →
        Sel2 K (p N) be Y0 al Y → ∀ i, ∑ j, z N m (al j) (Y j) i j = 0
end GlobalTheory.Pat
noncomputable section
open IsLocalRing Matrix TensorProduct
namespace GlobalTheory.Pat
structure Base {Φ : Frame} (Gb : PolGp Φ) where
  R : Pair Gb
  gen : TopGen R.B R.gens
  J : Ideal R.B
  M : Type
  [iM : AddCommGroup M] [iMB : Module R.B M]
  ann : Module.annihilator R.B M = J
  fin : letI := Module.compHom M R.lam; Module.Finite Φ.abelian₂ M
  free : letI := Module.compHom M R.lam; Module.Free Φ.abelian₂ M
attribute [instance] Base.iM Base.iMB
def splitIdeal {B : Type} [CommRing B] {q n : ℕ} (P : Fin q → Polynomial B) (ut : Fin q → Fin n → B) :
    Ideal (MvPowerSeries (Fin q × Fin n) B) :=
  Ideal.span {c | ∃ (j : Fin q) (e : ℕ), c = Polynomial.coeff
    ((∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i)))) -
      (P j).map (MvPowerSeries.C : B →+* MvPowerSeries (Fin q × Fin n) B)) e}
abbrev SplitLoc {B : Type} [CommRing B] {q n : ℕ} (P : Fin q → Polynomial B) (ut : Fin q → Fin n → B) :
    Type := MvPowerSeries (Fin q × Fin n) B ⧸ splitIdeal P ut
def splitU {B : Type} [CommRing B] {q n : ℕ} (P : Fin q → Polynomial B) (ut : Fin q → Fin n → B)
    (j : Fin q) (i : Fin n) : SplitLoc P ut :=
  Ideal.Quotient.mk _ (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i))
def fPoly {B : Type} [CommRing B] {q n : ℕ} (N : Fin q → ℕ) (u : Fin q → Fin n → B) : B :=
  ∏ j, ∏ i, ∏ i' ∈ Finset.univ.erase i, ((u j i - u j i') * (u j i - (N j : B) * u j i'))
def RegSplit {Φ : Frame} {Gb : PolGp Φ} (x : Point Gb) (g : Gb.Γ) : Prop :=
  ∃ α : Fin Φ.n → Φ.A, Function.Injective α ∧
    (x.r g).charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i))
structure GalTower {Φ : Frame} (Gb : PolGp Φ) {ι : Type} (x : ι → Point Gb) where
  q : ℕ
  G : ℕ → PolGp Φ
  p : ∀ N, Mor (G N) Gb

  H0 : Subgroup Gb.Γ
  openSubgroupNormal : H0.Normal
  openSubgroupIsOpen : IsOpen (H0 : Set Gb.Γ)
  openSubgroupSigmaStable : ∀ h ∈ H0, Gb.sig h ∈ H0
  openSubgroupCharTrivial : ∀ h ∈ H0, ∀ i, Gb.chi i h = 1
  proL : ∀ N, IsProL Φ.l (H0.comap (p N).p)
  h : ℕ
  gens : ∀ N, ∃ s : Fin h → (G N).Γ,
    (Subgroup.closure (Set.range s)).topologicalClosure = H0.comap (p N).p
  ph : ∀ N, Fin q → (G N).Γ
  ta : ∀ N, Fin q → (G N).Γ
  Nq : ℕ → Fin q → ℕ
  Nq_cong : ∀ N j, Nq N j ≡ 1 [MOD Φ.l ^ N]
  tame : ∀ N j, ph N j * ta N j ^ Nq N j = ta N j * ph N j
  ker : ∀ N, (p N).p.ker = (Subgroup.normalClosure
    (Set.range (ta N) ∪ Set.range (fun j => (G N).sig (ta N j)))).topologicalClosure
  sg : Fin q → Gb.Γ
  ph_chi : ∀ N j i, (G N).chi i (ph N j) = Gb.chi i (sg j)
  ph_r : ∀ a N j i i', (x a).r ((p N).p (ph N j)) i i' - (x a).r (sg j) i i' ∈
    Ideal.span {(PowerSeries.X : Φ.A) ^ N}
  reg : ∀ a j, RegSplit (x a) (sg j)
  ut : Fin q → Fin Φ.n → Φ.O
  ut_red : ∀ j i, residue Φ.O (ut j i) = ((Gb.chi i (sg j) : Φ.kˣ) : Φ.k)
  K : ∀ a, Kap (x a)
  spans : ∀ a, (K a).Spans (Mor.id Gb)
  sel : ∀ a, SelLev (K a) G p (Φ.d0 + Φ.n * q)
abbrev Base.C {Φ : Frame} {Gb : PolGp Φ} (b : Base Gb) {q : ℕ} (g : Fin q → Gb.Γ)
    (ut : Fin q → Fin Φ.n → Φ.O) : Type :=
  SplitLoc (fun j => b.R.D.chi (gp b.R.B (g j))) (fun j i => b.R.j (ut j i))
def Base.Cu {Φ : Frame} {Gb : PolGp Φ} (b : Base Gb) {q : ℕ} (g : Fin q → Gb.Γ)
    (ut : Fin q → Fin Φ.n → Φ.O) (j : Fin q) (i : Fin Φ.n) : b.C g ut :=
  splitU (fun j => b.R.D.chi (gp b.R.B (g j))) (fun j i => b.R.j (ut j i)) j i
structure HeckeLev {Φ : Frame} {Gb : PolGp Φ} (b : Base Gb) {G : PolGp Φ} (p : Mor G Gb) {q : ℕ}
    (ph ta : Fin q → G.Γ) (Nq : Fin q → ℕ) (ut : Fin q → Fin Φ.n → Φ.O) (N c : ℕ) where
  T : Pair G
  u : Fin q → Fin Φ.n → T.B
  u_red : ∀ j i, u j i - T.j (ut j i) ∈ maximalIdeal T.B
  sN : MvPowerSeries (Fin q × Fin Φ.n) Φ.abelian₂ →+* T.B
  sN_loc : IsLocalHom sN
  sN_C : sN.comp MvPowerSeries.C = T.lam
  MN : Type
  [iM : AddCommGroup MN] [iMT : Module T.B MN]
  e : Fin q → ℕ
  e_ge : ∀ j, N ≤ e j
  rk : ℕ
  bas : Fin rk → MN
  bas_span : ∀ m : MN, ∃ a : Fin rk → MvPowerSeries (Fin q × Fin Φ.n) Φ.abelian₂, m = ∑ s, sN (a s) • bas s
  bas_rel : ∀ a : Fin rk → MvPowerSeries (Fin q × Fin Φ.n) Φ.abelian₂, ∑ s, sN (a s) • bas s = 0 ↔
    ∀ s, a s ∈ Ideal.span (Set.range fun ji : Fin q × Fin Φ.n =>
      (1 + MvPowerSeries.X ji : MvPowerSeries (Fin q × Fin Φ.n) Φ.abelian₂) ^ (Φ.l ^ e ji.1) - 1)
  patchedRelationFirst : ∀ j (h : G.Γ) (m : MN),
    (fPoly Nq u ^ c * T.D.tr (gp T.B h * q1El G (ph j) (u j))) • m = 0
  patchedRelationSecond : ∀ j i (h : G.Γ) (m : MN), (fPoly Nq u ^ c * T.D.tr (gp T.B h *
    q2El G (ph j) (ta j) (u j) (fun i' => sN (MvPowerSeries.X (j, i'))) i)) • m = 0
  phm : b.C (fun j => p.p (ph j)) ut ⊗[b.R.B] b.M →+
    MN ⧸ (Ideal.span (Set.range fun ji => sN (MvPowerSeries.X ji)) • (⊤ : Submodule T.B MN))
  psm : (MN ⧸ (Ideal.span (Set.range fun ji => sN (MvPowerSeries.X ji)) • (⊤ : Submodule T.B MN))) →+
    b.C (fun j => p.p (ph j)) ut ⊗[b.R.B] b.M
  phm_lam : ∀ a m, phm (b.R.lam a • m) = T.lam a • phm m
  phm_D : ∀ i g m, phm (b.R.D.lam i (gp b.R.B (p.p g)) • m) = T.D.lam i (gp T.B g) • phm m
  phm_psi : ∀ v i g m, phm (((b.R.psi v i g : b.R.Bˣ) : b.R.B) • m) = ((T.psi v i g : T.Bˣ) : T.B) • phm m
  phm_u : ∀ j i m, phm (b.Cu (fun j => p.p (ph j)) ut j i • m) = u j i • phm m
  psm_lam : ∀ a m, psm (T.lam a • m) = b.R.lam a • psm m
  psm_D : ∀ i g m, psm (T.D.lam i (gp T.B g) • m) = b.R.D.lam i (gp b.R.B (p.p g)) • psm m
  psm_psi : ∀ v i g m, psm (((T.psi v i g : T.Bˣ) : T.B) • m) = ((b.R.psi v i g : b.R.Bˣ) : b.R.B) • psm m
  psm_u : ∀ j i m, psm (u j i • m) = b.Cu (fun j => p.p (ph j)) ut j i • psm m
  ph_ps : ∀ m, phm (psm m) = fPoly Nq u ^ c • m
  ps_ph : ∀ m, psm (phm m) = fPoly Nq (b.Cu (fun j => p.p (ph j)) ut) ^ c • m
attribute [instance] HeckeLev.iM HeckeLev.iMT
def HeckeTower {Φ : Frame} {Gb : PolGp Φ} (b : Base Gb) {ι : Type} {x : ι → Point Gb}
    (t : GalTower Gb x) : Prop :=
  ∃ c : ℕ, ∀ N, Nonempty (HeckeLev b (t.p N) (t.ph N) (t.ta N) (t.Nq N) t.ut N c)
structure IsCplAt {R S : Type} [CommRing R] [CommRing S] [IsLocalRing S] (q : Ideal R) (φ : R →+* S) :
    Prop where
  noeth : IsNoetherianRing S
  complete : IsAdicComplete (maximalIdeal S) S
  flat : φ.Flat
  max_eq : maximalIdeal S = q.map φ
  comap_eq : (maximalIdeal S).comap φ = q
  res : ∀ s : S, ∃ a b : R, b ∉ q ∧ φ b * s - φ a ∈ maximalIdeal S
def QuasiReg {R : Type} [CommRing R] {σ : Type} [Fintype σ] (y : σ → R) (M : Type) [AddCommGroup M]
    [Module R M] : Prop :=
  ∀ (d : ℕ) (S : Finset (σ →₀ ℕ)) (m : (σ →₀ ℕ) → M), (∀ α ∈ S, α.degree = d) →
    ∑ α ∈ S, (∏ i, y i ^ α i) • m α ∈ (Ideal.span (Set.range y)) ^ (d + 1) • (⊤ : Submodule R M) →
    ∀ α ∈ S, m α ∈ Ideal.span (Set.range y) • (⊤ : Submodule R M)
structure Patched {Φ : Frame} {Gb : PolGp Φ} (b : Base Gb) {ι : Type} (x : ι → Point Gb) where
  q : ℕ
  G : PolGp Φ
  p : Mor G Gb
  ph : Fin q → G.Γ
  ta : Fin q → G.Γ
  comm : ∀ j, ph j * ta j = ta j * ph j
  p_ta : ∀ j, p.p (ta j) = 1
  reg : ∀ a j, RegSplit (x a) (p.p (ph j))
  ut : Fin q → Fin Φ.n → Φ.O
  ut_red : ∀ j i, residue Φ.O (ut j i) = ((G.chi i (ph j) : Φ.kˣ) : Φ.k)
  K : ∀ a, Kap (x a)
  spans : ∀ a, (K a).Spans p
  sel : ∀ a, SelF (K a) p (Φ.d0 + Φ.n * q)

  R : Pair G
  u : Fin q → Fin Φ.n → R.B
  y : Fin q × Fin Φ.n → R.B
  u_red : ∀ j i, u j i - R.j (ut j i) ∈ maximalIdeal R.B
  y_mem : ∀ ji, y ji ∈ maximalIdeal R.B
  patchedRelationFirst : ∀ j (h : G.Γ), R.D.tr (gp R.B h * q1El G (ph j) (u j)) = 0
  patchedRelationSecond : ∀ j i (h : G.Γ), R.D.tr (gp R.B h * q2El G (ph j) (ta j) (u j) (fun i' => y (j, i')) i) = 0
  gen : TopGen R.B (R.gens ∪ {b | ∃ j i, b = u j i} ∪ Set.range y)

  pi0 : R.B →+* b.C (fun j => p.p (ph j)) ut
  projection_surjective_alt : Function.Surjective pi0
  projection_lambda : ∀ a, pi0 (R.lam a) = algebraMap b.R.B _ (b.R.lam a)
  projection_determinant : R.D.map pi0 = (b.R.D.map (algebraMap b.R.B _)).comap p.p
  projection_psi : ∀ v i g, pi0 ((R.psi v i g : R.Bˣ) : R.B) = algebraMap b.R.B _ ((b.R.psi v i g : b.R.Bˣ) : b.R.B)
  projection_variables : ∀ j i, pi0 (u j i) = b.Cu (fun j => p.p (ph j)) ut j i
  projection_auxiliary_zero : ∀ ji, pi0 (y ji) = 0

  BB : Type
  [iBB : CommRing BB]
  BB_noeth : IsNoetherianRing BB
  io : PowerSeries R.B →+* BB
  io_flat : io.Flat
  f_unit : IsUnit (io (PowerSeries.C (fPoly (fun _ => 1) u)))
  io_surj : ∀ (k : ℕ) (z : BB), ∃ (a : PowerSeries R.B) (e : ℕ),
    io (PowerSeries.C (fPoly (fun _ => 1) u)) ^ e * z - io a ∈
      Ideal.span (Set.range fun ji => io (PowerSeries.C (y ji))) ^ k
  io_inj : ∀ (k : ℕ) (a : PowerSeries R.B),
    io a ∈ Ideal.span (Set.range fun ji => io (PowerSeries.C (y ji))) ^ k →
    ∃ e : ℕ, PowerSeries.C (fPoly (fun _ => 1) u) ^ e * a ∈
      Ideal.span (Set.range fun ji => (PowerSeries.C (y ji) : PowerSeries R.B)) ^ k

  piB : BB →+* Localization.Away
    (PowerSeries.C (fPoly (fun _ => 1) (b.Cu (fun j => p.p (ph j)) ut)) :
      PowerSeries (b.C (fun j => p.p (ph j)) ut))
  piB_io : ∀ a, piB (io a) = algebraMap (PowerSeries (b.C (fun j => p.p (ph j)) ut)) _ (PowerSeries.map pi0 a)

  MM : Type
  [iMM : AddCommGroup MM] [iMB : Module BB MM]
  MM_fin : Module.Finite BB MM
  qreg : QuasiReg (fun ji => io (PowerSeries.C (y ji))) MM
  red : MM →+ Localization.Away
    (PowerSeries.C (fPoly (fun _ => 1) (b.Cu (fun j => p.p (ph j)) ut)) :
      PowerSeries (b.C (fun j => p.p (ph j)) ut)) ⊗[b.R.B] b.M
  red_surj : Function.Surjective red
  red_smul : ∀ z m, red (z • m) = piB z • red m
  red_ker : ∀ m, red m = 0 ↔
    m ∈ Ideal.span (Set.range fun ji => io (PowerSeries.C (y ji))) • (⊤ : Submodule BB MM)
attribute [instance] Patched.iBB Patched.iMM Patched.iMB
end GlobalTheory.Pat


