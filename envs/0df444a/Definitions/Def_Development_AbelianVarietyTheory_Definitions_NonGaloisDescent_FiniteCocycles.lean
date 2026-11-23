-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:11.554009+00:00
-- url     : https://prove2.me/theorems/c573a446-eb3f-48ba-94bc-135f3e5a9651
-- title:
--   Finite Cocycles
-- statement:
--   Definitions and structural lemmas for Finite Cocycles, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Polynomial IsLocalRing
namespace GlobalTheory.Pat
def AdicCont {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (f : Γ → R) : Prop :=
  ∀ N : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (I ^ N) (f g)
structure Det (n : ℕ) (A E : Type) [CommRing A] [Ring E] [Algebra A E] : Type 1 where
  D : ∀ (B : Type) [CommRing B] [Algebra A B], B ⊗[A] E →* B
  nat : ∀ (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (f : B →ₐ[A] B') (x : B ⊗[A] E),
    D B' (Algebra.TensorProduct.map f (AlgHom.id A E) x) = f (D B x)
  homog : ∀ (B : Type) [CommRing B] [Algebra A B] (b : B) (x : B ⊗[A] E), D B (b • x) = b ^ n * D B x
namespace Det
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
def chi (y : E) : A[X] := D.D A[X] (X ⊗ₜ 1 - 1 ⊗ₜ y)
def lam (i : ℕ) (y : E) : A := (-1) ^ i * (D.chi y).coeff (n - i)
def tr (y : E) : A := D.lam 1 y
def Kills (y : E) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] (h : B ⊗[A] E), D.D B (1 + h * (1 ⊗ₜ y)) = 1
def pull {E' : Type} [Ring E'] [Algebra A E'] (φ : E' →ₐ[A] E) : Det n A E' where
  D B _ _ := (D.D B).comp (Algebra.TensorProduct.map (AlgHom.id B B) φ).toMonoidHom
  nat B B' _ _ _ _ f x := by
    change D.D B' (Algebra.TensorProduct.map (AlgHom.id B' B') φ _) = f (D.D B (Algebra.TensorProduct.map (AlgHom.id B B) φ x))
    rw [← D.nat]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  homog B _ _ b x := by
    change D.D B (Algebra.TensorProduct.map (AlgHom.id B B) φ (b • x)) = b ^ n * D.D B (Algebra.TensorProduct.map (AlgHom.id B B) φ x)
    rw [map_smul, D.homog]
end Det
structure GDet (n : ℕ) (A G : Type) [CommRing A] [Group G] : Type 1 where
  D : ∀ (B : Type) [CommRing B] [Algebra A B], MonoidAlgebra B G →* B
  nat : ∀ (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (f : B →ₐ[A] B') (x : MonoidAlgebra B G),
    D B' (MonoidAlgebra.mapRingHom G (f : B →+* B') x) = f (D B x)
  homog : ∀ (B : Type) [CommRing B] [Algebra A B] (b : B) (x : MonoidAlgebra B G), D B (b • x) = b ^ n * D B x
namespace GDet
variable {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
@[ext] theorem ext {D D' : GDet n A G} (h : ∀ (B : Type) [CommRing B] [Algebra A B] (x), D.D B x = D'.D B x) : D = D' := by
  cases D; cases D'; congr; funext B _ _; exact MonoidHom.ext (h B)
def map {A' : Type} [CommRing A'] (f : A →+* A') : GDet n A' G where
  D B _ _ := letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra; D.D B
  nat B B' _ _ _ _ g x :=
    letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra
    letI : Algebra A B' := ((algebraMap A' B').comp f).toAlgebra
    D.nat B B' { (g : B →+* B') with commutes' := fun a => g.commutes (f a) } x
  homog B _ _ b x := letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra; D.homog B b x
def comap {H : Type} [Group H] (φ : H →* G) : GDet n A H where
  D B _ _ := (D.D B).comp (MonoidAlgebra.mapDomainRingHom B φ).toMonoidHom
  nat B B' _ _ _ _ f x := by
    change D.D B' (MonoidAlgebra.mapDomainRingHom B' φ _) = f (D.D B (MonoidAlgebra.mapDomainRingHom B φ x))
    rw [← D.nat]
    congr 1
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => simp
  homog B _ _ b x := by
    change D.D B (MonoidAlgebra.mapDomainAlgHom B B φ (b • x)) = b ^ n * D.D B (MonoidAlgebra.mapDomainAlgHom B B φ x)
    rw [map_smul, D.homog]
def repAlg {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι A) (B : Type) [CommRing B] [Algebra A B] :
    MonoidAlgebra B G →ₐ[B] Matrix ι ι B :=
  MonoidAlgebra.lift B (Matrix ι ι B) G ((RingHom.mapMatrix (algebraMap A B)).toMonoidHom.comp ρ)
def ofRep (ρ : G →* Matrix (Fin n) (Fin n) A) : GDet n A G where
  D B _ _ := Matrix.detMonoidHom.comp (repAlg ρ B).toMonoidHom
  nat B B' _ _ _ _ f x := by
    change (repAlg ρ B' _).det = f (repAlg ρ B x).det
    rw [AlgHom.map_det]
    congr 1
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => ext i j; simp [repAlg]
  homog B _ _ b x := by
    change (repAlg ρ B (b • x)).det = b ^ n * (repAlg ρ B x).det
    rw [map_smul, Matrix.det_smul, Fintype.card_fin]
def chi (y : MonoidAlgebra A G) : A[X] := D.D A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
def lam (i : ℕ) (y : MonoidAlgebra A G) : A := (-1) ^ i * (D.chi y).coeff (n - i)
def tr (y : MonoidAlgebra A G) : A := D.lam 1 y
def Kills (y : MonoidAlgebra A G) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] (h : MonoidAlgebra B G),
    D.D B (1 + h * MonoidAlgebra.mapRingHom G (algebraMap A B) y) = 1
def gen {m : ℕ} (y : Fin m → MonoidAlgebra A G) : MonoidAlgebra (MvPolynomial (Fin m) A) G :=
  ∑ j, (MvPolynomial.X j : MvPolynomial (Fin m) A) • MonoidAlgebra.mapRingHom G MvPolynomial.C (y j)
def CH : Set (MonoidAlgebra A G) :=
  {z | ∃ (m : ℕ) (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ), ∀ g : G,
    z.coeff g = MvPolynomial.coeff β
      ((Polynomial.aeval (gen y) ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (gen y))).coeff g)}
variable [TopologicalSpace G]
def IsCont (I : Ideal A) : Prop := ∀ i, AdicCont I fun g : G => D.lam i (MonoidAlgebra.single g 1)
end GDet
def closureIdeal {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] (I : Ideal A) (S : Set (MonoidAlgebra A G)) :
    TwoSidedIdeal (MonoidAlgebra A G) :=
  ⨅ (N : ℕ) (H : OpenNormalSubgroup G), TwoSidedIdeal.span
    (S ∪ {z | ∃ a ∈ I ^ N, z = MonoidAlgebra.single 1 a} ∪ {z | ∃ h ∈ H, z = MonoidAlgebra.single h 1 - 1})
end GlobalTheory.Pat
noncomputable section
open IsLocalRing
namespace GlobalTheory.Pat
def ContM {X : Type} [TopologicalSpace X] (A : Type) [CommRing A] [IsLocalRing A] (f : X → A) : Prop :=
  AdicCont (maximalIdeal A) f
def PhiFin (l : ℕ) (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  ∀ H : Subgroup G, IsOpen (H : Set G) →
    {f : H →* Multiplicative (ZMod l) | IsOpen (f.ker : Set H)}.Finite
def TopFG (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  ∃ S : Finset G, (Subgroup.closure (S : Set G)).topologicalClosure = ⊤
theorem PhiFin.of_finite (l : ℕ) [NeZero l] (G : Type) [Group G] [Finite G] [TopologicalSpace G] : PhiFin l G := by
  intro H _
  haveI : Finite (H →* Multiplicative (ZMod l)) := Finite.of_injective _ DFunLike.coe_injective
  exact Set.toFinite _
def IsProL (l : ℕ) {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) : Prop :=
  ∀ U : Subgroup G, U.Normal → IsOpen (U : Set G) → ∀ h ∈ H, ∃ e : ℕ, h ^ (l ^ e) ∈ U
def TopGen (B : Type) [CommRing B] [IsLocalRing B] (S : Set B) : Prop :=
  ∀ (N : ℕ) (a : B), ∃ b ∈ Subring.closure S, a - b ∈ maximalIdeal B ^ N
structure PG where
  G : Type
  [grp : Group G]
  [top : TopologicalSpace G]
  [tgrp : IsTopologicalGroup G]
  [cpt : CompactSpace G]
  [t2 : T2Space G]
  [td : TotallyDisconnectedSpace G]
attribute [instance] PG.grp PG.top PG.tgrp PG.cpt PG.t2 PG.td
instance : CoeSort PG Type := ⟨PG.G⟩
structure Frame where
  n : ℕ
  n_pos : 0 < n
  l : ℕ
  [hl : Fact l.Prime]
  l_odd : l ≠ 2
  O : Type
  [iO : CommRing O] [iOd : IsDomain O] [iOv : IsDiscreteValuationRing O]
  O_cpl : IsAdicComplete (maximalIdeal O) O
  k_fin : Finite (ResidueField O)
  l_mem : (l : O) ∈ maximalIdeal O
  d0 : ℕ
  Vl : Type
  [iVl : Fintype Vl]
  Gv : Vl → PG
  Gv_phi : ∀ v, PhiFin l (Gv v)
  Mu : ∀ v, Subgroup (Gv v)
  psib : ∀ v, Fin n → (Gv v →* (ResidueField O)ˣ)
  St : Type
  [iSt : Fintype St]
  Iu : St → PG
  Iu_phi : ∀ u, PhiFin l (Iu u)

  Lk : ∀ v, Set (Fin n × Gv v × MvPowerSeries (Fin d0) O)
  Lk_gen : TopGen (MvPowerSeries (Fin d0) O)
    (Set.range (MvPowerSeries.C : O →+* MvPowerSeries (Fin d0) O) ∪ {a | ∃ v i g, (i, g, a) ∈ Lk v})
  Lk_mu : ∀ v i, ∀ g ∈ Mu v, ∃ θ : O, θ - 1 ∈ maximalIdeal O ∧ (i, g, MvPowerSeries.C θ) ∈ Lk v
attribute [instance] Frame.hl Frame.iO Frame.iOd Frame.iOv Frame.iVl Frame.iSt
namespace Frame
variable (Φ : Frame)
abbrev k : Type := ResidueField Φ.O
abbrev abelian₂ : Type := MvPowerSeries (Fin Φ.d0) Φ.O
abbrev A : Type := PowerSeries Φ.k
abbrev F : Type := FractionRing Φ.A
abbrev Am (m : ℕ) : Type := Φ.A ⧸ Ideal.span {(PowerSeries.X : Φ.A) ^ m}
def jA : Φ.O →+* Φ.A := (PowerSeries.C : Φ.k →+* Φ.A).comp (residue Φ.O)
end Frame
structure PolGp (Φ : Frame) where
  Γ : PG
  sig : Γ →* Γ
  sig_cont : Continuous sig
  sig_sig : ∀ g, sig (sig g) = g
  mu : Γ →* Φ.Oˣ
  mu_cont : ContM Φ.O (fun g => ((mu g : Φ.Oˣ) : Φ.O))
  mu_sig : ∀ g, mu (sig g) = mu g
  iv : ∀ v, Φ.Gv v →* Γ
  iv_cont : ∀ v, Continuous (iv v)
  iu : ∀ u, Φ.Iu u →* Γ
  iu_cont : ∀ u, Continuous (iu u)
  chi : Fin Φ.n → (Γ →* Φ.kˣ)
  chi_open : ∀ i, IsOpen ((chi i).ker : Set Γ)
  chi_inj : Function.Injective chi

  fg : PhiFin Φ.l Γ
structure Mor {Φ : Frame} (G G' : PolGp Φ) where
  p : G.Γ →* G'.Γ
  cont : Continuous p
  surj : Function.Surjective p
  p_sig : ∀ g, p (G.sig g) = G'.sig (p g)
  p_mu : ∀ g, G'.mu (p g) = G.mu g
  p_iv : ∀ v g, p (G.iv v g) = G'.iv v g
  p_iu : ∀ u g, p (G.iu u g) = G'.iu u g
  p_chi : ∀ i g, G'.chi i (p g) = G.chi i g
def Mor.id {Φ : Frame} (G : PolGp Φ) : Mor G G :=
  ⟨MonoidHom.id _, continuous_id, Function.surjective_id, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
def Mor.comp {Φ : Frame} {G G' G'' : PolGp Φ} (q : Mor G' G'') (p : Mor G G') : Mor G G'' where
  p := q.p.comp p.p
  cont := q.cont.comp p.cont
  surj := q.surj.comp p.surj
  p_sig g := by rw [MonoidHom.comp_apply, p.p_sig, q.p_sig]; rfl
  p_mu g := (q.p_mu _).trans (p.p_mu g)
  p_iv v g := by rw [MonoidHom.comp_apply, p.p_iv, q.p_iv]
  p_iu u g := by rw [MonoidHom.comp_apply, p.p_iu, q.p_iu]
  p_chi i g := (q.p_chi i _).trans (p.p_chi i g)
abbrev DetG (n : ℕ) (Γ B : Type) [Group Γ] [CommRing B] : Type 1 := GDet n B Γ
abbrev gp {Γ : Type} (B : Type) [Group Γ] [CommRing B] (g : Γ) : MonoidAlgebra B Γ := MonoidAlgebra.single g 1
abbrev sc {B : Type} (Γ : Type) [Group Γ] [CommRing B] (b : B) : MonoidAlgebra B Γ := MonoidAlgebra.single 1 b
def DetOver {n : ℕ} {Γ Γ' B B' : Type} [Group Γ] [Group Γ'] [CommRing B] [CommRing B']
    (D : DetG n Γ B) (D' : DetG n Γ' B') (p : Γ →* Γ') (φ : B →+* B') : Prop :=
  D.map φ = D'.comap p
def DetCont {n : ℕ} {Γ B : Type} [Group Γ] [TopologicalSpace Γ] [CommRing B] [IsLocalRing B]
    (D : DetG n Γ B) : Prop :=
  D.IsCont (maximalIdeal B)
def Red {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [IsLocalRing B] (j : O →+* B) (b : B)
    (x : ResidueField O) : Prop :=
  ∃ o : O, residue O o = x ∧ b - j o ∈ maximalIdeal B
def diagRep {n : ℕ} {Γ K : Type} [Group Γ] [CommRing K] (chi : Fin n → (Γ →* Kˣ)) :
    Γ →* Matrix (Fin n) (Fin n) K where
  toFun g := Matrix.diagonal (fun i => ((chi i g : Kˣ) : K))
  map_one' := by simp
  map_mul' a b := by simp [Matrix.diagonal_mul_diagonal]
def DetLifts {n : ℕ} {Γ O B : Type} [Group Γ] [CommRing O] [IsLocalRing O] [CommRing B] [IsLocalRing B]
    (j : O →+* B) (D : DetG n Γ B) (chi : Fin n → (Γ →* (ResidueField O)ˣ)) : Prop :=
  ∀ κ : ResidueField O →+* ResidueField B, κ.comp (residue O) = (residue B).comp j →
    D.map (residue B) = (GDet.ofRep (diagRep chi)).map κ
structure IsCNL {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [IsLocalRing B] (j : O →+* B) :
    Prop where
  noeth : IsNoetherianRing B
  complete : IsAdicComplete (maximalIdeal B) B
  loc : IsLocalHom j
  res : Function.Surjective ((residue B).comp j)
section Elements
variable {Φ : Frame} (G : PolGp Φ) {B : Type} [CommRing B]
def star (j : Φ.O →+* B) (x : MonoidAlgebra B G.Γ) : MonoidAlgebra B G.Γ :=
  x.coeff.sum (fun g a => MonoidAlgebra.single (G.sig g)⁻¹ (a * j ((G.mu g : Φ.Oˣ) : Φ.O)))
def oEl (v : Φ.Vl) (ψ : Fin Φ.n → (Φ.Gv v →* Bˣ)) (g : Fin Φ.n → Φ.Gv v) : MonoidAlgebra B G.Γ :=
  (List.ofFn fun i => gp B (G.iv v (g i)) - sc G.Γ ((ψ i (g i) : Bˣ) : B)).prod
def q1El (ph : G.Γ) (u : Fin Φ.n → B) : MonoidAlgebra B G.Γ :=
  (List.ofFn fun i => gp B ph - sc G.Γ (u i)).prod
def q2El (ph ta : G.Γ) (u y : Fin Φ.n → B) (i : Fin Φ.n) : MonoidAlgebra B G.Γ :=
  (List.ofFn fun i' => if i' = i then 1 else gp B ph - sc G.Γ (u i')).prod *
    (gp B ta - 1 - sc G.Γ (y i))
end Elements
structure Pair {Φ : Frame} (G : PolGp Φ) where
  B : Type
  [iB : CommRing B] [iL : IsLocalRing B]
  lam : Φ.abelian₂ →+* B
  lam_loc : IsLocalHom lam
  cnl : IsCNL (lam.comp (MvPowerSeries.C : Φ.O →+* Φ.abelian₂))
  D : DetG Φ.n G.Γ B
  psi : ∀ v, Fin Φ.n → (Φ.Gv v →* Bˣ)
  cont : DetCont D
  lift : DetLifts (lam.comp (MvPowerSeries.C : Φ.O →+* Φ.abelian₂)) D G.chi
  psi_cont : ∀ v i, ContM B (fun g => ((psi v i g : Bˣ) : B))
  psi_lift : ∀ v i g, Red (lam.comp (MvPowerSeries.C : Φ.O →+* Φ.abelian₂)) ((psi v i g : Bˣ) : B)
    ((Φ.psib v i g : Φ.kˣ) : Φ.k)
  link : ∀ v i g a, (i, g, a) ∈ Φ.Lk v → ((psi v i g : Bˣ) : B) = lam a
  relP : ∀ (g : G.Γ) (i : ℕ),
    D.lam i (star G (lam.comp (MvPowerSeries.C : Φ.O →+* Φ.abelian₂)) (gp B g)) = D.lam i (gp B g)
  relO : ∀ v (g : Fin Φ.n → Φ.Gv v) (h : G.Γ), D.tr (gp B h * oEl G v (psi v) g) = 0
  relI : ∀ u (g : Φ.Iu u) (h : G.Γ), D.tr (gp B h * (gp B (G.iu u g) - 1)) = 0
attribute [instance] Pair.iB Pair.iL
namespace Pair
variable {Φ : Frame} {G : PolGp Φ} (R : Pair G)
def j : Φ.O →+* R.B := R.lam.comp (MvPowerSeries.C : Φ.O →+* Φ.abelian₂)
def gens : Set R.B :=
  Set.range R.j ∪ {b | ∃ i g, b = R.D.lam i (gp R.B g)} ∪ {b | ∃ v i g, b = ((R.psi v i g : R.Bˣ) : R.B)}
end Pair
section CH
variable {n : ℕ} {Γ B : Type} [Group Γ] [CommRing B] (D : DetG n Γ B)
abbrev QAlg [TopologicalSpace Γ] [IsLocalRing B] (S : Set (MonoidAlgebra B Γ)) {C : Type} [CommRing C]
    (φ : B →+* C) : Type :=
  (TwoSidedIdeal.span (MonoidAlgebra.mapRingHom Γ φ ''
    (closureIdeal (maximalIdeal B) S : Set (MonoidAlgebra B Γ)))).ringCon.Quotient
def IrrAt {K : Type} [Field K] (φ : B →+* K) : Prop :=
  ∃ ρ : Γ →* Matrix (Fin n) (Fin n) K,
    (∀ W : Submodule K (Fin n → K), (∀ g, ∀ w ∈ W, (ρ g).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤) ∧
    D.map φ = GDet.ofRep ρ
end CH
def toKap {B : Type} [CommRing B] (q : Ideal B) [q.IsPrime] : B →+* AlgebraicClosure q.ResidueField :=
  (algebraMap q.ResidueField (AlgebraicClosure q.ResidueField)).comp (algebraMap B q.ResidueField)
namespace Pair
variable {Φ : Frame} {G : PolGp Φ} (R : Pair G)
def E0gens : Set (MonoidAlgebra R.B G.Γ) :=
  R.D.CH ∪
  {z | ∃ v g, z = oEl G v (R.psi v) g ∨ z = star G R.j (oEl G v (R.psi v) g)} ∪
  {z | ∃ u g, z = gp R.B (G.iu u g) - 1 ∨ z = star G R.j (gp R.B (G.iu u g)) - 1}
def IsStable (q : Ideal R.B) [q.IsPrime] : Prop := IrrAt R.D (toKap q)
def IsThick (q : Ideal R.B) [q.IsPrime] : Prop :=
  ¬ R.IsStable q ∧ ¬ IsSemisimpleRing (QAlg R.E0gens (toKap q))
end Pair
end GlobalTheory.Pat
noncomputable section
open IsLocalRing Polynomial
namespace GlobalTheory.Pat.Example
theorem map_ofRep {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (f : A →+* A') :
    (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  ext B _ _ x
  letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra
  change (GDet.repAlg ρ B x).det = (GDet.repAlg (f.mapMatrix.toMonoidHom.comp ρ) B x).det
  congr 1
theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (y : MonoidAlgebra A G) :
    (GDet.ofRep ρ).chi y = (GDet.repAlg ρ A y).charpoly := by
  change (GDet.repAlg ρ A[X] _).det = _
  unfold Matrix.charpoly Matrix.charmatrix
  congr 1
  rw [map_sub]
  congr 1
  · ext i j; simp [GDet.repAlg, Matrix.one_apply, Matrix.diagonal_apply]
  · induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => ext i j; simp [GDet.repAlg]
theorem tr_ofRep {n : ℕ} {A G : Type} [CommRing A] [Nontrivial A] [Group G]
    (ρ : G →* Matrix (Fin (n+1)) (Fin (n+1)) A) (y : MonoidAlgebra A G) :
    (GDet.ofRep ρ).tr y = (GDet.repAlg ρ A y).trace := by
  unfold GDet.tr GDet.lam
  rw [chi_ofRep, Matrix.trace_eq_neg_charpoly_coeff]
  simp
def finPG (G : Type) [Group G] [Finite G] : PG :=
  letI : TopologicalSpace G := ⊥
  haveI : DiscreteTopology G := ⟨rfl⟩
  { G := G }
instance (G : Type) [Group G] [Finite G] : DiscreteTopology (finPG G) := ⟨rfl⟩
instance (G : Type) [Group G] [Finite G] : Finite (finPG G) := inferInstanceAs (Finite G)
theorem adic {X R : Type} [TopologicalSpace X] [DiscreteTopology X] [CommRing R] (I : Ideal R) (f : X → R) :
    AdicCont I f := fun _ => IsLocallyConstant.of_discrete _
abbrev S3 := DihedralGroup 3
def rZ : S3 → Matrix (Fin 2) (Fin 2) ℤ
  | .r i => if i = 0 then !![1,0;0,1] else if i = 1 then !![1,1;-3,-2] else !![-2,-1;3,1]
  | .sr i => if i = 0 then !![1,1;0,-1] else if i = 1 then !![-2,-1;3,2] else !![1,0;-3,-1]
def rhoZ : S3 →* Matrix (Fin 2) (Fin 2) ℤ where
  toFun := rZ
  map_one' := by decide
  map_mul' := by decide
def sgn : S3 →* ℤˣ where
  toFun g := match g with | .r _ => 1 | .sr _ => -1
  map_one' := by decide
  map_mul' := by decide
def inc : ℤˣ →* S3 where
  toFun u := if u = 1 then 1 else .sr 0
  map_one' := by decide
  map_mul' := by decide
def rho (A : Type) [CommRing A] : S3 →* Matrix (Fin 2) (Fin 2) A :=
  (Int.castRingHom A).mapMatrix.toMonoidHom.comp rhoZ
def chs (A : Type) [CommRing A] : Fin 2 → (ℤˣ →* Aˣ) := ![1, Units.map (Int.castRingHom A).toMonoidHom]
theorem three_mem : ((3 : ℕ) : ℤ_[3]) ∈ maximalIdeal ℤ_[3] := by
  rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
def frame : Frame where
  n := 2
  n_pos := by norm_num
  l := 3
  l_odd := by norm_num
  O := ℤ_[3]
  O_cpl := inferInstance
  k_fin := Finite.of_equiv _ (PadicInt.residueField (p := 3)).symm.toEquiv
  l_mem := three_mem
  d0 := 0
  Vl := Unit
  Gv _ := finPG ℤˣ
  Gv_phi _ := PhiFin.of_finite 3 _
  Mu _ := ⊥
  psib _ := chs _
  St := Unit
  Iu _ := finPG ℤˣ
  Iu_phi _ := PhiFin.of_finite 3 _
  Lk _ := {x | x.2.2 = MvPowerSeries.C ((chs ℤ_[3] x.1 x.2.1 : ℤ_[3]ˣ) : ℤ_[3])}
  Lk_gen := by
    intro N a
    refine ⟨a, Subring.subset_closure (Or.inl ⟨MvPowerSeries.constantCoeff a, ?_⟩), by simp⟩
    ext m
    have : m = 0 := Subsingleton.elim _ _
    subst this
    simp
  Lk_mu := by
    intro v i g hg
    refine ⟨1, by simp, ?_⟩
    have : g = 1 := by simpa using hg
    subst this
    change MvPowerSeries.C 1 = MvPowerSeries.C ((chs ℤ_[3] i 1 : ℤ_[3]ˣ) : ℤ_[3])
    simp
theorem three_k : (3 : ResidueField ℤ_[3]) = 0 := by
  have := (residue_eq_zero_iff _).2 three_mem
  rw [map_natCast] at this
  exact_mod_cast this
theorem neg_one_ne : (-1 : ResidueField ℤ_[3]) ≠ 1 := by
  intro h
  have h3 := three_k
  have : (1 : ResidueField ℤ_[3]) = 0 := by linear_combination h3 + h
  exact one_ne_zero this
def pol : PolGp frame where
  Γ := finPG S3
  sig := MonoidHom.id _
  sig_cont := continuous_of_discreteTopology
  sig_sig _ := rfl
  mu := 1
  mu_cont := adic _ _
  mu_sig _ := rfl
  iv _ := inc
  iv_cont _ := continuous_of_discreteTopology (α := finPG ℤˣ)
  iu _ := 1
  iu_cont _ := continuous_of_discreteTopology (α := finPG ℤˣ)
  chi i := (chs _ i).comp sgn
  chi_open _ := isOpen_discrete _
  chi_inj := by
    have key : ((chs (ResidueField ℤ_[3]) 0).comp sgn) ≠ ((chs (ResidueField ℤ_[3]) 1).comp sgn) := by
      intro h
      have := congrArg (fun f => ((f (DihedralGroup.sr 0) : (ResidueField ℤ_[3])ˣ) : ResidueField ℤ_[3])) h
      simp [chs, sgn] at this
      exact neg_one_ne this.symm
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd h key
    · exact absurd h.symm key
    · rfl
  fg := PhiFin.of_finite 3 _
theorem tri (B : Type) [CommRing B] (hB : (3 : B) = 0) (g : S3) :
    ((rhoZ g 1 0 : ℤ) : B) = 0 ∧ ((rhoZ g 0 0 : ℤ) : B) = 1 ∧ ((rhoZ g 1 1 : ℤ) : B) = ((sgn g : ℤ) : B) := by
  have h : ∀ g : S3, (3 : ℤ) ∣ rhoZ g 1 0 ∧ (3 : ℤ) ∣ rhoZ g 0 0 - 1 ∧ (3 : ℤ) ∣ rhoZ g 1 1 - sgn g := by decide
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := h g
  refine ⟨?_, ?_, ?_⟩
  · rw [ha]; simp [hB]
  · rw [sub_eq_iff_eq_add] at hb; rw [hb]; simp [hB]
  · rw [sub_eq_iff_eq_add] at hc; rw [hc]; simp [hB]
theorem det_char3 (K : Type) [CommRing K] (h3 : (3 : K) = 0) :
    GDet.ofRep (rho K) = GDet.ofRep (diagRep fun i => (chs K i).comp sgn) := by
  ext B _ _ x
  have hB : (3 : B) = 0 := by
    have := congrArg (algebraMap K B) h3
    simpa [map_ofNat] using this
  change (GDet.repAlg (rho K) B x).det = (GDet.repAlg (diagRep fun i => (chs K i).comp sgn) B x).det
  have : GDet.repAlg (rho K) B x 1 0 = 0 ∧ GDet.repAlg (diagRep fun i => (chs K i).comp sgn) B x 1 0 = 0 ∧
      GDet.repAlg (rho K) B x 0 0 = GDet.repAlg (diagRep fun i => (chs K i).comp sgn) B x 0 0 ∧
      GDet.repAlg (rho K) B x 1 1 = GDet.repAlg (diagRep fun i => (chs K i).comp sgn) B x 1 1 := by
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp [ha, hb]
    | single g r =>
      obtain ⟨h1, h2, h3⟩ := tri B hB g
      simp [GDet.repAlg, rho, diagRep, chs, h1, h2, h3]
  rw [Matrix.det_fin_two, Matrix.det_fin_two, this.1, this.2.1, this.2.2.1, this.2.2.2]
  simp
theorem rep_gp (A : Type) [CommRing A] (g : S3) : GDet.repAlg (rho A) A (gp A g) = rho A g := by
  simp [GDet.repAlg]
theorem rep_sc (A : Type) [CommRing A] (a : A) : GDet.repAlg (rho A) A (sc S3 a) = a • 1 := by
  simp [GDet.repAlg]
theorem charpoly_inv (g : S3) : (rhoZ g⁻¹).charpoly = (rhoZ g).charpoly := by
  have h1 : ∀ g : S3, (rhoZ g⁻¹).trace = (rhoZ g).trace := by decide
  have h2 : ∀ g : S3, (rhoZ g⁻¹).det = (rhoZ g).det := by decide
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two, h1, h2]
theorem o_zero (A : Type) [CommRing A] (a b : ℤˣ) :
    (rho A (inc a) - ((chs A 0 a : Aˣ) : A) • 1) * (rho A (inc b) - ((chs A 1 b : Aˣ) : A) • 1) = 0 := by
  have h : rhoZ (inc (-1)) = !![1,1;0,-1] := by decide
  rcases Int.units_eq_one_or a with rfl | rfl
  · simp
  rcases Int.units_eq_one_or b with rfl | rfl
  · simp
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rho, h, chs, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
theorem rep_oEl (g : Fin 2 → ℤˣ) :
    GDet.repAlg (rho ℤ_[3]) ℤ_[3] (oEl pol () (chs ℤ_[3]) g) = 0 := by
  have : oEl pol () (chs ℤ_[3]) g = (gp ℤ_[3] (inc (g 0)) - sc S3 ((chs ℤ_[3] 0 (g 0) : ℤ_[3]ˣ) : ℤ_[3])) *
      (gp ℤ_[3] (inc (g 1)) - sc S3 ((chs ℤ_[3] 1 (g 1) : ℤ_[3]ˣ) : ℤ_[3])) := by
    change (List.ofFn (n := 2) fun i => gp ℤ_[3] (inc (g i)) - sc S3 ((chs ℤ_[3] i (g i) : ℤ_[3]ˣ) : ℤ_[3])).prod = _
    simp [List.ofFn_succ]
  rw [this, map_mul, map_sub, map_sub, rep_gp, rep_gp, rep_sc, rep_sc, o_zero]
theorem j_eq : (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 0) ℤ_[3] →+* ℤ_[3]).comp MvPowerSeries.C =
    RingHom.id _ := by ext; simp
theorem star_gp (j : ℤ_[3] →+* ℤ_[3]) (g : S3) : star pol j (gp ℤ_[3] g) = gp ℤ_[3] g⁻¹ := by
  unfold star
  change (MonoidAlgebra.single g (1 : ℤ_[3])).coeff.sum
    (fun (g : S3) (a : ℤ_[3]) => MonoidAlgebra.single g⁻¹ (a * j 1)) = _
  rw [MonoidAlgebra.coeff_single, Finsupp.sum_single_index] <;> simp
theorem res_chs (i : Fin 2) (g : ℤˣ) : residue ℤ_[3] ((chs ℤ_[3] i g : ℤ_[3]ˣ) : ℤ_[3]) =
    ((chs (ResidueField ℤ_[3]) i g : (ResidueField ℤ_[3])ˣ) : ResidueField ℤ_[3]) := by
  fin_cases i <;> simp [chs]
theorem lam_inv (i : ℕ) (g : S3) :
    (GDet.ofRep (rho ℤ_[3])).lam i (gp ℤ_[3] g⁻¹) = (GDet.ofRep (rho ℤ_[3])).lam i (gp ℤ_[3] g) := by
  unfold GDet.lam
  rw [chi_ofRep, chi_ofRep, rep_gp, rep_gp]
  have h : ∀ g : S3, (rho ℤ_[3] g).charpoly = (rhoZ g).charpoly.map (Int.castRingHom _) := fun g =>
    Matrix.charpoly_map (rhoZ g) (Int.castRingHom ℤ_[3])
  rw [h, h, charpoly_inv]
theorem one_sub (A : Type) [CommRing A] : gp A (1 : S3) - 1 = 0 := sub_self _
theorem rep_one_sub (A : Type) [CommRing A] : GDet.repAlg (rho A) A (gp A (1 : S3) - 1) = 0 := by
  rw [one_sub, map_zero]
theorem tr_zero (x y : MonoidAlgebra ℤ_[3] S3) (hy : GDet.repAlg (rho ℤ_[3]) ℤ_[3] y = 0) :
    (GDet.ofRep (rho ℤ_[3])).tr (x * y) = 0 := by
  rw [tr_ofRep (n := 1), map_mul, hy]
  simp
def pair : Pair pol where
  B := ℤ_[3]
  lam := (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 0) ℤ_[3] →+* ℤ_[3])
  lam_loc := ⟨fun _ h => MvPowerSeries.isUnit_iff_constantCoeff.2 h⟩
  cnl := by
    change IsCNL ((MvPowerSeries.constantCoeff : MvPowerSeries (Fin 0) ℤ_[3] →+* ℤ_[3]).comp MvPowerSeries.C)
    rw [j_eq]
    exact ⟨inferInstance, inferInstance, inferInstance, residue_surjective⟩
  D := GDet.ofRep (rho ℤ_[3])
  psi _ := chs ℤ_[3]
  cont _ := adic (X := finPG S3) _ _
  lift := by
    change DetLifts ((MvPowerSeries.constantCoeff : MvPowerSeries (Fin 0) ℤ_[3] →+* ℤ_[3]).comp MvPowerSeries.C)
      (GDet.ofRep (rho ℤ_[3])) (fun i => (chs (ResidueField ℤ_[3]) i).comp sgn)
    rw [j_eq]
    intro κ hκ
    have : κ = RingHom.id _ := by
      ext x
      obtain ⟨y, rfl⟩ := residue_surjective x
      exact DFunLike.congr_fun hκ y
    subst this
    rw [← det_char3 _ three_k, map_ofRep, map_ofRep]
    congr 1
  psi_cont _ _ := adic (X := finPG ℤˣ) _ _
  psi_lift v i g := by
    change Red ((MvPowerSeries.constantCoeff : MvPowerSeries (Fin 0) ℤ_[3] →+* ℤ_[3]).comp MvPowerSeries.C)
      ((chs ℤ_[3] i g : ℤ_[3]ˣ) : ℤ_[3]) ((chs (ResidueField ℤ_[3]) i g : (ResidueField ℤ_[3])ˣ) : ResidueField ℤ_[3])
    rw [j_eq]
    refine ⟨((chs ℤ_[3] i g : ℤ_[3]ˣ) : ℤ_[3]), ?_, by simp⟩
    exact res_chs i g
  link v i g a h := by
    have : a = MvPowerSeries.C ((chs ℤ_[3] i g : ℤ_[3]ˣ) : ℤ_[3]) := h
    subst this
    exact (MvPowerSeries.constantCoeff_C _).symm
  relP g i := (congrArg ((GDet.ofRep (rho ℤ_[3])).lam i) (star_gp _ g)).trans (lam_inv i g)
  relO _ g h := tr_zero _ _ (rep_oEl g)
  relI _ _ h := tr_zero _ (gp ℤ_[3] (1 : S3) - 1) (rep_one_sub _)
example : pair.D.tr (gp ℤ_[3] (DihedralGroup.r 1 : S3)) = (-1 : ℤ_[3]) := by
  refine (?_ : (GDet.ofRep (rho ℤ_[3])).tr (gp ℤ_[3] (DihedralGroup.r 1 : S3)) = (-1 : ℤ_[3]))
  have h : rhoZ (.r 1) = !![1,1;-3,-2] := by decide
  rw [tr_ofRep (n := 1), rep_gp]
  simp [rho, h, Matrix.trace_fin_two]
  norm_num
example : star pol (RingHom.id ℤ_[3]) (gp ℤ_[3] (DihedralGroup.r 1 : S3)) = gp ℤ_[3] (DihedralGroup.r 2 : S3) :=
  star_gp _ _
end GlobalTheory.Pat.Example


