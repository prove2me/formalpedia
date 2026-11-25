-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PatchingModules_PairedDualFirstOrderDualMatrixSpace
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_PatchingModules_PairedDualFirstOrderDualMatrixSpace
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T16:44:15.157938+00:00
-- url     : https://prove2.me/theorems/f846349a-c7b7-5b20-9910-2dd2377dacd4
-- title:
--   Paired Dual First Order Dual Matrix Space
-- statement:
--   Definitions and structural lemmas for Paired Dual First Order Dual Matrix Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/PatchingModules/PairedDualFirstOrderDualMatrixSpace.lean

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_UniversalOrdinaryDeterminantRing
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebraHeight_OfDetToDet
import Theorems.Thm_UpperTheory_V_Alg_Lift_map_hom
import Theorems.Thm_UpperTheory_V_U3_unitaryThreeReflection_left
import Theorems.Thm_UpperTheory_V_U3_unitaryThreeReflection_right
import Theorems.Thm_UpperTheory_V_W_Det_mem_ker
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] UpperTheory.V.Alg.Lift.map_hom
attribute [local simp] UpperTheory.V.U3.unitaryThreeReflection_left
attribute [local simp] UpperTheory.V.U3.unitaryThreeReflection_right


set_option autoImplicit false
noncomputable section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W
namespace UpperTheory.V.Pa
structure Loc : Type 1 where
  Vl : Type
  [finV : Fintype Vl]
  Gv : Vl → Type
  [gv : ∀ v, Group (Gv v)]
  [tv : ∀ v, TopologicalSpace (Gv v)]
  [tgv : ∀ v, IsTopologicalGroup (Gv v)]
  [cv : ∀ v, CompactSpace (Gv v)]
  [dv : ∀ v, TotallyDisconnectedSpace (Gv v)]
  Iv : ∀ v, Subgroup (Gv v)
  St : Type
  [finT : Fintype St]
  Gu : St → Type
  [gu : ∀ u, Group (Gu u)]
  [tu : ∀ u, TopologicalSpace (Gu u)]
  [tgu : ∀ u, IsTopologicalGroup (Gu u)]
  [cu : ∀ u, CompactSpace (Gu u)]
  [du : ∀ u, TotallyDisconnectedSpace (Gu u)]
  Ju : ∀ u, Subgroup (Gu u)
attribute [instance] Loc.finV Loc.gv Loc.tv Loc.tgv Loc.cv Loc.dv Loc.finT Loc.gu Loc.tu Loc.tgu Loc.cu Loc.du
structure Glob (l : ℕ) [Fact l.Prime] (L : Loc) : Type 1 where
  Γ : Type
  [grp : Group Γ]
  [top : TopologicalSpace Γ]
  [tgrp : IsTopologicalGroup Γ]
  [cpt : CompactSpace Γ]
  [tdisc : TotallyDisconnectedSpace Γ]
  η : Γ →* ℤˣ
  η_open : IsOpen (η.ker : Set Γ)
  c : Γ
  c_sq : c * c = 1
  η_c : η c = -1
  ε : Γ →* ℤ_[l]ˣ
  ε_cont : Continuous ε
  φ : ∀ v, L.Gv v →* η.ker
  φ_cont : ∀ v, Continuous (φ v)
  φu : ∀ u, L.Gu u →* η.ker
  φu_cont : ∀ u, Continuous (φu u)
attribute [instance] Glob.grp Glob.top Glob.tgrp Glob.cpt Glob.tdisc
variable {l : ℕ} [Fact l.Prime] {L : Loc}
namespace Glob
abbrev frame (G : Glob l L) : GFrame l where
  Γ := G.Γ
  η := G.η
  η_open := G.η_open
  c := G.c
  c_sq := G.c_sq
  η_c := G.η_c
  ε := G.ε
  ε_cont := G.ε_cont
  Vl := L.Vl
  Gv := L.Gv
  φ := G.φ
  φ_cont := G.φ_cont
  Iv := L.Iv
  St := L.St
  Iu u := (L.Ju u).map (G.φu u)
  D0 := ⊥
  I0 := ⊥
abbrev G₀ (G : Glob l L) : Type := G.η.ker
structure Hom (G G' : Glob l L) where
  p : G.Γ →* G'.Γ
  cont : Continuous p
  surj : Function.Surjective p
  η : ∀ g, G'.η (p g) = G.η g
  c : p G.c = G'.c
  ε : ∀ g, G'.ε (p g) = G.ε g
  φ : ∀ v g, p (G.φ v g) = G'.φ v g
  φu : ∀ u g, p (G.φu u g) = G'.φu u g
def Hom.p₀ {G G' : Glob l L} (h : Hom G G') : G.G₀ →* G'.G₀ :=
  (h.p.comp G.η.ker.subtype).codRestrict _ fun g => by
    have := h.η g
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, this]
    exact g.2
def Hom.refl (G : Glob l L) : Hom G G :=
  ⟨MonoidHom.id _, continuous_id, Function.surjective_id, fun _ => rfl, rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
def Compat {G G' : Glob l L} (h : Hom G G') {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    (r : Resid G.frame O n) (r' : Resid G'.frame O n) : Prop :=
  (∀ i, r.chib i = (r'.chib i).comp h.p₀) ∧ r.psib = r'.psib ∧ r.th = r'.th
end Glob
variable (l) in

def PL {Γ : Type} [Group Γ] [TopologicalSpace Γ] (H : Subgroup Γ) : Subgroup Γ :=
  ⨅ (U : OpenNormalSubgroup Γ) (_ : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U), U.toSubgroup
@[ext] structure DD (X : Type) (g : ℕ) where
  a : X
  ep : Fin g → X
  ep' : Fin g → X
  eta : X
namespace DD
variable {X : Type} [CommRing X] {g : ℕ}
def equiv : DD X g ≃ X × (Fin g → X) × (Fin g → X) × X where
  toFun x := (x.a, x.ep, x.ep', x.eta)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance : AddCommGroup (DD X g) := equiv.addCommGroup
instance : One (DD X g) := ⟨⟨1, 0, 0, 0⟩⟩
instance : Mul (DD X g) := ⟨fun x y => ⟨x.a * y.a, fun j => x.a * y.ep j + x.ep j * y.a,
  fun j => x.a * y.ep' j + x.ep' j * y.a,
  x.a * y.eta + x.eta * y.a + ∑ j, (x.ep j * y.ep' j + x.ep' j * y.ep j)⟩⟩
@[simp] theorem add_a (x y : DD X g) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_ep (x y : DD X g) (j) : (x + y).ep j = x.ep j + y.ep j := rfl
@[simp] theorem add_ep' (x y : DD X g) (j) : (x + y).ep' j = x.ep' j + y.ep' j := rfl
@[simp] theorem add_eta (x y : DD X g) : (x + y).eta = x.eta + y.eta := rfl
@[simp] theorem zero_a : (0 : DD X g).a = 0 := rfl
@[simp] theorem zero_ep (j) : (0 : DD X g).ep j = 0 := rfl
@[simp] theorem zero_ep' (j) : (0 : DD X g).ep' j = 0 := rfl
@[simp] theorem zero_eta : (0 : DD X g).eta = 0 := rfl
@[simp] theorem neg_a (x : DD X g) : (-x).a = -x.a := rfl
@[simp] theorem neg_ep (x : DD X g) (j) : (-x).ep j = -x.ep j := rfl
@[simp] theorem neg_ep' (x : DD X g) (j) : (-x).ep' j = -x.ep' j := rfl
@[simp] theorem neg_eta (x : DD X g) : (-x).eta = -x.eta := rfl
@[simp] theorem one_a : (1 : DD X g).a = 1 := rfl
@[simp] theorem one_ep (j) : (1 : DD X g).ep j = 0 := rfl
@[simp] theorem one_ep' (j) : (1 : DD X g).ep' j = 0 := rfl
@[simp] theorem one_eta : (1 : DD X g).eta = 0 := rfl
@[simp] theorem mul_a (x y : DD X g) : (x * y).a = x.a * y.a := rfl
@[simp] theorem mul_ep (x y : DD X g) (j) : (x * y).ep j = x.a * y.ep j + x.ep j * y.a := rfl
@[simp] theorem mul_ep' (x y : DD X g) (j) : (x * y).ep' j = x.a * y.ep' j + x.ep' j * y.a := rfl
@[simp] theorem mul_eta (x y : DD X g) :
    (x * y).eta = x.a * y.eta + x.eta * y.a + ∑ j, (x.ep j * y.ep' j + x.ep' j * y.ep j) := rfl
instance : CommRing (DD X g) :=
  { (inferInstance : AddCommGroup (DD X g)) with
    mul := (· * ·)
    one := 1
    left_distrib := fun x y z => by
      ext <;> simp [mul_add, add_mul, Finset.sum_add_distrib] <;> ring
    right_distrib := fun x y z => by
      ext <;> simp [mul_add, add_mul, Finset.sum_add_distrib] <;> ring
    zero_mul := fun x => by ext <;> simp
    mul_zero := fun x => by ext <;> simp
    mul_assoc := fun x y z => by
      ext <;> simp [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm] <;> ring
    one_mul := fun x => by ext <;> simp
    mul_one := fun x => by ext <;> simp
    mul_comm := fun x y => by
      ext <;> simp [Finset.sum_add_distrib, mul_comm] <;> ring }
def C : X →+* DD X g where
  toFun x := ⟨x, 0, 0, 0⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp
@[simp] theorem C_a (x : X) : (C x : DD X g).a = x := rfl
@[simp] theorem C_ep (x : X) (j) : (C x : DD X g).ep j = 0 := rfl
@[simp] theorem C_ep' (x : X) (j) : (C x : DD X g).ep' j = 0 := rfl
@[simp] theorem C_eta (x : X) : (C x : DD X g).eta = 0 := rfl
instance {A : Type} [CommRing A] [Algebra A X] : Algebra A (DD X g) := (C.comp (algebraMap A X)).toAlgebra
def epM {n : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) X) : Matrix (Fin n) (Fin n) (DD X g) :=
  Matrix.of fun a b => ⟨0, fun j => Z j a b, 0, 0⟩
end DD
section Sel
variable {n : ℕ}
def blkMat {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (n a : ℕ) (V₁ V₂ : Submodule A R) :
    Submodule A (Matrix (Fin n) (Fin n) R) where
  carrier := {Z | ∀ i j : Fin n, ((((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ V₁) ∧ (¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ V₂)}
  add_mem' h h' i j := ⟨fun e => V₁.add_mem ((h i j).1 e) ((h' i j).1 e), fun e => V₂.add_mem ((h i j).2 e) ((h' i j).2 e)⟩
  zero_mem' _ _ := ⟨fun _ => V₁.zero_mem, fun _ => V₂.zero_mem⟩
  smul_mem' c _ h i j := ⟨fun e => V₁.smul_mem c ((h i j).1 e), fun e => V₂.smul_mem c ((h i j).2 e)⟩
abbrev Ev (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (n a : ℕ) := blkMat (A := A) (R := R) n a ⊤ ⊥
abbrev Od (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (n a : ℕ) := blkMat (A := A) (R := R) n a ⊥ ⊤
def ddPart (A X : Type) [CommRing A] [CommRing X] [Algebra A X] (g : ℕ) (a ep ep' eta : Bool) : Submodule A (DD X g) where
  carrier := {x | (a = false → x.a = 0) ∧ (ep = false → x.ep = 0) ∧ (ep' = false → x.ep' = 0) ∧ (eta = false → x.eta = 0)}
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨fun e => by simp [a1 e, b1 e], fun e => ?_, fun e => ?_, fun e => by simp [a4 e, b4 e]⟩
    · funext j; simp [a2 e, b2 e]
    · funext j; simp [a3 e, b3 e]
  zero_mem' := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4⟩
    have hc : c • x = DD.C (algebraMap A X c) * x := rfl
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · simp [hc, a1 e]
    · funext j; simp [hc, a2 e]
    · funext j; simp [hc, a3 e]
    · simp [hc, a4 e]
variable (A X : Type) [CommRing A] [CommRing X] [Algebra A X] (g : ℕ) (n) (a : ℕ)
def W1 := blkMat n a (ddPart A X g true false false false) (ddPart A X g false true false false)
def pairedDualFirstOrderDualMatrixSpace := blkMat n a (ddPart A X g false false false true) (ddPart A X g false false true false)
def W2 := blkMat n a (ddPart A X g false false true false) (ddPart A X g false false false true)
variable {A X g n a}
variable (F : GFrame l) {R : Type} [CommRing R] [Algebra A R]
def dY (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (Y : Matrix (Fin n) (Fin n) R) (g : F.G₀) : Matrix (Fin n) (Fin n) R :=
  ρ g * Y * ρ g⁻¹ - Y
def LocAt (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R)
    (z : F.G₀ → Matrix (Fin n) (Fin n) R) (v : F.Vl) (Y : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ g : F.Gv v, (∀ i j, j < i → (wi v * (z (F.φ v g) - dY F ρ Y (F.φ v g)) * w v) i j = 0) ∧
    (g ∈ F.mu v → ∀ i, (wi v * (z (F.φ v g) - dY F ρ Y (F.φ v g)) * w v) i i = 0)
def SelZ (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R)
    (V : Submodule A (Matrix (Fin n) (Fin n) R)) : Set (F.G₀ → Matrix (Fin n) (Fin n) R) :=
  {z | (∀ g, z g ∈ V) ∧ (∀ i j, AdicCont (Ideal.span {algebraMap A R t}) fun g => z g i j) ∧
    (∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹) ∧ (∀ g, z (F.conj g) = -(z g)ᵀ) ∧
    (∀ u, ∀ g ∈ F.Iu u, z g = 0) ∧ ∀ v, ∃ Y ∈ V, LocAt F ρ w wi z v Y}
def Bd (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)) :
    Set (F.G₀ → Matrix (Fin n) (Fin n) R) := {z | ∃ Y ∈ V, Yᵀ = -Y ∧ z = dY F ρ Y}
end Sel
structure NP (F : GFrame l) (n : ℕ) : Type 1 where
  K : Type
  [field : Field K]
  [fin : Finite K]
  [algZ : Algebra ℤ_[l] K]
  ρ : F.G₀ →* GL (Fin n) (PowerSeries K)
  cont : ∀ i j, AdicCont (maximalIdeal (PowerSeries K)) fun g => mat ρ g i j
  form : F.IsForm ℤ_[l] n ρ 1
  a : ℕ
  a_pos : 1 ≤ a
  a_le : a ≤ n
  blk : ∀ g, mat ρ g ∈ Ev (PowerSeries K) (PowerSeries K) n a
  span : ∀ Z ∈ Ev (PowerSeries K) (PowerSeries K) n a, ∃ s : ℕ,
    (PowerSeries.X : PowerSeries K) ^ s • Z ∈ Submodule.span (PowerSeries K) (mat ρ '' (F.G' : Set F.G₀))
  ine : ∀ u, ∀ g ∈ F.Iu u, ρ g = 1
  ψ : ∀ v, Fin n → F.Gv v →* (PowerSeries K)ˣ
  ψ_mu : ∀ v i, ∀ g ∈ F.mu v, ψ v i g = 1
  w : F.Vl → GL (Fin n) (PowerSeries K)
  ty : F.Vl → Fin n → Bool
  w_blk : ∀ v (i j : Fin n), decide ((i : ℕ) < a) ≠ ty v j → w v i j = 0
  tri : ∀ v g, (∀ i j, j < i → ((w v)⁻¹ * ρ (F.φ v g) * w v : GL (Fin n) (PowerSeries K)) i j = 0) ∧
    ∀ i, ((w v)⁻¹ * ρ (F.φ v g) * w v : GL (Fin n) (PowerSeries K)) i i = (ψ v i g : PowerSeries K)
  N1 : ∀ v, (∀ i j, i ≠ j → ψ v i ≠ ψ v j) ∧
    ∀ i j, i < j → ψ v i ≠ ψ v j * (F.eps ℤ_[l] (PowerSeries K)).comp (F.φ v)
attribute [instance] NP.field NP.fin NP.algZ
namespace NP
variable {F : GFrame l} {n : ℕ} (x : NP F n)
abbrev A : Type := PowerSeries x.K
abbrev t : x.A := PowerSeries.X
abbrev Am (m : ℕ) : Type := x.A ⧸ Ideal.span {x.t ^ m}
def N3 : Prop :=
  ∀ U : Set F.G₀, IsOpen U → (U ∩ (F.G' : Set F.G₀)).Nonempty →
    ∃ σ ∈ U ∩ (F.G' : Set F.G₀), ((mat x.ρ σ).charpoly.map (algebraMap x.A (FractionRing x.A))).Separable
def N4 (D : Subgroup F.G₀) : Prop :=
  ∀ Z : Matrix (Fin n) (Fin n) x.A,
    (∀ g ∈ D, ((F.eps ℤ_[l] x.A g : x.Aˣ) : x.A) • (mat x.ρ g * Z) = Z * mat x.ρ g) → Z = 0
variable (X : Type) [CommRing X] [Algebra x.A X]
def ρX (g : F.G₀) : Matrix (Fin n) (Fin n) X := (mat x.ρ g).map (algebraMap x.A X)
def wX (v : F.Vl) : Matrix (Fin n) (Fin n) X := (x.w v : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A X)
def wiX (v : F.Vl) : Matrix (Fin n) (Fin n) X := (((x.w v)⁻¹ : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A X)
end NP
structure Kap {F : GFrame l} {n : ℕ} (x : NP F n) where
  g : ℕ
  κ : Fin g → F.G₀ → Matrix (Fin n) (Fin n) x.A
  mem : ∀ j, κ j ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a)
  Y : Fin g → F.Vl → Matrix (Fin n) (Fin n) x.A
  Y_mem : ∀ j v, Y j v ∈ Od x.A x.A n x.a
  loc : ∀ j v, LocAt F (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (κ j) v (Y j v)
  indep : ∀ c : Fin g → x.A, ∑ j, c j • κ j ∈ Bd F (x.ρX x.A) (Od x.A x.A n x.a) → c = 0
  gen : ∀ z ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a), ∃ (s : ℕ) (c : Fin g → x.A),
    x.t ^ s • z - ∑ j, c j • κ j ∈ Bd F (x.ρX x.A) (Od x.A x.A n x.a)
namespace Kap
variable {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X]
def ρ1 (g : F.G₀) : Matrix (Fin n) (Fin n) (DD X k.g) :=
  (1 + DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) * x.ρX (DD X k.g) g
def w1 (v : F.Vl) : Matrix (Fin n) (Fin n) (DD X k.g) :=
  (1 - DD.epM fun j => (k.Y j v).map (algebraMap x.A X)) * x.wX (DD X k.g) v
def wi1 (v : F.Vl) : Matrix (Fin n) (Fin n) (DD X k.g) :=
  x.wiX (DD X k.g) v * (1 + DD.epM fun j => (k.Y j v).map (algebraMap x.A X))
end Kap
section Cover
variable {G G0 : Glob l L} (h : G.Hom G0) {n : ℕ} (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X]
def SelP := SelZ G.frame x.t (fun g => x.ρX X (h.p₀ g)) (x.wX X) (x.wiX X) (Ev x.A X n x.a)
def SelM := SelZ G.frame x.t (fun g => x.ρX X (h.p₀ g)) (x.wX X) (x.wiX X) (Od x.A X n x.a)
def BdM := Bd G.frame (fun g => x.ρX X (h.p₀ g)) (Od x.A X n x.a)
variable {x} (k : Kap x)
def Sel1 := SelZ G.frame x.t (fun g => k.ρ1 X (h.p₀ g)) (k.w1 X) (k.wi1 X) (W1 n x.A X k.g x.a)
def Bd1 := Bd G.frame (fun g => k.ρ1 X (h.p₀ g)) (W1 n x.A X k.g x.a)
def Sel2 := SelZ G.frame x.t (fun g => k.ρ1 X (h.p₀ g)) (k.w1 X) (k.wi1 X) (W2 n x.A X k.g x.a)
end Cover
def DiscSt {n : ℕ} {R G : Type} [CommRing R] [Group G] (D : GDet n R G) (Q : Ideal R) : Prop :=
  ∃ g h : Fin (n * n) → G, (Matrix.of fun i j => D.tr (MonoidAlgebra.single (g i * h j) 1)).det ∉ Q
def NonSS {R S G : Type} [CommRing R] [CommRing S] [Group G] (I : Set (MonoidAlgebra R G)) (φ : R →+* S) (Q : Ideal S) : Prop :=
  ∃ (κ : Type) (_ : Field κ) (f : S →+* κ), RingHom.ker f = Q ∧
    ¬ IsSemisimpleRing (TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (f.comp φ) '' I)).ringCon.Quotient
def GenBy (O : Type) {B : Type} [CommRing O] [CommRing B] [Algebra O B] [IsLocalRing B] (S : Set B) : Prop :=
  ∀ (N : ℕ) (b : B), ∃ a ∈ Algebra.adjoin O S, b - a ∈ maximalIdeal B ^ N
structure IsCompl (R : Type) [CommRing R] (q : Ideal R) (B : Type) [CommRing B] [Algebra R B] [IsLocalRing B] : Prop where
  noeth : IsNoetherianRing B
  complete : IsAdicComplete (maximalIdeal B) B
  dense : ∀ (N : ℕ) (b : B), ∃ a s : R, s ∉ q ∧ algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ N
  mem_iff : ∀ (N : ℕ) (a : R), algebraMap R B a ∈ maximalIdeal B ^ N ↔ ∃ s, s ∉ q ∧ s * a ∈ q ^ N
end UpperTheory.V.Pa


