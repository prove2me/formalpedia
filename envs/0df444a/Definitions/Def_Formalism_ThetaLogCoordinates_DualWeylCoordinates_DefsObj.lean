-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsObj
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsObj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:37.25574+00:00
-- url     : https://prove2.me/theorems/5816113d-7bdf-4d8d-a2e3-cb28bd5a93a3
-- title:
--   Defs Obj
-- statement:
--   Definitions and structural lemmas for Defs Obj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DefsObj.lean

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
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
structure UniformizedDVR (p : ℕ) (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] where

  w : O
  w_irr : Irreducible w

  p_mem : (p : O) ∈ IsLocalRing.maximalIdeal O
  p_ne : (p : O) ≠ 0

  complete : IsAdicComplete (IsLocalRing.maximalIdeal O) O
variable {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
abbrev KK (O : Type*) [CommRing O] [IsDomain O] := FractionRing O
structure Letters (ι : Type*) where
  vec : ι → Bool
def multideg {ι : Type*} {n : ℕ} (m : ι × Fin n →₀ ℕ) (i : ι) : ℕ := ∑ c : Fin n, m (i, c)
def Pol (R : Type*) [CommSemiring R] {ι : Type*} (n : ℕ) (d : ι → ℕ) :
    Submodule R (MvPolynomial (ι × Fin n) R) :=
  MvPolynomial.restrictSupport R {m | ∀ i, multideg m i = d i}
def genMat (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) R) :=
  Matrix.of fun a b => X (a, b)
abbrev GLCoord (R : Type*) [CommRing R] (n : ℕ) := Localization.Away (genMat R n).det
def lastIdx (n : ℕ) [NeZero n] : Fin n := ⟨n - 1, Nat.sub_lt (NeZero.pos n) Nat.one_pos⟩
open Classical in

def glAct (R : Type*) [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) (a b : Fin n) :
    MvPolynomial (ι × Fin n) R →ₗ[R] MvPolynomial (ι × Fin n) R :=
  ∑ l : ι,
    if l ∈ S then
      (if LL.vec l then (LinearMap.mulLeft R (X (l, a))) ∘ₗ (pderiv (l, b)).toLinearMap
       else -((LinearMap.mulLeft R (X (l, b))) ∘ₗ (pderiv (l, a)).toLinearMap))
    else 0
abbrev GLOps (n : ℕ) (K V : Type*) [Field K] [AddCommGroup V] [Module K V] := Fin n → Fin n → Module.End K V
variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
def weightSp (E : GLOps n K V) (mu : Fin n → ℤ) : Submodule K V :=
  ⨅ a, LinearMap.ker (E a a - (mu a : K) • (1 : Module.End K V))
def IsGLRep (E : GLOps n K V) : Prop :=
  (∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)) ∧
  (∀ x : V, ∃ W : Submodule K V, FiniteDimensional K W ∧ x ∈ W ∧ ∀ a b, ∀ y ∈ W, E a b y ∈ W) ∧
  (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤
def wtsOf (E : GLOps n K V) (W : Submodule K V) : Set (Fin n → ℤ) := {mu | weightSp E mu ⊓ W ≠ ⊥}
def Dominant (mu : Fin n → ℤ) : Prop := Antitone mu
def dualWt (lam : Fin n → ℤ) : Fin n → ℤ := fun a => -lam (Fin.rev a)
def divPowE (E : GLOps n K V) (a b : Fin n) (k : ℕ) : Module.End K V := ((k.factorial : K)⁻¹) • (E a b) ^ k
def binomE (E : GLOps n K V) (a : Fin n) (k : ℕ) : Module.End K V :=
  ((k.factorial : K)⁻¹) • ((List.range k).map fun j : ℕ => E a a - (j : K) • (1 : Module.End K V)).prod
def UZgens (E : GLOps n K V) : Set (Module.End K V) :=
  {u | (∃ a b k, a ≠ b ∧ u = divPowE E a b k) ∨ (∃ a k, u = binomE E a k)}
def UZmon (E : GLOps n K V) : Submonoid (Module.End K V) := Submonoid.closure (UZgens E)
def Umon (E : GLOps n K V) : Submonoid (Module.End K V) := Submonoid.closure (Set.range fun ab : Fin n × Fin n => E ab.1 ab.2)
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
def UZStable [Module O V] [Algebra O K] [IsScalarTower O K V] (E : GLOps n K V) (M : Submodule O V) : Prop := ∀ u ∈ UZgens E, ∀ x ∈ M, u x ∈ M
def UZLattice [Module O V] [Algebra O K] [IsScalarTower O K V] (E : GLOps n K V) (M : Submodule O V) : Prop :=
  UZStable (O := O) E M ∧ M.FG
def MQ [Module O V] [Algebra O K] [IsScalarTower O K V] (M : Submodule O V) : Submodule K V := Submodule.span K (M : Set V)
def IsHWV (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) : Prop :=
  v ≠ 0 ∧ v ∈ weightSp E lam ∧ ∀ a b, a < b → E a b v = 0
def IsIrrHW (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) : Prop :=
  IsGLRep E ∧ Dominant lam ∧ IsHWV E lam v ∧ Submodule.span K {x | ∃ u ∈ Umon E, x = u v} = ⊤
def Delta [Module O V] [Algebra O K] [IsScalarTower O K V] (E : GLOps n K V) (v : V) : Submodule O V :=
  Submodule.span O {x | ∃ u ∈ UZmon E, x = u v}
def otherWts (E : GLOps n K V) (lam : Fin n → ℤ) : Submodule K V := ⨆ mu ∈ {mu | mu ≠ lam}, weightSp E mu
def Nabla [Module O V] [Algebra O K] [IsScalarTower O K V] (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) : Set V :=
  {x | ∀ u ∈ UZmon E, ∃ c : O, u x - (algebraMap O K c) • v ∈ otherWts E lam}
def NablaSub [Module O V] [Algebra O K] [IsScalarTower O K V] (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) :
    Submodule O V where
  carrier := Nabla (O := O) E lam v
  zero_mem' := fun u _ => ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy u hu
    obtain ⟨c, hc⟩ := hx u hu
    obtain ⟨d, hd⟩ := hy u hu
    refine ⟨c + d, ?_⟩
    have : u (x + y) - (algebraMap O K (c + d)) • v = (u x - (algebraMap O K c) • v) + (u y - (algebraMap O K d) • v) := by
      rw [map_add, map_add, add_smul]; abel
    rw [this]; exact Submodule.add_mem _ hc hd
  smul_mem' := by
    intro a x hx u hu
    obtain ⟨c, hc⟩ := hx u hu
    refine ⟨a * c, ?_⟩
    have : u (a • x) - (algebraMap O K (a * c)) • v = (algebraMap O K a) • (u x - (algebraMap O K c) • v) := by
      rw [← algebraMap_smul K a x, map_smul, map_mul, smul_sub, mul_smul]
    rw [this]; exact Submodule.smul_mem _ _ hc
def isoSub (E : GLOps n K V) (lam : Fin n → ℤ) : Submodule K V :=
  Submodule.span K {x | ∃ u ∈ Umon E, ∃ v, IsHWV E lam v ∧ x = u v}
def IsIsoProj (E : GLOps n K V) (lam : Fin n → ℤ) (e : Module.End K V) : Prop :=
  (∀ x ∈ isoSub E lam, e x = x) ∧ ∀ mu, mu ≠ lam → ∀ x ∈ isoSub E mu, e x = 0
def IsWtProj (E : GLOps n K V) (mu : Fin n → ℤ) (e : Module.End K V) : Prop :=
  (∀ x ∈ weightSp E mu, e x = x) ∧ ∀ nu, nu ≠ mu → ∀ x ∈ weightSp E nu, e x = 0
def HStrip (nu mu : Fin n → ℤ) (b : ℕ) : Prop :=
  (∀ a, nu a ≤ mu a) ∧ (∀ a : Fin n, ∀ h : a.1 + 1 < n, mu ⟨a.1 + 1, h⟩ ≤ nu a) ∧ ∑ a, (mu a - nu a) = (b : ℤ)
structure PPath (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) where
  mu : Fin (N + 1) → Fin n → ℤ
  zero : mu 0 = 0
  dom : ∀ i, Dominant (mu i)
  step : ∀ i : Fin N, if LL.vec i then HStrip (mu i.castSucc) (mu i.succ) (B i) else HStrip (mu i.succ) (mu i.castSucc) (B i)
def glOps (K : Type*) [Field K] {ι : Type*} [Fintype ι] (n : ℕ) (LL : Letters ι) (S : Set ι) :
    GLOps n K (MvPolynomial (ι × Fin n) K) :=
  fun a b => glAct K LL S a b
def pEnd {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : Fin n → ℤ := mu (Fin.last N)
def colH {n : ℕ} (mu : Fin n → ℤ) (c : ℤ) : ℕ := (univ.filter fun m => c ≤ mu m).card
def extOne {n : ℕ} {P : Type*} [CommRing P] : Finset (Fin n) → P := fun J => if J = ∅ then 1 else 0
def wedgeR {n : ℕ} {P : Type*} [CommRing P] (x : Fin n → P) (K : Finset (Fin n) → P) : Finset (Fin n) → P :=
  fun J => ∑ m ∈ J, (-1 : P) ^ (J.filter fun j => m < j).card * x m * K (J.erase m)
def contrR {n : ℕ} {P : Type*} [CommRing P] (x : Fin n → P) (K : Finset (Fin n) → P) : Finset (Fin n) → P :=
  fun J => ∑ m ∈ univ \ J, (-1 : P) ^ (J.filter fun j => m < j).card * x m * K (insert m J)
def colStep {n : ℕ} {P : Type*} [CommRing P] (c : ℤ) (hP hN : ℕ) (x : Fin n → P) (K : Finset (Fin n) → P) :
    Finset (Fin n) → P :=
  if hP < hN then (if 1 ≤ c then wedgeR x K else contrR x K)
  else if hN < hP then (if 1 ≤ c then contrR x K else wedgeR x K)
  else K
def letVec (R : Type*) [CommRing R] {N n : ℕ} (i : Fin N) : Fin n → MvPolynomial (Fin N × Fin n) R :=
  fun m => X (i, m)
def Kcol (R : Type*) [CommRing R] {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ) :
    ℕ → Finset (Fin n) → MvPolynomial (Fin N × Fin n) R
  | 0 => extOne
  | j + 1 =>
    if h : j < N then
      colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (letVec R ⟨j, h⟩) (Kcol R mu c j)
    else Kcol R mu c j
def colRange {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : Finset ℤ :=
  let T : ℤ := ∑ i, ∑ m, |mu i m|
  Finset.Icc (-T) T
def Psi (R : Type*) [CommRing R] {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (I : ℤ → Finset (Fin n)) :
    MvPolynomial (Fin N × Fin n) R :=
  ∏ c ∈ colRange mu, Kcol R mu c N (I c)
def Ican {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : ℤ → Finset (Fin n) := fun c =>
  if 1 ≤ c then univ.filter (fun m : Fin n => m.val < colH (pEnd mu) c)
  else univ.filter (fun m : Fin n => colH (pEnd mu) c ≤ m.val)
def tabCol {n : ℕ} (I : ℤ → Finset (Fin n)) (c : ℤ) : Finset (Fin n) := if 1 ≤ c then I c else univ \ I c
def IsSt {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (I : ℤ → Finset (Fin n)) : Prop :=
  (∀ c, c ∉ colRange mu → I c = ∅) ∧
  (∀ c, (I c).card = if 1 ≤ c then colH (pEnd mu) c else n - colH (pEnd mu) c) ∧
  ∀ c (t : Fin n), ((tabCol I (c + 1)).filter (· ≤ t)).card ≤ ((tabCol I c).filter (· ≤ t)).card
end Formalism.InvariantFactorPaths.ColumnFamilies


