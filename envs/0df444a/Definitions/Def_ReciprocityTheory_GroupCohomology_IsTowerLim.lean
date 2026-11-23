-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_IsTowerLim
-- name    : ReciprocityTheory_GroupCohomology_IsTowerLim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:22.118199+00:00
-- url     : https://prove2.me/theorems/f42e65a9-05d3-4b3a-9d55-03e44a803cb1
-- title:
--   Is Tower Lim
-- statement:
--   Definitions and structural lemmas for Is Tower Lim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/IsTowerLim.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
noncomputable section
universe u
variable {R : Type u} [CommRing R]
structure Cx (R : Type u) [CommRing R] where
  X : ℕ → Type u
  [acg : ∀ n, AddCommGroup (X n)]
  [mod : ∀ n, Module R (X n)]
  d : ∀ n, X n →ₗ[R] X (n + 1)
  dd : ∀ n x, d (n + 1) (d n x) = 0
attribute [instance] Cx.acg Cx.mod
namespace Cx
def Z (A : Cx R) (n : ℕ) : Submodule R (A.X n) := LinearMap.ker (A.d n)
def B (A : Cx R) : (n : ℕ) → Submodule R (A.X n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (A.d n)
abbrev H (A : Cx R) (n : ℕ) := A.Z n ⧸ (A.B n).comap (A.Z n).subtype
def cls (A : Cx R) (n : ℕ) (x : A.X n) (hx : A.d n x = 0) : A.H n := Submodule.Quotient.mk ⟨x, hx⟩
structure Hom (A B : Cx R) where
  f : ∀ n, A.X n →ₗ[R] B.X n
  comm : ∀ n x, f (n + 1) (A.d n x) = B.d n (f n x)
variable {A B C : Cx R}
def Hom.id (A : Cx R) : Hom A A := ⟨fun _ => LinearMap.id, fun _ _ => rfl⟩
def Hom.comp (ψ : Hom B C) (φ : Hom A B) : Hom A C :=
  ⟨fun n => (ψ.f n).comp (φ.f n), fun n x => by simp [φ.comm, ψ.comm]⟩
def Hom.Z (φ : Hom A B) (n : ℕ) : A.Z n →ₗ[R] B.Z n :=
  (φ.f n).restrict fun x hx => by
    have hx' : A.d n x = 0 := hx
    show B.d n (φ.f n x) = 0
    rw [← φ.comm, hx', map_zero]
def Hom.H (φ : Hom A B) (n : ℕ) : A.H n →ₗ[R] B.H n :=
  Submodule.mapQ _ _ (φ.Z n) fun x hx => by
    cases n with
    | zero =>
      have hx' : x.1 = 0 := hx
      show φ.f 0 x.1 ∈ (⊥ : Submodule R _)
      rw [hx', map_zero]; exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨y, hy⟩ := hx
      refine ⟨φ.f n y, ?_⟩
      show B.d n (φ.f n y) = φ.f (n + 1) x.1
      rw [← φ.comm, hy]; rfl
def Hom.QuasiIso (φ : Hom A B) : Prop := ∀ n, Function.Bijective (φ.H n)
structure SES (i : Hom A B) (p : Hom B C) : Prop where
  inj : ∀ n, Function.Injective (i.f n)
  exact : ∀ n, Function.Exact (i.f n) (p.f n)
  surj : ∀ n, Function.Surjective (p.f n)
def IsConn (i : Hom A B) (p : Hom B C) (δ : ∀ n, C.H n →ₗ[R] A.H (n + 1)) : Prop :=
  ∀ n (b : B.X n) (a : A.X (n + 1)) (hc : C.d n (p.f n b) = 0) (ha : A.d (n + 1) a = 0),
    B.d n b = i.f (n + 1) a → δ n (C.cls n (p.f n b) hc) = A.cls (n + 1) a ha
structure LES (i : Hom A B) (p : Hom B C) (δ : ∀ n, C.H n →ₗ[R] A.H (n + 1)) : Prop where
  inj : Function.Injective (i.H 0)
  exB : ∀ n, Function.Exact (i.H n) (p.H n)
  exC : ∀ n, Function.Exact (p.H n) (δ n)
  exA : ∀ n, Function.Exact (δ n) (i.H (n + 1))
def up (B : Cx R) : Cx R where
  X n := match n with | 0 => PUnit | n + 1 => B.X n
  acg n := match n with | 0 => inferInstance | _ + 1 => inferInstance
  mod n := match n with | 0 => inferInstance | _ + 1 => inferInstance
  d n := match n with | 0 => 0 | n + 1 => -B.d n
  dd n x := match n with
    | 0 => by show -B.d 0 0 = 0; simp
    | n + 1 => by show -B.d (n + 1) (-B.d n x) = 0; simp [B.dd]
def fib (φ : Hom A B) : Cx R where
  X n := A.X n × B.up.X n
  d n := LinearMap.prod ((A.d n).comp (LinearMap.fst R _ _))
    ((show A.X n →ₗ[R] B.up.X (n + 1) from φ.f n).coprod (B.up.d n))
  dd n x := by
    refine Prod.ext (A.dd n x.1) ?_
    have h := B.up.dd n x.2
    show φ.f (n + 1) (A.d n x.1) + -B.d n (φ.f n x.1 + (show B.X n from B.up.d n x.2)) = 0
    have h' : -B.d n (show B.X n from B.up.d n x.2) = 0 := h
    rw [map_add, neg_add, h', φ.comm]; simp
def fibFst (φ : Hom A B) : Hom (fib φ) A := ⟨fun _ => LinearMap.fst R _ _, fun _ _ => rfl⟩
def IsFibConn (φ : Hom A B) (δ : ∀ n, B.H n →ₗ[R] (fib φ).H (n + 1)) : Prop :=
  ∀ n (b : B.X n) (hb : B.d n b = 0) (h : (fib φ).d (n + 1) (0, b) = 0),
    δ n (B.cls n b hb) = (fib φ).cls (n + 1) (0, b) h
def prod (A B : Cx R) : Cx R where
  X n := A.X n × B.X n
  d n := (A.d n).prodMap (B.d n)
  dd n x := Prod.ext (A.dd n x.1) (B.dd n x.2)
def pi {ι : Type u} (A : ι → Cx R) : Cx R where
  X n := ∀ v, (A v).X n
  d n := LinearMap.pi fun v => ((A v).d n).comp (LinearMap.proj v)
  dd n x := funext fun v => (A v).dd n (x v)
def prodFst (A B : Cx R) : Hom (prod A B) A := ⟨fun _ => LinearMap.fst R _ _, fun _ _ => rfl⟩
def prodSnd (A B : Cx R) : Hom (prod A B) B := ⟨fun _ => LinearMap.snd R _ _, fun _ _ => rfl⟩
def piProj {ι : Type u} (A : ι → Cx R) (v : ι) : Hom (pi A) (A v) :=
  ⟨fun _ => LinearMap.proj v, fun _ _ => rfl⟩
def FinLen (A : Cx R) (N : ℕ) : Prop :=
  (∀ n, IsFiniteLength R (A.H n)) ∧ ∀ n, N < n → Subsingleton (A.H n)
def chi (A : Cx R) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (-1) ^ n * ((Module.length R (A.H n)).toNat : ℤ)
structure IsTowerLim (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (L : Cx R) (π : ∀ m, Hom L (A m)) :
    Prop where
  surj : ∀ m n, Function.Surjective ((τ m).f n)
  compat : ∀ m n x, (τ m).f n ((π (m + 1)).f n x) = (π m).f n x
  ext : ∀ n (x : L.X n), (∀ m, (π m).f n x = 0) → x = 0
  lift : ∀ n (y : ∀ m, (A m).X n), (∀ m, (τ m).f n (y (m + 1)) = y m) → ∃ x, ∀ m, (π m).f n x = y m
end Cx
end
end ReciprocityTheory.Coh


