-- Prove2me | Definitions.Def_GuardedSubstitutionReadout
-- name    : GuardedSubstitutionReadout
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T19:31:03.938225+00:00
-- url     : https://prove2.me/theorems/74dccb6c-b8c3-5b11-8609-86d1f306b5a5
-- title:
--   Guard summaries and prefix caches for substitution-generated words
-- statement:
--   A block of guarded affine updates is represented on homogeneous coordinates by a linear map and the subspace of states admitted by its guards. Chronological composition transports the later admissibility subspace back along the earlier map and intersects it with the earlier subspace. A finite rule assigns a word to each symbol, allowing empty words. At each substitution depth a vector stores the length and ordered product for each symbol; a prefix query follows a single partially included child at each level and reuses cached whole-child products.
-- source:
--   For grammar-compressed word access see Bille, Landau, Raman, Sadakane, Satti, and Weimann, Random Access to Grammar-Compressed Strings and Trees, SIAM Journal on Computing 44(3), Section 3, https://arxiv.org/abs/1001.1565. The guarded affine summary is the additional construction defined here.

import Mathlib

set_option autoImplicit false

namespace GuardedSubstitution.Affine

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def affineStep (A : Module.End K V) (b : V) (x : V) : V := A x + b

/-- Affine update on the first component, using the second as the constant
coordinate. -/
def liftUpdate (A : Module.End K V) (b : V) : Module.End K (V × K) where
  toFun x := (A x.1 + x.2 • b, x.2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul, Prod.mk_add_mk]
    congr 1
    abel
  map_smul' k x := by
    simp [smul_add, mul_smul]

/-- The observation is zero exactly when the affine guard takes its expected
value, provided the second component is one. -/
def liftGuard (guard : V →ₗ[K] K) (bias expected : K) : (V × K) →ₗ[K] K where
  toFun x := guard x.1 + (bias - expected) * x.2
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, mul_add]
    abel
  map_smul' k x := by
    change guard (k • x.1) + (bias - expected) * (k * x.2) =
      k * (guard x.1 + (bias - expected) * x.2)
    rw [map_smul]
    change k * guard x.1 + (bias - expected) * (k * x.2) =
      k * (guard x.1 + (bias - expected) * x.2)
    ring

end GuardedSubstitution.Affine

namespace GuardedSubstitution.Chunks

section Linear

variable (K V : Type*) [Semiring K] [AddCommMonoid V] [Module K V]

/-- A chronological chunk acts by its linear update on the states admitted
by all guards in the chunk. The update is recorded on the ambient space. -/
@[ext] structure Summary where
  update : Module.End K V
  admissible : Submodule K V

variable {K V}

private def chronological (early late : Summary K V) : Summary K V :=
  ⟨late.update.comp early.update, early.admissible ⊓ late.admissible.comap early.update⟩

private def empty : Summary K V := ⟨LinearMap.id, ⊤⟩

instance : Monoid (Summary K V) where
  one := empty
  mul := chronological
  one_mul a := by
    apply Summary.ext
    · ext x; rfl
    · ext x
      change (True ∧ x ∈ a.admissible) ↔ x ∈ a.admissible
      simp only [true_and]
  mul_one a := by
    apply Summary.ext
    · ext x; rfl
    · ext x
      change (x ∈ a.admissible ∧ True) ↔ x ∈ a.admissible
      simp only [and_true]
  mul_assoc a b c := by
    apply Summary.ext
    · ext x; rfl
    · ext x
      change ((x ∈ a.admissible ∧ a.update x ∈ b.admissible) ∧
        b.update (a.update x) ∈ c.admissible) ↔
        x ∈ a.admissible ∧ a.update x ∈ b.admissible ∧
          b.update (a.update x) ∈ c.admissible
      exact and_assoc

@[simp] theorem update_one (x : V) : (1 : Summary K V).update x = x := rfl

@[simp] theorem mem_one (x : V) : x ∈ (1 : Summary K V).admissible := trivial

@[simp] theorem update_mul (a b : Summary K V) (x : V) :
    (a * b).update x = b.update (a.update x) := rfl

@[simp] theorem mem_mul (a b : Summary K V) (x : V) :
    x ∈ (a * b).admissible ↔ x ∈ a.admissible ∧ a.update x ∈ b.admissible := Iff.rfl


end Linear

section Affine

open GuardedSubstitution.Affine (affineStep liftGuard liftUpdate)

variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]

/-- One affine update with an equality guard before the update. -/
structure Action where
  linear : Module.End K V
  translate : V
  probe : V →ₗ[K] K
  bias : K
  expected : K

variable {K V}

/-- Lifting adds the usual constant coordinate. Rejecting a guard is
represented by failure to lie in the kernel of its lifted probe. -/
def Action.summary (a : Action K V) : Summary K (V × K) :=
  ⟨liftUpdate a.linear a.translate, LinearMap.ker (liftGuard a.probe a.bias a.expected)⟩

@[simp] theorem action_summary_update (a : Action K V) (x : V) :
    a.summary.update (x, 1) = (affineStep a.linear a.translate x, 1) := by
  change (a.linear x + (1 : K) • a.translate, 1) = _
  rw [one_smul]
  rfl

@[simp] theorem action_summary_mem (a : Action K V) (x : V) :
    (x, (1 : K)) ∈ a.summary.admissible ↔ a.probe x + a.bias = a.expected := by
  rw [Action.summary, LinearMap.mem_ker]
  change a.probe x + (a.bias - a.expected) * 1 = 0 ↔ _
  rw [mul_one, ← add_sub_assoc, sub_eq_zero]

end Affine

end GuardedSubstitution.Chunks

namespace GuardedSubstitution.Prefixes

variable {k : ℕ} {M : Type*} [Monoid M]

/-- The semantic word after a fixed number of simultaneous substitutions. -/
def expansion (rule : Fin k → List (Fin k)) : ℕ → Fin k → List (Fin k)
  | 0, a => [a]
  | depth+1, a => (rule a).flatMap (expansion rule depth)

structure BlockSummary (M : Type*) where
  length : ℕ
  product : M

def combine (cached : Fin k → BlockSummary M) (children : List (Fin k)) : BlockSummary M :=
  ⟨(children.map fun b => (cached b).length).sum,
    (children.map fun b => (cached b).product).prod⟩

/-- Each level stores its complete summaries as an eager finite vector. -/
inductive Cache (k : ℕ) (M : Type*) : ℕ → Type _
  | leaf (values : Vector (BlockSummary M) k) : Cache k M 0
  | push {depth : ℕ} (values : Vector (BlockSummary M) k) (prior : Cache k M depth) :
      Cache k M (depth+1)

def Cache.top {depth : ℕ} : Cache k M depth → Vector (BlockSummary M) k
  | .leaf values => values
  | .push values _ => values

def build (rule : Fin k → List (Fin k)) (weight : Fin k → M) (depth : ℕ) : Cache k M depth :=
  match depth with
  | 0 => .leaf (Vector.ofFn fun a => ⟨1,weight a⟩)
  | depth+1 =>
    let prior := build rule weight depth
    .push (Vector.ofFn fun a => combine prior.top.get (rule a)) prior


/-- Whole skipped children contribute a cached product. Only the one
partial child invokes the lower-level prefixProduct query. -/
def scanPrefix (values : Fin k → BlockSummary M) (within : Fin k → ℕ → M) :
    List (Fin k) → ℕ → M
  | [],_ => 1
  | b::bs,t =>
    if t ≤ (values b).length then within b t
    else (values b).product * scanPrefix values within bs (t-(values b).length)

def prefixProduct (rule : Fin k → List (Fin k)) {depth : ℕ} (cache : Cache k M depth) :
    Fin k → ℕ → M :=
  match cache with
  | .leaf values => fun a t => if t = 0 then 1 else (values.get a).product
  | .push _ prior => fun a t => scanPrefix prior.top.get (prefixProduct rule prior) (rule a) t


end GuardedSubstitution.Prefixes

namespace GuardedSubstitution.Readout

open GuardedSubstitution.Prefixes GuardedSubstitution.Chunks
open GuardedSubstitution.Affine (affineStep)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {k : ℕ}

/-- A cache entry is both an update and the subspace admitted by all
guards. Its time index is the length of the represented action prefix. -/
def prefixSummary (rule : Fin k → List (Fin k)) (action : Fin k → Action K V)
    (depth : ℕ) (label : Fin k) (t : ℕ) : Summary K (V × K) :=
  prefixProduct rule (build rule (Action.summary ∘ action) depth) label t

end GuardedSubstitution.Readout


