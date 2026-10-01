-- Prove2me | Definitions.Def_Yukon_2a6b3412af2af8cd7980168b
-- name    : Yukon_2a6b3412af2af8cd7980168b
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T16:19:56.388211+00:00
-- url     : https://prove2.me/theorems/e0040c0c-74ca-4c09-92c0-f9e033d65cfd
-- title:
--   YukonModule.PolyFun.Control.Monad.Hom.part0
-- statement:
--   Source module PolyFun.Control.Monad.Hom.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/Control/Monad/Hom.lean
--
--   yukon-proof-operation:949178b48fe8d0203f56047a199e5bc7453456b8deb750fa80a2ccd3528d13a9
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246OTQ5MTc4YjQ4ZmU4ZDAyMDNmNTYwNDdhMTk5ZTViYzc0NTM0NTZiOGRlYjc1MGZhODBhMmNjZDM1MjhkMTNhOSIsImhhc2giOiIzNzdkMTc1YjdiMTFiMzVlYjEzYzJmNGVmYWM4MmJiZGE5ZGMyOGExN2ZlMWQ5YTNkZmYzNTg0MTViM2JjOTg5Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8yYTZiMzQxMmFmMmFmOGNkNzk4MDE2OGIiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Definitions.Def_Yukon_a28c9fe400a38bdf3eceff63

public import Mathlib.CategoryTheory.Monad.Types


public import Mathlib.Order.CompleteLattice.Basic
public import Init
meta import Definitions.Def_Yukon_a28c9fe400a38bdf3eceff63
set_option backward.isDefEq.respectTransparency.types false
/-!
# Morphisms Between Monads

Basic definitions of maps between monads parameterized over any possible output type.
This is implemented with more constrained universes as `m ⟶ n` in mathlib category theory,
but this gives definitions more standardized to a cs context.

TODO: Evaluate more fine-grained `PureHom`/`BintHom`/etc, with `Class` versions as well.
Probably should be in the context of upstreaming things.
-/

@[expose] public section

universe u v w x y z

variable {m : Type u → Type v} {n : Type u → Type w}

/-- A `NatHom m n` for two functors `m` and `n` is a map `m α → n α` for each possible type `α`.
This is exactly an element of the category `m ⟶ n`, but that has more restricted universes -/
structure NatHom (m : Type u → Type v) (n : Type u → Type w) where
  /-- The underlying family of maps `m α → n α`, one for each type `α`. -/
  toFun : (α : Type u) → m α → n α

/-- `f mx` notation for `NatHom m n` applied to an element of `m α`, with implicit `α` inferred. -/
instance  _root_.instCoeFunNatHomForallForall : CoeFun (NatHom m n) (fun _f => {α : Type u} → m α → n α) where
  coe f {α} x := f.toFun α x

-- /-- A natural morphism / transformation that preserves the `pure` operation. -/
-- structure PureHom (m : Type u → Type v) [Pure m] (n : Type u → Type w) [Pure n]
--     extends NatHom m n where
--   toFun_pure' {α : Type u} (x : α) : toFun (pure x) = (pure x : n α)

-- /-- A natural morphism / transformation that preserves the `bind` operation. -/
-- structure BindHom (m : Type u → Type v) [Bind m] (n : Type u → Type w) [Bind n]
--     extends NatHom m n where
--   toFun_bind' {α β : Type u} (x : m α) (y : α → m β) :
--     toFun β (x >>= y) = toFun α x >>= toFun β ∘ y

/-- A `MonadHom m n` bundles a monad map `m ⟶ n` (represented as a `NatHom`) with proofs that
it respects the `bind` and `pure` operations in the underlying monad. -/
@[ext] structure MonadHom (m : Type u → Type v) [Pure m] [Bind m]
    (n : Type u → Type w) [Pure n] [Bind n] extends NatHom m n where --, PureHom m n, BindHom m n
  toFun_pure' {α} (x : α) : toFun α (pure x) = pure x
  toFun_bind' {α β} (x : m α) (y : α → m β) :
    toFun β (x >>= y) = toFun α x >>= fun x => toFun β (y x)

@[inherit_doc] infixr:25 " →ᵐ " => MonadHom

attribute [simp, grind =] MonadHom.toFun_pure' MonadHom.toFun_bind'

/-- `f mx` notation for `NatHom m n` applied to an element of `m α`, with implicit `α` inferred. -/
instance  _root_.instCoeFunMonadHomForallForall {m : Type u → Type v} [Pure m] [Bind m] {n : Type u → Type w} [Pure n] [Bind n] :
    CoeFun (m →ᵐ n) (fun _f => {α : Type u} → m α → n α) where
  coe f {α} x := f.toFun α x

/-- Similar to `AddHomClass` but for `MonadHom`. This becomes more important if we start defining
a hierarchy of these types (e.g. for `AlternativeMonad`s).
Note that getting `FunLike` to work has some `outParam` challenges, may not be workable. -/
class MonadHomClass (F : Type _)
    (m : outParam (Type u → Type v)) [Monad m]
    (n : outParam (Type u → Type w)) [Monad n]
    [hf : (α : Type u) → FunLike F (m α) (n α)] where
  map_pure {α} (x : α) (f : F) : (f : m α → n α) (pure x : m α) = pure x
  map_bind {α β} (x : m α) (y : α → m β) (f : F) :
    (f : m β → n β) (x >>= y) = (f : m α → n α) x >>= f ∘ y

-- namespace MonadHomClass

-- variable {F : Type _}
--   {m : outParam (Type u → Type v)} [Monad m]
--   {n : outParam (Type u → Type w)} [Monad n]
--   [hf : (α : Type u) → FunLike F (m α) (n α)]

-- @[simp] lemma mmap_pure [hf : (α : Type u) → FunLike F (m α) (n α)]
--     (f : F) [@MonadHomClass F m _ n _ hf]
--     (x : α) : F α (pure x) = pure x :=
--   MonadHomClass.map_pure x

-- -- dt: should we be using `F ∘ my`?
-- @[simp] lemma mmap_bind (F : (α : Type u) → m α → n α) [MonadHomClass m n F]
--     (mx : m α) (my : α → m β) : F β (mx >>= my) = F α mx >>= fun x => F β (my x) :=
--   MonadHomClass.map_bind mx my

-- @[simp] lemma mmap_map [LawfulMonad m] [LawfulMonad n] (F : (α : Type u) → m α → n α)
--     [MonadHomClass m n F] (x : m α) (g : α → β) : F β (g <$> x) = g <$> F α x := by
--   simp [map_eq_bind_pure_comp]

-- @[simp] lemma mmap_seq [LawfulMonad m] [LawfulMonad n] (F : (α : Type u) → m α → n α)
--     [MonadHomClass m n F] (x : m (α → β)) (y : m α) : F β (x <*> y) = F _ x <*> F α y := by
--   simp [seq_eq_bind_map]

-- @[simp] lemma mmap_seqLeft [LawfulMonad m] [LawfulMonad n] (F : (α : Type u) → m α → n α)
--     [MonadHomClass m n F] (x : m α) (y : m β) : F α (x <* y) = F α x <* F β y := by
--   simp [seqLeft_eq]

-- @[simp] lemma mmap_seqRight [LawfulMonad m] [LawfulMonad n] (F : (α : Type u) → m α → n α)
--     [MonadHomClass m n F] (x : m α) (y : m β) : F β (x *> y) = F α x *> F β y := by
--   simp [seqRight_eq]

-- instance ofLawfulMonadLiftT {m n : Type u → Type _} [Monad m] [Monad n]
--     [MonadLiftT m n] [LawfulMonadLiftT m n] : MonadHomClass m n (@liftM m n _) where
--   map_pure := by aesop
--   map_bind := by aesop

-- instance {m : Type u → Type _} [Monad m] : MonadHomClass m m (fun _ => id) where
--   map_pure := by aesop
--   map_bind := by aesop

-- instance {m n n' : Type u → Type _} [Monad m] [Monad n] [Monad n']
--     (f : (α : Type u) → m α → n α) (g : (α : Type u) → n α → n' α)
--     [MonadHomClass m n f] [MonadHomClass n n' g] : MonadHomClass m n' (fun α => g α ∘ f α) where
--   map_pure := by aesop
--   map_bind := by aesop

-- end MonadHomClass

namespace MonadHom

variable {m : Type u → Type v} [Monad m]
  {n : Type u → Type w} [Monad n]
  {n' : Type u → Type x} [Monad n']
  {n'' : Type u → Type y} [Monad n'']
  {α β γ : Type u}

/-- Extensionality for monad homomorphisms: two morphisms agreeing on every argument at every
type are equal. -/
@[ext] protected theorem ext' {F G : m →ᵐ n}
    (h : ∀ α (x : m α), F x = G x) : F = G := by aesop

@[grind =] lemma mmap_pure (F : m →ᵐ n) (x : α) : F (pure x) = pure x := by grind

-- dt: should we be using `F ∘ my`?
@[grind =] lemma mmap_bind (F : m →ᵐ n) (mx : m α) (my : α → m β) :
    F (mx >>= my) = F mx >>= fun x => F (my x) := by grind

@[simp, grind =] lemma mmap_map [LawfulMonad m] [LawfulMonad n] (F : m →ᵐ n) (x : m α) (g : α → β) :
    F (g <$> x) = g <$> F x := by simp [monad_norm]

@[simp] lemma mmap_seq [LawfulMonad m] [LawfulMonad n] (F : m →ᵐ n) (x : m (α → β)) (y : m α) :
    F (x <*> y) = F x <*> F y := by simp [monad_norm]

@[simp] lemma mmap_seqLeft [LawfulMonad m] [LawfulMonad n] (F : m →ᵐ n) (x : m α) (y : m β) :
    F (x <* y) = F x <* F y := by simp [seqLeft_eq]

@[simp] lemma mmap_seqRight [LawfulMonad m] [LawfulMonad n] (F : m →ᵐ n) (x : m α) (y : m β) :
    F (x *> y) = F x *> F y := by simp [seqRight_eq]

/-- Construct a `MonadHom` from a lawful monad lift. -/
def ofLift (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] : m →ᵐ n where
  toFun _ mx := liftM mx
  toFun_pure' := by simp
  toFun_bind' := by simp

@[simp, grind =] lemma ofLift_apply [MonadLiftT m n] [LawfulMonadLiftT m n] {α : Type u} (x : m α) :
    ofLift m n x = liftM x := rfl

/-- The identity morphism between a monad and itself. -/
def id (m : Type u → Type v) [Monad m] : m →ᵐ m where
  toFun _ mx := mx
  toFun_pure' _ := by simp
  toFun_bind' _ _ := by simp

@[simp, grind =] lemma id_apply (mx : m α) : MonadHom.id m mx = mx := rfl

/-- Compose two `MonadHom`s together by applying them in sequence. -/
protected def comp (G : n →ᵐ n') (F : m →ᵐ n) : m →ᵐ n' where
  toFun _ := G.toFun _ ∘ F.toFun _
  toFun_pure' := by simp
  toFun_bind' := by simp

/-- Infix notation for composition of monad homomorphisms, `G ∘ₘ F`. -/
infixr:90 " ∘ₘ "  => MonadHom.comp

@[simp, grind =] lemma comp_apply (G : n →ᵐ n') (F : m →ᵐ n) (x : m α) :
    (G ∘ₘ F) x = G (F x) := rfl

@[simp, grind =] lemma comp_id (F : m →ᵐ n) : F.comp (MonadHom.id m) = F := rfl

@[simp, grind =] lemma id_comp (F : m →ᵐ n) : (MonadHom.id n).comp F = F := rfl

@[grind =] lemma comp_assoc (H : n' →ᵐ n'') (G : n →ᵐ n') (F : m →ᵐ n) :
    (H ∘ₘ G) ∘ₘ F = H ∘ₘ (G ∘ₘ F) := rfl

/-- `pure`/`return` lawfully embed the `Id` monad into any lawful monad. -/
protected def pure (m) [Monad m] [LawfulMonad m] : Id →ᵐ m where
  toFun _ mx := pure mx.run
  toFun_pure' x := by simp
  toFun_bind' mx my := by simp

@[simp, grind =] lemma pure_apply (m) [Monad m] [LawfulMonad m] (x : Id α) :
    MonadHom.pure m x = pure x.run := rfl

end MonadHom

namespace StateT

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  [LawfulMonad m] [LawfulMonad n] {σ α : Type u}

/-- `StateT σ` is functorial on monad morphisms: a monad morphism `φ : m →ᵐ n` lifts to a monad
morphism `StateT σ m →ᵐ StateT σ n`, acting on the underlying state-run and threading the state
unchanged. This transports the naturality of a fold (for example,
`FreeM.liftM_natural`) through a *stateful*
handler — the form a `StateT`-threaded semantic morphism (such as an evaluation-distribution map)
needs. -/
def mapHom (φ : m →ᵐ n) : StateT σ m →ᵐ StateT σ n where
  toFun _ x := StateT.mk fun s => φ (x.run s)
  toFun_pure' a := by ext s; simp
  toFun_bind' x y := by ext s; simp

omit [LawfulMonad m] [LawfulMonad n] in
@[simp] lemma run_mapHom (φ : m →ᵐ n) (x : StateT σ m α) (s : σ) :
    (StateT.mapHom φ x).run s = φ (x.run s) := rfl

end StateT


