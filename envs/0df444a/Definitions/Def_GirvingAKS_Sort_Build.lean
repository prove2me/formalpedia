-- Prove2me | Definitions.Def_GirvingAKS_Sort_Build
-- name    : GirvingAKS_Sort_Build
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:30:29.432789+00:00
-- url     : https://prove2.me/theorems/2fb9e9f9-dbeb-4915-88b8-143bd760d812
-- title:
--   AKS sorting networks (Seiferas port) — Build Monad for Comparator Networks
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Sort/Build.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** A writer monad that incrementally builds a `ComparatorNetwork` while computing a result. `Build n α` has a `.net` (accumulated comparators) and a `.value` (the result).
--
--   Use `emit` to append comparators, and standard `do` notation to sequence build steps that return intermediate results (e.g., new bag assignments after a split stage).
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Sort/Build.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Sort_Defs

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Sort/Build.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Build Monad for Comparator Networks

  A writer monad that incrementally builds a `ComparatorNetwork` while
  computing a result. `Build n α` has a `.net` (accumulated comparators)
  and a `.value` (the result).

  Use `emit` to append comparators, and standard `do` notation to
  sequence build steps that return intermediate results (e.g., new bag
  assignments after a split stage).
-/


section


/-- Writer monad that accumulates a `ComparatorNetwork n` alongside a result. -/
@[ext] structure Build (n : ℕ) (α : Type) where
  net : ComparatorNetwork n
  value : α

instance {n : ℕ} : Monad (Build n) where
  pure a := ⟨⟨[]⟩, a⟩
  bind b f := let r := f b.value; ⟨⟨b.net.comparators ++ r.net.comparators⟩, r.value⟩

instance {n : ℕ} : LawfulMonad (Build n) where
  map_const := by intros; funext; apply Build.ext <;> simp [Functor.mapConst, Functor.map]
  id_map := by intros; apply Build.ext <;> simp [Functor.map, List.append_nil]
  seqLeft_eq := by intros; apply Build.ext <;> simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.append_nil]
  seqRight_eq := by intros; apply Build.ext <;> simp [SeqRight.seqRight, Seq.seq, Functor.map]
  pure_seq := by intros; apply Build.ext <;> simp [Seq.seq, Functor.map, Pure.pure]
  bind_pure_comp := by intros; apply Build.ext <;> simp [Functor.map, Bind.bind, Pure.pure, List.append_nil]
  bind_map := by intros; apply Build.ext <;> simp [Seq.seq, Functor.map, Bind.bind]
  pure_bind := by intros; apply Build.ext <;> simp [Bind.bind, Pure.pure]
  bind_assoc := by intros; apply Build.ext <;> simp [Bind.bind, List.append_assoc]

/-- Append a comparator network to the accumulator. -/
def Build.emit {n : ℕ} (net : ComparatorNetwork n) : Build n Unit :=
  ⟨net, ()⟩

/-- Append a single comparator. -/
def Build.compare {n : ℕ} (c : Comparator n) : Build n Unit :=
  Build.emit ⟨[c]⟩

/-! **Simp lemmas** -/

@[simp] theorem Build.net_pure {n : ℕ} {α : Type} (a : α) :
    (Pure.pure a : Build n α).net = ⟨[]⟩ := rfl

@[simp] theorem Build.value_pure {n : ℕ} {α : Type} (a : α) :
    (Pure.pure a : Build n α).value = a := rfl

@[simp] theorem Build.net_emit {n : ℕ} (net : ComparatorNetwork n) :
    (Build.emit net).net = net := rfl

@[simp] theorem Build.net_bind {n : ℕ} {α β : Type}
    (b : Build n α) (f : α → Build n β) :
    (b >>= f).net = ⟨b.net.comparators ++ (f b.value).net.comparators⟩ := rfl

@[simp] theorem Build.value_bind {n : ℕ} {α β : Type}
    (b : Build n α) (f : α → Build n β) :
    (b >>= f).value = (f b.value).value := rfl

/-! **Execution** -/

/-- Executing the network from a bind is sequential execution. -/
theorem Build.exec_bind {n : ℕ} {α β γ : Type} [LinearOrder γ]
    (b : Build n α) (f : α → Build n β) (v : Fin n → γ) :
    (b >>= f).net.exec v = (f b.value).net.exec (b.net.exec v) := by
  show (⟨b.net.comparators ++ (f b.value).net.comparators⟩ : ComparatorNetwork n).exec v = _
  exact ComparatorNetwork.exec_append b.net (f b.value).net v

theorem Build.exec_pure {n : ℕ} {α β : Type} [LinearOrder α]
    (a : β) (v : Fin n → α) :
    (Pure.pure a : Build n β).net.exec v = v := by
  show (⟨[]⟩ : ComparatorNetwork n).exec v = v
  simp [ComparatorNetwork.exec]

theorem Build.exec_emit {n : ℕ} {α : Type} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) :
    (Build.emit net).net.exec v = net.exec v := rfl

end


