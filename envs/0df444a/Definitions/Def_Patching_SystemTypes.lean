-- Prove2me | Definitions.Def_Patching_SystemTypes
-- name    : Patching_SystemTypes
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/82df6253-8ab8-51d2-b1d9-fda7b14dc517
-- title:
--   Typeclass vocabulary for Taylor–Wiles patching systems
-- statement:
--   Six declarations set up the language in which an abstract patching argument over an index type $\iota$ can be stated. [`IsLocalRing.IsAdicTopology R`](../def/Patching_SystemTypes.html#L17), for a commutative local ring $R$ carrying a topological ring structure, is the one-field class asserting that this topology is the $\mathfrak{m}_R$-adic one, in Mathlib's sense of `IsAdic (maximalIdeal R)`. [`Algebra.TopologicallyFG R S`](../def/Patching_SystemTypes.html#L23), for an $R$-algebra $S$ that is a topological ring, asserts that there is a finite subset $s \subseteq S$ whose generated subalgebra $R[s]$ is dense in $S$; an instance records that an $R$-algebra of finite type is topologically finitely generated in this sense. [`Module.depth R M`](../def/Patching_SystemTypes.html#L34), for a module $M$ over a local ring $R$, is defined with values in $\mathbb{N} \cup \{\infty\}$ as the supremum of the lengths of those lists $s$ of elements of $R$ which are weakly $M$-regular (Mathlib's `RingTheory.Sequence.IsWeaklyRegular`) and all of whose entries lie in $\mathfrak{m}_R$; no nonvanishing condition on $M/sM$ is imposed, and the supremum of the empty set of lengths cannot occur since the empty list qualifies.
--
--   Three classes express the uniformity and convergence conditions consumed by patching. For a family $(R_i)_{i \in \iota}$ of local rings, [`Algebra.UniformlyBoundedRank`](../def/Patching_SystemTypes.html#L46) asks that for every $k$ there be a single $n \in \mathbb{N}$ with $\#(R_i/\mathfrak{m}_{R_i}^k) < n$ for all $i$, the cardinalities being taken as `Nat.card`, which vanishes on infinite types, so that the bound constrains the finite quotients. For a family $(M_i)$ of modules over a fixed ring $R$, [`Module.UniformlyBoundedRank`](../def/Patching_SystemTypes.html#L50) asks for one $n \in \mathbb{N}$ bounding every rank $\operatorname{rank}_{R/\operatorname{Ann}_R(M_i)} M_i$, the module structure over the quotient by the annihilator being the canonical one. Finally, [`IsPatchingSystem R M F`](../def/Patching_SystemTypes.html#L54), for a topological ring $R$, a family $(M_i)$ of $R$-modules and a filter $F$ on $\iota$, asserts that for every ideal $\alpha \subseteq R$ that is open as a subset, one has $\operatorname{Ann}_R(M_i) \le \alpha$ for $F$-almost all $i$; that is, the annihilators tend to $0$ along $F$.
--
--   **Relation to Mathlib.** The ingredients `IsAdic`, `Algebra.FiniteType`, `RingTheory.Sequence.IsWeaklyRegular`, `Module.annihilator` and `Module.quotientAnnihilator` are Mathlib's; the adic-topology class, the topological finite generation class (implied by `Algebra.FiniteType`, registered as an instance), the $\mathbb{N}\cup\{\infty\}$-valued depth of a module over a local ring, and the three patching predicates are the project's own.
--
--   **Where it is used.** These predicates are the hypotheses on a tower $(\Lambda, R_i, M_i)$ that the Taylor–Wiles patching method consumes: the $R_i$ are deformation rings at the successive Taylor–Wiles levels and the $M_i$ the associated modules of automorphic forms, and the uniform bounds together with the vanishing of the annihilators along a filter (an ultrafilter, in the applications) produce a patched module over a patched ring whose freeness is detected by a depth and dimension count. They thereby underlie the abstract form of the $R = \mathbb{T}$ statement used for modularity lifting in the proof of Fermat's Last Theorem.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (portions (≈42%; pre-publication provenance note: 'typeclass/predicate definitions of the Taylor–Wiles–Kisin patching set-up, itself ported from ImperialCollegeLondon/FLT (Andrew Yang, Kevin Buzzard et al.)'): `FLT/Patching/Utils/TopologicallyFG.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard; `FLT/Patching/Utils/Depth.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Michael Rothgang; `FLT/Patching/Utils/AdicTopology.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard; `FLT/Patching/Algebra.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Yaël Dillies; `FLT/Patching/Module.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Pietro Monticone, David Renshaw). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Patching_SystemTypes.lean

import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.Data.ENat.Lattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

namespace IsLocalRing

class IsAdicTopology (R : Type*) [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R] : Prop where
  isAdic : IsAdic (maximalIdeal R)

end IsLocalRing

class Algebra.TopologicallyFG (R S : Type*) [CommRing R] [Ring S] [Algebra R S]
    [TopologicalSpace S] [IsTopologicalRing S] : Prop where
  out : ∃ s : Finset S, Dense (Algebra.adjoin R (s : Set S) : Set S)

instance (priority := 100) {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    [TopologicalSpace S] [IsTopologicalRing S] [Algebra.FiniteType R S] :
    Algebra.TopologicallyFG R S where
  out := have ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S); ⟨s, by simp [hs]⟩

open RingTheory in

noncomputable def Module.depth (R M : Type*) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] : ℕ∞ :=
  sSup { List.length s | (s : List R)
    (_ : Sequence.IsWeaklyRegular M s)
    (_ : ∀ r ∈ s, r ∈ maximalIdeal R) }

section PatchingPredicates

attribute [local instance] Module.quotientAnnihilator

variable {ι : Type*}

class Algebra.UniformlyBoundedRank (R : ι → Type*) [∀ i, CommRing (R i)]
    [∀ i, IsLocalRing (R i)] : Prop where
  cond : ∀ k, ∃ n : ℕ, ∀ i, Nat.card (R i ⧸ maximalIdeal (R i) ^ k) < n

class Module.UniformlyBoundedRank (R : Type*) (M : ι → Type*) [CommRing R]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] : Prop where
  cond : ∃ n : ℕ, ∀ i, Module.rank (R ⧸ Module.annihilator R (M i)) (M i) < n

class IsPatchingSystem (R : Type*) (M : ι → Type*) [CommRing R] [TopologicalSpace R]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (F : Filter ι) : Prop where
  cond : ∀ α : Ideal R, IsOpen (X := R) α → ∀ᶠ i in F, Module.annihilator R (M i) ≤ α

end PatchingPredicates


