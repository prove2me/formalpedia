-- Prove2me | Definitions.Def_LanglandsTunnell_SchwartzBruhatSpace
-- name    : LanglandsTunnell_SchwartzBruhatSpace
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/09d86bd2-7c72-5e1e-865d-1410c24244f1
-- title:
--   Schwartz–Bruhat test functions as a complex submodule
-- statement:
--   Over a topological space $X$, the module assembles the Schwartz–Bruhat test functions into a single algebraic object. By the definition of `IsSchwartzBruhat` in the local Tate theory module, a function $f : X \to \mathbb{C}$ is a Schwartz–Bruhat function exactly when it is locally constant (in Mathlib's sense: preimages of arbitrary sets are open) and has compact support (its topological support, the closure of $\{x : f(x) \neq 0\}$, is compact). The declaration `testSpace X` is the $\mathbb{C}$-submodule of the function space $X \to \mathbb{C}$ whose carrier is the set of such $f$: the zero function qualifies, a sum of two qualifying functions qualifies, and a scalar multiple $c \cdot f$ qualifies, local constancy being preserved under postcomposition with $x \mapsto cx$ and compact support under postcomposition with a map fixing $0$.
--
--   The remaining declarations record the elementary consequences of this description. Membership in `testSpace X` is the predicate `IsSchwartzBruhat f` itself (`mem_testSpace`), equivalently the conjunction of local constancy and compact support (`mem_testSpace_iff`), with the two projections and the converse construction stated separately (`isLocallyConstant_of_mem`, `hasCompactSupport_of_mem`, `mem_testSpace_of`). For a clopen compact $U \subseteq X$ and $c \in \mathbb{C}$, the function equal to $c$ on $U$ and $0$ off $U$ belongs to `testSpace X` (`indicator_mem_testSpace`). The submodule is stable under multiplication by an arbitrary locally constant function: if $e$ is locally constant and $f \in$ `testSpace X`, then $e \cdot f \in$ `testSpace X` (`mul_mem_testSpace`). Finally, for a member $f$ the set $\{x : f(x) \neq 0\}$ is clopen, being the complement of the fibre of $f$ over $0$ (`isClopen_support_of_mem`), and hence is itself compact, being a closed subset of the compact topological support (`isCompact_support_of_mem`). No topology, norm or measure is placed on `testSpace X`; its algebraic structure is that of a submodule of a function space.
--
--   **Relation to Mathlib.** `IsLocallyConstant` and `HasCompactSupport` are Mathlib's; Mathlib's `SchwartzMap` is the archimedean Schwartz space of rapidly decreasing smooth functions, a different notion, and it has no non-archimedean Schwartz–Bruhat space, so the predicate `IsSchwartzBruhat` and the submodule `testSpace` are the project's own.
--
--   **Where it is used.** The test space is the domain on which the local zeta integrals and the Fourier transform of the accompanying local Tate theory are intended to act, inputs to the Langlands–Tunnell part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_SchwartzBruhatSpace.lean

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Compact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.TateLocal

noncomputable section

namespace SchwartzBruhatSpace

section Space

variable (X : Type*) [TopologicalSpace X]

abbrev testSpace : Submodule ℂ (X → ℂ) where
  carrier := {f | IsSchwartzBruhat f}
  zero_mem' := IsSchwartzBruhat.zero
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    refine ⟨?_, ?_⟩
    · exact hf.1.comp (c * ·)
    · exact hf.2.comp_left (g := (c * ·)) (mul_zero c)

variable {X}

theorem mem_testSpace {f : X → ℂ} : f ∈ testSpace X ↔ IsSchwartzBruhat f :=
  Iff.rfl

theorem mem_testSpace_iff {f : X → ℂ} : f ∈ testSpace X ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl

theorem isLocallyConstant_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) : IsLocallyConstant f :=
  hf.1

theorem hasCompactSupport_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) : HasCompactSupport f :=
  hf.2

theorem mem_testSpace_of {f : X → ℂ} (h₁ : IsLocallyConstant f) (h₂ : HasCompactSupport f) :
    f ∈ testSpace X :=
  ⟨h₁, h₂⟩

theorem indicator_mem_testSpace {U : Set X} (hU : IsClopen U) (hUc : IsCompact U) (c : ℂ) :
    (U.indicator fun _ => c) ∈ testSpace X :=
  IsSchwartzBruhat.indicator_const hU hUc c

theorem mul_mem_testSpace {e f : X → ℂ} (he : IsLocallyConstant e) (hf : f ∈ testSpace X) :
    e * f ∈ testSpace X :=
  ⟨he.mul hf.1, hf.2.mul_left⟩

theorem isClopen_support_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) : IsClopen (Function.support f) := by
  have h : Function.support f = {x | f x = 0}ᶜ := by
    ext x
    simp only [Function.mem_support, Set.mem_compl_iff, Set.mem_setOf_eq, ne_eq]
  rw [h]
  exact (hf.1.isClopen_fiber 0).compl

theorem isCompact_support_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) : IsCompact (Function.support f) :=
  (hasCompactSupport_of_mem hf).isCompact.of_isClosed_subset (isClopen_support_of_mem hf).isClosed (subset_tsupport _)

end Space

end SchwartzBruhatSpace


