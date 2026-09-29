-- Prove2me | Definitions.Def_AutomorphicForm_GL2RealKTypeModule
-- name    : AutomorphicForm_GL2RealKTypeModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/52a247a9-d663-5474-8709-416106100cd1
-- title:
--   (g,K)-modules for GL2​(R) via weight data
-- statement:
--   Fix a complex vector space $M$. The structure [`AutomorphicForm.IsGL2RealKTypeModule`](../def/AutomorphicForm_GL2RealKTypeModule.html#L9) is a predicate on a chosen presentation: the data are a family of $\mathbb C$-subspaces $wt : \mathbb Z \to \mathrm{Submodule}\ \mathbb C\ M$, written $M_n = wt(n)$, together with three $\mathbb C$-linear endomorphisms $E, L, \varepsilon$ of $M$, and the fields assert: (i) $M$ is the internal direct sum of the $M_n$ (`DirectSum.IsInternal wt`); (ii) $E(M_n) \subseteq M_{n+2}$ and (iii) $L(M_n) \subseteq M_{n-2}$, stated as inclusions of images of submodules; (iv) for every $n$ and every $v \in M_n$, $E(Lv) - L(Ev) = n\cdot v$, the scalar being the image of $n \in \mathbb Z$ in $\mathbb C$; (v) $\varepsilon(M_n) \subseteq M_{-n}$; (vi) $\varepsilon \circ \varepsilon = \mathrm{id}$; (vii) $\varepsilon \circ E = L \circ \varepsilon$. Thus $M_n$ plays the role of the subspace of $\mathrm{SO}(2)$-weight $n$, $E$ and $L$ of the raising and lowering elements of $\mathfrak{gl}_2(\mathbb R)\otimes\mathbb C$ with $[E,L]$ acting by the weight, and $\varepsilon$ of the reflection in $\mathrm O(2)$; no central or Casimir datum is part of the structure.
--
--   `IsGL2RealKTypeSubmodule wt E L ε W` is the conjunction of four conditions on a subspace $W$: $W \le \bigsqcup_n (W \sqcap M_n)$ (the supremum of the intersections of $W$ with the weight spaces), and $E(W) \subseteq W$, $L(W) \subseteq W$, $\varepsilon(W) \subseteq W$. `IsIrreducibleGL2RealKTypeModule wt E L ε` asserts that some $v \in M$ is nonzero and that every such $W$ equals $\bot$ or $\top$; note that it does not itself require `IsGL2RealKTypeModule`.
--
--   The remaining declarations record: the two definitions unfold to their stated conjunctions; $\bot$ is always such a submodule and $\top$ is one whenever `IsGL2RealKTypeModule` holds (via the internal direct sum spanning $M$); a subsingleton $M$ is never irreducible; and, from the axioms, $\varepsilon \circ L = E \circ \varepsilon$, $\varepsilon(\varepsilon v) = v$, and the pointwise forms $v \in M_n \Rightarrow Ev \in M_{n+2}$, $Lv \in M_{n-2}$, $\varepsilon v \in M_{-n}$.
--
--   **Relation to Mathlib.** Mathlib has no notion of $(\mathfrak g,K)$-module or of $K$-type decomposition; this axiomatisation is the project's own, phrased with Mathlib's `DirectSum.IsInternal`, `Submodule.map` and the submodule lattice.
--
--   **Where it is used.** These predicates supply the vocabulary in which the archimedean component of an automorphic representation of $\mathrm{GL}_2$ at a real place is described through its $\mathrm{O}(2)$-types: weight spaces, weight-stable invariant subspaces, and irreducibility in that sense. Several modules of the development import them for statements about real local components and their weights.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_GL2RealKTypeModule.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AutomorphicForm

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

structure IsGL2RealKTypeModule (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) : Prop where
  isInternal : DirectSum.IsInternal wt
  map_raise_le : ∀ n : ℤ, (wt n).map E ≤ wt (n + 2)
  map_lower_le : ∀ n : ℤ, (wt n).map L ≤ wt (n - 2)
  raise_lower_sub : ∀ (n : ℤ) (v : M), v ∈ wt n → E (L v) - L (E v) = (n : ℂ) • v
  map_refl_le : ∀ n : ℤ, (wt n).map ε ≤ wt (-n)
  refl_comp_refl : ε ∘ₗ ε = LinearMap.id
  refl_comp_raise : ε ∘ₗ E = L ∘ₗ ε

def IsGL2RealKTypeSubmodule (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M)
    (W : Submodule ℂ M) : Prop :=
  W ≤ (⨆ n : ℤ, W ⊓ wt n) ∧ W.map E ≤ W ∧ W.map L ≤ W ∧ W.map ε ≤ W

def IsIrreducibleGL2RealKTypeModule (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) : Prop :=
  (∃ v : M, v ≠ 0) ∧
    ∀ W : Submodule ℂ M, IsGL2RealKTypeSubmodule wt E L ε W → W = ⊥ ∨ W = ⊤

theorem isGL2RealKTypeSubmodule_iff (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M)
    (W : Submodule ℂ M) :
    IsGL2RealKTypeSubmodule wt E L ε W ↔
      W ≤ (⨆ n : ℤ, W ⊓ wt n) ∧ W.map E ≤ W ∧ W.map L ≤ W ∧ W.map ε ≤ W :=
  Iff.rfl

theorem isIrreducibleGL2RealKTypeModule_iff (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) :
    IsIrreducibleGL2RealKTypeModule wt E L ε ↔
      (∃ v : M, v ≠ 0) ∧
        ∀ W : Submodule ℂ M, IsGL2RealKTypeSubmodule wt E L ε W → W = ⊥ ∨ W = ⊤ :=
  Iff.rfl

theorem isGL2RealKTypeSubmodule_bot (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) :
    IsGL2RealKTypeSubmodule wt E L ε ⊥ := by
  refine ⟨bot_le, ?_, ?_, ?_⟩ <;> simp

theorem isGL2RealKTypeSubmodule_top {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) : IsGL2RealKTypeSubmodule wt E L ε ⊤ := by
  refine ⟨?_, le_top, le_top, le_top⟩
  have htop : (⨆ n : ℤ, wt n) = ⊤ := h.isInternal.submodule_iSup_eq_top
  simp only [top_inf_eq]
  rw [htop]

theorem not_isIrreducibleGL2RealKTypeModule_of_subsingleton [Subsingleton M]
    (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) :
    ¬ IsIrreducibleGL2RealKTypeModule wt E L ε := fun h => by
  obtain ⟨⟨v, hv⟩, -⟩ := h
  exact hv (Subsingleton.elim v 0)

theorem IsGL2RealKTypeModule.refl_comp_lower {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) : ε ∘ₗ L = E ∘ₗ ε := by
  have hεε : ∀ v : M, ε (ε v) = v := fun v => by
    simpa using LinearMap.congr_fun h.refl_comp_refl v
  have hεE : ∀ v : M, ε (E v) = L (ε v) := fun v => by
    simpa using LinearMap.congr_fun h.refl_comp_raise v
  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply]
  have := hεE (ε v)
  rw [hεε] at this
  rw [← this, hεε]

theorem IsGL2RealKTypeModule.refl_refl {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) (v : M) : ε (ε v) = v := by
  have := LinearMap.congr_fun h.refl_comp_refl v
  simpa using this

theorem IsGL2RealKTypeModule.raise_mem {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) {n : ℤ} {v : M} (hv : v ∈ wt n) : E v ∈ wt (n + 2) :=
  h.map_raise_le n (Submodule.mem_map_of_mem hv)

theorem IsGL2RealKTypeModule.lower_mem {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) {n : ℤ} {v : M} (hv : v ∈ wt n) : L v ∈ wt (n - 2) :=
  h.map_lower_le n (Submodule.mem_map_of_mem hv)

theorem IsGL2RealKTypeModule.refl_mem {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) {n : ℤ} {v : M} (hv : v ∈ wt n) : ε v ∈ wt (-n) :=
  h.map_refl_le n (Submodule.mem_map_of_mem hv)

end AutomorphicForm

section Battery
open AutomorphicForm
#check @IsGL2RealKTypeModule
#check @IsGL2RealKTypeSubmodule
#check @IsIrreducibleGL2RealKTypeModule
#print axioms AutomorphicForm.isGL2RealKTypeSubmodule_bot
#print axioms AutomorphicForm.isGL2RealKTypeSubmodule_top
#print axioms AutomorphicForm.not_isIrreducibleGL2RealKTypeModule_of_subsingleton
#print axioms AutomorphicForm.IsGL2RealKTypeModule.refl_comp_lower
#print axioms AutomorphicForm.IsGL2RealKTypeModule.refl_refl
end Battery


