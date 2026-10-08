-- Prove2me | Definitions.Def_QLLL_LocalLemma_Basic
-- name    : QLLL_LocalLemma_Basic
-- status  : Definition
-- author  : @sattath
-- created : 2026-10-06T17:32:35.842732+00:00
-- url     : https://prove2.me/theorems/f4d318a6-29b7-420b-8949-ccd15093e112
-- title:
--   Valuations on bounded lattices, mutual independence, dependency graphs and relative dimension
-- statement:
--   Definitions for the abstract local lemma (namespace `QLLL`).
--
--   1. **Valuation.** For a bounded lattice $L$, a valuation is a function $R : L \to \mathbb{R}$ such that $R(x) \ge 0$, $R$ is monotone, $R(x) + R(y) = R(x \vee y) + R(x \wedge y)$ for all $x, y$, $R(\top) = 1$ and $R(\bot) = 0$. These are properties (i), (ii) and (iv) of Lemma 8 of the paper together with normalisation; probability on events and relative dimension on subspaces are the two motivating examples. The bundle provides the coercion of a valuation to a function.
--   2. **Mutual independence** (`Valuation.MutuallyIndepOn`). An element $x$ is mutually $R$-independent of a family $(Y_j)_{j \in T}$, $T$ finite, if $R\big(x \wedge \bigwedge_{j \in S} Y_j\big) = R(x)\,R\big(\bigwedge_{j \in S} Y_j\big)$ for every $S \subseteq T$.
--   3. **Dependency graph** (`Valuation.IsDependencyGraph`). For $X_1, \dots, X_n \in L$, sets $\Gamma(i) \subseteq \{1, \dots, n\}$ form a dependency graph if each $X_i$ is mutually $R$-independent of $\{X_j : j \notin \Gamma(i),\ j \neq i\}$.
--   4. **Relative dimension** (`relDim`). For a subspace $X$ of a vector space $V$ over a field, $\mathrm{R}(X) = \dim X / \dim V$ (Definition 3 of the paper), and `relDimValuation` packages it as a valuation on the lattice of subspaces when $V$ is finite-dimensional and nonzero.
--
--   **Formalization Note** Mutual independence is in product form, not the conditional form of Definition 9, which is ill-behaved when the conditioning element has value $0$. The dependency graph excludes $i$ itself, unlike a literal reading of Definition 12.
-- source:
--   A. Ambainis, J. Kempe, O. Sattath, A Quantum Lovász Local Lemma, J. ACM 59(5):24 (2012), arXiv:0911.1696 (numbering of the arXiv version), Definitions 3, 9 and 12 and Lemma 8

import Mathlib

/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# The Quantum Lovász Local Lemma

Formalization of Ambainis, Kempe, Sattath, *A Quantum Lovász Local Lemma*
(arXiv:0911.1696).

## Design

The paper observes, after its Theorem 14, that the proof uses only properties
(i)-(iv) of its Lemma 8, i.e. that these "are the only properties of `R` we
need in the proof". We take that literally: the local lemma is proved once for
an abstract `Valuation` on a bounded lattice, and then instantiated at

* `Submodule 𝕜 V` with `relDim X = finrank X / finrank V`, giving the quantum
  LLL (Theorem 14 of the paper), and
* a probability space with `Pr`, giving the classical asymmetric LLL
  (Erdős-Lovász 1975, Theorem 13 of the paper).

Mathlib currently contains no Lovász local lemma in either form, so the second
instantiation is a contribution independent of the paper.

## Main statements

* `Valuation.cond_inf_mul` : Lemma 8(iii), the chain rule.
* `Valuation.cond_ge_of_notMem` : Lemma 15, the inductive heart.
* `Valuation.lll` : Theorem 14, the asymmetric local lemma.
* `Valuation.lll_symmetric` : Theorem 4, the symmetric version.
-/

namespace QLLL

open Finset

/-- A "probability-like" valuation on a bounded lattice: the abstraction of
both `Pr` on events and relative dimension on subspaces. The fields are
exactly items (i), (ii) and (iv) of Lemma 8 of the paper, plus normalisation.

Note that `sup` plays the role of the paper's `X + Y` (sum of subspaces,
disjunction of events) and `inf` the role of `X ∩ Y`. -/
structure Valuation (α : Type*) [Lattice α] [BoundedOrder α] where
  /-- The valuation itself, the paper's `R`. -/
  toFun : α → ℝ
  /-- Lemma 8(i), lower bound. -/
  nonneg' : ∀ x, 0 ≤ toFun x
  /-- Lemma 8(ii), monotonicity. -/
  monotone' : Monotone toFun
  /-- Lemma 8(iv), inclusion/exclusion. For subspaces this is modularity of
  `finrank`; for events, finite additivity. -/
  modular' : ∀ x y, toFun x + toFun y = toFun (x ⊔ y) + toFun (x ⊓ y)
  /-- Normalisation. -/
  map_top' : toFun ⊤ = 1
  /-- Normalisation. -/
  map_bot' : toFun ⊥ = 0

namespace Valuation

variable {α : Type*} [Lattice α] [BoundedOrder α]

instance : CoeFun (Valuation α) (fun _ => α → ℝ) := ⟨Valuation.toFun⟩

variable (R : Valuation α)

/-- Mutual R-independence (Definition 9), relativised to an index set `T`:
`x` is mutually R-independent of `{Y j | j ∈ T}`.

Design note. The paper phrases this with the conditional,
`R(x | ⋂_{j ∈ S} Y_j) = R(x)`. That phrasing is wrong when
`R(⋂_{j ∈ S} Y_j) = 0`, which a constraint with no satisfying states really can
achieve: the conditional is then `0` by the junk-value convention while `R(x)`
need not be. We use the product form of Definition 3 instead,
`R(x ∩ y) = R(x) · R(y)`, which agrees with the conditional form whenever the
latter is meaningful (`MutuallyIndepOn.cond_eq`) and is what every proof below
actually consumes. -/
def MutuallyIndepOn {ι : Type*} (x : α) (Y : ι → α)
    (T : Finset ι) : Prop :=
  ∀ S ⊆ T, R (x ⊓ S.inf Y) = R x * R (S.inf Y)

/-- Definition 12(ii): `Γ` is (the out-neighbourhood function of) a dependency
graph for the family `X`, i.e. `Γ i = {j | (i,j) ∈ E}`.

Design note. The paper asks that `X i` be mutually R-independent of
`{X j | (i,j) ∉ E}`, a set which literally contains `i` itself whenever
`(i,i) ∉ E`; that would force `R (X i) ∈ {0, 1}`. We therefore exclude `i`,
which is the standard formulation of the classical LLL and is what the proof of
Lemma 15 uses (there `i ∉ S`, hence `i` never lies in the independent part
`I`). -/
def IsDependencyGraph {n : ℕ} (X : Fin n → α) (Γ : Fin n → Finset (Fin n)) :
    Prop :=
  ∀ i, R.MutuallyIndepOn (X i) X ((univ \ Γ i).erase i)

variable {n : ℕ} {X : Fin n → α} {Γ : Fin n → Finset (Fin n)} {y : Fin n → ℝ}

end Valuation

/-! ## Instantiation at subspaces: relative dimension -/

open Module

variable {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- Relative dimension (Definition 3): `R X = dim X / dim V`. -/
noncomputable def relDim (X : Submodule 𝕜 V) : ℝ :=
  (finrank 𝕜 X : ℝ) / (finrank 𝕜 V : ℝ)

variable [FiniteDimensional 𝕜 V] [Nontrivial V]

/-- Relative dimension is a `Valuation`. Modularity is
`Submodule.finrank_sup_add_finrank_inf_eq`. -/
noncomputable def relDimValuation : Valuation (Submodule 𝕜 V) where
  toFun := relDim
  nonneg' _ := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  monotone' := by
    intro X Y h
    have hXY : finrank 𝕜 X ≤ finrank 𝕜 Y := Submodule.finrank_mono h
    unfold relDim
    gcongr
  modular' := by
    intro X Y
    have h := Submodule.finrank_sup_add_finrank_inf_eq X Y
    unfold relDim
    rw [← add_div, ← add_div]
    congr 1
    exact_mod_cast h.symm
  map_top' := by
    have hV : (finrank 𝕜 V : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Module.finrank_pos_iff.mpr inferInstance).ne'
    unfold relDim
    rw [finrank_top]
    exact div_self hV
  map_bot' := by simp [relDim, finrank_bot]

/-! ## TODO

* Lemma 11: two projectors acting on disjoint sets of qubits are mutually
  R-independent. This is the step that needs the tensor-product structure
  `⨂ i, H i` (`PiTensorProduct`), and is expected to be the hardest part of the
  definitional layer.
* Corollary 16 / Corollary 5: a `k`-QSAT instance of rank-`≤ r` projectors in
  which every qubit appears in at most `2 ^ k / (e * r * k)` projectors is
  satisfiable.
* Instantiate `Valuation` at a probability space to obtain the classical
  asymmetric LLL (Theorem 13).
-/

end QLLL


