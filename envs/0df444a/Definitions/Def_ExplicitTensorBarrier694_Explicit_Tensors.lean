-- Prove2me | Definitions.Def_ExplicitTensorBarrier694_Explicit_Tensors
-- name    : ExplicitTensorBarrier694_Explicit_Tensors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:00.762197+00:00
-- url     : https://prove2.me/theorems/d3a679fa-e475-4752-8c3d-0ec425110885
-- title:
--   Complex tensors, border rank, contraction and dual restriction
-- statement:
--   Let $T\in\mathbb C^a\otimes\mathbb C^b\otimes\mathbb C^c$ be represented by its coordinates $T_{ijk}$. Its ordinary rank $R(T)$ uses the published tensor-object rank, applied to the standard-basis expansion of $T$. Define
--
--   $$\underline R(T)=\min\{r\in\mathbb N:T\in\overline{\{S:R(S)\le r\}}\}.$$
--
--   Closure is in the usual finite product topology on complex coordinates. The feasible set is nonempty because $R(T)$ is finite. A pure tensor has entries $x_i y_j z_k$. Covectors are their values on the first standard basis; contraction sends $\varphi$ to the matrix with entries $\sum_i\varphi_iT_{ijk}$. A-conciseness is injectivity of this map. For every complex dual subspace $W$, restriction is this contraction map on $W$, expressed in a chosen basis of $W$. The minimum over all $q$-dimensional $W$ is a natural-number infimum, attained when $q\le a$; for $q>a$ its empty-set value is zero and the theorems never use that case.
--
--   These are the common interfaces for border substitution and the explicit construction. Empty coordinate factors and the zero tensor have rank and border rank zero. Arbitrary complex summands and approximants are allowed, including when the witness has integer entries.
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), §1 p.1 and §2 p.5 (PDF pp.1,5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_mme_tensor
import Definitions.Def_mme_tensor_rank

open scoped BigOperators

namespace ExplicitTensorBarrier694.Explicit

/-- Coordinates in arbitrary finite complex mode spaces after choosing bases (§2, p.5). -/
abbrev Tensor (a b c : ℕ) := Fin a → Fin b → Fin c → ℂ

/-- The three coordinate mode dimensions, with their order fixed. -/
def modeDim (a b c : ℕ) : Fin 3 → ℕ := ![a, b, c]

/-- Package an array as the actual tensor, using the published general tensor object.
The sum is over the standard basis, not a rank decomposition supplied as input. -/
noncomputable def tensorObject {a b c : ℕ} (T : Tensor a b c) : MME.TensorObj ℂ 3 where
  V l := Fin (modeDim a b c l) → ℂ
  t := ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
    T i j k • PiTensorProduct.tprod ℂ (fun l =>
      match l with
      | ⟨0, _⟩ => Pi.single i 1
      | ⟨1, _⟩ => Pi.single j 1
      | ⟨2, _⟩ => Pi.single k 1)

/-- Usual ordinary rank, reusing the published least diagonal-restriction size. -/
noncomputable def ordinaryRank {a b c : ℕ} (T : Tensor a b c) : ℕ :=
  MME.tensorRankObj (tensorObject T)

/-- Border rank in the usual finite product topology on complex coordinates (p.1).
All approximants and all rank decompositions are complex; integer witnesses impose
no integrality restriction on the approximants. The feasible set is nonempty:
ordinary rank is finite and a set is contained in its closure. -/
noncomputable def borderRank {a b c : ℕ} (T : Tensor a b c) : ℕ :=
  sInf {r : ℕ | T ∈ closure {S : Tensor a b c | ordinaryRank S ≤ r}}

/-- A pure tensor, allowing zero factors without changing rank minima/maxima. -/
def pure {a b c : ℕ} (x : Fin a → ℂ) (y : Fin b → ℂ) (z : Fin c → ℂ) :
    Tensor a b c := fun i j k => x i * y j * z k

/-- Covectors are their values on the first mode's standard basis (§2, p.5). -/
def contract {a b c : ℕ} (T : Tensor a b c) (φ : Fin a → ℂ) :
    Fin b → Fin c → ℂ := fun j k => ∑ i, φ i * T i j k

/-- Injectivity of the first contraction map, exactly A-conciseness. -/
def AConcise {a b c : ℕ} (T : Tensor a b c) : Prop :=
  Function.Injective (contract T)

/-- Restrict to ANY dual subspace. A chosen basis of W merely gives coordinates
on W*; no coordinate-subspace or genericity assumption is made. -/
noncomputable def restrict {a b c : ℕ} (T : Tensor a b c)
    (W : Submodule ℂ (Fin a → ℂ)) : Tensor (Module.finrank ℂ W) b c :=
  fun l => contract T ((Module.finBasis ℂ W l : W) : Fin a → ℂ)

/-- Minimum over the whole Grassmannian, indexed by subspace dimension q.
For q ≤ a there are q-dimensional subspaces, so this Nat infimum is an attained
minimum; Lemma 2.4 includes 1 ≤ q ≤ a. Off this domain the empty infimum is 0. -/
noncomputable def restrictionMinimum {a b c : ℕ} (T : Tensor a b c) (q : ℕ) : ℕ :=
  sInf {r : ℕ | ∃ W : Submodule ℂ (Fin a → ℂ),
    Module.finrank ℂ W = q ∧ borderRank (restrict T W) = r}

end ExplicitTensorBarrier694.Explicit


