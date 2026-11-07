-- Prove2me | Definitions.Def_CompPermOracle_opTensor
-- name    : CompPermOracle_opTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:46:41.918584+00:00
-- url     : https://prove2.me/theorems/91e15336-1d64-4839-91ab-8bfbde1dad3c
-- title:
--   Operators on finite Hilbert spaces: $|u\rangle\langle v|$, $S\otimes T$, coherent control, $\mathrm{Col}$ and $\mathrm{Row}$
-- statement:
--   For a finite set $X$, $\mathcal H(X)$ is the Hilbert space with orthonormal basis $\{|x\rangle : x\in X\}$. This file fixes the operator vocabulary of the mission: the rank-one operator $|u\rangle\langle v|$, the product vector $u\otimes v$, the tensor product $S\otimes T$ determined by $(S\otimes T)|a,x\rangle=S|a\rangle\otimes T|x\rangle$, and coherent control $\sum_c |c\rangle\langle c|\otimes \mathrm{op}_c$.
--
--   For a family of operators $T=(T_y)_y$, the column and row square functions are
--   $$
--   \mathrm{Col}(T)=\Big\|\sum_y T_y^\dagger T_y\Big\|^{1/2},\qquad \mathrm{Row}(T)=\Big\|\sum_y T_y T_y^\dagger\Big\|^{1/2}.
--   $$
--   These two family norms carry the one-query estimates of the source.
--
--   **Formalization Note** $\mathcal H(X)$ is `EuclideanSpace ℂ X`, and operators are bounded linear maps. The tensor product is defined on the basis $|a,x\rangle$.
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), §3.1, p.6; eq. (14), p.13

import Mathlib

namespace CompPermOracle

/-- The Hilbert space `ℋ(X)` with orthonormal basis `X` (Carolan, Majenz, Compressed Permutation
Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), §3.1, p.6). -/
abbrev Hil (X : Type*) := EuclideanSpace ℂ X

/-- The basis vector `|x⟩`. -/
noncomputable def ket {X : Type*} [DecidableEq X] (x : X) : Hil X := EuclideanSpace.single x 1

/-- The rank-one operator `|u⟩⟨v|`. -/
noncomputable def ketBra {X Y : Type*} [Fintype X] [Fintype Y] (u : Hil Y) (v : Hil X) :
    Hil X →L[ℂ] Hil Y :=
  (innerSL ℂ v).smulRight u

/-- The product vector `u ⊗ v`. -/
noncomputable def ketTensor {A X : Type*} (u : Hil A) (v : Hil X) : Hil (A × X) :=
  WithLp.toLp 2 fun p => u p.1 * v p.2

/-- The tensor product `S ⊗ T` of operators, fixed by `(S ⊗ T)|a, x⟩ = S|a⟩ ⊗ T|x⟩`. -/
noncomputable def opTensor {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
    [DecidableEq A] [DecidableEq X] (S : Hil A →L[ℂ] Hil B) (T : Hil X →L[ℂ] Hil Y) :
    Hil (A × X) →L[ℂ] Hil (B × Y) :=
  ∑ p : A × X, ketBra (ketTensor (S (ket p.1)) (T (ket p.2))) (ket p)

/-- Coherent control on a register `C`: `∑_c |c⟩⟨c| ⊗ op c` (arXiv:2609.28469, Definitions 3.1,
3.2 and 3.6, pp.6 and 8). -/
noncomputable def controlled {C A B : Type*} [Fintype C] [Fintype A] [Fintype B]
    [DecidableEq C] [DecidableEq A] (op : C → Hil A →L[ℂ] Hil B) :
    Hil (C × A) →L[ℂ] Hil (C × B) :=
  ∑ c : C, opTensor (ketBra (ket c) (ket c)) (op c)

/-- The column square function `Col(T) = ‖∑_y T_y† T_y‖^{1/2}` of a family of operators
(arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), eq. (14), p.13). -/
noncomputable def Col {I X Z : Type*} [Fintype I] [Fintype X] [Fintype Z]
    (T : I → Hil X →L[ℂ] Hil Z) : ℝ :=
  Real.sqrt ‖∑ y, (ContinuousLinearMap.adjoint (T y)).comp (T y)‖

/-- The row square function `Row(T) = ‖∑_y T_y T_y†‖^{1/2}` of a family of operators
(arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), eq. (14), p.13). -/
noncomputable def Row {I X Z : Type*} [Fintype I] [Fintype X] [Fintype Z]
    (T : I → Hil X →L[ℂ] Hil Z) : ℝ :=
  Real.sqrt ‖∑ y, (T y).comp (ContinuousLinearMap.adjoint (T y))‖

end CompPermOracle


