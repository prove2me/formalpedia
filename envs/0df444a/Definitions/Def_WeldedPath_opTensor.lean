-- Prove2me | Definitions.Def_WeldedPath_opTensor
-- name    : WeldedPath_opTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:53:33.54785+00:00
-- url     : https://prove2.me/theorems/2d0ee37b-7d35-4ce6-8ab1-327ff3abf9e5
-- title:
--   Finite-dimensional Hilbert spaces, tensor products and coherent control
-- statement:
--   For a finite set $X$, $\mathcal H(X)$ is the Hilbert space with orthonormal basis $\{|x\rangle:x\in X\}$. This file fixes the operator vocabulary used by the compressed-oracle statements: the rank-one operator $|u\rangle\langle v|$, the product vector $u\otimes v$, the tensor product $S\otimes T$ determined by $(S\otimes T)|a,x\rangle=S|a\rangle\otimes T|x\rangle$, the permutation operator $|i\rangle\mapsto|\sigma(i)\rangle$ of a map of bases, and **coherent control**
--   $$
--   \sum_c |c\rangle\langle c|\otimes O_c .
--   $$
--   A bound on $O_c$ "holds with coherent controls" if it also holds for this operator.
--
--   **Formalization Note** $\mathcal H(X)$ is `EuclideanSpace ℂ X`; operators are continuous linear maps, and norms are operator norms. The same vocabulary appears in the companion `CompPermOracle` drafts, which are not published.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), §2, p.8; §2.1, p.12

import Mathlib

namespace WeldedPath

/-- The Hilbert space `H(X)` with orthonormal basis `{|x⟩ : x ∈ X}` (Carolan, Childs, Coudron,
Gilani, Miloschewsky, Podder, arXiv:2611.05912 (sha256 b31400a0…), §2, pp.8–9: "All Hilbert spaces
considered here are finite-dimensional"). -/
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

/-- Coherent control on a register `C`: `Σ_c |c⟩⟨c| ⊗ O_c` (arXiv:2611.05912 (sha256 b31400a0…),
§2.1, p.12: "a bound on `O_c` holds with coherent controls if it also holds for
`Σ_c |c⟩⟨c| ⊗ O_c`"). -/
noncomputable def controlled {C A B : Type*} [Fintype C] [Fintype A] [Fintype B]
    [DecidableEq C] [DecidableEq A] (op : C → Hil A →L[ℂ] Hil B) :
    Hil (C × A) →L[ℂ] Hil (C × B) :=
  ∑ c : C, opTensor (ketBra (ket c) (ket c)) (op c)

/-- The operator `|σ(i)⟩ ⟵ |i⟩` of a map `σ` between finite bases (a permutation matrix when `σ`
is a bijection). -/
noncomputable def basisMap {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (σ : X → Y) : Hil X →L[ℂ] Hil Y :=
  ∑ i : X, ketBra (ket (σ i)) (ket i)

end WeldedPath


