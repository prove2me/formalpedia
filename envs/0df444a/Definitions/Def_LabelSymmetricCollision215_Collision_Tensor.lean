-- Prove2me | Definitions.Def_LabelSymmetricCollision215_Collision_Tensor
-- name    : LabelSymmetricCollision215_Collision_Tensor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:50.091093+00:00
-- url     : https://prove2.me/theorems/cbb7f493-c0a3-4c9e-adff-74d97b1e7147
-- title:
--   Collision-free tensors, deletion, arrangement graph and sector coordinates
-- statement:
--   For $s$ positions let $H_s=\ell_2((\mathbb Z/N\mathbb Z)^s)$. Let $C_s^\perp$ be the span of injective basis tuples, $W$ the zero-sum label subspace, and $W^{\otimes s}$ the span of actual pure tensors with each factor in $W$. Intersection and orthogonal projections use these concrete finite Hilbert subspaces.
--
--   The deletion map sums the unnormalized coordinate deletions, with its domain restricted to injective tuples and its target indexed by a deleted position and an injective assignment to the remaining positions. At $s=1$ each remaining assignment is the unique empty tuple. Arrangement adjacency has coefficient one exactly when two injective tuples differ at one coordinate. It is defined independently of deletion. The sector map reads occupied cells in increasing address order and is zero on other sectors. Label actions are diagonal permutation actions. Eigenspaces are actual kernels of adjacency minus the scalar identity.
--
--   The coefficient spaces retain the Euclidean norm throughout, including operator norms of projection errors.
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, §§4.2–4.5; PDF 23–30 / printed 21–28

import Definitions.Def_LabelSymmetricCollision215_Collision_Recording

noncomputable section
open scoped ComplexConjugate

namespace LabelSymmetricCollision215.Collision
attribute [local instance] Classical.propDecidable

/-! Actual tensor-coordinate spaces, unnormalized deletion and arrangement adjacency (§§4.2–4.5). -/
abbrev Tuple (N s : ℕ) := Fin s → ZMod N
abbrev InjectiveTuple (N s : ℕ) := {y : Tuple N s // Function.Injective y}

def freeTensor (N s : ℕ) [NeZero N] : Submodule ℂ (H (Tuple N s)) :=
  Submodule.span ℂ {v | ∃ y : InjectiveTuple N s, v = basis y.val}

def zeroSum (N : ℕ) [NeZero N] : Submodule ℂ (H (ZMod N)) :=
  (mat (fun (_ : Unit) (_ : ZMod N) => (1 / (Real.sqrt N : ℂ)))).toLinearMap.ker

def wTensor (N s : ℕ) [NeZero N] : Submodule ℂ (H (Tuple N s)) :=
  Submodule.span ℂ {v | ∃ u : Fin s → H (ZMod N),
    (∀ r, u r ∈ zeroSum N) ∧ v = WithLp.toLp 2 (fun y => ∏ r, u r (y r))}

def intersection (N s : ℕ) [NeZero N] := freeTensor N s ⊓ wTensor N s

def injectiveEmbedding (N s : ℕ) [NeZero N] : H (InjectiveTuple N s) →L[ℂ] H (Tuple N s) :=
  mat (fun y z => if y = z.val then 1 else 0)

abbrev Deleted (N s : ℕ) :=
  Σ r : Fin s, {z : ({j : Fin s // j ≠ r} → ZMod N) // Function.Injective z}

def deletion (N s : ℕ) [NeZero N] : H (InjectiveTuple N s) →L[ℂ] H (Deleted N s) :=
  mat (fun z y => if ∀ j : {j : Fin s // j ≠ z.1}, z.2.val j = y.val j.val then 1 else 0)

def arrangement (N s : ℕ) [NeZero N] : H (InjectiveTuple N s) →L[ℂ] H (InjectiveTuple N s) :=
  mat (fun y z => if (Finset.univ.filter (fun j => y.val j ≠ z.val j)).card = 1 then 1 else 0)

def tupleAction (N s : ℕ) [NeZero N] (σ : Equiv.Perm (ZMod N)) :
    H (Tuple N s) →L[ℂ] H (Tuple N s) :=
  mat (fun y z => if y = σ ∘ z then 1 else 0)

def injectiveAction (N s : ℕ) [NeZero N] (σ : Equiv.Perm (ZMod N)) :
    H (InjectiveTuple N s) →L[ℂ] H (InjectiveTuple N s) :=
  mat (fun y z => if y.val = σ ∘ z.val then 1 else 0)

/-- Positions are listed in increasing address order by Finset.orderEmbOfFin. -/
def sectorMap {M N : ℕ} {W : Type} [Fintype W] [NeZero N]
    (η : Reg M N W) (I : Finset (Fin M)) :
    H (Reg M N W × DB M N) →L[ℂ] H (Tuple N I.card) :=
  mat (fun y a => if a.1 = η ∧ occupied a.2 = I ∧
    ∀ j : Fin I.card, a.2 (I.orderEmbOfFin rfl j) = some (y j) then 1 else 0)

def projectionError (N s : ℕ) [NeZero N] : H (Tuple N s) →L[ℂ] H (Tuple N s) :=
  (wTensor N s).starProjection.comp (freeTensor N s).starProjection -
    (intersection N s).starProjection

def Eigen (N s : ℕ) [NeZero N] (a : ℝ) : Prop :=
  ∃ v : H (InjectiveTuple N s), v ≠ 0 ∧ arrangement N s v = (a : ℂ) • v

def eigenSpace (N s : ℕ) [NeZero N] (a : ℝ) : Submodule ℂ (H (InjectiveTuple N s)) :=
  ((arrangement N s - (a : ℂ) • ContinuousLinearMap.id ℂ _).toLinearMap).ker

end LabelSymmetricCollision215.Collision


