-- Prove2me | Definitions.Def_IntMul_Kappa_DeferredReadoutProjectors
-- name    : IntMul_Kappa_DeferredReadoutProjectors
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T08:02:45.995958+00:00
-- url     : https://prove2.me/theorems/41a3dd7b-e22c-53db-a8fd-a79e2436ae3f
-- title:
--   Rational frame projectors and the deferred auxiliary readout edge
-- statement:
--   For the integer-multiplication readouts, the ambient vector space has 23 rational coordinates. The bilinear form is represented here by the integer matrix $9G=9I-J$, where $J$ is the all-ones matrix. For a nondegenerate frame $U$, its projector maps onto $U$ along its $G$-orthogonal complement. A finite certificate for nondegeneracy gives a vector $w\in U$ and a positive integer $d$ such that $(9G)(x,w)=d\sum_i x_i$ on $U$. The frame-projector definition uses zero on a degenerate subspace. The staircase assertion verifies nondegeneracy for every scheduled frame.
--
--   For a triple of coordinates with indicator $t$, let $P_t$ project onto its line. At a deferred readout the edge on the tensor-square space is
--   $$A(U,t)=I-(I-\pi_U)\otimes P_t.$$
--   Targets are triples in lexicographic order. The chronological list retains repeated frames.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/deferred-readout/check_frames.py#L112-L148; https://prove2.me/missions/Integer_multiplication%3A_%CE%BA_%3D_0.00006397891967576_%28Jain_round_seven%29 (October 20, 2026 discussion of the deferred auxiliary edge).

import Definitions.Def_IntMul_Kappa_DeferredReadoutCertificates
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection

namespace IntMul.Kappa.DeferredReadout
open Matrix
open scoped Kronecker

abbrev V := VectorQ 23
abbrev Subspace := Submodule ℚ V
abbrev Mat := Matrix (Fin 23) (Fin 23) ℚ

def total : V →ₗ[ℚ] ℚ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

/-- Nine times Jain's form G = I - J/9. Scaling preserves orthogonal complements. -/
def gramForm : LinearMap.BilinForm ℚ V :=
  (9 : ℚ) • dotProductBilin ℚ ℚ - total.smulRight total

/-- One exact vector in the frame represents the coordinate-sum functional
for the restricted Gram form. This suffices to rule out a radical. -/
structure GramCertificate where
  den : Nat
  terms : List (Nat × Int)
  vector : Array Int
deriving Inhabited

def GramCertificate.coord (c : GramCertificate) (i : Fin 23) : Int :=
  c.vector[i.val]?.getD 0

def GramCertificate.ok (c : GramCertificate) (tbl : RowTable) (B : Frame) : Bool :=
  decide (0 < c.den) && c.terms.all (fun v => B.contains v.1) &&
  (List.finRange 23).all (fun i => c.coord i == combination tbl c.terms i.val) &&
  B.all (fun r =>
    let u := fun i : Fin 23 => tbl r i.val
    let s := ∑ i, u i
    9 * (∑ i, u i * c.coord i) - s * (∑ i, c.coord i) == (c.den : Int) * s)

noncomputable def project (U : Subspace) : Mat := by
  classical
  exact if h : IsCompl U (gramForm.orthogonal U) then
    LinearMap.toMatrix' (U.projection _ h) else 0

def aux (frame target : Mat) : Matrix (Fin 23 × Fin 23) (Fin 23 × Fin 23) ℚ :=
  1 - (1 - frame) ⊗ₖ target

def targetCovector (t : V) : V := fun i => 9 * t i - total t

/-- The rank-one G-orthogonal projector along a nonisotropic target direction. -/
def targetProjector (t : V) : Mat :=
  let v := targetCovector t
  vecMulVec t ((v ⬝ᵥ t)⁻¹ • v)

def targetTriples : Array (Nat × Nat × Nat) :=
  ((List.range 23).flatMap fun i => (List.range 23).flatMap fun j =>
    ((List.range 23).filter fun k => i < j && j < k).map fun k => (i,j,k)).toArray

def targetDirection (t : Fin 1771) : V :=
  let tri := targetTriples[t.val]?.getD (0,0,0)
  fun j => if j.val = tri.1 ∨ j.val = tri.2.1 ∨ j.val = tri.2.2 then 1 else 0

def gramChecks (d : Block) (cs : Array GramCertificate) : Bool :=
  (List.range d.frames.size).all fun i => (cs[i]?.getD default).ok d.entry (d.basis i)

def eventFrameBounds (d : Block) : Bool :=
  d.targets.toList.all fun es => es.all fun e => decide (e.frame < d.frames.size)

/-- Ordered auxiliary readouts in the 23 × 23 network coordinate space. -/
noncomputable def readoutEdges (fs : List Subspace) (t : V) :=
  fs.map (fun U => aux (project U) (targetProjector t))

end IntMul.Kappa.DeferredReadout


