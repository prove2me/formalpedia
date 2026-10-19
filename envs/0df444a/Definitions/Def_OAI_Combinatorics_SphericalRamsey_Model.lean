-- Prove2me | Definitions.Def_OAI_Combinatorics_SphericalRamsey_Model
-- name    : OAI_Combinatorics_SphericalRamsey_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:05:01.498991+00:00
-- url     : https://prove2.me/theorems/0793acdc-e835-4bd2-ac26-9a3a69f5832e
-- title:
--   Weights of the twelve-point spherical witness
-- statement:
--   Let $t=\sum_{m\ge1}10^{-m!}$ (a Liouville number), $u=\frac{1-t^2}{1+t^2}$ and $v=\frac{2t}{1+t^2}$, so $u^2+v^2=1$. The witness consists of twelve points of the unit circle, labelled by $(k,q)\in\{0,1,2\}\times\{0,1,2,3\}$: the square $Q=\{(1,0),(-1,0),(0,1),(0,-1)\}$ rotated by the angle with cosine $u$ and sine $v$ ($k=0$), rotated by the opposite angle ($k=1$), and unrotated ($k=2$). The weight of a label is $1$ for $k=0,1$ and $-2$ for $k=2$.
--
--   The weight function is
--   $$
--   w(k,q)=\begin{cases}-2,&k=2,\\1,&k\in\{0,1\}.\end{cases}
--   $$
--
--   The weighted sum of a derivative energy over the twelve points is a fixed constant for every isometric copy of the witness. This rigidity is what defeats a fifty-colouring.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SphericalRamsey/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SphericalRamsey/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GrahamSpherical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_GrahamSpherical

namespace OAI

/-!
The explicit twelve-point witness and the ordinary Euclidean Ramsey property.
These definitions contain no proof-specific field derivation or affine-placement assumption.
-/
noncomputable section

namespace GrahamSpherical

def weight (i : Label) : ℤ := if i.1 = 2 then -2 else 1

end GrahamSpherical

end

/-! Independent statement of the full authored result. -/
namespace GrahamSpherical.Specification

end GrahamSpherical.Specification

end OAI


