-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_LowPackingCertificate
-- name    : Sensitivity214439_PairedSemantic_Solutions_LowPackingCertificate
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T20:11:59.301935+00:00
-- url     : https://prove2.me/theorems/dd93cc23-d61c-4e4a-af59-0d89ede705c5
-- title:
--   Finite low-one packing graphs, states, and certificates
-- statement:
--   A packing graph stores its finite vertex list, bit-encoded directed conflicts and compatibility, and a base cost at each vertex. A partial state fixes selected multiplicities. Its conditioned base includes the load sent to already fixed vertices; the state also determines fixed mass, possible fixed zero vertices, remaining live candidates, and weight $2$ at zero-base candidates or $1$ otherwise.
--
--   Certificates either reject an infeasible fixed assignment, verify a leaf using weighted and unweighted clique certificates, or branch on a vertex's multiplicity $0,1,2,3$. Agreement identifies a state with an actual multiplicity function. Feasibility requires $n_v+2(b_v+\sum_{v\to w}n_w)\le3$ at occupied vertices, and positive multiplicity at most two with zero total load at every designated zero vertex.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/LowPackingCertificate.lean lines 13–95; SHA256 9369710d4b37528ce9d43825665df5aca623b38f242b1f3f08a0c5362829c88c; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_CliqueCertificate
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_LowPackingCliqueBounds
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_WeightedCliqueCertificate
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

namespace SensitivityCliqueCertificate
end SensitivityCliqueCertificate
namespace SensitivityLowPacking
end SensitivityLowPacking
namespace SensitivityLowPackingCertificate
end SensitivityLowPackingCertificate



/-! A finite certificate for the low-one packing problem.  Branches assign an
actual macro multiplicity in {0,1,2,3}; leaves prove weighted independence and
zero-population bounds on the remaining possible macros. -/
namespace SensitivityLowPackingCertificate

open scoped BigOperators
open SensitivityLowPacking SensitivityCliqueCertificate
set_option autoImplicit false

structure Graph where
  vertices : List ℕ
  out : ℕ → ℕ
  compatible : ℕ → ℕ
  base : ℕ → ℕ

def directed (g : Graph) (v w : ℕ) : Prop := v ≠ w ∧ (g.out v).testBit w = true

instance (g : Graph) (v w : ℕ) : Decidable (directed g v w) := by
  unfold directed
  infer_instance

def graphCheck (g : Graph) : Bool :=
  g.vertices.all fun v => g.vertices.all fun w =>
    decide (v ≠ w → ¬directed g v w → ¬directed g w v → (g.compatible v).testBit w = true)

structure State where
  fixed : Finset ℕ
  value : ℕ → ℕ

def initial : State := ⟨∅, fun _ => 0⟩

def assign (state : State) (v n : ℕ) : State :=
  ⟨insert v state.fixed, Function.update state.value v n⟩

def rawBase (g : Graph) (state : State) (v : ℕ) : ℕ :=
  g.base v + ∑ w ∈ state.fixed, if directed g v w then state.value w else 0

def rawMass (state : State) : ℕ := ∑ v ∈ state.fixed, state.value v

def rawFixedZeros (g : Graph) (state : State) : Finset ℕ :=
  state.fixed.filter fun v => 0 < state.value v ∧ state.value v ≤ 2 ∧ rawBase g state v = 0

def rawLive (g : Graph) (state : State) : Finset ℕ :=
  (g.vertices.toFinset \ state.fixed).filter fun v => rawBase g state v ≤ 1 ∧
    ∀ w ∈ state.fixed, 0 < state.value w → directed g w v →
      state.value w + 2 * (rawBase g state w + 1) ≤ 3

def rawWeight (g : Graph) (state : State) (v : ℕ) : ℕ := if rawBase g state v = 0 then 2 else 1

def liveMask (g : Graph) (state : State) : ℕ :=
  maskOf (g.vertices.filter fun v => decide (v ∈ rawLive g state))

def zeroMask (g : Graph) (state : State) : ℕ :=
  maskOf (g.vertices.filter fun v => decide (v ∈ (rawLive g state).filter
    (fun w => rawBase g state w = 0)))

def rejectCheck (g : Graph) (state : State) : Bool :=
  decide (∃ v ∈ state.fixed, 0 < state.value v ∧ 3 < state.value v + 2 * rawBase g state v)

def leafCheck (g : Graph) (state : State) (total zero alpha zeroAlpha : ℕ)
    (weightCert zeroCert : Certificate) : Bool :=
  decide (rawMass state + (rawFixedZeros g state).card + (3 * alpha) / 2 ≤ total) &&
  (decide ((rawFixedZeros g state).card + zeroAlpha ≤ zero) &&
  (SensitivityWeightedCliqueCertificate.check g.compatible (rawWeight g state)
      (liveMask g state) alpha weightCert &&
    SensitivityCliqueCertificate.check g.compatible (zeroMask g state) zeroAlpha zeroCert))

inductive PackingCertificate where
  | reject
  | leaf (alpha zeroAlpha : ℕ) (weightCert zeroCert : Certificate)
  | split (v : ℕ) (zero one two three : PackingCertificate)

def check (g : Graph) (total zero : ℕ) (state : State) : PackingCertificate → Bool
  | .reject => rejectCheck g state
  | .leaf alpha zeroAlpha weightCert zeroCert => leafCheck g state total zero alpha zeroAlpha weightCert zeroCert
  | .split v c0 c1 c2 c3 =>
    decide (v ∈ g.vertices) &&
      (check g total zero (assign state v 0) c0 &&
      (check g total zero (assign state v 1) c1 &&
      (check g total zero (assign state v 2) c2 && check g total zero (assign state v 3) c3)))

noncomputable section
open scoped Classical

def Agrees (state : State) (count : ℕ → ℕ) : Prop := ∀ v ∈ state.fixed, state.value v = count v

structure Fits (g : Graph) (count : ℕ → ℕ) (zeros : Finset ℕ) : Prop where
  budget : ∀ v ∈ g.vertices.toFinset, 0 < count v →
    count v + 2 * (g.base v + weightedOut (directed g) g.vertices.toFinset count v) ≤ 3
  zeroSupport : zeros ⊆ Support g.vertices.toFinset count
  zeroSmall : ∀ v ∈ zeros, count v ≤ 2
  zeroLoad : ∀ v ∈ zeros, g.base v + weightedOut (directed g) g.vertices.toFinset count v = 0























end
end SensitivityLowPackingCertificate


