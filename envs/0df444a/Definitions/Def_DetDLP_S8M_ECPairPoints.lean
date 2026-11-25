-- Prove2me | Definitions.Def_DetDLP_S8M_ECPairPoints
-- name    : DetDLP_S8M_ECPairPoints
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:50:24.474638+00:00
-- url     : https://prove2.me/theorems/ad406a78-8f18-4903-99bc-60014f568ac7
-- title:
--   EC pair point-slot witnesses
-- statement:
--   Two arrays of independently certified point slots decode bijectively to the pair set after imposing the interleaved prefix and target-sum equations.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8H_ECPointSlots
import Definitions.Def_DetDLP_S8I_ECQueryCount

set_option autoImplicit false
namespace DetDLP.S8M.ECPair.Points
open S8H S8H.ECPointSlots M89S1

variable {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
variable (mul : w3_modMulInterface) (T : ℕ) (hT : T ≤ p) (S : ECSeed p m)
abbrev Point := E.toAffine.Point
abbrev Slot (i : Fin m) := {w // elemOK E S i T (bitLen p) [] w}
abbrev Pinned (i : Fin m) := {P : Point E // P ∈ ecFactorBlock E T S i}

noncomputable def decode (i : Fin m) : Slot E T S i ≃ Pinned E T S i :=
  (elemEquiv (E := E) mul S i T (bitLen p) hT []).trans <| Equiv.subtypeEquivRight fun P => by
    simp [ECPointGadget.elemPin,ecFactorBlock]

abbrev Slots := (∀ i, Slot E T S i) × (∀ i, Slot E T S i)
abbrev Pair := (Fin m → Point E) × (Fin m → Point E)

noncomputable def project (w : Slots E T S) : Pair (m := m) E :=
  (fun i => (decode E mul T hT S i (w.1 i)).1,fun i => (decode E mul T hT S i (w.2 i)).1)

variable (X : Point E) (η : List Bool)

def pin (ab : Pair (m := m) E) := (tupleWord (ecWord (bitLen p)) ab).take η.length = η ∧
  (∑ i, (ab.1 i + ab.2 i)) = X

/-- An independent slot for each of the two entries of each block. The two remaining
    predicates are imposed on the interleaved public word and the same decoded points. -/
noncomputable def pairEquiv : {w : Slots E T S // pin E X η (project E mul T hT S w)} ≃
    {ab : Pair (m := m) E // (∀ i, ab.1 i ∈ ecFactorBlock E T S i ∧ ab.2 i ∈ ecFactorBlock E T S i) ∧ pin E X η ab} where
  toFun w := ⟨project E mul T hT S w.1,fun i => ⟨(decode E mul T hT S i (w.1.1 i)).2,
    (decode E mul T hT S i (w.1.2 i)).2⟩,w.2⟩
  invFun ab := ⟨(fun i => (decode E mul T hT S i).symm ⟨ab.1.1 i,(ab.2.1 i).1⟩,
      fun i => (decode E mul T hT S i).symm ⟨ab.1.2 i,(ab.2.1 i).2⟩),by
    simpa only [project,Equiv.apply_symm_apply] using ab.2.2⟩
  left_inv w := by apply Subtype.ext; apply Prod.ext <;> funext i <;> exact Equiv.symm_apply_apply _ _
  right_inv ab := by
    apply Subtype.ext; apply Prod.ext <;> funext i <;> exact congrArg Subtype.val (Equiv.apply_symm_apply _ _)

noncomputable def countedEquiv : {w : Slots E T S // pin E X η (project E mul T hT S w)} ≃
    S8I.ECQueryCount.PairSet p m E T η (bitLen p) S X :=
  (pairEquiv E mul T hT S X η).trans <| Equiv.subtypeEquivRight fun ab => by
    simp only [S8I.ECQueryCount.pairSet,Finset.mem_filter,Finset.mem_univ,true_and,pin]

end DetDLP.S8M.ECPair.Points


