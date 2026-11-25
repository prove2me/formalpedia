-- Prove2me | Definitions.Def_DetDLP_M3B_ECChains
-- name    : DetDLP_M3B_ECChains
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T11:51:40.342615+00:00
-- url     : https://prove2.me/theorems/179da6ed-c422-4ca7-9d47-16b03b9c670e
-- title:
--   Unique EC addition chains at a shared endpoint
-- statement:
--   Proves the 2m-entry tuple chain lengths and the unique pair of short-Weierstrass addition traces exactly for Stage II additive witnesses, retaining arbitrary prefix pins.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3B_ECCert
import Definitions.Def_DetDLP_S8O_ECAddTile
import Definitions.Def_DetDLP_S8O_ECMapTile
import Theorems.Thm_DetDLP_w3_m5_modmul_r2

set_option autoImplicit false
namespace DetDLP.M3B.ECChains
open ECCert S8M.ECPair S8H.ECPointArithmetic

variable {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
variable (F : Fin m → List (Point E)) (hp : 3 < p)

def xChain (P : Point E) (X : (base E F).BlockTuple) := P :: factors E F X
def yChain (Y : (base E F).BlockTuple) := (0 : Point E) :: factors E F Y

theorem xChain_length (P : Point E) (X : (base E F).BlockTuple) :
    (xChain E F P X).length = 2*m+1 := by simp [xChain,factors_length]

theorem yChain_length (Y : (base E F).BlockTuple) :
    (yChain E F Y).length = 2*m+1 := by simp [yChain,factors_length]

theorem xEndpoint (P : Point E) (X : (base E F).BlockTuple) (Z : Point E)
    (h : (base E F).tupleVal X + P = Z) :
    ∃! w : Witness.Trace p, traceOK E F hp P X Z w :=
  trace_unique E F hp w3_m5_modmul_r2 P X Z h

theorem yEndpoint (Y : (base E F).BlockTuple) (Z : Point E)
    (h : (base E F).tupleVal Y = Z) :
    ∃! w : Witness.Trace p, traceOK E F hp 0 Y Z w := by
  apply trace_unique E F hp w3_m5_modmul_r2 0 Y Z
  simpa using h

theorem sharedEndpoint_iff (P : Point E) (t : Tuples E F) :
    (∃ Z, (base E F).tupleVal t.2 = Z ∧ (base E F).tupleVal t.1 + P = Z) ↔
      (base E F).tupleVal t.2 = (base E F).tupleVal t.1 + P := by
  constructor
  · rintro ⟨Z,h₁,h₂⟩; exact h₁.trans h₂.symm
  · intro h; exact ⟨(base E F).tupleVal t.2,rfl,h.symm⟩

theorem joinedEndpoint (P : Point E) (t : Tuples E F)
    (h : (base E F).tupleVal t.2 = (base E F).tupleVal t.1 + P) :
    ∃! r : Joined E, joinedOK E F hp P t r :=
  joined_unique E F hp P w3_m5_modmul_r2 t h

theorem joinedEndpoint_sound (P : Point E) (t : Tuples E F) (r : Joined E)
    (h : joinedOK E F hp P t r) :
    (base E F).tupleVal t.2 = (base E F).tupleVal t.1 + P :=
  ECCert.joined_sound (E:=E) (F:=F) (hp:=hp) (P:=P) w3_m5_modmul_r2 t r h

theorem pinnedEndpoint (P : Point E) (t : Tuples E F) (pre : List Bool)
    (ht : prefixOK E F pre t)
    (h : (base E F).tupleVal t.2 = (base E F).tupleVal t.1 + P) :
    ∃! r : Joined E, joinedOK E F hp P t r ∧ prefixOK E F pre t := by
  obtain ⟨r,hr,ur⟩ := joinedEndpoint E F hp P t h
  exact ⟨r,⟨hr,ht⟩,fun s hs => by rw [ur s hs.1]⟩

end DetDLP.M3B.ECChains


