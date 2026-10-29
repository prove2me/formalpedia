-- Prove2me | Definitions.Def_ElectManip_Scoring_Manipulation
-- name    : ElectManip_Scoring_Manipulation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:21:30.47777+00:00
-- url     : https://prove2.me/theorems/cc940686-473b-4407-a2da-00e8428df436
-- title:
--   Three-candidate constructive coalitional weighted manipulation
-- statement:
--   For exactly three candidates, an instance $I=(S,T,p)$ consists of a finite list $S$ of fixed weighted ballots, a finite list $T$ of coalition weights, and a preferred candidate $p$. For a fixed positional scoring protocol $\alpha$, manipulation is possible exactly when the coalition can independently choose one complete ballot for each entry of $T$ so that $p$ is the unique winner:
--
--   $$\operatorname{Manipulable}_\alpha(I)\iff
--   \exists (b_i)_{i<|T|},\quad
--   \forall q\ne p,\quad s_\alpha(S\mathbin{+\!+}[(T_i,b_i)]_{i<|T|},q)
--   <s_\alpha(S\mathbin{+\!+}[(T_i,b_i)]_{i<|T|},p).$$
--
--   The plurality predicate for a sorted triple means $\alpha_0>\alpha_1=\alpha_2$, exactly positive affine equivalence to $(1,0,0)$. It does not include constant vectors. This definition supplies the complete-information, deterministic decision question in Definition 1. No original truthful ballot or improvement in utility is required, and manipulators need not vote identically or place $p$ first. All voter counts and weights are unbounded, and either list can be empty.
--
--   **Formalization Note** The ballot list has exactly the length of the coalition weight list before the two lists are zipped, so no voter is dropped. The protocol and integer score conventions are those of the separate positional-scoring definition.
-- source:
--   Conitzer, Sandholm and Lang, When Are Elections with Few Candidates Hard to Manipulate?, Journal of the ACM (2007), DOI 10.1145/1236457.1236461, p. 8, Definition 1 and tie convention; p. 15, Theorem 6 and plurality equivalence in its proof (PDF pp. 8, 15).

import Definitions.Def_ElectManip_Scoring_Protocol

namespace ElectManip.Scoring

/-- The complete-information input for constructive weighted coalition manipulation. -/
structure Instance where
  fixedVotes : Profile 3
  coalitionWeights : List ℕ
  preferred : Fin 3

/-- Each coalition member may choose any complete ranking independently. -/
def Manipulable (α : Protocol 3) (I : Instance) : Prop :=
  ∃ ballots : List (Ballot 3),
    ballots.length = I.coalitionWeights.length ∧
    UniqueWinner α (I.fixedVotes ++ I.coalitionWeights.zip ballots) I.preferred

/-- Exactly the sorted triples positively affinely equivalent to plurality. -/
def IsPlurality (α : Protocol 3) : Prop :=
  α.points 1 < α.points 0 ∧ α.points 1 = α.points 2

end ElectManip.Scoring

/- BEGIN IMPORTED LEAN AUDIT CONTEXT
The following are declaration excerpts from the imported modules.
They are copied code, not a mathematical read-back.

namespace ElectManip.Scoring
abbrev Ballot (n : ℕ) := Equiv.Perm (Fin n)
structure Protocol (n : ℕ) where
  points : Fin n → ℤ
  nonincreasing : Antitone points
abbrev Profile (n : ℕ) := List (ℕ × Ballot n)
def score {n : ℕ} (α : Protocol n) (votes : Profile n) (c : Fin n) : ℤ :=
  (votes.map fun v => (v.1 : ℤ) * α.points (v.2 c)).sum
def UniqueWinner {n : ℕ} (α : Protocol n) (votes : Profile n) (p : Fin n) : Prop :=
  ∀ q : Fin n, q ≠ p → score α votes q < score α votes p
end ElectManip.Scoring

END IMPORTED LEAN AUDIT CONTEXT -/


