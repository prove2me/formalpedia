-- Prove2me | Definitions.Def_IIDMatchHard_Supplement_RandPolicyGuarantee
-- name    : IIDMatchHard_Supplement_RandPolicyGuarantee
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:19:44.233208+00:00
-- url     : https://prove2.me/theorems/89df8d91-60ca-48a3-8f62-d8aca05fefc9
-- title:
--   Randomized polynomial-time construction of online policies with joint expected guarantee
-- statement:
--   A randomized policy constructor receives the binary encoding of a valid unweighted known-i.i.d. matching instance, uses polynomially many fair coins, and outputs a finite code within a worst-case polynomial time bound on every coin string. A uniform polynomial-time interpreter turns every output code into a deterministic online policy that sees only the past types, matched offline set, and current type.
--
--   Its **constructed value** is the expectation, over both the constructor's fair coins and the independent i.i.d. arrival sequence, of the number of matches obtained by the resulting policy. The guarantee at error $\varepsilon$ is
--
--   $$
--   \mathbb E_{r,Y}\big[M_{\pi_r}(T)\big] \;\ge\; (1-\varepsilon/2)\operatorname{OPT}(I)
--   $$
--
--   for every valid instance $I$ in the published two-neighbor class.
--
--   **Formalization Note** The expectation is an average of the published exact policy value over all fair seeds. It is not a seed-by-seed guarantee; the interpreter's machine bound separately ensures that every output policy is executable online in polynomial time.
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Theorem 3.10, p.10 (PDF p.11); proof p.24 (PDF p.25)

import Mathlib
import Definitions.Def_IIDMatchHard_Inst
import Definitions.Def_IIDMatchHard_Supplement_NPSubsetBPP
import Definitions.Def_NSWApxHard_Reduction_Welfare

set_option autoImplicit false

namespace IIDMatchHard

namespace Supplement

/-- Binary encoding of an online-policy query: the instance, the observed type history, the
matched-set bit vector, and the current type. Every component is finite and the integer fields
use the self-delimiting `natBits` encoding. -/
def policyQuery (I : Inst) (code : Word) (h : List (Fin I.nTy))
    (S : Finset (Fin I.nOff)) (y : Fin I.nTy) : Word :=
  encInst I ++ NSWApxHard.Reduction.natBits code.length ++ code ++
    NSWApxHard.Reduction.natBits h.length ++
    (h.map fun z => NSWApxHard.Reduction.natBits z.val).flatten ++
    (List.ofFn fun u : Fin I.nOff => decide (u ∈ S)) ++
    NSWApxHard.Reduction.natBits y.val

/-- Encoding of a policy's proposed action (`false` for rejection, `true` followed by an offline
vertex index for a proposal). -/
def encAction {n : ℕ} : Option (Fin n) → Word
  | none => [false]
  | some u => true :: NSWApxHard.Reduction.natBits u.val

/-- A uniform polynomial-time interpreter for finite codes of deterministic online policies.
The interpreter supplies the policy denoted by every code and one ordinary Turing machine that
evaluates every such policy on the encoded instance and observed online state in polynomial time.

**Formalization Note.** Policies have exactly the published base type: they see past types, the
matched set and the current type, but no future arrival. Invalid or already-matched proposals are
rejected by the published run semantics. -/
structure PolicyInterpreter where
  policy : (I : Inst) → Word → Policy (Fin I.nOff) (Fin I.nTy)
  machine : NKtLB.Machine
  timeConst : ℕ
  timeDegree : ℕ
  computes : ∀ (I : Inst) (code : Word) (h : List (Fin I.nTy))
    (S : Finset (Fin I.nOff)) (y : Fin I.nTy),
      machine.Computes
        (ApproxPolySatCH.Main.clock timeConst timeDegree
          (policyQuery I code h S y).length)
        (policyQuery I code h S y)
        (encAction (policy I code h S y))

/-- A randomized polynomial-time constructor of policy codes. It uses a uniformly polynomial
number of fair bits and every branch outputs within one uniformly polynomial worst-case clock. -/
structure RandPolicyConstructor where
  out : Word → Word → Word
  machine : NKtLB.Machine
  timeConst : ℕ
  timeDegree : ℕ
  coinConst : ℕ
  coinDegree : ℕ
  computes : ∀ (x : Word)
    (r : Fin (ApproxPolySatCH.Main.clock coinConst coinDegree x.length) → Bool),
      machine.HaltsWith ∅ ⟨x, [], [], List.ofFn r⟩
        (ApproxPolySatCH.Main.clock timeConst timeDegree x.length)
        (NKtLB.bitsSym (out x (List.ofFn r)))

/-- Joint expected value of the policy constructor on `I`: average over the constructor's fair
coins of the published exact i.i.d.-arrival expectation of the decoded deterministic policy. -/
noncomputable def constructedValue (E : PolicyInterpreter) (A : RandPolicyConstructor)
    (I : Inst) : ℝ :=
  let q := ApproxPolySatCH.Main.clock A.coinConst A.coinDegree (encInst I).length
  (∑ r : Fin q → Bool,
      value I.toModel (E.policy I (A.out (encInst I) (List.ofFn r)))) / (2 : ℝ) ^ q

/-- A randomized polynomial-time constructor satisfies the policy clause of Theorem 3.10 at
error `ε`: on every valid unweighted, two-neighbor known-i.i.d. instance, its joint expectation
over the constructor coins and the i.i.d. arrivals is at least `(1 - ε/2) OPT(I)`.

Teng–Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), Theorem 3.10, p.10 (PDF p.11), proof p.24 (PDF p.25).

**Formalization Note.** The guarantee is on the average over output policies, matching the
`ζ_j` experiment in Appendix B.10; it does not require every coin outcome to produce a good
policy. `PolicyInterpreter.computes` separately requires every output policy to run online in
polynomial time. -/
def RandPolicyGuarantee (ε : ℝ) (E : PolicyInterpreter) (A : RandPolicyConstructor) : Prop :=
  ∀ I : Inst, I.Valid → (1 - ε / 2) * onlineOpt I ≤ constructedValue E A I

end Supplement

end IIDMatchHard


