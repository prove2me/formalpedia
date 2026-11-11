-- Prove2me | Definitions.Def_TrapdoorHCF_CCA2_Auxiliary
-- name    : TrapdoorHCF_CCA2_Auxiliary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T19:40:16.939206+00:00
-- url     : https://prove2.me/theorems/fd6b2ef2-9438-4ecb-be12-4d88d3fe2cf4
-- title:
--   Fresh-evaluation, multi-sample and hidden-candidate experiments
-- statement:
--   The **fresh-evaluation experiment** runs an oracle machine $B$ with partial-inversion access, interprets its output as a tuple-coded finite set $S$, independently samples $X$, and tests $\operatorname{Eval}(pk,X)\in S$. Its output bound makes $S$ polynomial in size. Duplicate entries have no effect; entries outside the evaluation range cannot be hit.
--
--   The **multi-sample experiment** gives a two-stage machine $q(\lambda)$ ordered independent pairs $(Y_i,Z_i)$, where $Y_i=\operatorname{Eval}(pk,X_i)$ and each $Z_i$ is either real or an independent uniform bit. Stage 1 has full partial inversion and stage 2's oracle rejects every $Y_i$.
--
--   The **hidden-candidate experiment** first runs a CCA2 adversary with genuine decryption, then samples a fair challenge bit and $\lambda$ independent candidate pairs. The first matching candidate determines the challenge as in the construction. If its evaluation is $Y_I$, the hidden values are $H_I=\{Y_j:j\ne I\}\setminus\{Y_I\}$; without a match, all candidate evaluations are hidden. In both experiments stage 2 uses genuine decryption excluding only the exact challenge. The tested event is
--
--   $$\mathrm{Bad}=\{\text{stage 2 submits }(y,0)\text{ with }y\in H_I\}.$$
--
--   A later timeout does not erase earlier queries. Invalid challenge messages abort as in the underlying IND-CCA2 game. These definitions specify the distributions in Lemmas 2–4, including collisions and the empty candidate tuple.
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Lemma 2, p.37; Lemma 3, p.38; Lemma 4, p.40

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Constructions
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2

/-- Lemma 2, p.37. B finishes with a tuple-coded list representing S. Duplicates
are harmless; size is bounded by the reactive machine's polynomial output bound.
The fresh input is sampled independently after B terminates. -/
noncomputable def expFresh (T : TDHF) (B : RestrictedDec.Adversary) (lam : ℕ) : PMF Bool := do
  let keys ← T.keyLaw lam
  let pre ← runStage B lam (T.pInv lam keys.2) (B.p.eval lam + 1) []
    (BeyondDS.tup [encNat lam, keys.1])
  let x ← T.inputLaw lam
  let s := match pre.output with
    | none => []
    | some out => BeyondDS.untup out
  pure (decide (T.eval lam keys.1 x ∈ s))

/-- Independent candidates for Lemmas 3 and 4. For random=false the z values are
real; for random=true they are independent uniform one-bit strings. -/
noncomputable def samplePairs (T : TDHF) (lam : ℕ) (pk : Str) (random : Bool) :
    ℕ → PMF (List (Str × Str))
  | 0 => pure []
  | k + 1 => do
      let x ← T.inputLaw lam
      let u ← coinsLaw 1
      let tail ← samplePairs T lam pk random k
      pure ((T.eval lam pk x, if random then List.ofFn u else T.hEval lam pk x) :: tail)

/-- Lemma 3, p.38. The challenge tuple preserves its order, including collisions.
The post-challenge oracle refuses all evaluation strings in this tuple. -/
noncomputable def expMulti (T : TDHF) (q : ℕ → ℕ) (D : RestrictedDec.Adversary)
    (random : Bool) (lam : ℕ) : PMF Bool := do
  let keys ← T.keyLaw lam
  let pre ← runStage D lam (T.pInv lam keys.2) (D.p.eval lam + 1) []
    (BeyondDS.tup [encNat lam, keys.1])
  match pre.output with
  | none => pure false
  | some sigma =>
      let pairs ← samplePairs T lam keys.1 random (q lam)
      let ys := pairs.map Prod.fst
      let oracle := fun y => if y ∈ ys then none else T.pInv lam keys.2 y
      let challenge := BeyondDS.tup (pairs.map fun yz => BeyondDS.tup [yz.1, yz.2])
      let post ← runStage D lam oracle pre.fuel pre.state
        (BeyondDS.tup [encNat lam, keys.1, sigma, challenge])
      pure ((post.output.getD []).headD false)

/-- H_I of p.40, removing every evaluation equal to the selected one, even if
multiple candidate indices collide. Without a matching candidate all are hidden. -/
def hiddenCandidates (m : Str) (pairs : List (Str × Str)) : List Str :=
  let ys := pairs.map Prod.fst
  match pairs.find? (fun yz => decide (yz.2 = m)) with
  | some selected => ys.filter (fun y => decide (y ≠ selected.1))
  | none => ys

/-- Bad tests submitted ciphertexts, before their answers are delivered. -/
def hiddenQuery (hidden : List Str) : Str → Bool
  | false :: y => decide (y ∈ hidden)
  | _ => false

/-- Lemma 4's two experiments, p.40. Both stages use genuine decryption of the
Theorem 7 scheme, with exact-challenge exclusion only in stage 2. Invalid challenge
messages abort just as in Definition 2. Bad records all stage-2 queries even if the
machine later exhausts its budget. -/
noncomputable def expBad (T : TDHF) (A : RestrictedDec.Adversary)
    (random : Bool) (lam : ℕ) : PMF Bool := do
  let keys ← T.keyLaw lam
  let pre ← runStage A lam ((cca2Scheme T).dec lam keys.2) (A.p.eval lam + 1) []
    (BeyondDS.tup [encNat lam, keys.1])
  match pre.output with
  | none => pure false
  | some out =>
      let ms := BeyondDS.untup out
      let m0 := ms.getD 0 []
      let m1 := ms.getD 1 []
      if m0.length = 1 ∧ m1.length = 1 ∧ m0.length = m1.length then
        let b ← PMF.uniformOfFintype Bool
        let m := if b then m1 else m0
        let pairs ← samplePairs T lam keys.1 random lam
        let ct := chooseCipher m pairs
        let hidden := hiddenCandidates m pairs
        let post ← runStage A lam (exclude ((cca2Scheme T).dec lam keys.2) ct)
          pre.fuel pre.state (BeyondDS.tup [ct, pre.state])
        pure (post.queries.any (hiddenQuery hidden))
      else pure false

end TrapdoorHCF.CCA2


