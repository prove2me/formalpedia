-- Prove2me | Definitions.Def_WICanon_Soundness
-- name    : WICanon_Soundness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:05:08.342784+00:00
-- url     : https://prove2.me/theorems/4fd839fe-8515-4bac-a777-e1e6d6ccab18
-- title:
--   Completeness and soundness of interactive proofs and arguments
-- statement:
--   For a protocol $(P,V)$ for $\mathcal R$:
--
--   1. **$(1-\alpha)$-completeness:** for every $(x,w)\in\mathcal R$, $\Pr[\mathrm{Out}(\langle P(x,w),V(x)\rangle)=1]\ge 1-\alpha(|x|)$.
--   2. **$\beta$-statistical soundness:** for every $x\notin\mathcal L(\mathcal R)$ and every prover, the acceptance probability is at most $\beta(|x|)$.
--   3. **$\beta$-computational soundness:** the same for non-uniform PPT provers.
--
--   An **interactive proof** is efficient with negligible completeness error and negligible statistical soundness error; an **interactive argument** has computational soundness instead.
--
--   **Formalization Note** Read literally, the printed computational soundness allows the machine to depend on $x$, and a finite table then makes it statistical soundness. Here each machine is bound from some length on (`SoundCompAt`), or has one negligible error at all lengths (`SoundCompNegl`). A cheating prover keeps one coin tape across rounds and receives $x$. A statistical prover is a deterministic function of the verifier's messages, which loses nothing against a fixed verifier.
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Definition 2.8, p.13

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_QiOPoQ_NUPPT
import Definitions.Def_OWFLocalDesc_Negligible
import Definitions.Def_WICanon_IsNPRelation
import Definitions.Def_WICanon_ProtocolProps

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity QAdvFew.PoQOracle QiOPoQ OWFLocalDesc

/-- **`(1 − α)`-completeness** (Arnon, Mazor, Pass, Silbak, STOC 2027 submission manuscript, sha256
3f78ec3d…, Definition 2.8, p.13): for every `(x, w) ∈ R`, `Pr[Out(⟨P(x, w), V(x)⟩) = 1] ≥ 1 − α(|x|)`. -/
def CompleteAt (pv : Protocol) (R : Relation) (α : ℕ → ℝ) : Prop :=
  ∀ x w, R x w → 1 - α x.length ≤ pv.acceptProb x w

/-- **`β`-statistical soundness** (Definition 2.8, p.13): for every `x ∉ L(R)` and every (possibly
inefficient) prover.

**Formalization Note.** Prover strategies are functions of the verifier's messages so far. A
deterministic function loses nothing against a fixed verifier: the acceptance probability of a
randomized prover is an average over its coins. -/
def SoundStatAt (pv : Protocol) (R : Relation) (β : ℕ → ℝ) : Prop :=
  ∀ x, ¬ InLang R x → ∀ respond : List Str → Str, pv.acceptProbAgainst x respond ≤ β x.length

/-- The reply function of a non-uniform PPT cheating prover `A` on input `x`, on the one coin tape
`r` it keeps across rounds. It holds the advice of length `|x|` and receives `x` (§2, p.11).

**Formalization Note.** `NUPPT.expect` draws fresh coins per call and sizes them by the input
length, so it cannot model a prover that keeps one tape across rounds; `A.run` is applied directly
here and the tape has `A.coins(|x|)` bits. -/
def cheatRespond (A : NUPPT) (x r : Str) : List Str → Str := fun ρs =>
  A.run (pair (A.advice x.length) (pair (unary x.length) (pair (pair x (tup ρs)) r)))

/-- `Pr[Out(⟨P̂, V(x)⟩) = 1]` for a non-uniform PPT prover `P̂ = A`. -/
noncomputable def compAcceptProb (pv : Protocol) (A : NUPPT) (x : Str) : ℝ :=
  avgCoins (A.coins.eval x.length) fun r => pv.acceptProbAgainst x (cheatRespond A x r)

/-- **`β`-computational soundness** (Definition 2.8, p.13).

**Formalization Note.** Printed, "For every x ∉ LR and every non-uniform PPT prover": read literally
the machine may depend on `x`, and a finite table then makes computational soundness equal to
statistical soundness. The reading here is the standard asymptotic one, which the paper uses: every
machine is bound from some length on. -/
def SoundCompAt (pv : Protocol) (R : Relation) (β : ℕ → ℝ) : Prop :=
  ∀ A : NUPPT, ∃ n₀ : ℕ, ∀ x, n₀ ≤ x.length → ¬ InLang R x → compAcceptProb pv A x ≤ β x.length

/-- Negligible computational soundness ("When α and β are not specified, they are assumed to be
negligible functions", p.13): for each machine one negligible error at all lengths. -/
def SoundCompNegl (pv : Protocol) (R : Relation) : Prop :=
  ∀ A : NUPPT, ∃ β : ℕ → ℝ, Negligible β ∧
    ∀ x, ¬ InLang R x → compAcceptProb pv A x ≤ β x.length

/-- **Interactive proof** for `R` (Definition 2.8, p.13): efficient, with negligible completeness
error and negligible statistical soundness error. -/
def IsInteractiveProof (pv : Protocol) (R : Relation) : Prop :=
  pv.IsEfficient ∧ (∃ α, Negligible α ∧ CompleteAt pv R α) ∧
    ∃ β, Negligible β ∧ SoundStatAt pv R β

/-- **Interactive argument** for `R` (Definition 2.8, p.13): efficient, with negligible completeness
error and negligible computational soundness error. -/
def IsInteractiveArgument (pv : Protocol) (R : Relation) : Prop :=
  pv.IsEfficient ∧ (∃ α, Negligible α ∧ CompleteAt pv R α) ∧ SoundCompNegl pv R

end WICanon


