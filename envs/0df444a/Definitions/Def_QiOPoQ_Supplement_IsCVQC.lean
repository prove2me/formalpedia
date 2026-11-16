-- Prove2me | Definitions.Def_QiOPoQ_Supplement_IsCVQC
-- name    : QiOPoQ_Supplement_IsCVQC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:47:50.032307+00:00
-- url     : https://prove2.me/theorems/ec45e446-e3e1-492f-b79a-f02dbebf6801
-- title:
--   Definition 3.5: privately verifiable two-message classical verification of quantum computation
-- statement:
--   A protocol $(\mathrm{Gen},\mathrm{Prove},\mathrm{Verify})$ for classical verification of quantum computation (Definition 3.5):
--
--   1. $\mathrm{Gen}(1^\lambda,C)\to(\mathsf{chall},\mathsf{state})$ is classical PPT; $\mathrm{Prove}(1^\lambda,\mathsf{chall})$ is quantum polynomial time with classical output; $\mathrm{Verify}(1^\lambda,C,\mathsf{chall},\mathsf{state},\mathsf{resp})\in\{0,1,\bot\}$ is deterministic classical polynomial time.
--   2. Correctness: for every polynomial-size family $\{C_\lambda\}\in\mathcal C_{\mathsf{BQP}}$ with bits $a_\lambda$ such that $\|C_\lambda-X^{a_\lambda}\|_\diamond\le\mathrm{negl}(\lambda)$, the honest prover makes Verify output $a_\lambda$ with probability at least $1-\mathrm{negl}(\lambda)$.
--   3. Soundness: for every such family and every non-uniform QPT prover $A$,
--   $$\Pr\big[\mathrm{Verify}(1^\lambda,C_\lambda,\mathsf{chall},\mathsf{state},A(1^\lambda,\mathsf{chall}))=1-a_\lambda\big]\le\mathrm{negl}(\lambda).$$
--
--   **Formalization Note** Gen's randomness is a list of independent uniform draws whose ranges are computed in polynomial time (uniform bits, and uniform elements of $[m]$ as Figure 7 needs); `avgDice` averages over them. The honest prover is given by the classical description of the circuits it runs. $\bot$ is `none`. "The unique bit $a_\lambda$" is read as every bit sequence within negligible diamond distance (it is unique for all large $\lambda$).
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Definition 3.5, pp.15–16

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_InCBQP
import Definitions.Def_QiOPoQ_encCirc
import Definitions.Def_QiOPoQ_qptExpect
import Definitions.Def_QiOPoQ_Supplement_NUQPT

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAdvFew.PoQOracle QAlgorithms.Complexity

/-- The average of `g` over a uniform choice of `ω = (ω_0, …, ω_{k−1})` with each `ω_i` uniform in
`{0, …, rad_i − 1}` independently: the randomness of a classical sampler that draws uniform bits
(`rad_i = 2`) and uniform elements of `[m]` (`rad_i = m`). -/
noncomputable def avgDice (rad : List ℕ) (g : List ℕ → ℝ) : ℝ :=
  (∑ ω : (i : Fin rad.length) → Fin (rad.get i), g (List.ofFn fun i => (ω i).val)) / (rad.prod : ℝ)

/-- The description of a sample `ω` (each entry in unary). -/
def encDice (ω : List ℕ) : Str := tup (ω.map encNat)

/-- The description of a verifier output in `{0, 1, ⊥}`: `[b]` for a bit, `[]` for `⊥`. -/
def encOptBool : Option Bool → Str
  | none => []
  | some b => [b]

/-- The syntax of Definition 3.5 (Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage
and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289, sha256 fe2f9210…,
Definition 3.5, p.15): "Gen(1^λ, C) → (chall, state) is a classical PPT algorithm that returns a
classical challenge chall and a classical secret state state"; "Prove(1^λ, chall) → resp is a
quantum polynomial-time algorithm that returns a classical response resp"; "Verify(1^λ, C, chall,
state, resp) → {0, 1, ⊥} is a deterministic classical polynomial-time algorithm that returns a bit
or a rejection symbol ⊥."

`rad λ C` lists the ranges of Gen's uniform draws (computed in polynomial time, so the number of
draws and each range are polynomial in `λ + |C|`; each range is `≥ 1`); `gen λ C ω` is Gen's output
on draws `ω`, computed in polynomial time; `prove λ chall` is the tuple of circuit descriptions
that the quantum prover runs (`qptExpect`), computed in polynomial time; `verify` is computed in
polynomial time. -/
def CVQCEfficient {G : GateSet} (rad : ℕ → Circ G → List ℕ) (gen : ℕ → Circ G → List ℕ → Str × Str)
    (prove : ℕ → Str → Str) (verify : ℕ → Circ G → Str → Str → Str → Option Bool) : Prop :=
  (∀ n C, ∀ k ∈ rad n C, 1 ≤ k) ∧
    (∃ g : Str → Str, PolyTimeComputable g ∧
      ∀ n C, g (pair (unary n) (encCirc C)) = encDice (rad n C)) ∧
    (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ n C (ω : List ℕ), List.Forall₂ (· < ·) ω (rad n C) →
      g (tup [unary n, encCirc C, encDice ω]) = pair (gen n C ω).1 (gen n C ω).2) ∧
    (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ n (c : Str), g (pair (unary n) c) = prove n c) ∧
    (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ n C (c st resp : Str),
      g (tup [unary n, encCirc C, c, st, resp]) = encOptBool (verify n C c st resp))

/-- Correctness (Definition 3.5, p.16): "For every polynomial-size circuit ensemble
{C_λ}λ∈N ∈ C_BQP, let a_λ be the unique bit such that ∥C_λ − X^{a_λ}∥⋄ ≤ negl(λ). We require that
Pr[Verify(1^λ, C_λ, chall, state, resp) = a_λ : (chall, state) ← Gen(1^λ, C_λ),
resp ← Prove(1^λ, chall)] ≥ 1 − negl(λ)."

**Formalization Note.** "The unique bit a_λ" is read as every bit sequence `a` with
`∥C_λ − X^{a_λ}(·)∥⋄ ≤ μ(λ)` for a negligible `μ` (it is unique for all large `λ`). -/
def CVQCCorrect (G : GateSet) (rad : ℕ → Circ G → List ℕ) (gen : ℕ → Circ G → List ℕ → Str × Str)
    (prove : ℕ → Str → Str) (verify : ℕ → Circ G → Str → Str → Str → Option Bool) : Prop :=
  ∀ Cf : ℕ → Circ G, InCBQP Cf → ∀ a : ℕ → Bool,
    (∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n, diamond (chanAs (Cf n) 1 1) (bitFlip (a n)) ≤ μ n) →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ n, 1 - ν n ≤ avgDice (rad n (Cf n)) fun ω =>
      qptExpect G (prove n (gen n (Cf n) ω).1) fun resp =>
        if verify n (Cf n) (gen n (Cf n) ω).1 (gen n (Cf n) ω).2 resp = some (a n) then 1 else 0

/-- Soundness (Definition 3.5, p.16): "For every polynomial-size circuit ensemble
{C_λ}λ∈N ∈ C_BQP, let a_λ be the unique bit such that ∥C_λ − X^{a_λ}∥⋄ ≤ negl(λ). For every
possibly nonuniform QPT prover A, we must have that Pr[Verify(1^λ, C_λ, chall, state,
A(1^λ, chall)) = 1 − a_λ : (chall, state) ← Gen(1^λ, C_λ)] ≤ negl(λ)." Provers are `NUQPT`;
the negligible bound is chosen after the family and the prover. -/
def CVQCSound (G : GateSet) (rad : ℕ → Circ G → List ℕ) (gen : ℕ → Circ G → List ℕ → Str × Str)
    (verify : ℕ → Circ G → Str → Str → Str → Option Bool) : Prop :=
  ∀ Cf : ℕ → Circ G, InCBQP Cf → ∀ a : ℕ → Bool,
    (∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n, diamond (chanAs (Cf n) 1 1) (bitFlip (a n)) ≤ μ n) →
    ∀ A : NUQPT, ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ n, avgDice (rad n (Cf n)) (fun ω =>
      A.expect G n (gen n (Cf n) ω).1 fun resp =>
        if verify n (Cf n) (gen n (Cf n) ω).1 (gen n (Cf n) ω).2 resp = some (!(a n)) then 1 else 0)
      ≤ ν n

/-- **Definition 3.5 ((Privately verifiable, two-message) classical verification of quantum
computation).** arXiv:2609.40289, Definition 3.5, pp.15–16: "A (privately verifiable) protocol
for classical verification of quantum computation is a tuple (Gen, Prove, Verify)" with the
syntax of `CVQCEfficient`, correctness (`CVQCCorrect`) and soundness (`CVQCSound`). Blindness,
optional in Definition 3.5, is `IsBlindCVQC`. -/
def IsCVQC (G : GateSet) (rad : ℕ → Circ G → List ℕ) (gen : ℕ → Circ G → List ℕ → Str × Str)
    (prove : ℕ → Str → Str) (verify : ℕ → Circ G → Str → Str → Str → Option Bool) : Prop :=
  CVQCEfficient rad gen prove verify ∧ CVQCCorrect G rad gen prove verify ∧
    CVQCSound G rad gen verify

end QiOPoQ.Supplement


