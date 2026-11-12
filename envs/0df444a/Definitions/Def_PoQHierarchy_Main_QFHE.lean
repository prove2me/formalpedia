-- Prove2me | Definitions.Def_PoQHierarchy_Main_QFHE
-- name    : PoQHierarchy_Main_QFHE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:41.033819+00:00
-- url     : https://prove2.me/theorems/555867d2-050c-4386-92ae-fed6bd41d18b
-- title:
--   Secret-key QFHE: correctness with auxiliary input and IND-CPA security against QPT adversaries
-- statement:
--   A **secret-key quantum fully homomorphic encryption scheme** (Definition 3.3, Remark 3.4) is a tuple $(\mathsf{Gen},\mathsf{Enc},\mathsf{Eval},\mathsf{Dec})$ of machines of the mission's model, each given $1^\lambda$:
--
--   - $\mathsf{Gen}(1^\lambda)$ outputs a secret key $sk$, and $\mathsf{Enc}(sk,x)$ a ciphertext; both are $\mathsf{PPT}$;
--   - $\mathsf{Eval}(C,ct)$ is $\mathsf{QPT}$ and acts on a quantum register $A$: its device workspace consists of $A$ followed by its own ancillas in $|0\rangle$, and it outputs a classical ciphertext;
--   - $\mathsf{Dec}(sk,ct)$ is $\mathsf{QPT}$ and outputs a classical string on a classical ciphertext.
--
--   Here $C$ ranges over quantum circuits with classical output over the gate set, $C:\mathcal H_A\times(\mathbb C^2)^{\otimes m}\to\{0,1\}^*$, i.e. gates on $A$, an $m$-bit input and ancillas, followed by a measurement.
--
--   **Correctness with auxiliary input.** For every such circuit $C$ there is a negligible $\mu$ such that for every $\lambda$, every state $|\Psi\rangle_{AB}$ (with $B$ any number of qubits), every $x\in\{0,1\}^m$, every $sk$ in the support of $\mathsf{Gen}(1^\lambda)$ and every $ct$ in the support of $\mathsf{Enc}(sk,x)$, the two classical–quantum outputs
--
--   - *Game 1*: evaluate $C$ on $x$ and $A$, output $y$ and register $B$;
--   - *Game 2*: $ct'\leftarrow\mathsf{Eval}_C(\cdot\otimes|0\rangle^{\mathrm{poly}},ct)$ on $A$, $y'=\mathsf{Dec}(sk,ct')$, output $y'$ and register $B$;
--
--   have trace distance at most $\mu(\lambda)$. The trace distance of two classical–quantum outputs is the largest difference of acceptance probabilities of a test $\{0\le M_\ell\le I\}$ on $B$ indexed by the classical label.
--
--   **IND-CPA security against quantum distinguishers.** For any two messages $x_0,x_1$ of equal length and any $\mathsf{QPT}$ adversary $A$ with classical access to the oracle $\mathsf{Enc}_{sk}(\cdot)$,
--   $$\Bigl|\Pr\bigl[A^{\mathsf{Enc}_{sk}(\cdot)}(ct_0)=1\bigr]-\Pr\bigl[A^{\mathsf{Enc}_{sk}(\cdot)}(ct_1)=1\bigr]\Bigr|\le\mathrm{negl}(\lambda),\qquad sk\leftarrow\mathsf{Gen}(1^\lambda),\ ct_b\leftarrow\mathsf{Enc}(sk,x_b).$$
--
--   A **post-quantum secure QFHE scheme** satisfies the efficiency requirements, correctness for all circuits, and IND-CPA security. Schemes of this kind are known under the hardness of LWE [Bra18, Mah18], so the hypothesis is not vacuous.
--
--   **Formalization Note** Only the classical-output behaviour of $\mathsf{Eval}$ and $\mathsf{Dec}$ is modelled, because no property refers to quantum outputs. A run of $\mathsf{Gen}$ or $\mathsf{Enc}$ without output gives the empty string. The trace distance is taken in its variational (Helstrom) form, which equals $\tfrac12\|\rho-\sigma\|_1$ for normalized outputs.
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), Definition 3.3 (pp.20–21), Remark 3.4 (p.21), p.24 (QPT); canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_Machine

open QAlgorithms.Complexity
open scoped ComplexOrder
set_option autoImplicit false

namespace PoQHierarchy.Main

/-!
Bacho, Leichtle, Arora, Cojocaru, STOC 2027 submission #1666, Definition 3.3 (pp.20–21) and
Remark 3.4: secret-key quantum fully homomorphic encryption.

`Gen`, `Enc` are `PPT`, `Eval`, `Dec` are `QPT = PPT^{∞-intQPT}` machines of the mission's one
machine model. Every algorithm also receives `1^λ`. `Eval` acts on a quantum input register `A`:
its device workspace is `A` followed by its own ancillas, while a further register `B` (the
auxiliary input) lies outside its reach.

Two properties are required: correctness with auxiliary input, for every circuit with classical
output over the gate set, and IND-CPA security against `QPT` adversaries with classical access to an
encryption oracle.
-/

/-- A quantum circuit with classical output `C : H_A × (ℂ²)^{⊗m} → {0,1}*` over the gate set:
qubits `0, …, a-1` form the register `A`, qubits `a, …, a+m-1` hold the classical input `x`, and
`anc` further qubits start in `|0⟩`; the circuit applies its gates and measures `meas`. -/
structure QCirc where
  a : ℕ
  m : ℕ
  anc : ℕ
  gates : List Gate
  meas : List ℕ

/-- The circuit acts on its own `a + m + anc` qubits only. -/
def QCirc.WellFormed (C : QCirc) : Bool :=
  (Circuit.mk C.gates C.meas).WellFormed (C.a + C.m + C.anc)

/-- The classical description of a circuit, as given to `Eval`. -/
def QCirc.code (C : QCirc) : Str :=
  pack [natCode C.a, natCode C.m, natCode C.anc, circuitCode (Circuit.mk C.gates C.meas)]

/-- A secret-key QFHE scheme `(Gen, Enc, Eval, Dec)` (Definition 3.3, Remark 3.4). Inputs:
`Gen(1^λ)`, `Enc(1^λ, sk, x)`, `Eval(1^λ, C, ct)` on the register `A` plus `Eval.qubits` ancillas,
`Dec(1^λ, sk, ct)`; the arguments are combined with `pack`. -/
structure QFHE where
  gen : IntMachine
  enc : IntMachine
  eval : IntMachine
  dec : IntMachine

namespace QFHE

variable (S : QFHE)

/-- The distribution of `sk ← Gen(1^λ)` (a run without output gives the empty key). -/
noncomputable def genDist (lam : ℕ) : WList Str :=
  (S.gen.outDist (unary lam)).map fun p => (p.1, p.2.getD [])

/-- The distribution of `ct ← Enc(sk, x)` (a run without output gives the empty ciphertext). -/
noncomputable def encDist (lam : ℕ) (sk x : Str) : WList Str :=
  (S.enc.outDist (pack [unary lam, sk, x])).map fun p => (p.1, p.2.getD [])

/-- The distribution of `Dec(sk, ct)` on a classical ciphertext: a classical string, or `none` if
`Dec` produces no output. -/
noncomputable def decDist (lam : ℕ) (sk ct : Str) : WList (Option Str) :=
  S.dec.outDist (pack [unary lam, sk, ct])

/-- Efficiency (Definition 3.3): `Gen`, `Enc` are `PPT`, `Eval`, `Dec` are `QPT`. Keys and
ciphertexts have polynomial length because every action string does. -/
def Efficient : Prop :=
  S.gen ∈ PPT ∧ S.enc ∈ PPT ∧ S.eval ∈ QPT ∧ S.dec ∈ QPT

end QFHE

/-! ### Correctness with auxiliary input -/

/-- `⟨ψ|(I ⊗ M)|ψ⟩` for a state on `R + b` qubits and an operator `M` on the last `b` qubits
(the register `B`). -/
noncomputable def expectB {R b : ℕ} (ψ : QVec (R + b))
    (M : Matrix (Fin b → Bool) (Fin b → Bool) ℂ) : ℝ :=
  (∑ zr : Fin R → Bool, ∑ u : Fin b → Bool, ∑ v : Fin b → Bool,
    star (ψ (Fin.append zr u)) * M u v * ψ (Fin.append zr v)).re

/-- The acceptance probability of the test `{M_ℓ}` on a classical–quantum output: each branch
carries a weight, a classical label `ℓ` and an unnormalized state whose last `b` qubits are `B`. -/
noncomputable def cqTest {R b : ℕ} (d : WList (Option Str × QVec (R + b)))
    (M : Option Str → Matrix (Fin b → Bool) (Fin b → Bool) ℂ) : ℝ :=
  d.expect fun p => expectB p.2 (M p.1)

/-- The trace distance of two classical–quantum outputs (classical label, register `B`), in its
variational (Helstrom) form: the largest difference of acceptance probabilities over all tests
`0 ≤ M_ℓ ≤ I`. -/
noncomputable def cqDistance {R R' b : ℕ} (d : WList (Option Str × QVec (R + b)))
    (d' : WList (Option Str × QVec (R' + b))) : ℝ :=
  sSup {t | ∃ M : Option Str → Matrix (Fin b → Bool) (Fin b → Bool) ℂ,
    (∀ ℓ, (M ℓ).PosSemidef ∧ (1 - M ℓ).PosSemidef) ∧ t = |cqTest d M - cqTest d' M|}

/-- **Game 1** of Definition 3.3: start with `(x, |Ψ⟩_{AB})`, evaluate `C` on `x` and register `A`,
obtaining the classical string `y`; output `y` and register `B`. The workspace is `C`'s
`a + m + anc` qubits followed by the `b` qubits of `B`. -/
noncomputable def game1 (C : QCirc) (b : ℕ) (Ψ : QVec (C.a + b)) (x : Str) :
    WList (Option Str × QVec ((C.a + C.m + C.anc) + b)) :=
  let ψ0 : QVec ((C.a + C.m + C.anc) + b) := fun z =>
    let zr : Fin (C.a + C.m + C.anc) → Bool := fun i => z (Fin.castAdd b i)
    let zb : Fin b → Bool := fun j => z (Fin.natAdd (C.a + C.m + C.anc) j)
    (if (∀ j : Fin C.m, zr ⟨C.a + j, by omega⟩ = x.getD j false) ∧
        (∀ j : Fin C.anc, zr ⟨C.a + C.m + j, by omega⟩ = false)
      then Ψ (Fin.append (fun i : Fin C.a => zr ⟨i, by omega⟩) zb) else 0)
  (allStrings C.meas.length).map fun y =>
    (1, some y, project C.meas y (applyGates C.gates ψ0))

/-- **Game 2** of Definition 3.3: start with `ct` and `|Ψ⟩_{AB}`; compute
`ct' ← Eval_C(· ⊗ |0⟩^{poly}, ct)` on register `A` (the device of `Eval` addresses `A` and its own
ancillas, not `B`); compute `y' = Dec(sk, ct')`; output `y'` and register `B`. -/
noncomputable def game2 (S : QFHE) (lam : ℕ) (C : QCirc) (b : ℕ) (Ψ : QVec (C.a + b))
    (sk ct : Str) :
    WList (Option Str × QVec ((C.a + S.eval.qubits (pack [unary lam, C.code, ct]).length) + b)) :=
  let e := S.eval.qubits (pack [unary lam, C.code, ct]).length
  let ψ0 : QVec ((C.a + e) + b) := fun z =>
    let zr : Fin (C.a + e) → Bool := fun i => z (Fin.castAdd b i)
    let zb : Fin b → Bool := fun j => z (Fin.natAdd (C.a + e) j)
    (if ∀ j : Fin e, zr ⟨C.a + j, by omega⟩ = false
      then Ψ (Fin.append (fun i : Fin C.a => zr ⟨i, by omega⟩) zb) else 0)
  (S.eval.exec (pack [unary lam, C.code, ct]) noEnv (C.a + e) ((C.a + e) + b) ψ0).bind fun p =>
    let ct' : Str := match p.1 with
      | .halted o => o
      | _ => []
    (S.decDist lam sk ct').map fun q => (q.1, q.2, p.2.2)

namespace QFHE

variable (S : QFHE)

/-- **Correctness with auxiliary input** (Definition 3.3), for the class of all circuits with
classical output over the gate set (QFHE): for every such circuit `C` there is a negligible `μ`
such that for every `λ`, every state `|Ψ⟩_{AB}` (with `B` any number of qubits), every input
`x ∈ {0,1}^m`, every `sk ← Gen(1^λ)` and every `ct ← Enc(sk, x)`, Games 1 and 2 have trace distance
at most `μ(λ)`. -/
def CorrectAux : Prop :=
  ∀ C : QCirc, C.WellFormed = true →
    ∃ μ : ℕ → ℝ, CompNonlocal.Negligible μ ∧
      ∀ (lam b : ℕ) (Ψ : QVec (C.a + b)), normSq Ψ = 1 →
      ∀ x : Str, x.length = C.m →
      ∀ sk : Str, (S.genDist lam).InSupport sk →
      ∀ ct : Str, (S.encDist lam sk x).InSupport ct →
        cqDistance (game1 C b Ψ x) (game2 S lam C b Ψ sk ct) ≤ μ lam

/-- The classical encryption oracle `Enc_sk(·)`: every query `x` is answered by a fresh
`Enc(sk, x)`; it sends no opening message. -/
noncomputable def encOracle (lam : ℕ) (sk : Str) : Env := fun sent =>
  match sent.getLast? with
  | none => WList.pure none
  | some x => (S.encDist lam sk x).map fun p => (p.1, some p.2)

/-- `Pr[A^{Enc_sk(·)}(ct) = 1]` for `sk ← Gen(1^λ)`, `ct ← Enc(sk, x)`; the adversary receives
`(1^λ, ct)` and outputs `1` by halting with output `[true]`. -/
noncomputable def cpaAccept (A : IntMachine) (lam : ℕ) (x : Str) : ℝ :=
  (S.genDist lam).expect fun sk =>
    (S.encDist lam sk x).expect fun ct =>
      (A.outcomes (pack [unary lam, ct]) (S.encOracle lam sk)).prob
        fun p => decide (p.1 = .halted [true])

/-- **IND-CPA security against quantum distinguishers** (Definition 3.3): for any two messages
`x₀, x₁` of equal length and any `QPT` adversary with classical access to `Enc_sk(·)`, the
distinguishing advantage is negligible. -/
def INDCPA : Prop :=
  ∀ A ∈ QPT, ∀ x₀ x₁ : Str, x₀.length = x₁.length →
    CompNonlocal.Negligible fun lam => |S.cpaAccept A lam x₀ - S.cpaAccept A lam x₁|

/-- A **post-quantum secure QFHE scheme** (Definition 3.3, Remark 3.4): efficient, correct with
auxiliary input for all circuits, and IND-CPA secure against `QPT` adversaries. -/
def IsSecureQFHE : Prop :=
  S.Efficient ∧ S.CorrectAux ∧ S.INDCPA

end QFHE

end PoQHierarchy.Main


