-- Prove2me | Definitions.Def_QuantumPRC_Supplement_CodeRec
-- name    : QuantumPRC_Supplement_CodeRec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:36:55.870486+00:00
-- url     : https://prove2.me/theorems/a5f44360-a955-4a7e-8057-330cd31ee752
-- title:
--   The codeword-recognition game and hardness of recognizing codewords (Definitions 9.2, 9.7)
-- statement:
--   Let $(\mathrm{KeyGen},\mathrm{Enc},\mathrm{Dec})$ be a keyed code from $n_L$ to $n_P$ qubits and let $t\ge1$. In the **codeword-recognition game** $\mathrm{CodeRec}^{(t)}$ (Definition 9.2) the challenger samples $\mathsf{sk}\leftarrow\mathrm{KeyGen}(1^\lambda)$ and a bit $b$. If $b=0$ it picks one $x\leftarrow\{0,1\}^{n_L}$ and sends $\mathrm{Enc}_{\mathsf{sk}}(|x\rangle\langle x|)^{\otimes t}$; if $b=1$ it sends $|\psi\rangle\langle\psi|^{\otimes t}$ for a Haar-random $n_P$-qubit pure state $|\psi\rangle$ independent of the key. The learner then gets quantum oracle access to $\mathrm{Enc}_{\mathsf{sk}}$ and outputs $b'$; it wins if $b'=b$. So
--
--   $$
--   \Pr[\mathcal A\text{ wins}]=\tfrac12\Pr[b'=0\mid b=0]+\tfrac12\Pr[b'=1\mid b=1].
--   $$
--
--   The keyed code has **hardness of recognizing codewords** (Definition 9.7) if for every polynomial $t\ge1$ and every uniform QPT learner $\mathcal A$ there is a negligible $\nu$ with $\Pr[\mathcal A\text{ wins}]\le\tfrac12+\nu(\lambda)$ for all $\lambda$.
--
--   **Formalization Note** The learner is a uniform family of oracle circuits (the base mission's model); it starts with the challenge on its first $t(\lambda)\,n_P(\lambda)$ wires and $|0\rangle$ elsewhere (a circuit with fewer wires outputs $b'=0$), and $b'$ is the measurement of wire $0$. The Haar state is $U|0^{n_P}\rangle$ with $U$ Haar-distributed on $U(2^{n_P})$. "No learner wins with probability at least $\tfrac12+1/\mathrm{poly}(\lambda)$" is read as negligible advantage.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Definitions 9.1, 9.2, p.65; Definition 9.7, p.67

import Mathlib
import Definitions.Def_QuantumPRC_ChScheme

open Matrix MeasureTheory

namespace QuantumPRC.Supplement

/-- The `t`-fold tensor power `M^{⊗t}` of an operator on `n` qubits, an operator on `t·n` qubits;
copy `i` occupies the wires `n·i, …, n·i + n − 1` (`finProdFinEquiv`). -/
def tensorPow {n : ℕ} (t : ℕ) (M : Matrix (Bits n) (Bits n) ℂ) :
    Matrix (Bits (t * n)) (Bits (t * n)) ℂ :=
  fun x x' => ∏ i : Fin t, M (fun j => x (finProdFinEquiv (i, j))) (fun j => x' (finProdFinEquiv (i, j)))

/-- The Haar-random pure state `|ψ⟩⟨ψ|` with `|ψ⟩ = U|0^{nP}⟩`, `U` Haar-random on `U(2^{nP})`
(`haarIsoMat 0 nP U` is the isometry from `0` qubits, i.e. the vector `U|0^{nP}⟩`). -/
def haarState (nP : ℕ) (U : Matrix.unitaryGroup (Fin (2 ^ nP)) ℂ) : Matrix (Bits nP) (Bits nP) ℂ :=
  conjMap (haarIsoMat 0 nP U) 1

/-- **Acceptance probability of an oracle circuit started on a quantum state.** The circuit starts
from `σ ⊗ |0⟩⟨0|`, with `σ` (an operator on `K` qubits) on the first `K` wires and `|0⟩` on all other
wires, applies its instructions with the oracles `O`, and measures wire `0`; the result is the
probability of outcome `1`. A circuit with fewer than `K` wires cannot receive the state and outputs
`0` (probability `0` of outcome `1`). This extends `QuantumPRC.OCirc.accept`, which starts from a
classical basis input. -/
noncomputable def acceptFrom {nIn nOut k K : ℕ} (A : OCirc nIn nOut k)
    (O : Fin k → Superop (Bits nIn) (Bits nOut)) (σ : Matrix (Bits K) (Bits K) ℂ) : ℝ := by
  classical
  exact
    if h : K ≤ A.N then
      let ρ0 : Matrix (Bits A.N) (Bits A.N) ℂ := fun x x' =>
        if (∀ i : Fin A.N, K ≤ i.val → x i = false ∧ x' i = false) then
          σ (fun j => x ⟨j.val, lt_of_lt_of_le j.isLt h⟩) (fun j => x' ⟨j.val, lt_of_lt_of_le j.isLt h⟩)
        else 0
      let ρ := A.instrs.foldl (fun σ ins => ins.apply O σ) ρ0
      (∑ x : Bits A.N, if (∃ h : 0 < A.N, x ⟨0, h⟩ = true) then ρ x x else 0).re
    else 0

variable {nL nP : ℕ → ℕ}

/-- **Winning probability in the codeword-recognition game `CodeRec^{(t)}_D`**, Definition 9.2.
Hsieh, Yamada, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d…), p.65: "1. `C` chooses
`W ← D`. 2. The challenger `C` chooses `b ← {0,1}`. If `b = 0`, `C` chooses one `x ← {0,1}^{nL}` and
sends `W(|x⟩⟨x|)^{⊗t}` to `A`. If `b = 1`, `C` samples a Haar-random `nP`-qubit pure state `|ψ⟩`
independently of `W` and sends `|ψ⟩⟨ψ|^{⊗t}` to `A`. 3. After receiving the challenge, `A` receives
oracle access to `W` and may make adaptive quantum queries to `W` on arbitrary inputs to output
`b′ ∈ {0,1}`. `A` wins if and only if `b = b′`." Here `D` outputs `Enc_sk` for `sk ← KeyGen(1^λ)`
(Definition 9.7, p.67), with the scheme run at parameter `W λ`.

`Pr[A wins] = ½ Pr[b′ = 0 | b = 0] + ½ Pr[b′ = 1 | b = 1]`; `b′` is the measured wire `0`.

**Formalization Note.** The learner is an oracle circuit with one oracle from `nL(λ)` to `nP(λ)`
qubits (adaptive, possibly entangled quantum queries); the challenge occupies its first `t(λ)·nP(λ)`
wires. In the case `b = 1` the oracle is `Enc_sk` for a key independent of the Haar state; the Haar
state is `U|0^{nP}⟩` under `QAlgorithms.Schur.unitaryHaar`. The integrand is a polynomial in the
entries of `U` and `Ū`, so the Bochner integral is the true expectation. -/
noncomputable def codeRecWin (S : ChScheme nL nP) (W t : ℕ → ℕ)
    (A : ∀ lam, OCirc (nL lam) (nP lam) 1) (lam : ℕ) : ℝ :=
  let enc : Bits (S.kc lam) → Superop (Bits (nL lam)) (Bits (nP lam)) :=
    fun r => S.enc lam (W lam) (S.keyGen lam (W lam) r)
  let p0 : ℝ := avg fun r : Bits (S.kc lam) => avg fun x : Bits (nL lam) =>
    acceptFrom (A lam) (fun _ => enc r) (tensorPow (t lam) (enc r (Matrix.single x x 1)))
  let p1 : ℝ := avg fun r : Bits (S.kc lam) =>
    ∫ U, acceptFrom (A lam) (fun _ => enc r) (tensorPow (t lam) (haarState (nP lam) U))
      ∂(QAlgorithms.Schur.unitaryHaar (2 ^ nP lam))
  (1 / 2 : ℝ) * (1 - p0) + (1 / 2 : ℝ) * p1

/-- **Hardness of recognizing codewords**, Definition 9.7, p.67: "a keyed-QECC satisfies the hardness
of recognizing codewords if, for any polynomial `t = t(λ)`, no QPT learner can win `CodeRec^{(t)}_D`
with probability at least `1/2 + 1/poly(λ)`, where `D` is the distribution that outputs `Enc_sk` under
`sk ← KeyGen(1^λ)`."

**Formalization Note.** "Cannot win with probability at least `1/2 + 1/poly(λ)`" is read as the
standard negligible advantage: for every polynomial `t ≥ 1` (`EffPoly`; Definition 9.2 requires
`t ≥ 1`) and every uniform learner there is a negligible `ν` with `Pr[A wins] ≤ 1/2 + ν(λ)` for all `λ`
(`∃ negl` after `t` and `A`). The scheme is run at the parameter sequence `W`. -/
def HardToRecognize (S : ChScheme nL nP) (W : ℕ → ℕ) : Prop :=
  ∀ t : ℕ → ℕ, EffPoly t → (∀ lam, 1 ≤ t lam) →
    ∀ A : ∀ lam, OCirc (nL lam) (nP lam) 1, IsUniformAdv A →
      ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam, codeRecWin S W t A lam ≤ 1 / 2 + ν lam

end QuantumPRC.Supplement


