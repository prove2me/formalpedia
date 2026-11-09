-- Prove2me | Definitions.Def_NoisyOWMPC_Distinguisher
-- name    : NoisyOWMPC_Distinguisher
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:43:00.742614+00:00
-- url     : https://prove2.me/theorems/71b47fe9-c466-48b1-98b2-48a114a21318
-- title:
--   Nonuniform distinguishers as polynomial-size circuit families
-- statement:
--   A **nonuniform distinguisher** $\mathcal A$ is a family of Boolean circuits $A_\lambda$, one for every security parameter; it has **polynomial size** if the number of inputs and of gates of $A_\lambda$ is at most $(\lambda+2)^c$. The bit $\mathcal A(1^\lambda,u)$ is the value of $A_\lambda$ on the string $u$, and $\Pr[\mathcal A(1^\lambda,U)=1]$ is computed in a finite experiment.
--
--   These are the paper's "nonuniform PPT distinguishers" in $\approx^c$, in the indistinguishability of iO, and in the hard-core bit property.
--
--   **Formalization Note** A string is fed as $u10\cdots0$ cut or padded to the circuit's input length. A randomized nonuniform distinguisher is matched by the circuit with its best coins hard-wired, so bounds over this class are the paper's bounds.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), §3 Notation and conventions, p.15

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit_eval
import Definitions.Def_LaconicBarrier_MCircuit
import Definitions.Def_NoisyOWMPC_wprob

namespace NoisyOWMPC

open KarpLiptonOM

/-- A **nonuniform distinguisher** (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256
3a9569fa…), §3, p.15: "adversaries and distinguishers may be nonuniform"): one Boolean circuit
`A_λ` with `inLen λ` inputs for every security parameter `λ`, built on the published
`KarpLiptonOM.Circuit` model.

**Formalization Note** A string `u` is fed to `A_λ` as `u10⋯0` cut or padded to `inLen λ` bits
(the published `LaconicBarrier.padIn`). Distinguishers are deterministic circuits: a randomized
nonuniform distinguisher is matched by the circuit with its best coins hard-wired, uniformly over
the finitely many inputs at each `λ`, so the bounds quantified over this class are those of the
paper's class. -/
structure Distinguisher where
  /-- the number of input wires of `A_λ` -/
  inLen : ℕ → ℕ
  /-- the circuit `A_λ` -/
  circ : (lam : ℕ) → Circuit (inLen lam)

/-- The distinguisher has **polynomial size**: input length and gate count at most `(λ + 2)^c`
(§3, p.15: "nonuniform PPT distinguisher"). -/
def Distinguisher.IsPoly (A : Distinguisher) : Prop :=
  ∃ c : ℕ, ∀ lam, A.inLen lam ≤ (lam + 2) ^ c ∧ (A.circ lam).gates.length ≤ (lam + 2) ^ c

/-- The bit `A(1^λ, u)` output by the distinguisher on the string `u`. -/
def Distinguisher.acc (A : Distinguisher) (lam : ℕ) (u : List Bool) : Bool :=
  (A.circ lam).eval (LaconicBarrier.padIn (A.inLen lam) u)

/-- `Pr[A(1^λ, U) = 1]` for the finite experiment with weights `w` and outcome string `u`. -/
noncomputable def Distinguisher.accProb (A : Distinguisher) (lam : ℕ) {Ω : Type} [Fintype Ω]
    (w : Ω → ℝ) (u : Ω → List Bool) : ℝ :=
  wprob w (fun ω => A.acc lam (u ω) = true)

end NoisyOWMPC


