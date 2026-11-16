-- Prove2me | Definitions.Def_FourMsgQMA_Supplement_BaseSoundAt
-- name    : FourMsgQMA_Supplement_BaseSoundAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:25:00.407377+00:00
-- url     : https://prove2.me/theorems/3cebc6b2-267b-42d3-8b52-cf8e078dba4e
-- title:
--   Base completeness and soundness at a given resource bound $T$ (§3.4, Def 3.7)
-- statement:
--   For a four-message base protocol $\Pi_0=(\mathrm{Gen},P_1,P_2,V)$ (§3.4), the setup $\mathrm{Gen}(1^\lambda,T)$ takes a local resource bound $T$. The batch constructions of §4.2 and §5.1 run one setup for a whole batch, with $T$ a common bound on the local resources of every entry, so each entry $x$ is run at some $T\ge t_L(x)$.
--
--   1. **Statistical completeness with error $\varepsilon_0$**: for every $\lambda$, every $T$, every $x\in L_{\mathrm{yes}}$ with $t_L(x)\le T$ and every $\rho\in W_Q(x,2/3)$, the honest execution at $T$ with $N(\lambda,T)$ copies of $\rho$ accepts with probability at least $1-\varepsilon_0(\lambda)$.
--   2. **Negligible base soundness** (Definition 3.7 with $s_0=0$): for every fixed sequence $x_\lambda\in L_{\mathrm{no}}$ of polynomial length, every polynomially bounded $T_\lambda\ge t_L(x_\lambda)$ and every QPT adversary $(A_1,A_2)$, the acceptance probability is negligible.
--
--   These are the base hypotheses of Theorems 4.1 and 5.1.
--
--   **Formalization Note** The published `FourMsgQMA.BaseProtocol.Complete`/`Sound` fix $T=t_L(x)$; these are the same experiments at every admissible $T$.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.4 and Definition 3.7, p.13 (PDF 15); §5.1, p.34 (PDF 36)

import Mathlib
import Definitions.Def_FourMsgQMA_BaseProtocol
import Definitions.Def_FourMsgQMA_Supplement_HashFamily

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §3.4 and Definition 3.7 (p.13, PDF 15):
statistical completeness and base soundness of a four-message base protocol at a **given** local
resource bound `T`.

The published `FourMsgQMA.BaseProtocol.Complete` and `FourMsgQMA.BaseProtocol.Sound` fix
`T = t_L(x)`. The batch constructions of §4.2 and §5.1 run one setup `Gen(1^λ, T)` for the whole
batch, with `T` a common bound on the local resources of every entry ("Let `T` bound the local
base-protocol resources", p.34), so an entry `x` is run at a `T ≥ t_L(x)`. These two definitions are
Definition 3.7 and the completeness experiment of §3.4 for every such `T`.
-/

namespace Supplement

open QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main

/-- The acceptance probability of the honest execution on `x` at resource bound `T`, with the
resource `ρ^{⊗N(λ, T)}` on the first wires of the honest core (all other wires `|0⟩`). -/
noncomputable def baseHonestAcceptAt (B : BaseProtocol) (F : QMAFamily) (lam T : ℕ) (x : Str)
    (ρ : Matrix (Qubits (F.wit x.length)) (Qubits (F.wit x.length)) ℂ) : ℝ :=
  let S := B.core lam x
  S.acceptMixed (B.toCore lam x) (B.toVerifier lam x) (B.verifierSeq (fun _ => x) (fun _ => T)) lam
    (loadedState (fun _ : Unit => F.wit x.length) (fun _ => ρ) (List.replicate (B.copies lam T) ()) S.n)

/-- Statistical completeness with error `ε₀` at every admissible resource bound (§3.4, p.13): for
every `λ`, every `T`, every `x ∈ L_yes` with `t_L(x) ≤ T` and every `ρ ∈ W_Q(x, 2/3)`, the honest
execution at `T` accepts with probability at least `1 − ε₀(λ)`. -/
def baseCompleteAt (B : BaseProtocol) (L : PromiseProblem) (F : QMAFamily) (ε0 : ℕ → ℝ) : Prop :=
  ∀ (lam T : ℕ) (x : Str), x ∈ L.yes → localCost F x ≤ T →
    ∀ ρ ∈ WQ F x (2 / 3), 1 - ε0 lam ≤ baseHonestAcceptAt B F lam T x ρ

/-- Negligible base soundness, Definition 3.7 (p.13) with `s₀ = 0`, at every admissible resource
bound: for every polynomial bound `B'`, every sequence of fixed no-instances `x_λ ∈ L_no` with
`|x_λ| ≤ B'(λ)`, every polynomially bounded sequence `T_λ ≥ t_L(x_λ)` and every QPT adversary
`(A₁, A₂)`, the acceptance probability is negligible. -/
def baseSoundAt (B : BaseProtocol) (L : PromiseProblem) (F : QMAFamily) : Prop :=
  ∀ B' : ℕ → ℕ, PolyBound B' → ∀ x : ℕ → Str, (∀ lam, x lam ∈ L.no ∧ (x lam).length ≤ B' lam) →
    ∀ T : ℕ → ℕ, PolyBound T → (∀ lam, localCost F (x lam) ≤ T lam) →
    ∀ Adv : ℕ → Strategy, IsQPT Adv →
      Negligible fun lam => (Adv lam).acceptProb (B.verifierSeq x T) lam

end Supplement

end FourMsgQMA


