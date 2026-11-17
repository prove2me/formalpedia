-- Prove2me | Definitions.Def_NoisyOWMPC_Supplement_MalOWSC
-- name    : NoisyOWMPC_Supplement_MalOWSC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:01:53.133201+00:00
-- url     : https://prove2.me/theorems/27d6786b-c84d-4f37-930f-ef5630af8e2d
-- title:
--   Malicious one-way secure computation (Definition E.1)
-- statement:
--   Let $C : \mathcal X \to \mathcal Y$ be a channel, $f : \mathcal M \times \{0,1\}^q \to \mathcal O$ a randomized functionality given by a public target circuit, and $\Pi = (S, R)$ a one-receiver protocol for $f$ over $C$ in the syntax of Definition 4.2, with public-message length $L$ and $N_\Pi$ channel uses. Extend $f$ by $f(\mathsf{fail}; \rho) = \mathsf{fail}$.
--
--   $\Pi$ has **security error $\varepsilon$ against a malicious sender** if there is a PPT simulator $\mathrm{Sim}_S(1^\lambda, \tau, \hat x) \to x' \in \mathcal M \cup \{\mathsf{fail}\}$ such that for every $\tau \in \{0,1\}^L$ and every $\hat x \in \mathcal X^{N_\Pi}$,
--   $$
--   f\big(\mathrm{Sim}_S(1^\lambda, \tau, \hat x); \rho\big) \;\approx^c_{\varepsilon}\; R\big(1^\lambda, \tau, C^{N_\Pi}(\hat x)\big),
--   $$
--   where $\rho \leftarrow \{0,1\}^q$ is fresh and independent of the simulator's coins. $\Pi$ is a **malicious one-way secure computation with errors $(\varepsilon_{\mathrm{cor}}, \varepsilon_{\mathrm{sec}})$** if it has correctness error $\varepsilon_{\mathrm{cor}}$, security error $\varepsilon_{\mathrm{sec}}$ for the semi-honest coalitions $\{S\}$ and $\{1\}$ of Definition 4.2, and security error $\varepsilon_{\mathrm{sec}}$ against a malicious sender.
--
--   This is the security notion of Theorems E.9 and E.10.
--
--   **Formalization Note** The simulator's output string $1x$ encodes the input $x$, and every other string encodes $\mathsf{fail}$; the simulator decides before $\rho$ is sampled. The negligible term of $\approx^c$ is uniform over $(\tau, \hat x)$.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Definition E.1, pp.60–61

import Mathlib
import Definitions.Def_NoisyOWMPC_SecErr
import Definitions.Def_NoisyOWMPC_Supplement_Verifiable
import Definitions.Def_NoisyOWMPC_Supplement_WiretapScheme

namespace NoisyOWMPC.Supplement

open LaconicBarrier

/-- The simulator's choice `x′ ∈ M ∪ {fail}` read off its output string (Ishai, Lu, Zafar, STOC 2027
submission (manuscript sha256 3a9569fa…), Definition E.1, p.60: "`Sim_S(1^λ, τ, x̂) → x′ ∈ M ∪
{fail}`"): `1x` with `x ∈ {0,1}^n` is the input `x`; every other string is `fail` (`none`). -/
def decodeIn (n : ℕ) : List Bool → Option (Fin n → Bool)
  | true :: v => if v.length = n then some (fun j => v.getD j.val false) else none
  | _ => none

variable {X Yc : Type} [Fintype X] [Fintype Yc] {F : Functionality 1}

/-- **Security against a malicious sender with error `ε`** (Definition E.1, (E.1), p.60): there is a
PPT simulator `Sim_S(1^λ, τ, x̂) → x′ ∈ M ∪ {fail}` such that for every `τ ∈ {0,1}^L` and
`x̂ ∈ X^{N_Π}`, `f(Sim_S(1^λ, τ, x̂); ρ) ≈^c_ε R(1^λ, τ, C^{N_Π}(x̂))`, where `ρ ← {0,1}^q` is fresh
and independent of the simulator's coins, `f(fail; ρ) = fail`.

**Formalization Note** The simulator's choice is made from its own coins before `ρ` is used; the
negligible term of `≈^c` is chosen before `λ`, `τ` and `x̂` (p.61: "The distinguishing bounds are
uniform over the prescribed inputs"). Outputs in `O ∪ {fail}` are compared by their encoding
`optEnc`. -/
def MalSenderErr (P : Protocol 1 X (oneY Yc) F) (C : DMC X Yc) (ε : ℕ → ℝ) : Prop :=
  ∃ Sim : CoinAlg, Sim.IsPPT ∧
    CompClose (I := fun lam => (Fin (P.L lam) → Bool) × (Fin (P.N lam) → X))
      (fun lam _ => unifW ((Fin (Sim.coins lam) → Bool) × (Fin (F.r 0 lam) → Bool)))
      (fun lam q ω => optEnc ((decodeIn (F.lx lam)
        (Sim.run lam (QAdvFew.PoQOracle.tup [bits q.1, wordEnc X q.2]) ω.1)).map
          (fun x' => F.f lam 0 x' ω.2)))
      (fun lam q (y : Fin (P.N lam) → Yc) => chanW C q.2 y)
      (fun lam q y => optEnc (P.recv lam 0 q.1 y)) ε

/-- **Malicious one-way secure computation with errors `(ε_cor, ε_sec)`** (Definition E.1, p.60):
correctness error `ε_cor` and security error `ε_sec` for the semi-honest coalitions `{S}` and `{1}`
of Definition 4.2 (published `CorrErr`, `SecErr` with `k = 1`), and security error `ε_sec` against
a malicious sender. -/
def IsMalOWSC (P : Protocol 1 X (oneY Yc) F) (C : DMC X Yc) (εcor εsec : ℕ → ℝ) : Prop :=
  P.CorrErr (oneC C) εcor ∧ P.SecErr (oneC C) true ∅ εsec ∧
    P.SecErr (oneC C) false Finset.univ εsec ∧ MalSenderErr P C εsec

end NoisyOWMPC.Supplement


