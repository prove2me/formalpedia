-- Prove2me | Definitions.Def_QFairEx_PerfectlySecure
-- name    : QFairEx_PerfectlySecure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:24:42.788203+00:00
-- url     : https://prove2.me/theorems/539b8b3f-6b5d-4643-b097-f2816c3012c8
-- title:
--   Perfect security against pre-determined fail-stop adversaries (Definition 4.3)
-- statement:
--   Let $S_0\le\mathbb C^{\iota_0}$ and $S_1\le\mathbb C^{\iota_1}$ be the accepting subspaces. A protocol is **perfectly secure against fail-stop adversaries** for $(S_0,S_1)$ if for all valid pure inputs, i.e. unit vectors $\psi_0\in S_0$, $\psi_1\in S_1$:
--
--   1. **completeness**: in the honest execution, $\Pr[d_0=d_1=\mathrm{acc}]=1$;
--   2. for every cut $t\in\{0,\dots,T\}$ and every $b\in\{0,1\}$, in the execution where the adversary controls $P_{1-b}$ with cut $t$:
--      - **valid-state preservation**: $P_b$'s output conditioned on acceptance is supported on $S_{1-b}$, and conditioned on rejection on $S_b$;
--      - **exact-state resilience**: with probability $1$, $P_b$ either rejects and outputs $|\psi_b\rangle$ or accepts and outputs $|\psi_{1-b}\rangle$, i.e.
--      $$\sigma^{(b)}_{\mathrm{rej}}=\Pr[f_b=\mathrm{rej}]\,|\psi_b\rangle\langle\psi_b|,\qquad \sigma^{(b)}_{\mathrm{acc}}=\Pr[f_b=\mathrm{acc}]\,|\psi_{1-b}\rangle\langle\psi_{1-b}|.$$
--
--   Theorem 4.8 shows that no protocol with a classical trusted party satisfies this when both accepting subspaces have dimension at least two.
--
--   **Formalization Note** Both error bounds are zero, so no security parameter or negligible function appears, and the pair $(S_0,S_1)$ is fixed; $\mathrm{Ver}_b$ enters only through $S_b$. Outputs are subnormalized and conditioned on the decision only; nothing is divided by a possibly zero probability. For pure targets this is equivalent to conditioning on all measurement outcomes.
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), Definition 4.3, p.20

import Mathlib
import Definitions.Def_QFairEx_SupportedOn
import Definitions.Def_QFairEx_Protocol
import Definitions.Def_QFairEx_Protocol_honestState
import Definitions.Def_QFairEx_Protocol_stopAcc0

namespace QFairEx

open Matrix

/-- **Perfect security against pre-determined fail-stop adversaries** (Definition 4.3).
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), Definition 4.3, p.20.

For accepting subspaces `S0 ≤ ℂ^{ι0}`, `S1 ≤ ℂ^{ι1}`, `PerfectlySecure P S0 S1` says: for all
valid pure inputs, i.e. unit vectors `ψ0 ∈ S0`, `ψ1 ∈ S1`, with `X = |ψ₀⟩⟨ψ₀| ⊗ |ψ₁⟩⟨ψ₁|`,
1. *(completeness)* in the honest execution `Pr[d₀ = d₁ = acc] = 1`;
2. for every cut `t ∈ {0, …, T}` and the honest party `P_b` against the fail-stop adversary
   controlling `P_{1−b}` with cut `t` (the execution Stop(b, t)):
   * *(valid-state preservation)* the output conditioned on `acc` is supported on `S_{1−b}` and
     the one conditioned on `rej` on `S_b`;
   * *(exact-state resilience)* the output conditioned on `rej` is `Pr[rej] · |ψ_b⟩⟨ψ_b|` and
     the one conditioned on `acc` is `Pr[acc] · |ψ_{1−b}⟩⟨ψ_{1−b}|`.

**Formalization Note.**
1. Perfect security takes both error bounds of Definition 4.3 to be zero, so no security
   parameter or negligible function appears; the pair `(S0, S1)` is fixed (the singleton
   family of verifier pairs).
2. `Ver_b` enters only through its accepting subspace `S_b`.
3. Conditional outputs are subnormalized: `stopAcc0 X t` has trace `Pr[f₀ = acc]`, so "with
   probability 1, outputs `|ψ⟩` on acceptance" is `σ_acc = tr(σ_acc) · |ψ⟩⟨ψ|`; nothing is
   divided by a possibly zero probability. Outputs are conditioned on the decision only (all
   other classical records summed); for a pure target this is equivalent to conditioning on all
   measurement outcomes.
4. Only fixed cuts are quantified (a random cut is a mixture of fixed cuts). -/
def PerfectlySecure {ι0 ι1 : Type} [Fintype ι0] [Fintype ι1] [DecidableEq ι0] [DecidableEq ι1]
    (P : Protocol ι0 ι1) (S0 : Submodule ℂ (ι0 → ℂ)) (S1 : Submodule ℂ (ι1 → ℂ)) : Prop :=
  ∀ ψ0 : ι0 → ℂ, ∀ ψ1 : ι1 → ℂ, ψ0 ∈ S0 → IsUnitVec ψ0 → ψ1 ∈ S1 → IsUnitVec ψ1 →
    P.honestAccAcc (pureDensity (prodVec ψ0 ψ1)) = 1 ∧
    ∀ t : ℕ, t ≤ P.T →
      -- honest P₀, adversary controls P₁
      SupportedOn S1 (P.stopAcc0 (pureDensity (prodVec ψ0 ψ1)) t) ∧
      SupportedOn S0 (P.stopRej0 (pureDensity (prodVec ψ0 ψ1)) t) ∧
      P.stopAcc0 (pureDensity (prodVec ψ0 ψ1)) t =
        (P.stopAcc0 (pureDensity (prodVec ψ0 ψ1)) t).trace • pureDensity ψ1 ∧
      P.stopRej0 (pureDensity (prodVec ψ0 ψ1)) t =
        (P.stopRej0 (pureDensity (prodVec ψ0 ψ1)) t).trace • pureDensity ψ0 ∧
      -- honest P₁, adversary controls P₀
      SupportedOn S0 (P.stopAcc1 (pureDensity (prodVec ψ0 ψ1)) t) ∧
      SupportedOn S1 (P.stopRej1 (pureDensity (prodVec ψ0 ψ1)) t) ∧
      P.stopAcc1 (pureDensity (prodVec ψ0 ψ1)) t =
        (P.stopAcc1 (pureDensity (prodVec ψ0 ψ1)) t).trace • pureDensity ψ0 ∧
      P.stopRej1 (pureDensity (prodVec ψ0 ψ1)) t =
        (P.stopRej1 (pureDensity (prodVec ψ0 ψ1)) t).trace • pureDensity ψ1

end QFairEx


