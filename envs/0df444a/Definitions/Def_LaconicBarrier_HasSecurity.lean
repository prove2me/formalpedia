-- Prove2me | Definitions.Def_LaconicBarrier_HasSecurity
-- name    : LaconicBarrier_HasSecurity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:44:02.865744+00:00
-- url     : https://prove2.me/theorems/b5a56e67-cbdf-493b-936c-5dd71ece76fa
-- title:
--   $\Gamma$-security of a game
-- statement:
--   A game $(\mathcal C, c)$ has **$\Gamma$-security** if no non-uniform family $\{A_\lambda\}$ of adversary circuits with $|A_\lambda| \le \Gamma(\lambda)$ $\Gamma$-breaks it: for every such family the advantage $\lambda \mapsto \mathrm{Adv}_{(\mathcal C,c)}(A_\lambda;\lambda)$ does not exceed $1/p(\Gamma(\lambda))$ infinitely often, for any polynomial $p$.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.2, p.15

import Mathlib
import Definitions.Def_LaconicBarrier_Game_advCirc
import Definitions.Def_LaconicBarrier_Breaks

namespace LaconicBarrier

/-- **Γ-security** (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256 1af78662…),
Definition 4.2, p.15): no non-uniform adversary family `{A_λ}` of circuits with `|A_λ| ≤ Γ(λ)`
Γ-breaks the game `(C, c)`. -/
def HasSecurity (G : Game) (Γ : ℕ → ℕ) : Prop :=
  ∀ A : ℕ → Σ n, MCircuit n, (∀ lam, (A lam).2.size ≤ Γ lam) →
    ¬ Breaks Γ (fun lam => G.advCirc lam (A lam))

end LaconicBarrier


