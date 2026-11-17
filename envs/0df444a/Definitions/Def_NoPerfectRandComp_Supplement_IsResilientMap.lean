-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_IsResilientMap
-- name    : NoPerfectRandComp_Supplement_IsResilientMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:06:29.011128+00:00
-- url     : https://prove2.me/theorems/f1264cd1-9f9a-40d3-868a-d220cc254cee
-- title:
--   Surjective $t$-resilient cell map $\phi:\{0,1\}^C\to\Gamma$
-- statement:
--   A map $\phi : \{0,1\}^C \to \Gamma$ from $C$-bit strings onto an alphabet $\Gamma$ is a **surjective $t$-resilient map** when it is onto and any $t$ of the encoding bits of a cell are uniform and independent of the symbol: for every symbol $\gamma \in \Gamma$, every set $J$ of at most $t$ bit positions and every pattern $\rho \in \{0,1\}^J$,
--   $$
--   2^{|J|}\cdot\#\{y : \phi(y) = \gamma,\ y|_J = \rho\} \;=\; \#\{y : \phi(y) = \gamma\}.
--   $$
--   That is, under the uniform distribution on each fibre $\phi^{-1}(\gamma)$, the bits in $J$ are uniform.
--
--   Blais and Brody encode each pointer-cell symbol by a $\lfloor C_q/3\rfloor$-resilient map with $C_q = \Theta(q\log q)$; the theorems of this supplement take such a map as a parameter.
--
--   **Formalization Note** Surjectivity is part of the definition (the map encodes every symbol). Admissible maps exist for the pointer alphabet: decoding through a private linear map of the base mission's Lemma 4.5 with payload $a \ge \log_2|\Gamma|$ and $C = 36a$ gives a $12a = C/3$-resilient map.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §2.6, p.7

import Mathlib

namespace NoPerfectRandComp

namespace Supplement

open Classical in
/-- A surjective `t`-resilient cell map (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.6, p.7):
`ϕ : {0,1}^C → Γ` is onto, and "any `t` of the encoding bits of a cell are uniform and
independent of the symbol". That is, for every symbol `γ`, every set `J` of at most `t` bit
positions and every pattern `ρ ∈ {0,1}^J`, the uniform distribution on the fibre `ϕ⁻¹(γ)` gives
`ρ` probability `2^{-|J|}`:
`2^{|J|} · #{y : ϕ(y) = γ, y|_J = ρ} = #{y : ϕ(y) = γ}`.

The paper's block uses `t = ⌊C/3⌋` (a "`C_q/3`-resilient map").

**Formalization Note** Resilience is a property of the uniform distribution on each fibre, stated
as the count identity above; surjectivity is part of the definition because `ϕ` encodes every
symbol of the alphabet. Admissible maps exist for the pointer alphabet with `C = Θ(q log q)`:
decoding through a private linear map of the published Lemma 4.5 (`NoPerfectRandComp.lemma_4_5`,
`9f96dbba-…`) with payload `a ≥ log₂ |Γ|` and `C = 36a` gives a `12a = C/3`-resilient map. -/
def IsResilientMap {Γ : Type} {C : ℕ} (t : ℕ) (ϕ : (Fin C → Bool) → Γ) : Prop :=
  Function.Surjective ϕ ∧
  ∀ (γ : Γ) (J : Finset (Fin C)), J.card ≤ t → ∀ ρ : J → Bool,
    2 ^ J.card * (Finset.univ.filter (fun y => ϕ y = γ ∧ ∀ j : J, y j = ρ j)).card =
      (Finset.univ.filter (fun y => ϕ y = γ)).card

end Supplement

end NoPerfectRandComp


