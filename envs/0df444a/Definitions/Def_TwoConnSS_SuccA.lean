-- Prove2me | Definitions.Def_TwoConnSS_SuccA
-- name    : TwoConnSS_SuccA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:48:15.424027+00:00
-- url     : https://prove2.me/theorems/1073e442-feec-4235-b81a-868213f608a4
-- title:
--   Successful exchanges of Algorithm A
-- statement:
--   Let $S_0$ be the initial cover. A step from $(S, M)$ to $(S', M')$ is a **successful exchange of Algorithm A** if:
--
--   1. $(S', M')$ is a canonical weak 2-edge-cover for Algorithm A;
--   2. every 4-cycle component of $S'$ is primitive;
--   3. every 2EC block of $S$ lies inside a 2EC block of $S'$ (block preservation);
--   4. $\mathrm{cost}_A(S', M') \le \mathrm{cost}_A(S, M)$;
--   5. the potential $\phi_A = (-W_A, \mathrm{br})$, with $W_A(S) = \sum_{B} |V(B)|^2$ over the 2EC blocks, strictly decreases lexicographically: $W_A(S') > W_A(S)$, or $W_A(S') = W_A(S)$ and $\mathrm{br}(S') < \mathrm{br}(S)$.
--
--   Algorithm A is a sequence of such exchanges, which is why its running time is polynomial.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §8.1.2, pp.38–39, display (13)

import Mathlib
import Definitions.Def_TwoConnSS_costA
import Definitions.Def_TwoConnSS_Primitive

namespace TwoConnSS

variable {V : Type*} [Fintype V]

/-- `W_A(S) = Σ_{B ∈ B(S)} |V(B)|²` (p.39). -/
noncomputable def WA (S : Finset (Sym2 V)) : ℕ :=
  ∑ B ∈ blocks S, B.card ^ 2

/-- `ϕ_A(S') < ϕ_A(S)` for `ϕ_A = (−W_A, br)` in lexicographic order, i.e. display (13), p.39:
`W_A(S') > W_A(S)` or (`W_A(S') = W_A(S)` and `br(S') < br(S)`). -/
def LexA (S S' : Finset (Sym2 V)) : Prop :=
  WA S < WA S' ∨ (WA S' = WA S ∧ br S' < br S)

/-- **A successful exchange of Algorithm A** from `(S, M)` to `(S', M')`.
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), p.39: "For r ∈ {A, B}, a successful
exchange produces a canonical cover for Algorithm r, satisfies the preservation requirements above,
and obeys costr(S′) ≤ costr(S), ϕr(S′) < ϕr(S). The notation includes the updated pairing in
Algorithm A." The preservation requirements (p.38): every 4-cycle component remains primitive, and
"For Algorithm A, each B ∈ B(S) must satisfy V(B) ⊆ V(B′) for some B′ ∈ B(S′)."

`SuccA G S₀ (S, M) (S', M')` bundles the five conditions: `(S', M')` canonical for A, every 4-cycle
component of `S'` primitive (relative to `S₀`), every block of `S` inside a block of `S'`,
`cost_A(S', M') ≤ cost_A(S, M)`, and `ϕ_A(S') < ϕ_A(S)`. Also defined here: `W_A` and the
lexicographic decrease `LexA`.

**Formalization Note.** Every `S' ⊆ E(G)` is an exchange `(S \ F⁻) ∪ F⁺` of `S` (p.27), so no
separate exchange clause is needed. -/
def SuccA (G : SimpleGraph V) (S₀ : Finset (Sym2 V))
    (p p' : Finset (Sym2 V) × Finset (Sym2 V)) : Prop :=
  IsCanonA G p'.1 p'.2 ∧ Primitive S₀ p'.1 ∧
  (∀ B ∈ blocks p.1, ∃ B' ∈ blocks p'.1, B ⊆ B') ∧
  costA p'.1 p'.2 ≤ costA p.1 p.2 ∧ LexA p.1 p'.1

end TwoConnSS


