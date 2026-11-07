-- Prove2me | Definitions.Def_ReplParity_IsRealizablyPAC
-- name    : ReplParity_IsRealizablyPAC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:39.821124+00:00
-- url     : https://prove2.me/theorems/049788c2-5a75-408a-a7be-2ec4714f1b53
-- title:
--   Definition 2.2 — realizably $(\varepsilon,\delta)$-PAC
-- statement:
--   Let $H$ be a class of functions $X\to\{0,1\}$. A learner, which outputs a hypothesis or the symbol $\bot$, is **realizably $(\varepsilon,\delta)$-PAC for $H$** if for every labeled distribution $D$ such that $\mathrm{err}_D(h^\star)=0$ for some $h^\star\in H$,
--   $$\Pr_{S\sim D^m,\,r}\big[A(S;r)=\bot\ \text{ or }\ \mathrm{err}_D(A(S;r))>\varepsilon\big]\le\delta .$$
--
--   **Formalization Note** The output $\bot$ is `none` and a hypothesis $h$ is `some h`; the domain is finite and the seed uniform on a finite set.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), Definition 2.2, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_ReplParity_prIID
import Definitions.Def_ReplParity_err

namespace ReplParity

/-- **Realizably (ε, δ)-PAC (Definition 2.2).** Shen, Zhong, *Replicable Parity Learning: Cubic
Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript sha256
40424491…), Definition 2.2, p.11 (PDF p.13): "Let H be a class of functions X → {0, 1}. A learner
is realizably (ε, δ)-PAC for H if for every labeled distribution D such that err_D(h⋆) = 0 for some
h⋆ ∈ H, Pr_{S∼D^m, r}[A(S; r) = ⊥ or err_D(A(S; r)) > ε] ≤ δ."

The learner returns `none` for `⊥` and `some h` for a hypothesis `h`.

**Formalization Note.** `X` is finite, labels are `ZMod 2`, the seed is uniform on `Ω`. -/
def IsRealizablyPAC {X Ω : Type*} [Fintype X] [Fintype Ω] (H : Set (X → ZMod 2)) {m : ℕ}
    (A : (Fin m → X × ZMod 2) → Ω → Option (X → ZMod 2)) (ε δ : ℝ) : Prop :=
  ∀ D : PMF (X × ZMod 2), (∃ h ∈ H, err D h = 0) →
    prIID D m (fun S r => A S r = none ∨ ∃ h, A S r = some h ∧ ε < err D h) ≤ δ

end ReplParity


