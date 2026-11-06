-- Prove2me | Definitions.Def_NondualOpt_Assumption3
-- name    : NondualOpt_Assumption3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:02:33.720646+00:00
-- url     : https://prove2.me/theorems/0b3586d1-9314-4a83-8cc4-eac2681e19b8
-- title:
--   Assumption 3: the minimax interchange ① for the max-regret game
-- statement:
--   Let $X\subseteq E$, $H\subseteq F$ with a bilinear pairing, and $T\in\mathbb N$. **Assumption 3** holds if
--
--   1. $X$ and $H$ are nonempty and convex;
--   2. $H=-H$;
--   3. $\Lambda_{X,H}<\infty$;
--   4. the minimax interchange ① holds: $V^{\max}_{X,H,T}$ equals the value of the randomized game in which the adversary announces laws $r_t$ on the affine losses before the player picks laws $s_t$ on $X$.
--
--   Under this assumption the max-regret game can be analyzed through the randomized, minimax-swapped game (Proposition 4, Theorem 6).
--
--   **Formalization Note** (i) The pairing is abstract ($F$ in place of $E^*$), so "$H$ bounded" is replaced by $\Lambda_{X,H}<\infty$, which is all the proofs use. (ii) The laws of ① are finitely supported (footnote 6); for such laws the measurable $\eta$-minimizer clause is automatic and is not stated. (iii) $H=-H$ is written $g\in H\Rightarrow -g\in H$.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Assumption 3, p.9

import Mathlib
import Definitions.Def_NondualOpt_Vmax
import Definitions.Def_NondualOpt_VrandFS

namespace NondualOpt

/-- Assumption 3: `X` and `H` are nonempty and convex, `H = −H`, `Λ_{X,H} < ∞`, and the minimax
consequence ① of (8) holds: the deterministic value `V^max_{X,H,T}` equals the value of the
randomized game.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Assumption 3, p.9.

**Formalization Note.** (i) The pairing is abstract (`F` in place of `E∗`), so "H bounded" is
replaced by `Λ_{X,H} < ∞` (the set `{|⟨g, u⟩|}` is bounded above), which is all the proofs use.
(ii) The laws of ① are finitely supported (footnote 6); for such laws the measurable
η-minimizer clause of Assumption 3 is automatic and is not stated. (iii) `H = −H` is written
`∀ g ∈ H, −g ∈ H`, which is equivalent. -/
def Assumption3 {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (pair : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (X : Set E) (H : Set F) (T : ℕ) : Prop :=
  X.Nonempty ∧ Convex ℝ X ∧ H.Nonempty ∧ Convex ℝ H ∧ (∀ g ∈ H, -g ∈ H) ∧
    BddAbove {r : ℝ | ∃ g ∈ H, ∃ u ∈ X, r = |pair g u|} ∧
    Vmax pair X H T = VrandFS pair X H T

end NondualOpt


