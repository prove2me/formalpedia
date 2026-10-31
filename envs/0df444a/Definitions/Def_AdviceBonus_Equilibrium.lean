-- Prove2me | Definitions.Def_AdviceBonus_Equilibrium
-- name    : AdviceBonus_Equilibrium
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:32.773895+00:00
-- url     : https://prove2.me/theorems/0a51385b-6550-4184-a6e9-25c477fe61b8
-- title:
--   Strategy set, symmetric equilibrium of the compensation stage, and first-order sufficiency
-- statement:
--   **Strategy set** (p.8). Payments are non-negative by limited liability, $F_n(1)=f_n\ge0$ and $F_n(2)=2f_n+b_n\ge0$, so a firm chooses its scheme from
--   $$
--   X=\{(f,b)\in\mathbb R^2:\ f\ge0,\ 2f+b\ge0\}.
--   $$
--   A negative bonus is allowed.
--
--   **Symmetric equilibrium** (§4, p.16). At a common price $p$, unit cost $c$ and liability $w$, a scheme $(f,b)$ is a *symmetric equilibrium compensation scheme* if $(f,b)\in X$ and the profile in which both firms offer $(f,b)$ is a pure Nash equilibrium of the game in which each firm chooses a scheme in $X$ and earns its profit (6):
--   $$
--   \pi_A\big((f',b'),(f,b)\big)\le\pi_A\big((f,b),(f,b)\big),\qquad \pi_B\big((f,b),(f',b')\big)\le\pi_B\big((f,b),(f,b)\big)\qquad\text{for all }(f',b')\in X.
--   $$
--   The advisor follows the cutoffs (2)–(4) and customers follow the advice.
--
--   **First-order sufficiency.** Against a rival scheme $r$, profits satisfy first-order sufficiency if, for each firm, every own scheme $(f',b')$ in the interior of $X$ ($f'>0$, $2f'+b'>0$) at which all three advice cutoffs are interior and the firm's profit has both partial derivatives in its own $f'$ and its own $b'$ equal to $0$ maximizes that profit over $X$, the rival offering $r$. This is how the proofs use the paper's assumption of "strict quasiconcavity of firm profits in the two instruments" (pp.36–37): to pass from first-order conditions to optimality.
--
--   **Formalization Note** The Nash condition is the published general definition `CompetingChains.Cournot.IsPureNash`, with both strategy types the subtype $X$. Literal strict quasiconcavity on $X$ cannot be used: when $f_A$ is large and $b_A\ge0$ all cutoffs are $0$, firm $A$ makes both sales, and $\pi_A=2(p-c-f_A)-b_A$ is affine, hence not strictly quasiconcave, for every $G$. The restriction to interior cutoffs excludes regions where the profit is locally constant (e.g. $0$ where the firm never sells), whose points are critical without being best responses; without it the condition fails whenever $p-c>w$.
-- source:
--   Honda–Inderst–Ottaviani, When Liability is Not Enough, SSRN 4125013 (May 2022), §2, limited liability F_n(s_n) ≥ 0, F_n(1) = f_n, F_n(2) = 2f_n + b_n, p.8; §4, symmetric equilibrium at given p, p.16; strict quasiconcavity assumption, Appendix A, proofs of Propositions 3 and 4, pp.36–37

import Mathlib
import Definitions.Def_AdviceBonus_Model
import Definitions.Def_CompetingChains_Cournot_TwoPlayerGame

namespace AdviceBonus

/-!
Honda, Inderst, Ottaviani, *When Liability is Not Enough*, SSRN 4125013 (May 2022 version):
the firms' strategy set (§2, p.8), the symmetric equilibrium of the compensation stage (§4,
p.16), and the regularity assumption on profits used in the proofs (pp.36–37).
-/

/-- The strategy set of a firm, p.8: schemes `(f, b)` with non-negative payments
`F(1) = f ≥ 0` and `F(2) = 2f + b ≥ 0` (limited liability; `F(0) = 0`). A negative bonus is
allowed. -/
def X : Set (ℝ × ℝ) := {s | 0 ≤ s.1 ∧ 0 ≤ 2 * s.1 + s.2}

/-- A symmetric equilibrium compensation scheme `(f, b)` at the common price `p`, cost `c` and
liability `w` (§4, p.16): the profile in which both firms offer `(f, b)` is a pure Nash
equilibrium of the two-firm game in which each firm chooses a scheme in `X` and earns its profit
(6), the advisor recommending by the cutoffs (2)–(4) (Lemma 1) and customers following the advice.

**Formalization Note** The Nash condition is the published
`CompetingChains.Cournot.IsPureNash`, with both strategy types the subtype `X`; player 1 is firm A
with payoff `profitA`, player 2 is firm B with payoff `profitB`. The advisor's participation needs
nothing: payments are non-negative and the outside option is `0` (p.8). -/
def IsSymEq (D : Dist) (p c w : ℝ) (s : ℝ × ℝ) : Prop :=
  ∃ h : s ∈ X, CompetingChains.Cournot.IsPureNash
    (fun (x : X) (y : X) => profitA D p c w x.1 y.1)
    (fun (x : X) (y : X) => profitB D p c w x.1 y.1) ⟨s, h⟩ ⟨s, h⟩

/-- First-order sufficiency of the firms' profits in their own two instruments against the rival
scheme `r`: for each firm, every own scheme `s` in the interior of `X` (`f > 0`, `2f + b > 0`) at
which all three advice cutoffs are interior and both partial derivatives of the firm's profit in its
own `f` and its own `b` exist and vanish maximizes that profit over all of `X`, the rival offering
`r`.

This is the form in which the proofs use the paper's assumption "strict quasiconcavity of firm
profits in the two instruments" (proof of Proposition 3, p.36; proof of Proposition 4, p.37): to
pass from first-order conditions to optimality of a firm's best response to the rival's scheme.

**Formalization Note** Literal strict quasiconcavity on `X` fails for every `G`: when `f_A` is
large and `b_A ≥ 0` all cutoffs clamp to `0` and `π_A = 2(p − c − f_A) − b_A` is affine. The
restriction to interior cutoffs excludes the regions where every cutoff is clamped and the profit
is locally constant (for instance `0` when the rival's commission exceeds the firm's by more than
`w`), whose points are critical without being maximizers; without it the condition fails whenever
`p − c > w`. The rival scheme `r` is a parameter: Proposition 2 assumes the condition against the
candidate equilibrium scheme, which is the best-response problem the Nash condition poses. -/
def FOCSufficient (D : Dist) (p c w : ℝ) (r : ℝ × ℝ) : Prop :=
  ∀ s : ℝ × ℝ, 0 < s.1 → 0 < 2 * s.1 + s.2 →
    (q1 D w s r ∈ Set.Ioo (0 : ℝ) 1 → q2A w s r ∈ Set.Ioo (0 : ℝ) 1 →
      q2B w s r ∈ Set.Ioo (0 : ℝ) 1 →
      HasDerivAt (fun f => profitA D p c w (f, s.2) r) 0 s.1 →
      HasDerivAt (fun b => profitA D p c w (s.1, b) r) 0 s.2 →
      ∀ t ∈ X, profitA D p c w t r ≤ profitA D p c w s r) ∧
    (q1 D w r s ∈ Set.Ioo (0 : ℝ) 1 → q2A w r s ∈ Set.Ioo (0 : ℝ) 1 →
      q2B w r s ∈ Set.Ioo (0 : ℝ) 1 →
      HasDerivAt (fun f => profitB D p c w r (f, s.2)) 0 s.1 →
      HasDerivAt (fun b => profitB D p c w r (s.1, b)) 0 s.2 →
      ∀ t ∈ X, profitB D p c w r t ≤ profitB D p c w r s)

end AdviceBonus


