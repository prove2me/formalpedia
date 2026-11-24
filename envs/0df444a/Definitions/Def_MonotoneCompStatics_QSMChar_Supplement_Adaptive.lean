-- Prove2me | Definitions.Def_MonotoneCompStatics_QSMChar_Supplement_Adaptive
-- name    : MonotoneCompStatics_QSMChar_Supplement_Adaptive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:08:10.332818+00:00
-- url     : https://prove2.me/theorems/36364a9a-93ed-4d0d-83f6-5c7c929df1a9
-- title:
--   Consistency with adaptive learning
-- statement:
--   For a pure-action path $x:\mathbb N\to\prod_iS_i$, adaptive consistency is the following uniform exclusion condition:
--   $$\forall\epsilon>0\ \forall T\ \exists T'>T\ \forall t>T'\ \forall i,a,b,\quad\bigl[\forall s\in[T,t],\ \pi_i(a,x_{-i}(s))+\epsilon<\pi_i(b,x_{-i}(s))\bigr]\Longrightarrow x_i(t)\ne a.$$
--   The alternative $b$ can depend on $a$, but the later date is uniform over players and alternatives as printed. This is a condition on observed rival histories and does not require choosing a best response at every date. **Formalization Note** Dates are natural numbers and both endpoints of $[T,t]$ are included.
--
--   The file also names the concrete one-player source-error witness for Theorem 14: actions are $\mathbb N\cup\{\infty\}$, payoff is one at infinity and zero elsewhere, equilibrium is infinity, and the path at date $t$ is the finite action $t$. Its validity and inconsistency properties are theorem conclusions, not assumed fields.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), DOI 10.2307/2951479, pp.176–177, PDF 21–22, formal definition

import Mathlib
import Definitions.Def_MonotoneCompStatics_QSMChar_Supplement_NormalFormGame

namespace MonotoneCompStatics.QSMChar.Supplement

/-- Exact epsilon/start-date/later-date condition printed on p.177. -/
def AdaptiveConsistent {I : Type*} {S : I → Type*} (G : NormalFormGame I S)
    (x : ℕ → (i : I) → S i) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ T : ℕ, ∃ T' : ℕ, T < T' ∧
    ∀ t : ℕ, T' < t → ∀ (i : I) (a b : S i),
      (∀ s : ℕ, T ≤ s → s ≤ t →
        G.payoff i a (opponents (x s) i) + ε < G.payoff i b (opponents (x s) i)) →
      x t i ≠ a

/-- A one-player compact-chain game with an upward jump at its unique maximizer. -/
noncomputable def jumpGame : NormalFormGame Unit (fun _ => ℕ∞) where
  payoff := fun _ a _ => if a = ⊤ then 1 else 0

def jumpEquilibrium : Unit → ℕ∞ := fun _ => ⊤

def jumpPath (t : ℕ) : Unit → ℕ∞ := fun _ => (t : ℕ∞)

end MonotoneCompStatics.QSMChar.Supplement


