-- Prove2me | Definitions.Def_OnlineCarpoolingLei_Oblivious_Algorithm
-- name    : OnlineCarpoolingLei_Oblivious_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:59.920412+00:00
-- url     : https://prove2.me/theorems/c6af05aa-07ed-4785-9b3f-6b14bc989dee
-- title:
--   The algorithm of Section 3.2: laws $\mu_t$, minimal-norm admissible selections $p_t$, and the sign rule (3.3)
-- statement:
--   Fix $n\ge2$ and an input $e_1,e_2,\dots$. Define finitely supported probability measures $\mu_t$ and selections $p_t$ recursively: $\mu_0=\delta_0$; given $\mu_{t-1}$ and the next edge $e_t$, let $p_t$ minimize
--   $$\sum_{x\in\operatorname{supp}\mu_{t-1}}\Big(p(x)-\frac12\Big)^2$$
--   over the admissible selections for $(\mu_{t-1},e_t)$, and put $\mu_t=\mu_{t-1}^{p_t,e_t}$. The recursion determines $\mu_t$ and $p_t$ from $e_1,\dots,e_t$.
--
--   With independent $U_1,U_2,\dots$ uniform on $[0,1)$, the algorithm sets
--   $$\varepsilon_t=\begin{cases}+1,&U_t<p_t(d_{t-1}),\\-1,&\text{otherwise},\end{cases}\tag{3.3}$$
--   and updates $d_t=d_{t-1}+\varepsilon_te_t$.
--
--   This is the witness for Theorem 1.2; Proposition 3.4 establishes its two key properties (receiving gap at most $29$ and law $\mu_t$ of $d_t$).
--
--   **Formalization Note** `lawSeq E t` is $\mu_t$ and `optSel (lawSeq E t) (E t)` is $p_{t+1}$ (index shift of the input). The minimizer is taken by choice when one exists; if none existed the definition would return the constant $1/2$. Theorem 3.3 and compactness show the admissible set is nonempty and compact, so this branch is never taken; by strict convexity the minimizer is unique. A selection is read off the support as $0$; every realization keeps $d_t$ in $\operatorname{supp}\mu_t$, so this branch is never taken either. `paperAlg n` packages (3.3) as an online rule: at step $t+1$ it recomputes $\mu_t$, $p_{t+1}$ and $d_t$ from the revealed prefix and its own tape values. No efficiency claim is made.
-- source:
--   Yuhao Lei, STOC 2027 submission #416 (October 2026), Section 3.2 and (3.3), p.6 (PDF p.6)

import Mathlib
import Definitions.Def_OnlineCarpoolingLei_Oblivious_Model
import Definitions.Def_OnlineCarpoolingLei_Oblivious_ConvexOrder

/-!
Yuhao Lei, *Online carpooling against an oblivious adversary*, STOC 2027 submission #416
(October 2026), §3.2 (p.6): the laws `μ_t`, the selections `p_t`, and the sign rule (3.3).

`lawSeq E t` is `μ_t`; `optSel (lawSeq E t) (E t)` is `p_{t+1}`, the minimizer of
`∑_{x ∈ supp μ_t} (p(x) − 1/2)²` over the admissible selections for `(μ_t, e_{t+1})`.
If no minimizer existed the definition would fall back to the constant `1/2`; Theorem 3.3
and compactness show that this branch is never taken. A selection is evaluated off the
support as `0`; the paper shows `d_t ∈ supp μ_t` for every realization, so this branch is
not taken either.
-/

namespace OnlineCarpoolingLei.Oblivious

/-- The objective `∑_{x ∈ supp μ} (p(x) − 1/2)²`. -/
noncomputable def selObj {n : ℕ} (μ : (Fin n → ℝ) →₀ ℝ) (p : μ.support → ℝ) : ℝ :=
  ∑ x, (p x - 1 / 2) ^ 2

/-- The admissible selection minimizing `selObj` (fallback `1/2` if there is none). -/
noncomputable def optSel {n : ℕ} (μ : (Fin n → ℝ) →₀ ℝ) (e : Edge n) : μ.support → ℝ := by
  classical
  exact
    if h : ∃ p ∈ admissible μ e, ∀ q ∈ admissible μ e, selObj μ p ≤ selObj μ q then h.choose
    else fun _ => 1 / 2

/-- The laws `μ₀ = δ₀`, `μ_{t+1} = μ_t^{p_{t+1}, e_{t+1}}` determined by the input prefix. -/
noncomputable def lawSeq {n : ℕ} (E : ℕ → Edge n) : ℕ → ((Fin n → ℝ) →₀ ℝ)
  | 0 => Finsupp.single 0 1
  | t + 1 => pushSel (lawSeq E t) (E t) (optSel (lawSeq E t) (E t))

/-- Evaluate a selection at a point (`0` off the support). -/
noncomputable def evalSel {n : ℕ} (μ : (Fin n → ℝ) →₀ ℝ) (p : μ.support → ℝ)
    (x : Fin n → ℝ) : ℝ := by
  classical
  exact if h : x ∈ μ.support then p ⟨x, h⟩ else 0

/-- `p_{t+1}(x)`: the probability of moving from `x` to `x + e_{t+1}`. -/
noncomputable def selProb {n : ℕ} (E : ℕ → Edge n) (t : ℕ) (x : Fin n → ℝ) : ℝ :=
  evalSel (lawSeq E t) (optSel (lawSeq E t) (E t)) x

/-- The trajectory of the algorithm with tape `u`: (3.3) chooses `+1` exactly when
`U_{t+1} < p_{t+1}(d_t)`, and `−1` otherwise. -/
noncomputable def paperDisc {n : ℕ} (E : ℕ → Edge n) (u : ℕ → ℝ) : ℕ → Fin n → ℤ
  | 0 => 0
  | t + 1 =>
      paperDisc E u t +
        (if u t < selProb E t (fun i => (paperDisc E u t i : ℝ)) then (1 : ℤ) else -1) •
          (E t).vecZ

/-- Extend a finite prefix of length `t + 1` to an infinite sequence (repeating its last entry);
the algorithm's step `t + 1` only reads the first `t + 1` entries. -/
def extendPrefix {α : Type*} {t : ℕ} (a : Fin (t + 1) → α) : ℕ → α :=
  fun i => if h : i < t + 1 then a ⟨i, h⟩ else a (Fin.last t)

/-- The algorithm of §3.2 as an online rule: at step `t + 1` it recomputes `μ_t`, `p_{t+1}` and
`d_t` from the revealed prefix and its own tape, and outputs `+1` iff `U_{t+1} < p_{t+1}(d_t)`. -/
noncomputable def paperAlg (n : ℕ) : OnlineAlgorithm n where
  sign t E u :=
    decide (u (Fin.last t) <
      selProb (extendPrefix E) t (fun i => (paperDisc (extendPrefix E) (extendPrefix u) t i : ℝ)))

end OnlineCarpoolingLei.Oblivious


