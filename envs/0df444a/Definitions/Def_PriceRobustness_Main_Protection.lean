-- Prove2me | Definitions.Def_PriceRobustness_Main_Protection
-- name    : PriceRobustness_Main_Protection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:38:00.542994+00:00
-- url     : https://prove2.me/theorems/b8cb7087-4f23-4718-a9fc-ed4edce8cbd2
-- title:
--   Protection maximizers and source normalization
-- statement:
--   For a finite row $J$, weights $w_j$, and real budget $\Gamma$, an admissible pair $(S,t)$ has $S\subseteq J$, $|S|=\lfloor\Gamma\rfloor$, and $t\in J\setminus S$ when $0\le\Gamma<|J|$. Its value is
--   $$\sum_{j\in S}w_j+(\Gamma-\lfloor\Gamma\rfloor)w_t.$$
--   A maximizing pair is any admissible pair whose value is at least that of every admissible pair. All ties, including every permitted extra index at an integral budget, are retained. A minimizing index $r$ is any minimum-weight coordinate of $S\cup\{t\}$. Set
--   $$\gamma_j=\begin{cases}1&j\in S,\\w_j/w_r&j\notin S.\end{cases}$$
--   At full budget, the admissible choice is $S=J$ with no extra or minimizing index, so every coefficient on $J$ is one. This also handles the empty row. The maximization is defined by comparison with all candidates, with no supremum or assumed coefficient bound.
--
--   Formalization conventions: optional indices encode the full-budget endpoint from p. 6; real division sets a zero-denominator quotient to zero, an explicit extension where the source is undefined. The fractional coordinate in Eq. (5) is read as $t$, as specified in the surrounding model and Eq. (9); its printed $j$ is unbound. The counterexample with weights $(100,100,99,1)$, budget $2$, $S=\{1,2\}$, $t=r=4$ remains an admissible maximizer and yields $(1,1,99,1)$.
-- source:
--   Bertsimas and Sim, The Price of Robustness, authors' preprint, August 2001; revised August, 2002; PDF SHA-256 63f0bffaff9128b706a084acc869e1020ce79adf86108ac23b5b0dd598f189cb; p. 6, Eq. (5) and integer-budget endpoints; p. 8, Proposition 2

import Mathlib

open scoped BigOperators
noncomputable section

namespace PriceRobustness.Main

def AdmissibleProtection {N : ℕ} (J S : Finset (Fin N)) (Γ : ℝ)
    (t : Option (Fin N)) : Prop :=
  0 ≤ Γ ∧ Γ ≤ J.card ∧
  if Γ = (J.card : ℝ) then S = J ∧ t = none
  else S ⊆ J ∧ (S.card : ℤ) = ⌊Γ⌋ ∧ ∃ j ∈ J, j ∉ S ∧ t = some j

def protectionValue {N : ℕ} (w : Fin N → ℝ) (Γ : ℝ)
    (S : Finset (Fin N)) (t : Option (Fin N)) : ℝ :=
  (∑ j ∈ S, w j) + (Γ - (⌊Γ⌋ : ℤ)) * (t.elim 0 w)

def MaximizesProtection {N : ℕ} (J : Finset (Fin N)) (w : Fin N → ℝ) (Γ : ℝ)
    (S : Finset (Fin N)) (t : Option (Fin N)) : Prop :=
  AdmissibleProtection J S Γ t ∧
  ∀ S' t', AdmissibleProtection J S' Γ t' →
    protectionValue w Γ S' t' ≤ protectionValue w Γ S t

def MinimizesSelected {N : ℕ} (w : Fin N → ℝ) (S : Finset (Fin N))
    (t r : Option (Fin N)) : Prop :=
  match t with
  | none => r = none
  | some j => ∃ k, r = some k ∧ k ∈ insert j S ∧ ∀ l ∈ insert j S, w k ≤ w l

def sourceGamma {N : ℕ} (w : Fin N → ℝ) (S : Finset (Fin N))
    (r : Option (Fin N)) (j : Fin N) : ℝ :=
  if j ∈ S then 1 else w j / r.elim 0 w

end PriceRobustness.Main


