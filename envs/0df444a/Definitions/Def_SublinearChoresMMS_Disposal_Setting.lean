-- Prove2me | Definitions.Def_SublinearChoresMMS_Disposal_Setting
-- name    : SublinearChoresMMS_Disposal_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T03:29:34.689415+00:00
-- url     : https://prove2.me/theorems/914979ff-9604-4690-a1d1-f1736fb7bbc2
-- title:
--   Additive chores, cost MMS, MMS1, and the section parameters
-- statement:
--   There are $n$ agents and $m$ chores with singleton costs $c_i(e)\in\mathbb R$. The nonnegative-instance predicate is exactly $c_i(e)\ge0$; it allows zero-cost agents. The additive cost and complete-allocation bundles reuse published definitions. A complete allocation assigns each chore to one agent and allows empty bundles.
--
--   For a positive part count $d$, define
--
--   $$\mu_i^d=-\operatorname{mms}(-c_i,d,M),\qquad \mu_i=\mu_i^n,\qquad \mathrm{PROP}_i=\frac{c_i(M)}n.$$
--
--   Here the published maximin functional ranges over all labelled partitions with empty parts, so negation gives the cost minimum of maximum part costs. Set $\kappa_i=\max(0,\max_e c_i(e))$, with value zero when there are no chores. A bundle $S$ is **MMS1** if it is empty or some $e\in S$ leaves $c_i(S\setminus\{e\})\le\mu_i$. Non-MMS agents have cost strictly greater than their original full-set benchmark.
--
--   The internal normalized regime has strictly positive, distinct costs decreasing in the common chore order and $\mu_i=1$. This regime is used only in the supporting construction. The general goal has only nonnegative costs. Fractional costs are finite scalar products. The section parameter is $q=2^{\lfloor\log_2\sqrt{n\log n}\rfloor}$, with $L=\lfloor n/q\rfloor$, $h=n\bmod q$, $L$ unit bins and an extra bin of capacity $h/q$ exactly when $h>0$.
--
--   **Formalization Note** Labels start at zero. Part counts and divisors are positive wherever the formulas are used in a theorem.
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), §2, Definition 2.1, §3 and §3.1, printed pp. 4–6 / PDF pp. 5–7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_ChoresEFX_IsAlphaEFX
import Definitions.Def_SublinearChoresMMS_Disposal_FiniteLaw

noncomputable section

namespace SublinearChoresMMS.Disposal

abbrev Cost (n m : ℕ) := Fin n → Fin m → ℝ
abbrev Allocation (n m : ℕ) := Fin m → Fin n
abbrev cost {n m : ℕ} (c : Cost n m) (i : Fin n) (S : Finset (Fin m)) := ChoresEFX.cost c i S
abbrev bundle {n m : ℕ} (X : Allocation n m) (i : Fin n) := ChoresEFX.bundle X i

/-- The cost minimax share is the negative of the published goods maximin functional.
Only positive part counts are used in statements. Section 2, printed p. 4 / PDF p. 5. -/
def costShare {m : ℕ} (u : Fin m → ℝ) (d : ℕ) : ℝ :=
  -LittleCharity.MMS.mms (fun S => -∑ e ∈ S, u e) d Finset.univ

def mu {n m : ℕ} (c : Cost n m) (i : Fin n) : ℝ := costShare (c i) n

def propShare {n m : ℕ} (c : Cost n m) (i : Fin n) : ℝ :=
  cost c i Finset.univ / n

/-- Maximum single cost, with value zero on an empty chore set, for nonnegative costs. -/
def kappa {n m : ℕ} (c : Cost n m) (i : Fin n) : ℝ :=
  max 0 (⨆ e, c i e)

/-- Definition 2.1, with the source's normalization restored to the original share. -/
def MMS1 {n m : ℕ} (c : Cost n m) (i : Fin n) (S : Finset (Fin m)) : Prop :=
  S = ∅ ∨ ∃ e ∈ S, cost c i (S.erase e) ≤ mu c i

def nonMMS {n m : ℕ} (c : Cost n m) (X : Allocation n m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => mu c i < cost c i (bundle X i))

def Nonnegative {n m : ℕ} (c : Cost n m) : Prop := ∀ i e, 0 ≤ c i e

def IDO {n m : ℕ} (c : Cost n m) : Prop := ∀ i, Antitone (c i)

/-- The internal positive, distinct, normalized ordered regime, not a goal hypothesis.
Section 2, printed pp. 4–5 / PDF pp. 5–6. -/
def Normalized {n m : ℕ} (c : Cost n m) : Prop :=
  (∀ i e, 0 < c i e) ∧ (∀ i, StrictAnti (c i)) ∧ ∀ i, mu c i = 1

def fractionalCost {n m : ℕ} (c : Cost n m) (i : Fin n) (z : Fin m → ℝ) : ℝ :=
  ∑ e, c i e * z e

/-- §3 parameter; Nat.floor is used only in the sufficiently large n regime. -/
def blockSize (n : ℕ) : ℕ :=
  2 ^ ⌊Real.logb 2 (Real.sqrt ((n : ℝ) * Real.log n))⌋₊

def unitBins (n q : ℕ) : ℕ := n / q

def remainder (n q : ℕ) : ℕ := n % q

def binCount (n q : ℕ) : ℕ := n / q + if n % q = 0 then 0 else 1

def binCapacity (n q : ℕ) (v : Fin (binCount n q)) : ℝ :=
  if v.val < n / q then 1 else (n % q : ℕ) / (q : ℝ)

end SublinearChoresMMS.Disposal


