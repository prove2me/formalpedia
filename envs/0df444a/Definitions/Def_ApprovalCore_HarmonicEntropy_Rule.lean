-- Prove2me | Definitions.Def_ApprovalCore_HarmonicEntropy_Rule
-- name    : ApprovalCore_HarmonicEntropy_Rule
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:31:25.694693+00:00
-- url     : https://prove2.me/theorems/bbba25ac-e6c0-436a-a1d2-73303af1632c
-- title:
--   The harmonic entropy value $V(W)$, optimal payment systems, the harmonic entropy rule, unsaturated candidates and de-reserved systems
-- statement:
--   Fix an instance $(A, k)$ and a quota $q$. For a committee $W$ and a payment system $(r, p)$, by (P1) voter $i$'s reserve and payments form a probability vector $(r_i, p_i)$ on $1 + |A_i \cap W|$ coordinates, $p_i = (p_{ic})_{c \in A_i \cap W}$; if $A_i \cap W = \emptyset$ it is the vector $(r_i)$.
--
--   The **harmonic entropy value** of a committee $W \subseteq C$ is
--   $$V(W) = \max_{(r,p) \in P_{124}(W)} \sum_{i \in N} F(r_i, p_i),$$
--   with $F$ harmonic entropy; a maximizer is an **optimal payment system** of $W$. $V$ depends on $q$ through (P4) and is defined for every $W \subseteq C$.
--
--   **Harmonic entropy rule (Definition 6.1).** Given $I$, the rule selects all committees $W \in \mathcal W_k$ maximizing $V(W)$, i.e. $\arg\max_{W \in \mathcal W_k} V(W)$.
--
--   **Unsaturated candidates and de-reserved systems.** Given a payment system, $d \in W$ is **unsaturated** if $\sum_{i \in N_d} p_{id} < q$. Given $(r, p) \in P_{124}(W)$, a **de-reserved system** is $(\hat r, \hat p) \in P_{14}(W)$ with $\hat p_{ic} \ge p_{ic}$ for every $i$ and $c \in A_i \cap W$, such that if $d \in W$ is unsaturated in $(\hat r, \hat p)$ then $\hat r_i = 0$ for every $i \in N_d$.
--
--   **Formalization Note.** `voterDist A W (r,p) i : Fin (|A_i ∩ W| + 1) → ℝ` puts $r_i$ at index $0$ and the payment to the $j$-th element of $A_i \cap W$ (increasing candidate index) at index $j+1$. `V A q W` is the real `sSup` of $\{\sum_i F(r_i,p_i) : (r,p) \in P_{124}(W)\}$; that this set is non-empty, bounded and has a greatest element equal to `V` is the milestone `section_6_attainment`, so `V` is the paper's maximum. `IsOptimal` = in $P_{124}(W)$ and attaining `V`. `SelectedByRule I q W` = $|W| = k$ and $V(W') \le V(W)$ for every $|W'| = k$.
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), §5 p. 8; §6 p. 11 (V(W), optimal payment systems, Definition 6.1); §6 pp. 12–13 (unsaturated, de-reserved system)

import Mathlib
import Definitions.Def_ApprovalCore_HarmonicEntropy_RobinHood
import Definitions.Def_ApprovalCore_HarmonicEntropy_Election

namespace ApprovalCore.HarmonicEntropy

/-!
# The harmonic entropy value `V(W)` and the harmonic entropy rule

Becker, Greger, Peters, *Existence of the Core in Approval-Based Committee Elections*,
STOC 2027 submission (manuscript sha256 7cc237dc…), §5 p. 8 (a voter's payments and
reserve form a distribution), §6 p. 11 (`V(W)`, optimal payment systems, Definition 6.1),
§6 pp. 12–13 (unsaturated candidates, de-reserved systems).
-/

variable {n m : ℕ}

/-- Voter `i`'s distribution `(r_i, p_i)` (p. 8, p. 11): the vector on
`1 + |A_i ∩ W|` coordinates whose first coordinate (index `0`) is the reserve `r_i` and
whose coordinate `j + 1` is the payment `p_{ic}` to the `j`-th approved winner `c ∈ A_i ∩ W`
in increasing candidate order (`p_i = (p_{ic})_{c ∈ A_i ∩ W}`). If `A_i ∩ W = ∅` it is the
one-coordinate vector `(r_i)`. -/
noncomputable def voterDist (A : Fin n → Finset (Fin m)) (W : Finset (Fin m))
    (rp : PaymentPair n m) (i : Fin n) : Fin ((A i ∩ W).card + 1) → ℝ :=
  Fin.cons (rp.1 i) (fun j => rp.2 i ((A i ∩ W).orderEmbOfFin rfl j))

/-- Total harmonic entropy `∑_{i ∈ N} F(r_i, p_i)` of a payment system for `W` (p. 11). -/
noncomputable def totalEntropy (A : Fin n → Finset (Fin m)) (W : Finset (Fin m))
    (rp : PaymentPair n m) : ℝ :=
  ∑ i, harmonicEntropy (voterDist A W rp i)

/-- The harmonic entropy value `V(W) = max_{(r,p) ∈ P124(W)} ∑_{i ∈ N} F(r_i, p_i)` (p. 11),
for every committee `W ⊆ C`, at quota `q` (through (P4)). It is written as the supremum of
the attained values; that the supremum is attained (so it is the paper's maximum) is the
§6 footnote-6 milestone. -/
noncomputable def V (A : Fin n → Finset (Fin m)) (q : ℝ) (W : Finset (Fin m)) : ℝ :=
  sSup (totalEntropy A W '' P124 A q W)

/-- `(r, p)` is an optimal payment system of `W` (p. 11): it lies in `P124(W)` and attains
`V(W)`. -/
def IsOptimal (A : Fin n → Finset (Fin m)) (q : ℝ) (W : Finset (Fin m))
    (rp : PaymentPair n m) : Prop :=
  rp ∈ P124 A q W ∧ totalEntropy A W rp = V A q W

/-- The harmonic entropy rule (Definition 6.1, p. 11) selects `W` at quota `q`:
`W ∈ W_k` (`|W| = k`) and `W ∈ argmax_{W' ∈ W_k} V(W')`. -/
def SelectedByRule (I : Instance n m) (q : ℝ) (W : Finset (Fin m)) : Prop :=
  W.card = I.k ∧ ∀ W' : Finset (Fin m), W'.card = I.k → V I.A q W' ≤ V I.A q W

/-- Given a payment system, `d ∈ W` is unsaturated if `∑_{i ∈ N_d} p_{id} < q` (p. 12). -/
def Unsaturated (A : Fin n → Finset (Fin m)) (q : ℝ) (W : Finset (Fin m))
    (rp : PaymentPair n m) (d : Fin m) : Prop :=
  d ∈ W ∧ ∑ i ∈ supporters A d, rp.2 i d < q

/-- `(r̂, p̂)` is a de-reserved system of `(r, p)` (pp. 12–13): `(r̂, p̂) ∈ P14(W)`,
`p̂_{ic} ≥ p_{ic}` for every `i` and `c ∈ A_i ∩ W`, and if `d ∈ W` is unsaturated in
`(r̂, p̂)` then `r̂_i = 0` for every `i ∈ N_d`. -/
def IsDeReserved (A : Fin n → Finset (Fin m)) (q : ℝ) (W : Finset (Fin m))
    (rp rph : PaymentPair n m) : Prop :=
  rph ∈ P14 A q W ∧
    (∀ i, ∀ c ∈ A i ∩ W, rph.2 i c ≥ rp.2 i c) ∧
    ∀ d, Unsaturated A q W rph d → ∀ i ∈ supporters A d, rph.1 i = 0

end ApprovalCore.HarmonicEntropy


