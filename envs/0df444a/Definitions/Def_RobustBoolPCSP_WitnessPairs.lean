-- Prove2me | Definitions.Def_RobustBoolPCSP_WitnessPairs
-- name    : RobustBoolPCSP_WitnessPairs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:25:23.521333+00:00
-- url     : https://prove2.me/theorems/be98d832-e740-4bd9-9c9d-c58cb643b769
-- title:
--   The witness pairs $R_{\mathsf A}$ and $R_{\mathsf M}$ of Lemma 4.18
-- statement:
--   Weights count the entries equal to $1$ (i.e. $+1$ in sign notation). A relation pair $R_{\mathsf A}=(P,Q)$ of arity $n$ has **property (i)** if $P=\mathrm{Ham}_n(\{a\})$ with $n/2<a<n$ and $Q\in\{\mathrm{NAND}_n,\mathrm{NAE}_n\}$.
--
--   A relation pair $R_{\mathsf M}=(P,Q)$ of arity $n$ has **property (ii)** if $P=\mathrm{Ham}_n(S)$ with $S\subseteq\{0,\dots,\lfloor n/2\rfloor\}$ and $\beta=\max S\ge1$, every weight missing from $Q$ is at least $2\beta$, if $\beta=n/2$ then $S$ contains a smaller level, and $R_{\mathsf M}$ is preserved by every odd Majority but not by every odd Alternating Threshold.
--
--   These are the two pairs produced by the witness normal form and consumed by the simulation lemma.
--
--   **Formalization Note** A weight $w\le n$ is missing from $Q$ when no tuple of weight $w$ lies in $Q$. $\mathrm{Maj}_L$ and $\mathrm{AT}_L$ are the published `SymBoolPCSP.CFixing.Maj`, `AT` ($\mathrm{AT}_L(x)=1$ iff $x_1-x_2+\cdots\pm x_L>0$).
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §4.4, Lemma 4.18, p.25

import Mathlib
import Definitions.Def_RobustBoolPCSP_Canonical

set_option autoImplicit false

namespace RobustBoolPCSP

open SymBoolPCSP.CFixing

/-- Property (i) of Lemma 4.18 (p.25) for a pair `R_𝖠 = (P, Q)` of arity `n`:
"RA = (Hamn({a}), QA) with n/2 < a < n and QA ∈ {NANDn, NAEn}." Weights count `true` (= +1)
entries. -/
def IsWitnessRA {n : ℕ} (P Q : Set (Fin n → Bool)) : Prop :=
  ∃ a : ℕ, P = Ham n {a} ∧ n < 2 * a ∧ a < n ∧ (Q = NAND n ∨ Q = NAE n)

/-- Property (ii) of Lemma 4.18 (p.25) for a pair `R_𝖬 = (P, Q)` of arity `n`:
"RM = (Hamn(S), QM), of some arity n, with S ⊆ {0, . . . , ⌊n/2⌋} and β = max S ≥ 1; every weight
missing from QM is at least 2β; if β = n/2, then S contains a smaller level; and RM is preserved by
every odd Majority but not by every odd Alternating Threshold."

**Formalization Note.** A weight `w ≤ n` is missing from `Q` when no tuple of weight `w` lies in
`Q`. `⌊n/2⌋` is the natural-number quotient `n / 2`; `β = n/2` is `2β = n`. -/
def IsWitnessRM {n : ℕ} (P Q : Set (Fin n → Bool)) : Prop :=
  ∃ (S : Finset ℕ) (β : ℕ), P = Ham n ↑S ∧ (∀ s ∈ S, s ≤ n / 2) ∧
    β ∈ S ∧ (∀ s ∈ S, s ≤ β) ∧ 1 ≤ β ∧
    (∀ w : ℕ, w ≤ n → (∀ x : Fin n → Bool, hw x = w → x ∉ Q) → 2 * β ≤ w) ∧
    (2 * β = n → ∃ s ∈ S, s < β) ∧
    (∀ L : ℕ, Odd L → PolOf P Q (Maj L)) ∧
    ¬ (∀ L : ℕ, Odd L → PolOf P Q (AT L))

end RobustBoolPCSP


