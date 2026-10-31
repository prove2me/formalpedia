-- Prove2me | Definitions.Def_FirstChoiceDesign_StrategyProofForSchools
-- name    : FirstChoiceDesign_StrategyProofForSchools
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:24:39.572298+00:00
-- url     : https://prove2.me/theorems/fed5bc2b-433a-45af-b1ee-8becbd98ad27
-- title:
--   Definition 3 — strategy-proof for schools
-- statement:
--   Let $\Gamma$ be the domain of reports $(\rho_s,r_s)$ of one school. **Definition 3.** A gDA mechanism $\varphi$ is strategy-proof for school $s$ if for any $(I,S,\succ_I,(c_s)_{s\in S})$, any priority and lottery number profile $(\rho^*,r^*)\in\Gamma^{|S|}$, any preference $\succ^*_s$ responsive with respect to $(c_s,\rho^*_s,r^*_s)$, and any $(\rho'_s,r'_s)\in\Gamma$,
--
--   $$
--   \varphi_s(\rho^*,r^*)\succeq^*_s\varphi_s((\rho'_s,r'_s),(\rho^*_{-s},r^*_{-s})).
--   $$
--
--   The mechanism is strategy-proof for schools if it is strategy-proof for every school. This is used as a mathematical property of the algorithm, with no behavioural claim about schools.
--
--   **Formalization Note** `ValidReport` is $\Gamma$ restricted to numbers in $(0,1)$ that are distinct across students: the printed $\Gamma$ asks only for $\rho_{is}+r_{is}\ne\rho_{js}+r_{js}$, which does not make the mechanism's modified order strict. A smaller report domain makes the property easier to satisfy, so a theorem assuming it is stronger. Responsiveness is with respect to the original criterion $\rho^*_{is}+r^*_{is}$, while the mechanism uses the modified one. Reports are not tied to the lottery regime: under STB reported columns may differ. Preferences are strict total orders on the subsets of $I$. The quantifier ranges over all markets of every size. The verification file proves that the DA mechanism fails this property, by the misreport of p.21.
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Γ p.13, Definition 3 p.14

import Definitions.Def_FirstChoiceDesign_outcome
import Definitions.Def_FirstChoiceDesign_Swap
import Definitions.Def_FirstChoiceDesign_Responsive

namespace FirstChoiceDesign

/-- A report `(ρ_s, r_s)` of one school: the domain `Γ` of p.13, with `ρ_is ∈ {1, …, K}`, restricted
to numbers in `(0, 1)` that are distinct across students.

**Formalization Note** `Γ` on p.13 requires only `ρ_is + r_is ≠ ρ_js + r_js`, which does not make
the modified order of Definition 1 strict. Such reports leave `φ` undefined. Every report allowed
here lies in `Γ`, since `ρ` is an integer and `r` lies in `(0, 1)`, and a smaller domain makes the
hypothesis "strategy-proof" weaker. -/
def ValidReport {n : ℕ} (K : ℕ) (ρ : Fin n → ℕ) (r : Fin n → ℝ) : Prop :=
  (∀ i, 1 ≤ ρ i ∧ ρ i ≤ K) ∧ (∀ i, r i ∈ Set.Ioo (0 : ℝ) 1) ∧ Function.Injective r

/-- Definition 3, p.14: `φ` is strategy-proof for school `s` of `(I, S, ≻_I, (c_s)_{s ∈ S})`. For
any `(ρ*, r*) ∈ Γ^{|S|}`, any preference `≻*_s` responsive with respect to `(c_s, ρ*_s, r*_s)` and
any `(ρ'_s, r'_s) ∈ Γ`, `φ_s(ρ*, r*) ⪰*_s φ_s((ρ'_s, r'_s), (ρ*_{-s}, r*_{-s}))`.

**Formalization Note** Responsiveness is with respect to the original criterion `ρ*_is + r*_is`,
while the mechanism orders students by the modified one. Reports are not tied to the lottery regime:
under STB the reported columns may differ across schools (p.14 ranges over all of `Γ^{|S|}`).
Preferences are strict total orders on subsets of `I`. -/
def StrategyProofAt {n m : ℕ} (φ : GDA) (B : Setting n m) (s : Fin m) : Prop :=
  ∀ (ρ : Fin n → Fin m → ℕ) (r : Lottery n m), (∀ t, ValidReport (φ.K n) (ρ · t) (r · t)) →
    ∀ pref : Finset (Fin n) → Finset (Fin n) → Prop, IsStrictTotalOrder _ pref →
      Responsive (B.c s) (fun i => (ρ i s : ℝ) + r i s) pref →
      ∀ (ρ' : Fin n → ℕ) (r' : Fin n → ℝ), ValidReport (φ.K n) ρ' r' →
        WeakPref pref (assigned φ B ρ r s)
          (assigned φ B (updateColumn s ρ' ρ) (updateColumn s r' r) s)

/-- Definition 3, p.14: `φ` is strategy-proof for schools if it is strategy-proof for every school,
of every `(I, S, ≻_I, (c_s)_{s ∈ S})`. -/
def StrategyProofForSchools (φ : GDA) : Prop :=
  ∀ (n m : ℕ) (B : Setting n m) (s : Fin m), StrategyProofAt φ B s

end FirstChoiceDesign


