-- Prove2me | Definitions.Def_FirstChoiceDesign_Responsive
-- name    : FirstChoiceDesign_Responsive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:37.36606+00:00
-- url     : https://prove2.me/theorems/6c9f71c0-c5e5-48c5-8b1f-ce6a2eb85955
-- title:
--   Responsive preferences over sets of students
-- statement:
--   A preference $\succ$ over subsets of $I$ is **responsive** with respect to a capacity $c$ and a criterion $\mathrm{score}$ if
--
--   1. whenever $\mathrm{score}(i)<\mathrm{score}(i')$, then $I'\cup\{i\}\succ I'\cup\{i'\}$ for any $I'\subseteq I\setminus\{i,i'\}$;
--   2. $\emptyset\succ I'$ for any $I'\subseteq I$ with $|I'|>c$;
--   3. $I'\cup\{i\}\succ I'$ for any $I'\subseteq I$ with $|I'|<c$ and any $i\in I\setminus I'$.
--
--   The associated weak preference is `WeakPref`: strict preference or equality.
--
--   **Formalization Note** The source says "responsive with respect to $(c_s,\rho_s,r_s)$", which is $\mathrm{score}(i)=\rho_{is}+r_{is}$, and in Facts 1 and 2 "with respect to $(c_s,\rho^\varphi_s,r_s)$", which is $\mathrm{score}(i)=\rho^\varphi_{is}+r_{is}$. The criterion is an argument so that these two different notions cannot be confused. The mission's verification file proves that a strict total responsive order exists for every injective criterion.
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), pp.13–14 (Roth and Sotomayor, 1992)

import Mathlib

namespace FirstChoiceDesign

/-- Responsiveness of a preference `pref` over subsets of `I` with respect to a capacity `c` and a
criterion `score`, pp.13–14 (Roth and Sotomayor, 1992): (1) if `score i < score i'` then for any
`I' ⊆ I ∖ {i, i'}`, `I' ∪ {i} ≻ I' ∪ {i'}`; (2) `∅ ≻ I'` for `|I'| > c`; (3) for `|I'| < c` and
`i ∉ I'`, `I' ∪ {i} ≻ I'`.

**Formalization Note** The page writes "responsive with respect to `(c_s, ρ_s, r_s)`", with
`score i = ρ_is + r_is`. Facts 1 and 2, p.41, use the same notion with `(c_s, ρ^φ_s, r_s)`, with
`score i = ρ^φ_is + r_is`. Hence the generic `score`: the two criteria are different and each
statement names its own. -/
def Responsive {n : ℕ} (c : ℕ) (score : Fin n → ℝ)
    (pref : Finset (Fin n) → Finset (Fin n) → Prop) : Prop :=
  (∀ i i', score i < score i' → ∀ I' : Finset (Fin n), i ∉ I' → i' ∉ I' →
    pref (insert i I') (insert i' I')) ∧
  (∀ I' : Finset (Fin n), c < I'.card → pref ∅ I') ∧
  ∀ I' : Finset (Fin n), I'.card < c → ∀ i, i ∉ I' → pref (insert i I') I'

/-- The weak preference `⪰` associated with a strict preference `≻`, p.14. -/
def WeakPref {α : Type*} (pref : α → α → Prop) (A B : α) : Prop :=
  pref A B ∨ A = B

end FirstChoiceDesign


