-- Prove2me | Definitions.Def_FirstChoiceDesign_Lottery
-- name    : FirstChoiceDesign_Lottery
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:53.426466+00:00
-- url     : https://prove2.me/theorems/8ef258ce-a166-4d1e-97b0-def25249c917
-- title:
--   Lottery number profiles, the no-tie convention, consistency with the regime
-- statement:
--   A **lottery number profile** is $r=(r_{is})_{i\in I,s\in S}$. Realized numbers carry no tie: $r_{is}\ne r_{js}$ for all students $i\neq j$ and school $s$. Under STB a profile has $r_{is}=r_{is'}$ for all $i,s,s'$. A **potential lottery realization** (Definition 2) is a tieless profile consistent with the regime in this sense.
--
--   Consistency matters only for realizations: the proof of Theorem 1 also evaluates the mechanism at profiles that are not STB-consistent.
--
--   **Formalization Note** `Tieless r` asks for numbers in the open interval $(0,1)$, as footnote 9 of the source says, and distinct at each school. Then $\rho^\varphi_{is}+r_{is}$ gives a strict order at every school, since $\rho^\varphi$ is an integer. On the closed interval a boundary tie between priority values is possible and Definition 1's order is not total. The excluded profiles are a null set, and every order on $[0,1]$ is reached on $(0,1)$.
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), pp.6–7, footnote 9 p.7, Definition 2 p.10

import Definitions.Def_FirstChoiceDesign_GDA

namespace FirstChoiceDesign

/-- A lottery number profile `r = (r_is)_{i ∈ I, s ∈ S}`, pp.6–7. -/
abbrev Lottery (n m : ℕ) := Fin n → Fin m → ℝ

/-- The no-tie convention, p.7: "When referring to any realized lottery number vector `r`, I assume
no tie and `r_is ≠ r_js` for all students `i, j`, and school `s`."

**Formalization Note** Numbers lie in the open interval `(0, 1)`, as footnote 9, p.7 says. On the
closed interval a number `1` could tie a number `0` of the next priority value, and Definition 1's
order would not be total. The boundary is a null set, and every order reachable on `[0, 1]` is
reachable on `(0, 1)`. -/
def Tieless {n m : ℕ} (r : Lottery n m) : Prop :=
  (∀ i s, r i s ∈ Set.Ioo (0 : ℝ) 1) ∧ ∀ s, Function.Injective fun i => r i s

/-- Consistency with the lottery regime, pp.6–7: under STB, `r_is = r_is'` for all `i, s, s'`. -/
def Consistent {n m : ℕ} : Regime → Lottery n m → Prop
  | .STB, r => ∀ i s s', r i s = r i s'
  | .MTB, _ => True

/-- A potential lottery realization of Definition 2: tieless and consistent with the regime. -/
def Potential {n m : ℕ} (regime : Regime) (r : Lottery n m) : Prop :=
  Tieless r ∧ Consistent regime r

end FirstChoiceDesign


