-- Prove2me | Definitions.Def_ParallelSmallWorlds_SEU_UtilityAxioms
-- name    : ParallelSmallWorlds_SEU_UtilityAxioms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:52:24.525488+00:00
-- url     : https://prove2.me/theorems/a30805dc-5ab7-4960-9b1d-ba1dd99bee62
-- title:
--   Axioms PSW9–PSW15 on the preferences $\succeq_{C_w}$ and $\succeq_{S_w}$
-- statement:
--   A small world satisfies the **utility axioms** when:
--
--   1. **(PSW9)** $\succeq_C$ is complete and transitive on $C$;
--   2. **(PSW10)** $\succeq_S$ is complete and transitive on consequences and gambles, restricts to $\succeq_C$ on $C$, and $c_1\succeq_C c_2\iff\Psi_{c_1}\succeq_S\Psi_{c_2}$;
--   3. **(PSW11)** if $c_1\succ_C c_2$ then $c_1\alpha c_2\succ_S c_1\alpha' c_2\iff\alpha>\alpha'$;
--   4. **(PSW12)** there are $c^*,c_*$ with $c^*\succ_S c_*$ and $c^*\succeq_S c\succeq_S c_*$ for every $c$;
--   5. **(PSW13)** if $c_1\succeq_C c_2\succeq_C c_3$ with at least one strict preference, then $\{\alpha\in[0,1]:c_1\alpha c_3\succeq_S c_2\}$ and $\{\alpha\in[0,1]:c_2\succeq_S c_1\alpha c_3\}$ are closed;
--   6. **(PSW14, substitutability)** if $b\sim_S b'$ for prizes $b,b'$, then a gamble and the gamble obtained by substituting $b'$ for $b$ are indifferent;
--   7. **(PSW15, reduction of compound lotteries)** a mixture $\langle\pi_1,p_1;\dots;\pi_s,p_s\rangle$ of simple distributions is indifferent to its reduction $\langle\rho_1,c_1;\dots;\rho_r,c_r\rangle$, $\rho_j=\sum_i\pi_i\pi_{ij}$.
--
--   These are the von Neumann–Morgenstern-type axioms of the paper, phrased through standard gambles on the reference experiment.
--
--   **Formalization Note** PSW9–PSW13 are the sub-bundle `StandardGambleAxioms`, the axioms the proof of Lemma 2 names for the standard-gamble equivalent. In PSW14 and PSW15 the substituted and the reduced gamble are any objects carrying the substituted and the reduced weights. The indifference $c\sim_S\Psi_c$, which the proof of Lemma 2 uses, is the separate correction `CorrectionC2`.
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), Axioms PSW9–PSW15, pp.23–26 (PDF pp.24–27)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_SmallWorld

namespace ParallelSmallWorlds.SEU

open SmallWorld

/-- **Axioms PSW9–PSW13 on the preferences `⪰Cw` and `⪰Sw`, as printed.**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), Axioms PSW9–PSW13, pp.23–25 (PDF pp.24–26). These are
the axioms the proof of Lemma 2 (p.45, PDF p.46) names for the standard-gamble equivalent: "we
argue from PSW9 – PSW13"; `UtilityAxioms` below adds PSW14 and PSW15.

* **PSW9** (p.23): `⪰Cw` is a weak order on `Cw`.
* **PSW10** (p.24): (a) `⪰Sw` is a weak order on `C ∪ PSw`; (b) `⪰Sw` restricted to `Cw` is
  `⪰Cw`; (c) `c1 ⪰Cw c2 ⟺ Ψc1 ⪰Sw Ψc2`.
* **PSW11** (p.24): for `c1 ≻Cw c2`, `c1 α c2 ≻Sw c1 α′ c2 ⟺ α > α′`.
* **PSW12** (p.24): there are `c*_w, c_w*` with `c*_w ≻Sw c_w*` and `c*_w ⪰Sw c ⪰Sw c_w*` for
  every `c`.
* **PSW13** (p.25): for `c1 ⪰Cw c2 ⪰Cw c3` with at least one strict preference,
  `{α ∈ [0,1] | c1 α c3 ⪰Sw c2}` and `{α ∈ [0,1] | c2 ⪰Sw c1 α c3}` are closed.

**Formalization Note.** `α` ranges over `unitInterval`; the sets of PSW13 are subsets of it
(closed there iff closed in `ℝ`). A simple distribution `p` is the object `simpObj p`. The
indifference `c ∼Sw Ψc` that the proof of Lemma 2 uses is not part of PSW10 as printed; it is the
separate correction `CorrectionC2`. -/
structure StandardGambleAxioms {Θ C : Type*} (W : SmallWorld Θ C) : Prop where
  /-- PSW9: `⪰Cw` is complete. -/
  psw9_total : ∀ c c' : C, W.prefC c c' ∨ W.prefC c' c
  /-- PSW9: `⪰Cw` is transitive. -/
  psw9_trans : ∀ c c' c'' : C, W.prefC c c' → W.prefC c' c'' → W.prefC c c''
  /-- PSW10(a): `⪰Sw` is complete on `C ∪ PSw`. -/
  psw10a_total : ∀ x y : Obj C, W.prefS x y ∨ W.prefS y x
  /-- PSW10(a): `⪰Sw` is transitive on `C ∪ PSw`. -/
  psw10a_trans : ∀ x y z : Obj C, W.prefS x y → W.prefS y z → W.prefS x z
  /-- PSW10(b): `⪰Sw` restricted to `Cw` is `⪰Cw`. -/
  psw10b : ∀ c c' : C, W.prefS (Sum.inl c) (Sum.inl c') ↔ W.prefC c c'
  /-- PSW10(c): `c1 ⪰Cw c2 ⟺ Ψc1 ⪰Sw Ψc2`. -/
  psw10c : ∀ c c' : C,
    W.prefC c c' ↔ W.prefS (simpObj (SimpleDist.pure c)) (simpObj (SimpleDist.pure c'))
  /-- PSW11: monotonicity in the probability of the better prize. -/
  psw11 : ∀ c₁ c₂ : C, W.strictC c₁ c₂ → ∀ α α' : unitInterval,
    (W.strictS (simpObj (SimpleDist.twoPt c₁ c₂ α)) (simpObj (SimpleDist.twoPt c₁ c₂ α')) ↔
      α' < α)
  /-- PSW12: a best and a worst consequence, strictly ranked. -/
  psw12 : ∃ cs cw : C, W.strictS (Sum.inl cs) (Sum.inl cw) ∧
    ∀ c : C, W.prefS (Sum.inl cs) (Sum.inl c) ∧ W.prefS (Sum.inl c) (Sum.inl cw)
  /-- PSW13: the sets bracketing the standard-gamble probability are closed. -/
  psw13 : ∀ c₁ c₂ c₃ : C, W.prefC c₁ c₂ → W.prefC c₂ c₃ →
    (W.strictC c₁ c₂ ∨ W.strictC c₂ c₃) →
    IsClosed {α : unitInterval | W.prefS (simpObj (SimpleDist.twoPt c₁ c₃ α)) (Sum.inl c₂)} ∧
    IsClosed {α : unitInterval | W.prefS (Sum.inl c₂) (simpObj (SimpleDist.twoPt c₁ c₃ α))}

/-- **Axioms PSW9–PSW15 on the preferences `⪰Cw` and `⪰Sw`, as printed.**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), Axioms PSW9–PSW15, pp.23–26 (PDF pp.24–27).

`StandardGambleAxioms` (PSW9–PSW13) together with:

* **PSW14** (p.26, substitutability): if `b ∼Sw b′` (`b, b′ ∈ Cw ∪ PSw`), a gamble and the
  gamble obtained by substituting `b′` for `b` are indifferent.
* **PSW15** (p.26, reduction of compound lotteries): a mixture `⟨π1,p1; …; πs,ps⟩` of simple
  distributions is indifferent to the simple distribution `⟨ρ1,c1; …; ρr,cr⟩`,
  `ρj = Σ_i πi πij`.

**Formalization Note.** Gambles are one level deep (`Gamble C`). In PSW14 the substituted gamble
is any gamble whose weights are `substFun g b b'` (the weight of `b` moved to `b′`); in PSW15 the
reduced distribution is any simple distribution whose weights are `reduceFun g`, and the
mixture's prizes are all simple distributions, as printed. -/
structure UtilityAxioms {Θ C : Type*} (W : SmallWorld Θ C) : Prop
    extends StandardGambleAxioms W where
  /-- PSW14: substitutability. -/
  psw14 : ∀ (g g' : Gamble C) (b b' : C ⊕ SimpleDist C),
    W.indiffS (prizeObj b) (prizeObj b') → g'.toFun = substFun g b b' →
    W.indiffS (Sum.inr g) (Sum.inr g')
  /-- PSW15: reduction of compound lotteries. -/
  psw15 : ∀ (g : Gamble C) (q : SimpleDist C),
    (∀ b ∈ g.toFun.support, ∃ p : SimpleDist C, b = Sum.inr p) → q.toFun = reduceFun g →
    W.indiffS (Sum.inr g) (simpObj q)


