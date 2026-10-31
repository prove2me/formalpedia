-- Prove2me | Definitions.Def_FirstChoiceDesign_BelowCutoff
-- name    : FirstChoiceDesign_BelowCutoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:25:15.163508+00:00
-- url     : https://prove2.me/theorems/9236776c-7082-4377-b2f3-0a84de047c0a
-- title:
--   The switch conditions of Lemma 3 and Lemma 4
-- statement:
--   For students $i',i''$ and school $s$ with $\rho^\varphi_{i's}=\rho^\varphi_{i''s}$:
--
--   - `BelowCutoff` (the condition of Lemma 3) asks $\min\{\rho^\varphi_{i's}+r_{i's},\rho^\varphi_{i''s}+r_{i''s}\}>\rho^\varphi_{is}+r_{is}$ for all $i$ with $D_{is}(r)=1$: both are ranked behind every student assigned to $s$;
--   - `AboveCutoff` (the condition of Lemma 4) asks that there exist $i$ with $D_{is}(r)=1$ and $\max\{\rho^\varphi_{i's}+r_{i's},\rho^\varphi_{i''s}+r_{i''s}\}\le\rho^\varphi_{is}+r_{is}$: both are weakly ahead of some assigned student.
--
--   **Formalization Note** The name of the module is that of the first condition. When nobody is assigned to $s$, `BelowCutoff`'s second clause holds vacuously, as on the page.
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Lemma 3 p.41, Lemma 4 p.43

import Definitions.Def_FirstChoiceDesign_First

namespace FirstChoiceDesign

/-- The condition on the switched students `i', i''` in Lemma 3, p.41: `ρ^φ_i's = ρ^φ_i''s` and
`min{ρ^φ_i's + r_i's, ρ^φ_i''s + r_i''s} > ρ^φ_is + r_is` for all `i` with `D_is(r) = 1`. -/
def BelowCutoff {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (s : Fin m) (r : Lottery n m)
    (i' i'' : Fin n) : Prop :=
  φ.modified X.toSetting X.ρ i' s = φ.modified X.toSetting X.ρ i'' s ∧
    ∀ i, D φ X i s r →
      φ.score X.toSetting X.ρ r i s <
        min (φ.score X.toSetting X.ρ r i' s) (φ.score X.toSetting X.ρ r i'' s)

/-- The condition on the switched students `i', i''` in Lemma 4, p.43: `ρ^φ_i's = ρ^φ_i''s` and
there exists `i` with `D_is(r) = 1` with `max{ρ^φ_i's + r_i's, ρ^φ_i''s + r_i''s} ≤ ρ^φ_is + r_is`. -/
def AboveCutoff {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (s : Fin m) (r : Lottery n m)
    (i' i'' : Fin n) : Prop :=
  φ.modified X.toSetting X.ρ i' s = φ.modified X.toSetting X.ρ i'' s ∧
    ∃ i, D φ X i s r ∧
      max (φ.score X.toSetting X.ρ r i' s) (φ.score X.toSetting X.ρ r i'' s) ≤
        φ.score X.toSetting X.ρ r i s

end FirstChoiceDesign


