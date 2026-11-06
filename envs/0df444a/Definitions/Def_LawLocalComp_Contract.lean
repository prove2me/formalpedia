-- Prove2me | Definitions.Def_LawLocalComp_Contract
-- name    : LawLocalComp_Contract
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:12:36.939754+00:00
-- url     : https://prove2.me/theorems/1391c324-c98d-4d52-9888-22cd4becd29d
-- title:
--   Contracting guarantee (1) with distortion $\kappa$
-- statement:
--   A law-local map $\Phi$ satisfies the **contract** with resource $R$, input class $\mathcal C$ and distortion $\kappa$ if for every dimension $d$, every selection of independent jobs with rational laws $X_j\in\mathcal C$ and nonnegative directions $a_j\in\mathbb R^d_+$ admitted by $R$, and every norm $g$ monotone on $\mathbb R^d_+$,
--   $$\mathbb E g(\tilde L)\le\mathbb E g(L)\le\kappa\,\mathbb E g(\tilde L),\qquad L=\sum_j X_ja_j,\quad \tilde L=\sum_j\Phi(X_j)a_j .$$
--   The guarantee (1) is $\kappa=1+\varepsilon$.
--
--   **Formalization Note** Law-locality is the type $\Phi:\text{Law}\to\text{Law}$: the map sees one law, while the selection, directions and norm are quantified afterwards.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), (1), p.2

import Mathlib
import Definitions.Def_LawLocalComp_IsRatLaw
import Definitions.Def_LawLocalComp_IsMonotoneNorm
import Definitions.Def_LawLocalComp_expNorm
import Definitions.Def_LawLocalComp_dirRank
import Definitions.Def_LawLocalComp_Resource_admits

namespace LawLocalComp

/-- **The contracting guarantee (1) with distortion `κ`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), (1), p.2: `E g(L̃) ≤ E g(L) ≤ (1 + ε) E g(L̃)`.

`Contract Φ R cls κ`: for every dimension `d`, every selection of `n` independent jobs with rational
laws `X_j` in the class `cls` and nonnegative directions `a_j ∈ ℝ^d_+` admitted by the resource `R`,
and every norm `g` monotone on `ℝ^d_+`, the loads `L = ∑ X_j a_j` and `L̃ = ∑ Φ(X_j) a_j` (outputs
sampled independently per copy) satisfy `E g(L̃) ≤ E g(L) ≤ κ E g(L̃)`. (1) is `κ = 1 + ε`.

**Formalization Note.** The map sees one law at a time (`Φ : Law → Law`), which is law-locality;
the selection, the directions and the norm are quantified after `Φ`. -/
def Contract (Φ : Law → Law) (R : Resource) (cls : Law → Prop) (κ : ℝ) : Prop :=
  ∀ (d n : ℕ) (X : Fin n → Law) (a : Fin n → Fin d → ℝ), (∀ j, IsRatLaw (X j) ∧ cls (X j)) →
    (∀ j, 0 ≤ a j) → R.admits n (dirRank a) → ∀ g : (Fin d → ℝ) → ℝ, IsMonotoneNorm g →
      expNorm g (fun j => Φ (X j)) a ≤ expNorm g X a ∧
        expNorm g X a ≤ κ * expNorm g (fun j => Φ (X j)) a

end LawLocalComp


