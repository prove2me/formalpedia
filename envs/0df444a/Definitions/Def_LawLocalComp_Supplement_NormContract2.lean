-- Prove2me | Definitions.Def_LawLocalComp_Supplement_NormContract2
-- name    : LawLocalComp_Supplement_NormContract2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:06:38.091726+00:00
-- url     : https://prove2.me/theorems/eaa961d4-22f4-490c-9caa-63ab61624109
-- title:
--   The guarantee (1) for one norm and two directions
-- statement:
--   Let $\Phi$ map finite nonnegative laws to finite nonnegative laws, let $g : \mathbb R^2 \to \mathbb R$, let $a_1, a_2 \in \mathbb R^2$, let $N \in \mathbb N$ and $\kappa > 0$. $\Phi$ satisfies **(1) for $g$ and the two directions $a_1, a_2$ under horizon $N$** if for every selection of $n \le N$ independent jobs with rational laws $X_1, \dots, X_n$ and directions $a_{(j)} \in \{a_1, a_2\}$, the loads $L = \sum_j X_j a_{(j)}$ and $\tilde L = \sum_j Y_j a_{(j)}$, $Y_j \sim \Phi(X_j)$ independent, satisfy
--   $$
--   \mathbb E g(\tilde L) \le \mathbb E g(L) \le \kappa\,\mathbb E g(\tilde L).
--   $$
--   This is the hypothesis of Theorem 6.1's bound (22): the guarantee is required for one fixed norm and two directions only, not for every monotone norm.
--
--   **Formalization Note** The directions live in $\mathbb R^2$, so every such selection has rank at most two.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 6.1, p.9 ("One fixed monotone norm and two directions suffice")

import Mathlib
import Definitions.Def_LawLocalComp_IsRatLaw
import Definitions.Def_LawLocalComp_expNorm

namespace LawLocalComp

namespace Supplement

/-- **The guarantee (1) for one norm and two directions.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 6.1, p.9 ("One fixed monotone norm and two directions suffice").

`NormContract2 Φ g a₁ a₂ N κ`: for every selection of `n ≤ N` independent jobs with rational laws
`X_j` whose directions `a_j` all lie in `{a₁, a₂} ⊆ ℝ²`, the loads `L = ∑ X_j a_j` and
`L̃ = ∑ Φ(X_j) a_j` satisfy `E g(L̃) ≤ E g(L) ≤ κ E g(L̃)` for the one fixed function `g`.

**Formalization Note.** Since the directions lie in `ℝ²`, every such selection has rank at most
two, so it is admitted by horizon `N` and rank two. -/
def NormContract2 (Φ : Law → Law) (g : (Fin 2 → ℝ) → ℝ) (a₁ a₂ : Fin 2 → ℝ) (N : ℕ) (κ : ℝ) :
    Prop :=
  ∀ (n : ℕ) (X : Fin n → Law) (a : Fin n → Fin 2 → ℝ), n ≤ N → (∀ j, IsRatLaw (X j)) →
    (∀ j, a j = a₁ ∨ a j = a₂) →
      expNorm g (fun j => Φ (X j)) a ≤ expNorm g X a ∧
        expNorm g X a ≤ κ * expNorm g (fun j => Φ (X j)) a

end Supplement

end LawLocalComp


