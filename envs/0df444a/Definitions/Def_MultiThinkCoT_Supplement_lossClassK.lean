-- Prove2me | Definitions.Def_MultiThinkCoT_Supplement_lossClassK
-- name    : MultiThinkCoT_Supplement_lossClassK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:56:05.651409+00:00
-- url     : https://prove2.me/theorems/c887d301-5254-4fdf-895e-217c74b1eb01
-- title:
--   The $\kappa$-generator CoT loss class $\mathcal L^{\mathrm{CoT}\text{-}T}(\mathcal F;\kappa)$
-- statement:
--   Let $\mathcal F\subseteq\{0,1\}^{\{0,1\}^*}$ be a class of next-token generators, $\mathcal X\subseteq\{0,1\}^*$ an input domain, $T$ a generation length and $\kappa$ a number of generators. The **$\kappa$-generator CoT loss class** is the binary class over $\mathcal X\times\{0,1\}^T$
--
--   $$
--   \mathcal L^{\mathrm{CoT}\text{-}T}(\mathcal F;\kappa)=\Big\{(x,z)\mapsto\mathbb 1\big\{\forall j\in[\kappa],\ z\neq g_j^{\mathrm{CoT}\text{-}T}(x)\big\}\ :\ g_1,\dots,g_\kappa\in\mathcal F\Big\}.
--   $$
--
--   A member of the class flags a pair $(x,z)$ exactly when the trace $z$ is produced by none of the $\kappa$ generators $g_j$ on $x$. Its VC dimension controls the sample complexity of learning a set of $\kappa$ generators whose CoTs cover every observed trace (the rule $\kappa$-ConsistentCoT). For $\kappa=1$ it is the CoT loss class $\mathcal L^{\mathrm{CoT}\text{-}T}(\mathcal F)$ of eq. (10).
--
--   **Formalization Note** As in the published `MultiThinkCoT.cotLossClass`, $\{0,1\}^T$ is the subtype of length-$T$ Boolean lists, $\mathcal X$ is a subtype of `List Bool`, and the indicator is a Boolean. A tuple $(g_1,\dots,g_\kappa)$ is a function `Fin κ → Gen` with every value in $\mathcal F$. At $\kappa=0$ the class is the single constant-$1$ function.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), §7.1, eq. (11), p.21 (PDF p.21)

import Mathlib
import Definitions.Def_MultiThinkCoT_e2e

namespace MultiThinkCoT.Supplement

/-!
# The `κ`-generator CoT loss class `L^{CoT-T}(F; κ)` (11)

N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…), §7.1, eq. (11), p.21 (PDF p.21).

`L^{CoT-T}(F; κ) := {(x, z) ↦ 1{∀ j ∈ [κ], z ≠ g_j^{CoT-T}(x)} : g_1, …, g_κ ∈ F}`, "a binary loss
class over `X × {0,1}^T`".

**Formalization Note.**
* As in the published `MultiThinkCoT.cotLossClass` (the case `κ = 1`), `{0,1}^T` is the subtype of
  `List Bool` of length `T`, `X : Set (List Bool)` is a subtype, and the indicator is the Boolean
  `decide (∀ j, z ≠ cot (g j) T x)`.
* The generators are indexed by `Fin κ`; a tuple `g : Fin κ → Gen` with every `g j ∈ F` is an
  element of `F^κ`. At `κ = 0` the class is the single constant-`true` function.
-/

/-- (11) The loss class `L^{CoT-T}(F; κ)` over `X × {0,1}^T`. -/
def lossClassK (F : Set Gen) (T : ℕ) (X : Set (List Bool)) (κ : ℕ) :
    Set (X × {z : List Bool // z.length = T} → Bool) :=
  {l | ∃ g : Fin κ → Gen, (∀ j, g j ∈ F) ∧
    ∀ q : X × {z : List Bool // z.length = T}, l q = decide (∀ j, q.2.1 ≠ cot (g j) T q.1.1)}

end MultiThinkCoT.Supplement


