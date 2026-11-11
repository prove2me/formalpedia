-- Prove2me | Definitions.Def_QuadExt_Main_Closeness
-- name    : QuadExt_Main_Closeness
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:03:00.995408+00:00
-- url     : https://prove2.me/theorems/ade4f60b-e140-47f5-a08b-95f19c632110
-- title:
--   Smooth min-entropy, conditional closeness to uniform, and closeness to a convex combination
-- statement:
--   Distances are statistical (total variation) distances $d_{TV}$ and min-entropy is $H_\infty(X) = -\log_2 \max_x \Pr[X = x]$, as in the published `SSNonExt_TV`. Write $X \approx_\varepsilon Y$ for $d_{TV}(X, Y) \le \varepsilon$.
--
--   A source $X$ has **$\varepsilon$-smooth min-entropy** at least $k$, written $H^\varepsilon_\infty(X) \ge k$, if some distribution $\tilde X$ on the same set has $H_\infty(\tilde X) \ge k$ and $X \approx_\varepsilon \tilde X$.
--
--   For jointly distributed $(R, T)$, **$(R \approx_\varepsilon U) \mid T$** means
--   $$d_{TV}\big((R, T), (U, T)\big) \le \varepsilon,$$
--   where $U$ is uniform on the range of $R$ and independent of $T$.
--
--   A distribution $P$ is **$\varepsilon$-close to a convex combination** of distributions of a type $\mathcal C$ if there are finitely many distributions $Q_1, \dots, Q_J$, each of type $\mathcal C$, and weights $\lambda_j \ge 0$ with $\sum_j \lambda_j = 1$, such that $d_{TV}(P, \sum_j \lambda_j Q_j) \le \varepsilon$. Closeness is of the whole mixture, not of each component.
--
--   **Formalization Note.** `prob μ E` is $\Pr_{a \sim \mu}[E(a)]$ as a real number. The weights are a `PMF` on a finite index type and the mixture is `PMF.bind`. `indepPair μ ν` is the product distribution.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 3 (PDF 4), §2 Notation; p. 18 (PDF 19), Theorem 5.1 ('ε close to a convex combination')

import Mathlib
import Definitions.Def_SSNonExt_TV

namespace QuadExt.Main

/-!
# Probability of an event, smooth min-entropy, conditional closeness, closeness to a mixture

Chandrasekaran, Goodman, Zuckerman, *Quadratic Extractors*, STOC 2027 submission (manuscript
sha256 ddc80a9a…), §2 Notation, p. 3 (PDF 4): "`X ≈_ε Y` if `d_TV(X, Y) ≤ ε`"; "`(R ≈_ε S) | T`" for
`(R, T) ≈_ε (S, T)`; smooth min-entropy `H^ε_∞(X) ≥ k`; and "`X` is `ε` close to a convex
combination of …" (Theorem 5.1, Lemma 9.2). Statistical distance and min-entropy are the published
`SSNonExt.TV` and `SSNonExt.minEntropy`.
-/

/-- `Pr_{a ∼ μ}[E(a)]` as a real number. -/
noncomputable def prob {α : Type} (μ : PMF α) (E : α → Prop) : ℝ :=
  (μ.toOuterMeasure {a | E a}).toReal

/-- **Smooth min-entropy** `H^ε_∞(X) ≥ k` (p. 3): some distribution `X̃` on the same set has
`H_∞(X̃) ≥ k` and `d_TV(X, X̃) ≤ ε`. -/
def SmoothMinEntropyGE {α : Type} [Fintype α] [Nonempty α] (ε : ℝ) (P : PMF α) (k : ℝ) : Prop :=
  ∃ Q : PMF α, k ≤ SSNonExt.minEntropy Q ∧ SSNonExt.TV P Q ≤ ε

/-- The independent pair `(A, B)` with `A ∼ μ`, `B ∼ ν`. -/
noncomputable def indepPair {α β : Type} (μ : PMF α) (ν : PMF β) : PMF (α × β) :=
  μ.bind fun a => ν.map fun b => (a, b)

/-- **Conditional closeness to uniform** `(R ≈_ε U) | T` (p. 3), for the joint law `J` of `(R, T)`:
`d_TV((R, T), (U, T)) ≤ ε`, where `U` is uniform on the range of `R` and independent of `T`. -/
def CondCloseUnif {α β : Type} [Fintype α] [Nonempty α] [Fintype β] (ε : ℝ) (J : PMF (α × β)) :
    Prop :=
  SSNonExt.TV J (indepPair (PMF.uniformOfFintype α) (J.map Prod.snd)) ≤ ε

/-- **`ε`-close to a convex combination** of distributions of a given type `C`: there are finitely
many distributions `Q_j`, each of type `C`, and convex weights `λ` (a distribution on the finite
index set) with `d_TV(P, Σ_j λ_j Q_j) ≤ ε`. -/
def CloseToMixture {α : Type} [Fintype α] (ε : ℝ) (P : PMF α) (C : PMF α → Prop) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (lam : PMF J) (Q : J → PMF α),
    (∀ j, C (Q j)) ∧ SSNonExt.TV P (lam.bind Q) ≤ ε

end QuadExt.Main


