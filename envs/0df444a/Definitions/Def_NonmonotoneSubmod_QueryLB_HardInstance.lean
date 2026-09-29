-- Prove2me | Definitions.Def_NonmonotoneSubmod_QueryLB_HardInstance
-- name    : NonmonotoneSubmod_QueryLB_HardInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:13:30.778988+00:00
-- url     : https://prove2.me/theorems/20e776c8-e728-44c0-b820-b3635773c377
-- title:
--   The hard instances $f_C$ of Theorem 4.5, the cut function $g$, and balanced sets
-- statement:
--   Fix an even $n$ and an integer $m$ playing the role of $\epsilon n$ (so $\epsilon = m/n$). For integers $k, \ell \ge 0$ define
--
--   $$
--   f(k,\ell) = \begin{cases} (k+\ell)(n-k-\ell) & \text{if } |k-\ell| \le m,\\[2pt] k(n-2\ell) + (n-2k)\ell + m^2 - 2m|k-\ell| & \text{if } |k-\ell| > m. \end{cases}
--   $$
--
--   With $\epsilon n = m$ the second expression is the paper's $k(n-2\ell)+(n-2k)\ell+\epsilon^2n^2-2\epsilon n|k-\ell|$. The two expressions coincide when $|k-\ell| = m$, so assigning the boundary to either regime gives the same function.
--
--   For a set $C \subseteq [n]$, with $D = [n] \setminus C$, the **hard instance** is
--
--   $$
--   f_C(S) = f(|S \cap C|,\ |S \cap D|), \qquad S \subseteq [n].
--   $$
--
--   The **cut function of the complete graph** is $g(S) = |S|\,(n - |S|)$. A set $Q \subseteq [n]$ is **balanced** for $(C, D)$ if $\bigl||Q\cap C| - |Q \cap D|\bigr| \le m$, and **unbalanced** otherwise. On balanced sets, $f_C$ and $g$ agree.
--
--   These are the objects of the proof of Theorem 4.5: an algorithm that sees only balanced sets cannot tell $f_C$ from $g$, whose maximum is $\tfrac14 n^2$, while $f_C$ has a strictly larger maximum.
--
--   **Formalization Note** The ground set is `Fin n`, $D$ is `Cᶜ`, and all values are computed in $\mathbb{R}$. The boundary $|k-\ell| = m$ is assigned to the first (cut) regime. A (noncomputable) `Decidable` instance for `Balanced` is included so that sets of partitions can be filtered by it.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, pp. 1149–1150, §4.2, proof of Theorem 4.5 (construction of f(k, ℓ); definition of g and of unbalanced queries, p. 1150)

import Mathlib

namespace NonmonotoneSubmod.QueryLB

/-- The two-regime function `f(k, ℓ)` of the proof of Theorem 4.5
(Feige–Mirrokni–Vondrák 2011, pp. 1149–1150), with `ϵn = m`:
* if `|k − ℓ| ≤ m`: `f(k, ℓ) = (k + ℓ)(n − k − ℓ)`;
* otherwise: `f(k, ℓ) = k(n − 2ℓ) + (n − 2k)ℓ + m² − 2m|k − ℓ|`.
The two expressions agree on `|k − ℓ| = m`; the first is used there. -/
noncomputable def fkl (n m k l : ℕ) : ℝ :=
  if |(k : ℝ) - l| ≤ m then ((k : ℝ) + l) * ((n : ℝ) - k - l)
  else (k : ℝ) * ((n : ℝ) - 2 * l) + ((n : ℝ) - 2 * k) * l + (m : ℝ) ^ 2
    - 2 * (m : ℝ) * |(k : ℝ) - l|

/-- The hard instance `f_C` on `[n]` for the partition `(C, D)`, `D = Cᶜ`:
`f_C(S) = f(|S ∩ C|, |S ∩ D|)` (p. 1149). -/
noncomputable def fC (n m : ℕ) (C : Finset (Fin n)) (S : Finset (Fin n)) : ℝ :=
  fkl n m (S ∩ C).card (S ∩ Cᶜ).card

/-- The cut function of the complete graph on `[n]`, `g(S) = |S|(n − |S|)` (p. 1150). -/
def gCut (n : ℕ) (S : Finset (Fin n)) : ℝ :=
  (S.card : ℝ) * ((n : ℝ) - S.card)

/-- A set `Q` is balanced for the partition `(C, Cᶜ)` when `|Q ∩ C|` and `|Q ∩ Cᶜ|` differ by at
most `m = ϵn`; otherwise it is "unbalanced" (p. 1150). -/
def Balanced (n m : ℕ) (C Q : Finset (Fin n)) : Prop :=
  |((Q ∩ C).card : ℝ) - (Q ∩ Cᶜ).card| ≤ m

noncomputable instance (n m : ℕ) (C Q : Finset (Fin n)) : Decidable (Balanced n m C Q) := by
  unfold Balanced; infer_instance

end NonmonotoneSubmod.QueryLB


