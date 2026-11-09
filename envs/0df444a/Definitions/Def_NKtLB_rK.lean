-- Prove2me | Definitions.Def_NKtLB_rK
-- name    : NKtLB_rK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:00:06.291589+00:00
-- url     : https://prove2.me/theorems/d15b73d8-a525-4d5f-8a5a-7eda02246725
-- title:
--   $\mathrm{rK}^{(t;r),O}_\delta(x\mid y)$: randomized Kolmogorov complexity with $r$ random bits
-- statement:
--   For an oracle $O$, a time bound $t$, a length $r$, a real $\delta\in[0,1]$ and strings $x,y$,
--   $$
--   \mathrm{rK}^{(t;r),O}_\delta(x\mid y)=\min_M\Bigl\{|M| : \Pr_{w\sim\{0,1\}^r}\bigl[M^O(y,w)=x\text{ in }t\text{ steps}\bigr]\ge\delta\Bigr\}.
--   $$
--   The notation $\mathrm{rK}^{(t;r),O^{\le l}}_\delta$ is used when $M$ only makes queries to $O$ on strings of length at most $l$. The conditional string $y$ is omitted when empty, and $\delta$ is omitted when $\delta=2/3$.
--
--   **Formalization Note** $M$ is a program run by $U$ with $y$ on the auxiliary tape, an empty guess tape and $w$ on the randomness tape. The query bound is required for every $w\in\{0,1\}^r$ during the first $t$ steps. The value lies in $\mathbb N\cup\{\infty\}$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Definition 99, p.67

import Mathlib
import Definitions.Def_NKtLB_Machine
import Definitions.Def_NKtLB_prob

namespace NKtLB

/-- **`rK^{(t;r),O}_δ(x | y)`, randomized Kolmogorov complexity with `r` random bits** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026),
Definition 99, p.67): `rK^{(t;r),O}_δ(x | y) = min_M { |M| : Pr_{w∼{0,1}^r}[M^O(y, w) = x in t
steps] ≥ δ }`. "We use `rK^{(t;r),O^{≤l}}_δ(x | y)` when `M` only make queries to `O` on strings of
length at most `l`. We may omit the conditional string `y` when it is empty, simplify `(t; r)` to
`t` when `r ≥ t`, and omit `δ` when `δ = 2/3`."

**Formalization Note.** `M` is a program run by `U` with `y` on the auxiliary tape, an empty guess
tape and `w` on the randomness tape. The query bound `ℓ` is required on every `w ∈ {0,1}^r` during
the first `t` steps. Value in `ℕ∞`. -/
noncomputable def rK (U : Machine) (O : Set (List Bool)) (ℓ : ℕ∞) (t r : ℕ) (δ : ℝ)
    (x y : List Bool) : ℕ∞ :=
  ⨅ (p : List Bool) (_ : (∀ w : List Bool, w.length = r → U.QueryBounded O ℓ ⟨p, y, [], w⟩ t) ∧
      δ ≤ prob r (fun w => U.HaltsWith O ⟨p, y, [], w⟩ t (bitsSym x))), (p.length : ℕ∞)

end NKtLB


