-- Prove2me | Definitions.Def_MLManagesComplexity_Supplement_HasNextBitPseudoentropy
-- name    : MLManagesComplexity_Supplement_HasNextBitPseudoentropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:07:02.672891+00:00
-- url     : https://prove2.me/theorems/ab4f7cfc-05ec-4d64-b768-740fdec22922
-- title:
--   $(s,\epsilon)$-next-bit pseudoentropy at least $k$ (Definition C.1)
-- statement:
--   Let $X$ be distributed according to $D$ on $\{0,1\}^n$. Then $D$ has **$(s,\epsilon)$-next-bit pseudoentropy at least $k$** if there are random variables $Y_1,\dots,Y_n\in\{0,1\}$, jointly distributed with $X$, such that
--
--   1. $\sum_{i=1}^n H(Y_i\mid X_{<i})\ge k$, and
--   2. for every circuit $A$ of size at most $s$ that takes as input an index $i\in[n]$ and a string in $\{0,1\}^i$,
--   $$
--   \Big|\,\mathbb E_i\Pr[A(i,X_{<i}X_i)=1]-\mathbb E_i\Pr[A(i,X_{<i}Y_i)=1]\,\Big|\le\epsilon,
--   $$
--   where $i$ is uniform in $[n]$ and independent of $(X,Y)$.
--
--   Taking $Y_i=X_i$ shows that every $D$ has next-bit pseudoentropy at least $H(D)$; the notion is the computational entropy of Haitner, Reingold and Vadhan, in the form used by Vadhan and Zheng.
--
--   **Formalization Note** "Jointly distributed" is a joint law of $(X,Y)$ on $\{0,1\}^n\times\{0,1\}^n$ whose first marginal is $D$. $H(\cdot\mid\cdot)$ is conditional Shannon entropy in bits (published `AutoregressiveCompression.Main.conditionalEntropy`). Distinguishers are deterministic, as in the paper, well-formed published circuits with $n+1$ inputs; the pair $(i,w)$, $w\in\{0,1\}^i$, is given as $w$, a marker $1$, and $n-i$ zeros; "outputs 1" means the output is the one-bit string $1$. At $n=0$ the averages over $i$ are taken to be $0$.
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Definition C.1, p.20 (PDF p.21); deterministic distinguishers, App. C, p.20 (PDF p.21)

import Mathlib
import Definitions.Def_MLManagesComplexity_Supplement_PredClass

set_option autoImplicit false

open PPADSIS.SubexpSIS AutoregressiveCompression.Main

namespace MLManagesComplexity.Supplement

/-- The prefix `x_{<i+1} = x₁ … x_i ∈ {0,1}^i` of `x ∈ {0,1}^n`, for the Lean index `i : Fin n`
(the paper's index `i + 1`), as a function on `Fin i`. -/
def prefixFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin i.val → Bool :=
  fun j => x ⟨j.val, j.isLt.trans i.isLt⟩

/-- The conditional entropy `H(Y_{i+1} | X_{<i+1})` in bits under a joint law `J` of `(X, Y)`
(published `AutoregressiveCompression.Main.conditionalEntropy`, the marginal-weighted entropy of
the conditional laws, zero-mass prefixes contributing `0`). -/
noncomputable def condEntropyNextBit {n : ℕ} (J : PMF ((Fin n → Bool) × (Fin n → Bool)))
    (i : Fin n) : ℝ :=
  conditionalEntropy (J.map (fun p => (prefixFn p.1 i, p.2 i)))

/-- The 0/1 indicator that the deterministic circuit `A` outputs `1` (the one-bit string `[true]`)
on the encoding `padEnc n w` of the string `w` of length at most `n`. -/
noncomputable def acc (A : Circuit) (n : ℕ) (w : List Bool) : ℝ :=
  if A.eval (padEnc n w) = [true] then 1 else 0

/-- `E_i Pr[A(i, X_{<i} X_i) = 1]` for `i` uniform in `[n]`, independent of `(X, Y) ∼ J`. -/
noncomputable def avgAccX {n : ℕ} (A : Circuit) (J : PMF ((Fin n → Bool) × (Fin n → Bool))) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, ∑ p, mass J p * acc A n ((List.ofFn p.1).take (i.val + 1))

/-- `E_i Pr[A(i, X_{<i} Y_i) = 1]` for `i` uniform in `[n]`, independent of `(X, Y) ∼ J`. -/
noncomputable def avgAccY {n : ℕ} (A : Circuit) (J : PMF ((Fin n → Bool) × (Fin n → Bool))) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, ∑ p, mass J p * acc A n ((List.ofFn p.1).take i.val ++ [p.2 i])

/-- **`(s, ϵ)`-next-bit pseudoentropy at least `k`** (Fortnow, *How Does Machine Learning Manage
Complexity?*, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Definition C.1, printed
p.20, PDF p.21, after [HRV13, VZ12]): `D` on `{0,1}^n` has it if there are random variables
`Y₁, …, Yₙ ∈ {0,1}` jointly distributed with `X ∼ D`, i.e. a law `J` on pairs `(X, Y)` whose first
marginal is `D`, such that
1. `∑_{i=1}^n H(Y_i | X_{<i}) ≥ k`, and
2. for every circuit `A` of size at most `s` that takes as input an index `i ∈ [n]` and a string in
   `{0,1}^i`, `|E_i Pr[A(i, X_{<i}X_i) = 1] − E_i Pr[A(i, X_{<i}Y_i) = 1]| ≤ ϵ`, where `i` is
   uniform in `[n]`.

**Formalization Note** Distinguishers are deterministic (the paper: "we use deterministic
distinguishers throughout"), well-formed published `PPADSIS.SubexpSIS.Circuit`s with `n + 1` input
wires; the pair `(i, w)` with `w ∈ {0,1}^i` is given as `padEnc n w` (`w`, a marker `1`, zeros),
from which `i = |w|` is read off. "Outputs 1" means the output is the one-bit string `1`. Entropy
is in bits. At `n = 0` the averages over `i` are `0` by Lean's `1/0 = 0`. -/
def HasNextBitPseudoentropy {n : ℕ} (D : PMF (Fin n → Bool)) (s : ℕ) (ε k : ℝ) : Prop :=
  ∃ J : PMF ((Fin n → Bool) × (Fin n → Bool)), J.map Prod.fst = D ∧
    k ≤ ∑ i : Fin n, condEntropyNextBit J i ∧
    ∀ A : Circuit, A.WF → A.nIn = n + 1 → A.size ≤ s → |avgAccX A J - avgAccY A J| ≤ ε

end MLManagesComplexity.Supplement


