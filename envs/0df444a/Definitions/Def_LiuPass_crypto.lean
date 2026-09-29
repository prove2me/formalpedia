-- Prove2me | Definitions.Def_LiuPass_crypto
-- name    : LiuPass_crypto
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T22:23:46.256104+00:00
-- url     : https://prove2.me/theorems/288f88b6-1394-4f58-9496-f05813528cca
-- title:
--   Liu–Pass: one-way functions, average-case hardness, condEP-PRGs
-- statement:
--   This file states the definitions of Liu–Pass, *On One-way Functions and Kolmogorov Complexity*
--   that are phrased in terms of the computational model: Definitions 2.1, 2.2, 2.4, 2.5, 2.6, 5.1,
--   5.3 and 5.4, together with the information-theoretic quantities of Section 2.5.
--
--   **One-way functions (Definitions 2.1, 2.2).** In the inversion experiment on security parameter
--   $n$, a uniform $x \in \{0,1\}^n$ is drawn, the adversary receives the pair $(1^n, f(x))$ and a
--   uniform random tape, and succeeds when its output $z$ satisfies $f(z) = f(x)$, i.e.
--   $z \in f^{-1}(f(x))$. A polynomial-time computable $f$ is a **one-way function** if every PPT
--   adversary's success probability is bounded by a negligible function of $n$; it is an
--   $\alpha$-**weak one-way function** if every PPT adversary succeeds with probability strictly less
--   than $1 - \alpha(n)$ for all sufficiently large $n$, and a **weak one-way function** if this
--   holds for $\alpha = 1/q$ with $q$ a positive polynomial.
--
--   **Average-case hardness (Definitions 2.4, 2.5).** For an integer-valued function $F$ on strings,
--   a heuristic $H$ succeeds on $x$ if its numerical output equals $F(x)$, and $\beta$-approximately
--   succeeds if $|H(x) - F(x)| \le \beta(|x|)$. $F$ is $\alpha$-**hard-on-average** if every PPT
--   heuristic succeeds with probability $< 1 - \alpha(n)$ over uniform $n$-bit inputs, for all large
--   $n$, and **mildly** hard-on-average if this holds for some $\alpha = 1/p$ with $p$ a positive
--   polynomial; likewise for hardness to $\beta$-approximate.
--
--   **Entropy and statistical distance (Section 2.5).** For a probability vector $p$ on a finite set,
--   $$H(p) = \sum_a -p(a)\log_2 p(a), \qquad \mathrm{SD}(p,q) = \tfrac12 \sum_a |p(a) - q(a)|.$$
--
--   **Conditionally secure entropy-preserving PRGs (Definition 5.1).** An efficiently computable
--   $G$ mapping each $n$-bit seed to a string of length $n + \gamma \log_2 n$ is a
--   $\mu$-**condEP-PRG** if there are events $E_n \subseteq \{0,1\}^n$ of positive probability and a
--   constant $\alpha$ such that (i) for every PPT distinguisher $D$ and all sufficiently large $n$,
--   $$\left|\Pr[D(1^n, G(U_n \mid E_n)) = 1] - \Pr[D(1^n, U_{n+\gamma\log_2 n}) = 1]\right| < \mu(n),$$
--   and (ii) for all sufficiently large $n$ the Shannon entropy of $G(U_n \mid E_n)$ is at least
--   $n - \alpha \log_2 n$.
--
--   **One-way functions over a domain, and regularity (Definitions 5.3, 5.4).** Given sets
--   $S_n \subseteq \{0,1\}^n$, $f$ is an $S$-OWF if every PPT adversary inverts $f$ with negligible
--   probability when the input is drawn uniformly from $S_n$; $f$ has regularity $r$ over $S$ if for
--   all sufficiently large $n$ and every $x \in S_n$, the fibre of $f$ through $x$ inside $S_n$ has
--   between $2^{r(n)-1}$ and $2^{r(n)}$ elements.
--
--   **Formalization Note** All probabilities are finite counting probabilities, and conditioning on
--   an event is a ratio of two such probabilities. Logarithms appearing in lengths are base-2
--   integer logarithms, and $\gamma$ and the entropy-loss constant $\alpha$ are natural numbers. In
--   the regularity condition the lower bound is written with truncated subtraction, so for $r(n) = 0$
--   it reads $1 \le |f^{-1}(f(x)) \cap S_n|$.
-- source:
--   Yanyi Liu, Rafael Pass, On One-way Functions and Kolmogorov Complexity, arXiv:2009.11514v1 (FOCS 2020), https://arxiv.org/abs/2009.11514, Definitions 2.1, 2.2 (p. 7), 2.4, 2.5 (p. 8), 2.6 and Section 2.5 (p. 9), 5.1 (p. 11), 5.3 (p. 13), 5.4 (p. 14)

import Definitions.Def_LiuPass_model

/-!
# Liu–Pass, *On One-way Functions and Kolmogorov Complexity* — cryptographic notions

Definitions 2.1, 2.2, 2.4, 2.5, 2.6, 5.1, 5.3, 5.4 of the paper (arXiv:2009.11514v1), plus the
information-theoretic quantities of Section 2.5, phrased in the computational model of
`Definitions.Def_LiuPass_model`.
-/

namespace LiuPass

open Finset
open scoped Classical

/-! ### One-way functions (Definitions 2.1 and 2.2) -/

/-- The success probability of the inverter `A` in the one-way function experiment on security
parameter `n`: `Pr[x ← {0,1}^n ; y = f x : A (1^n, y) ∈ f⁻¹ (f x)]`. -/
noncomputable def invSucc (U : UMachine) (f : BitStr → BitStr) (A : PPT U) (n : ℕ) : ℝ :=
  prUnif₂ n (A.tape n) fun x r => f (A.out r (U.pair (unary n) (f x))) = f x

/-- Definition 2.1: `f` is a one-way function. -/
def IsOWF (U : UMachine) (f : BitStr → BitStr) : Prop :=
  PolyTimeComputable U f ∧
    ∀ A : PPT U, ∃ mu : ℕ → ℝ, Negligible mu ∧ ∀ n : ℕ, invSucc U f A n ≤ mu n

/-- Definition 2.2: `f` is an `α`-weak one-way function. -/
def IsWeakOWFWith (U : UMachine) (alpha : ℕ → ℝ) (f : BitStr → BitStr) : Prop :=
  PolyTimeComputable U f ∧
    ∀ A : PPT U, ∃ n₀ : ℕ, ∀ n ≥ n₀, invSucc U f A n < 1 - alpha n

/-- Definition 2.2: `f` is a weak one-way function, i.e. a `1/q`-weak one-way function for some
positive polynomial `q`. -/
def IsWeakOWF (U : UMachine) (f : BitStr → BitStr) : Prop :=
  ∃ q : ℕ → ℕ, IsPoly q ∧ (∀ n, 0 < q n) ∧ IsWeakOWFWith U (fun n => 1 / (q n : ℝ)) f

/-! ### Average-case hardness (Definitions 2.4 and 2.5) -/

/-- `Pr[x ← {0,1}^n : H x = F x]`, the success probability of the heuristic `H` for the
integer-valued function `F`. -/
noncomputable def heurSucc (U : UMachine) (F : BitStr → ℕ) (H : PPT U) (n : ℕ) : ℝ :=
  prUnif₂ n (H.tape n) fun x r => bitsToNat (H.out r x) = F x

/-- `Pr[x ← {0,1}^n : |H x - F x| ≤ β (|x|)]`, the success probability of the heuristic `H` at
`β`-approximating `F`. -/
noncomputable def heurApproxSucc (U : UMachine) (F : BitStr → ℕ) (beta : ℕ → ℕ) (H : PPT U)
    (n : ℕ) : ℝ :=
  prUnif₂ n (H.tape n) fun x r =>
    |(bitsToNat (H.out r x) : ℤ) - (F x : ℤ)| ≤ (beta x.length : ℤ)

/-- Definition 2.4: `F` is `α`-hard-on-average. -/
def HoA (U : UMachine) (alpha : ℕ → ℝ) (F : BitStr → ℕ) : Prop :=
  ∀ H : PPT U, ∃ n₀ : ℕ, ∀ n ≥ n₀, heurSucc U F H n < 1 - alpha n

/-- Definition 2.5: `F` is `α`-hard-on-average to `β`-approximate. -/
def HoAApprox (U : UMachine) (alpha : ℕ → ℝ) (beta : ℕ → ℕ) (F : BitStr → ℕ) : Prop :=
  ∀ H : PPT U, ∃ n₀ : ℕ, ∀ n ≥ n₀, heurApproxSucc U F beta H n < 1 - alpha n

/-- `F` is mildly hard-on-average: `1/p`-hard-on-average for some positive polynomial `p`. -/
def MildlyHoA (U : UMachine) (F : BitStr → ℕ) : Prop :=
  ∃ p : ℕ → ℕ, IsPoly p ∧ (∀ n, 0 < p n) ∧ HoA U (fun n => 1 / (p n : ℝ)) F

/-- `F` is mildly hard-on-average to `β`-approximate. -/
def MildlyHoAApprox (U : UMachine) (beta : ℕ → ℕ) (F : BitStr → ℕ) : Prop :=
  ∃ p : ℕ → ℕ, IsPoly p ∧ (∀ n, 0 < p n) ∧ HoAApprox U (fun n => 1 / (p n : ℝ)) beta F

/-! ### Statistical distance and entropy (Section 2.5) -/

/-- A probability vector on a finite type. -/
def IsProbVector {α : Type*} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- The uniform probability vector on a finite type. -/
noncomputable def unifVector (α : Type*) [Fintype α] : α → ℝ := fun _ => 1 / (Fintype.card α : ℝ)

/-- The Shannon entropy `H (X) = E [log (1 / Pr[X = x])]`, in bits. -/
noncomputable def shannonEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a, -(p a) * Real.logb 2 (p a)

/-- The statistical distance `SD (X, Y) = (1/2) ∑ |Pr[X = v] - Pr[Y = v]|`. -/
noncomputable def statDist {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1 / 2) * ∑ a, |p a - q a|

/-! ### Conditionally secure entropy-preserving pseudorandom generators (Definition 5.1) -/

/-- `Pr[G (U_n | E) = y]`, the probability that `G` applied to a uniform `n`-bit seed conditioned
on the event `E` outputs `y`. -/
noncomputable def condOutProb (n : ℕ) (E : BitStr → Prop) (G : BitStr → BitStr) (y : BitStr) :
    ℝ :=
  prUnif n (fun s => E s ∧ G s = y) / prUnif n E

/-- The Shannon entropy of `G (U_n | E)`, in bits. -/
noncomputable def condOutEntropy (n : ℕ) (E : BitStr → Prop) (G : BitStr → BitStr) : ℝ :=
  ∑ y ∈ univ.image fun v : Fin n → Bool => G (List.ofFn v),
    -(condOutProb n E G y) * Real.logb 2 (condOutProb n E G y)

/-- `Pr[D (1^n, G (U_n | E)) = 1]`. -/
noncomputable def distCondOne (U : UMachine) (D : PPT U) (n : ℕ) (E : BitStr → Prop)
    (G : BitStr → BitStr) : ℝ :=
  prUnif₂ n (D.tape n)
      (fun s r => E s ∧ bitsToNat (D.out r (U.pair (unary n) (G s))) = 1) / prUnif n E

/-- `Pr[D (1^n, U_m) = 1]`. -/
noncomputable def distUnifOne (U : UMachine) (D : PPT U) (n m : ℕ) : ℝ :=
  prUnif₂ m (D.tape n) fun y r => bitsToNat (D.out r (U.pair (unary n) y)) = 1

/-- Definition 5.1: `G : {0,1}^n → {0,1}^(n + γ log n)` is a `μ`-conditionally secure
entropy-preserving pseudorandom generator.  There must be a sequence of events `E n` of positive
probability and an entropy-loss constant `α` such that, conditioned on `E n`, the output of `G`
is `μ (n)`-indistinguishable from uniform and has Shannon entropy at least `n - α log n`. -/
def IsCondEPPRG (U : UMachine) (gamma : ℕ) (mu : ℕ → ℝ) (G : BitStr → BitStr) : Prop :=
  PolyTimeComputable U G ∧
    (∀ (n : ℕ) (s : BitStr), s.length = n → (G s).length = n + gamma * Nat.log 2 n) ∧
    ∃ (E : ℕ → BitStr → Prop) (alpha : ℕ),
      (∀ n : ℕ, 0 < prUnif n (E n)) ∧
      (∀ D : PPT U, ∃ n₀ : ℕ, ∀ n ≥ n₀,
        |distCondOne U D n (E n) G - distUnifOne U D n (n + gamma * Nat.log 2 n)| < mu n) ∧
      (∃ n₀ : ℕ, ∀ n ≥ n₀,
        (n : ℝ) - (alpha : ℝ) * Real.logb 2 n ≤ condOutEntropy n (E n) G)

/-! ### One-way functions over a subset of the domain (Definitions 5.3 and 5.4) -/

/-- The number of `n`-bit strings in `S` that `f` maps to `y`. -/
noncomputable def preimageCard (n : ℕ) (S : BitStr → Prop) (f : BitStr → BitStr) (y : BitStr) :
    ℕ :=
  (univ.filter fun v : Fin n → Bool => S (List.ofFn v) ∧ f (List.ofFn v) = y).card

/-- Definition 5.3 (restricted to a domain as in Definition 5.4): `f` has regularity `r` on the
sets `S n`, i.e. for all sufficiently long `x ∈ S n` the fibre of `f` through `x` inside `S n`
has between `2 ^ (r n - 1)` and `2 ^ r n` elements. -/
def IsRegularOver (S : ℕ → BitStr → Prop) (f : BitStr → BitStr) (r : ℕ → ℕ) : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x : BitStr, x.length = n → S n x →
    2 ^ (r n - 1) ≤ preimageCard n (S n) f (f x) ∧ preimageCard n (S n) f (f x) ≤ 2 ^ r n

/-- The success probability of the inverter `A` when the input is drawn uniformly from `S n`. -/
noncomputable def invSuccOver (U : UMachine) (S : ℕ → BitStr → Prop) (f : BitStr → BitStr)
    (A : PPT U) (n : ℕ) : ℝ :=
  prUnif₂ n (A.tape n)
      (fun x r => S n x ∧ f (A.out r (U.pair (unary n) (f x))) = f x) / prUnif n (S n)

/-- Definition 5.4: `f` is a one-way function over the sequence of sets `S` (an `S`-OWF). -/
def IsOWFOver (U : UMachine) (S : ℕ → BitStr → Prop) (f : BitStr → BitStr) : Prop :=
  PolyTimeComputable U f ∧
    ∀ A : PPT U, ∃ mu : ℕ → ℝ, Negligible mu ∧ ∀ n : ℕ, invSuccOver U S f A n ≤ mu n

end LiuPass


