-- Prove2me | Definitions.Def_PrivLearn_Parity_Learner
-- name    : PrivLearn_Parity_Learner
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:29.788077+00:00
-- url     : https://prove2.me/theorems/f98337b9-b12e-45de-9d1a-016cc1834945
-- title:
--   PARITY, the solution space $V_S$, the private learner $\mathcal A(z,\varepsilon)$, PAC error and the sampling probability
-- statement:
--   **PARITY.** For $d \in \mathbb N$ and $r \in \{0,1\}^d$, the parity function $c_r : \{0,1\}^d \to \{0,1\}$ is $c_r(x) = r \odot x$, the inner product modulo 2. PARITY is the class $\{c_r : r \in \{0,1\}^d\}$. A labeled example is a pair $(x, y) \in \{0,1\}^d \times \{0,1\}$, and a database is $z = (z_1,\dots,z_n)$ with $z_i = (x_i, y_i)$, arbitrary (it need not be labeled by any parity).
--
--   **Solution space.** For $S \subseteq [n]$, $V_S$ is the set of $r \in \{0,1\}^d$ that solve the linear system $\{x_i \odot r = y_i : i \in S\}$ over $\mathbb Z_2$. Given $S$, the learner outputs $c_r$ with probability $1/|V_S|$ if $r \in V_S$ and $0$ otherwise.
--
--   **Algorithm $\mathcal A(z, \varepsilon)$** (p. 14), with $p = \varepsilon/4$:
--
--   1. with probability $1/2$, output $\bot$ and terminate;
--   2. construct $S$ by picking each element of $[n]$ independently with probability $p$;
--   3. let $V_S$ be the solution space of $\{x_i \odot r = y_i : i \in S\}$;
--   4. pick $r^* \in V_S$ uniformly at random and output $c_{r^*}$; if $V_S = \emptyset$, output $\bot$.
--
--   Its output law is
--
--   $$
--   \mathcal A(z,\varepsilon) = \tfrac12\,\delta_\bot + \tfrac12 \sum_{S \subseteq [n]} p^{|S|}(1-p)^{n-|S|}\, \mu_S, \qquad \mu_S = \begin{cases} \frac{1}{|V_S|}\sum_{r \in V_S} \delta_{c_r} & V_S \neq \emptyset,\\ \delta_\bot & V_S = \emptyset.\end{cases}
--   $$
--
--   **PAC error and sampling.** For a distribution $\mathcal X$ on $\{0,1\}^d$ and a target $c_r$, the error of a hypothesis $c_{r'}$ is $\mathrm{err}(c_{r'}) = \Pr_{x \sim \mathcal X}[c_{r'}(x) \neq c_r(x)]$; the failure symbol $\bot$ has error $1$. For an algorithm $B$ on databases of size $n$ and a set $E$ of outputs, $\Pr[B(z) \in E]$ over the draw $x_1,\dots,x_n \sim \mathcal X$ i.i.d., $z_i = (x_i, c_r(x_i))$, and the coins of $B$ is
--
--   $$
--   \sum_{x \in (\{0,1\}^d)^n} \Big(\prod_{i} \mathcal X(x_i)\Big)\, \Pr[B(z_x) \in E].
--   $$
--
--   These objects carry the first learner of §4 and its utility and privacy analysis (Lemmas 4.1 and 4.2, Claim 4.3).
--
--   **Formalization Note** Bits are elements of `ZMod 2`, so $\{0,1\}^d$ is `Fin d → ZMod 2` and $c_r(x)$ is `dotProduct r x`. The output of $\mathcal A$ is `Option (Fin d → ZMod 2)`: `none` is $\bot$ and `some r` is $c_r$ (the map $r \mapsto c_r$ is injective, so nothing is lost); every set of outputs is measurable. Gaussian elimination is how the paper computes $V_S$; only the resulting law matters. In step 3 the right-hand side $c_r(x_i)$ is the label $y_i$ stored in the database, since privacy is required for arbitrary databases. The distribution $\mathcal X$ on the finite set $\{0,1\}^d$ is a `PMF`, and the probability over the examples is the finite sum displayed above. The weight $p^{|S|}(1-p)^{n-|S|}$ is a probability law on subsets for $0 \le p \le 1$, i.e. $0 \le \varepsilon \le 4$.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 13 (PARITY), p. 14 (algorithm A), p. 16 (Pr[A(z) = c_r* | S]), p. 9 (err, Definition 2.4)

import Mathlib

namespace PrivLearn.Parity

open MeasureTheory

/-- The parity function `c_r : {0,1}^d → {0,1}`, `c_r(x) = r ⊙ x`, the inner product modulo 2
(§4, p. 13). Bits are elements of `ZMod 2`; the class PARITY is `{parity r | r : Fin d → ZMod 2}`. -/
def parity {d : ℕ} (r x : Fin d → ZMod 2) : ZMod 2 :=
  dotProduct r x

/-- A labeled example `(x, y) ∈ {0,1}^d × {0,1}`; a database is `z : Fin n → Example d`. -/
abbrev Example (d : ℕ) := (Fin d → ZMod 2) × ZMod 2

/-- Outputs of the learner `A`: `none` is the failure symbol `⊥`, `some r` is the hypothesis
`c_r`. Every subset is measurable (a finite, discrete output space). -/
instance instMeasurableSpaceOutput (d : ℕ) : MeasurableSpace (Option (Fin d → ZMod 2)) := ⊤

/-- Step 3 of algorithm `A` (p. 14): the solution space `V_S` of the linear system
`{x_i ⊙ r = y_i : i ∈ S}` over `ℤ₂` imposed by the entries `z_i = (x_i, y_i)`, `i ∈ S`, of the
database (`y_i` is the label stored in the database). -/
def solSpace {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n)) : Finset (Fin d → ZMod 2) :=
  Finset.univ.filter fun r => ∀ i ∈ S, parity (z i).1 r = (z i).2

/-- `Pr[A(z) = c_r | S]` (proof of Claim 4.3, p. 16): `1/|V_S|` if `r ∈ V_S`, and `0` otherwise
(step 4 picks `r* ∈ V_S` uniformly at random). -/
noncomputable def outProb {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n))
    (r : Fin d → ZMod 2) : ℝ :=
  if r ∈ solSpace z S then 1 / ((solSpace z S).card : ℝ) else 0

/-- Step 2 of algorithm `A` (p. 14): the probability `p^{|S|} (1 − p)^{n − |S|}` that the set `S`
is constructed when each element of `[n]` is picked independently with probability `p`. -/
noncomputable def selWeight (p : ℝ) (n : ℕ) (S : Finset (Fin n)) : ℝ :=
  p ^ S.card * (1 - p) ^ (n - S.card)

/-- Algorithm `A(z, ε)` (p. 14), as the law of its output on `Option (Fin d → ZMod 2)`:
1. with probability `1/2`, output `⊥`;
2. otherwise pick each `i ∈ [n]` into `S` independently with probability `p = ε/4`;
3. let `V_S` be the solution space of `{x_i ⊙ r = y_i : i ∈ S}`;
4. output `c_{r*}` for `r* ∈ V_S` uniform, or `⊥` if `V_S = ∅`. -/
noncomputable def algA (ε : ℝ) {d n : ℕ} (z : Fin n → Example d) :
    Measure (Option (Fin d → ZMod 2)) :=
  (1 / 2 : ENNReal) • Measure.dirac none +
    (1 / 2 : ENNReal) • ∑ S : Finset (Fin n), ENNReal.ofReal (selWeight (ε / 4) n S) •
      (if (solSpace z S).Nonempty then
        ∑ r ∈ solSpace z S, ((solSpace z S).card : ENNReal)⁻¹ • Measure.dirac (some r)
      else Measure.dirac none)

/-- The PAC error (§2.2, p. 9) of an output of the learner when the target is `c_r` and the
examples are drawn from the distribution `𝒳` on `{0,1}^d`: `err(c_{r'}) = Pr_{x∼𝒳}[c_{r'}(x) ≠ c_r(x)]`;
the failure symbol `⊥` gets error `1`. -/
noncomputable def err {d : ℕ} (𝒳 : PMF (Fin d → ZMod 2)) (r : Fin d → ZMod 2) :
    Option (Fin d → ZMod 2) → ℝ
  | none => 1
  | some r' => (𝒳.toOuterMeasure {x | parity r' x ≠ parity r x}).toReal

/-- The database `z_i = (x_i, c_r(x_i))` labeled by the target `c_r`. -/
def labeled {d n : ℕ} (r : Fin d → ZMod 2) (x : Fin n → (Fin d → ZMod 2)) : Fin n → Example d :=
  fun i => (x i, parity r (x i))

/-- `Pr[A(z) ∈ E]` where the probability is over the i.i.d. draw `x_1, …, x_n ∼ 𝒳` of the examples,
`z_i = (x_i, c_r(x_i))`, and over the coins of `A` (Definition 2.4, p. 9). -/
noncomputable def samplePr {d n : ℕ} {O : Type*} [MeasurableSpace O] (𝒳 : PMF (Fin d → ZMod 2))
    (r : Fin d → ZMod 2) (A : (Fin n → Example d) → Measure O) (E : Set O) : ENNReal :=
  ∑ x : Fin n → (Fin d → ZMod 2), (∏ i, 𝒳 (x i)) * A (labeled r x) E

end PrivLearn.Parity


