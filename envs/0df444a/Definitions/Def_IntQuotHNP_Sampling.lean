-- Prove2me | Definitions.Def_IntQuotHNP_Sampling
-- name    : IntQuotHNP_Sampling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:11.18828+00:00
-- url     : https://prove2.me/theorems/8be0426b-8aec-480b-a505-12a7103149bc
-- title:
--   §4 — the sampling rule: shifts without replacement, the sampled input, uniform averages and probabilities
-- statement:
--   Fix a prime $p$, a secret $y^*\in\mathbb Z_p$ and $N<p$. The shifts $(t_1,\dots,t_N)$ are sampled uniformly without replacement from $\mathbb Z_p\setminus\{[-y^*]_p\}$: this is the uniform distribution on the finite set of ordered tuples of pairwise distinct residues with $y^*+t_i\not\equiv0$. The **sampled input** has the public data $p,X,N,t$ and
--   $$
--   z^*_i=[(y^*+t_i)^{-1}]_p,\qquad v_i=X\lfloor z^*_i/X\rfloor .
--   $$
--   For a finite set $s$, the **average** of $f$ is $|s|^{-1}\sum_{a\in s}f(a)$ and the **probability** of an event $P$ is $|\{a\in s:P(a)\}|/|s|$.
--
--   **Formalization Note** Inverses are taken in `ZMod p` and represented by `ZMod.val`; on the sampling domain they are genuine inverses. Both the average and the probability return $0$ on an empty set; every statement of this mission uses them on `shifts p N y` with $N<p$, which is nonempty, and on $\Omega$ of size at least $p-D$ in Lemma 4.6.
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), §4, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_IntQuotHNP_MIHNPInput

namespace IntQuotHNP

/-- **The sampling domain of the shifts.**
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), §4, p.22 (PDF p.23): "fix y∗ ∈ ℤ_p and sample t₁, . . . , t_N uniformly without
replacement from ℤ_p \ {[−y∗]_p}."

`shifts p N y` is the finite set of ordered tuples `(t₁, …, t_N)` of pairwise distinct residues
`t_i ∈ ℤ_p` with `t_i ≠ [−y]_p`, i.e. `y + t_i ≢ 0 (mod p)`.

**Formalization Note.** Sampling `N` values uniformly without replacement is the uniform
distribution on this set of injective tuples: every ordered tuple of distinct admissible values has
the same probability. The set is nonempty exactly when `N ≤ p − 1`. -/
def shifts (p N y : ℕ) : Finset (Fin N → Fin p) :=
  Finset.univ.filter fun t => Function.Injective t ∧ ∀ i, ((t i : ℕ) + y) % p ≠ 0

/-- **The hidden inverse `z∗_i = [(y∗ + t_i)⁻¹]_p`** of the sampling rule.
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), §4, p.22 (PDF p.23):
"z∗_i = [(y∗ + t_i)⁻¹]_p".

**Formalization Note.** The inverse is taken in `ZMod p` and represented by its least nonnegative
residue (`ZMod.val`). On the sampling domain `y + t_i ≢ 0`, so the inverse is a genuine inverse
(Lean's `0⁻¹ = 0` is never used there). -/
def zStar (p : ℕ) (y : ℕ) (t : ℕ) : ℕ :=
  (((y + t : ℕ) : ZMod p)⁻¹).val

/-- **The sampled MIHNP input.**
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), §4, p.22 (PDF p.23): "Set
z∗_i = [(y∗ + t_i)⁻¹]_p, v_i = X⌊z∗_i/X⌋, x∗_i = z∗_i − v_i (i ∈ [N])."

The public input with modulus `p`, bound `X`, `N` samples, shifts `t` and approximations
`v_i = X⌊z∗_i/X⌋` (the hidden errors are then `x∗_i = z∗_i mod X`).

**Formalization Note.** `⌊z/X⌋` is natural-number division. -/
def sampledInput (p X N y : ℕ) (t : Fin N → Fin p) : MIHNPInput where
  p := p
  X := X
  N := N
  t := fun i => (t i : ℕ)
  v := fun i => X * (zStar p y (t i) / X)

/-- **Expectation under the uniform distribution on a finite set.**
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), §4, p.22 (PDF p.23): "All
probabilities and expectations below use this sampling rule."

`avg s f = (1/|s|) ∑_{a ∈ s} f(a)`.

**Formalization Note.** On the empty set the value is `0`; every statement of the mission uses it
on `shifts p N y` with `N < p`, which is nonempty. -/
noncomputable def avg {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  (∑ a ∈ s, f a) / s.card

open Classical in
/-- **Probability of an event under the uniform distribution on a finite set.**
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), §4, p.22 (PDF p.23).

`prob s P = |{a ∈ s : P a}| / |s|`.

**Formalization Note.** On the empty set the value is `0`; see `avg`. -/
noncomputable def prob {α : Type*} (s : Finset α) (P : α → Prop) : ℝ :=
  ((s.filter P).card : ℝ) / s.card

end IntQuotHNP


