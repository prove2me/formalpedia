-- Prove2me | Definitions.Def_QCSepTotal_tv
-- name    : QCSepTotal_tv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:27.585252+00:00
-- url     : https://prove2.me/theorems/3971a81b-15bf-4db7-b294-639d3ae8db4e
-- title:
--   Total variation $\Delta(P,Q)$, product laws, probabilities, conditional laws and i.i.d. tuples
-- statement:
--   Let $P, Q$ be probability distributions on a common discrete space. The **total variation distance** is
--   $$\Delta(P,Q)=\frac12\sum_z\bigl|P(z)-Q(z)\bigr| .$$
--   The definition also fixes the elementary operations on distributions used throughout the paper:
--
--   1. the **product law** $P\otimes Q$ of two distributions (independent pairs);
--   2. the probability $\Pr[s]$ of an event $s$ under $P$;
--   3. the **conditional law** $\mathcal L(f\mid s)$ of a random variable $f$ given an event $s$ of positive probability (the superscript notation $Z^x$ of the paper);
--   4. the law of $c$ independent samples from a distribution $\mu$, a distribution on $c$-tuples.
--
--   Total variation is the distance in the extractor definition (3), in Lemma 2.1, in assumptions (7) and in Lemma 4.2.
--
--   **Formalization Note** Distributions are probability mass functions and the sum is an infinite sum, so the same definition covers the finite spaces of the paper and the countable space of transcripts; for two distributions the summands are always summable, so no junk value arises. When $s$ has probability $0$ the conditional law returns the unconditioned law $\mathcal L(f)$; it is only used on events of positive probability.
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), §2, p.3 (total variation; conventions on distributions and conditioning)

import Mathlib

namespace QCSepTotal

/-- **Total variation distance** `Δ(P, Q) = ½ ∑_z |P(z) − Q(z)|` (F. Le Gall, *Improved Separations
between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726, held
version sha256 970e1476…, §2, p.3).

**Formalization Note.** Distributions are `PMF`s and the sum is a `tsum`, so the same definition
covers the finite spaces of the paper and the countable transcript space `Pub × List Bool`.
For two `PMF`s the family `|P z − Q z|` is always summable (it is bounded by `P z + Q z`), so
the `tsum` never takes its junk value; on a finite type it is the finite sum of the paper. -/
noncomputable def tv {α : Type*} (P Q : PMF α) : ℝ :=
  (∑' z, |(P z).toReal - (Q z).toReal|) / 2

/-- The **product law** `P ⊗ Q` of two distributions ("tensor products of such distributions
indicate independent variables", §2, p.3). -/
noncomputable def prodLaw {α β : Type*} (P : PMF α) (Q : PMF β) : PMF (α × β) :=
  P.bind fun a => Q.map fun b => (a, b)

/-- The probability `Pr[s]` of an event `s` under a distribution `P`, as a real number. -/
noncomputable def prob {Ω : Type*} (P : PMF Ω) (s : Set Ω) : ℝ :=
  (P.toOuterMeasure s).toReal

open Classical in
/-- The **conditional law** `L(f | s)` of the random variable `f` given the event `s` (the
superscript notation of §2, p.3: "`Z^x` is the distribution of `Z` conditioned on `X = x`").

**Formalization Note.** When `s` has probability `0` the conditional law is undefined; the
definition then returns the unconditioned law `L(f)`. Every use in this mission conditions on an
event of positive probability (an element of a support), so this junk value is never read. -/
noncomputable def condLaw {Ω α : Type*} (P : PMF Ω) (s : Set Ω) (f : Ω → α) : PMF α :=
  if h : ∃ ω ∈ s, ω ∈ P.support then (P.filter s h).map f else P.map f

/-- The law of `c` independent samples from `μ`, as a distribution on tuples `Fin c → α`
("the pairs `(X_i, Y_i)` are independent samples from `µ`", p.8). Defined by drawing the first
coordinate and then the remaining `c − 1` coordinates independently. -/
noncomputable def iidLaw {α : Type*} (μ : PMF α) : (c : ℕ) → PMF (Fin c → α)
  | 0 => PMF.pure Fin.elim0
  | c + 1 => μ.bind fun a => (iidLaw μ c).map fun t => Fin.cons a t

end QCSepTotal


