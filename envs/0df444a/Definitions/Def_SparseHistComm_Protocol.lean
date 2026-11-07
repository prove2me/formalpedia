-- Prove2me | Definitions.Def_SparseHistComm_Protocol
-- name    : SparseHistComm_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:49.89397+00:00
-- url     : https://prove2.me/theorems/b97f8fa4-d191-458f-8de3-15ae9bda1596
-- title:
--   Protocol with public randomness, per-user message channels and a decoder
-- statement:
--   A **protocol** for $n$ users with inputs in $\{0,1\}^d$ consists of:
--
--   1. **public randomness** $R$ with an arbitrary law $\mu$ on a space $\Omega$, independent of the inputs, available to all users and to the server without communication cost;
--   2. for each user $i$ and each realization $R = r$, a **channel** $Q_{i,r}(\cdot \mid x)$, a probability distribution on binary strings $\{0,1\}^*$ for every input $x$; user $i$ sends $M_i \sim Q_{i,r}(\cdot \mid x_i)$, and given $R = r$ the messages are independent:
--   $$
--   P(M_1 = m_1,\dots,M_n = m_n \mid x_1,\dots,x_n, R = r) = \prod_{i=1}^n Q_{i,r}(m_i \mid x_i);
--   $$
--   3. a **decoder**: the server's estimate $\hat u = \hat u(r, m_1,\dots,m_n) \in \mathbb R^d$ of the histogram, a function of the public randomness and the ordered tuple of messages.
--
--   This is the heterogeneous model (4); the homogeneous model (5) is the subclass in which all users share the channel $Q_r$.
--
--   **Formalization Note** Messages are lists of booleans: the empty string is allowed, no prefix condition is imposed, and $|m|$ is the length of the list. $\Omega$ is any type with any measurable structure and probability measure; channel probabilities and the decoder are required to be measurable in $r$, which only excludes protocols whose success probability or expected cost would be undefined. The decoder is deterministic given $(r, m_1,\dots,m_n)$ (the proof of Lemma 2, p.15, conditions on all messages and $R$ to fix $\hat u$); server-side private randomness can be moved into $R$.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section I, pp.2–3, (3), (4), (5); proof of Lemma 2, p.15

import Mathlib

namespace SparseHistComm

/-- A **protocol** for `n` users and inputs in `{0,1}^d` (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section I, pp.2–3, (3)–(5)):
public randomness `R` with law `μ` on a space `Ω`, independent of the inputs and free of
communication cost; for each user `i` a channel `Q_{i,r}(· | xᵢ)` from the user's input to a
message `Mᵢ ∈ {0,1}*` (the heterogeneous model (4)); and the server's estimate `û`, a function of
the public randomness and the ordered tuple of messages. Given `R = r` the messages are
independent across users: the joint law of `(M₁, …, Mₙ)` is `∏ᵢ Q_{i,r}(mᵢ | xᵢ)` (4).

**Formalization Note**
1. Messages are `List Bool`; the empty string is allowed, no prefix condition is imposed, and
   `|m| = m.length`.
2. `Ω : Type` with any measurable structure and any probability measure `μ`; channels are
   `PMF (List Bool)`-valued, so a user may randomize privately.
3. The decoder is deterministic given `(r, m₁, …, mₙ)` ("Conditioning first on all messages and
   R makes both û … fixed", proof of Lemma 2, p.15); private server randomness can be moved into
   the public randomness.
4. The channel probabilities and the decoder are measurable in `r`. Every probability and
   expectation of the paper is an integral over `r`, so this only excludes protocols whose
   success probability or cost is undefined.
5. The homogeneous model (5) is the subclass `IsHomogeneous`. -/
structure Protocol (n d : ℕ) where
  /-- the space of the public randomness `R` -/
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  /-- the law of `R` -/
  μ : MeasureTheory.Measure Ω
  [isProb : MeasureTheory.IsProbabilityMeasure μ]
  /-- `enc i r x = Q_{i,r}(· | x)`, the law of user `i`'s message given input `x` and `R = r` -/
  enc : Fin n → Ω → Finset (Fin d) → PMF (List Bool)
  /-- `dec r m = û`, the server's estimate from `R = r` and the messages `m = (m₁, …, mₙ)` -/
  dec : Ω → (Fin n → List Bool) → Fin d → ℝ
  enc_measurable : ∀ i x m, Measurable fun r => enc i r x m
  dec_measurable : ∀ m a, Measurable fun r => dec r m a

attribute [instance] Protocol.mΩ Protocol.isProb

end SparseHistComm


