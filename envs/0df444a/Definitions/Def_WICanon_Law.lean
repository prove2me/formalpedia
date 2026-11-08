-- Prove2me | Definitions.Def_WICanon_Law
-- name    : WICanon_Law
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:30.419362+00:00
-- url     : https://prove2.me/theorems/ea576942-4598-4728-a418-5bb7082fbb56
-- title:
--   Finite laws on bit strings and statistical distance $\mathrm{SD}$
-- statement:
--   A **law** is a finitely supported mass function on bit strings; every distribution in the paper arises from finitely many uniform coins. For $f:\{0,1\}^m\to\{0,1\}^*$, the law of $f(r)$ with $r$ uniform in $\{0,1\}^m$ is written $\mathrm{coinLaw}(m,f)$. There are the usual operations: drawing $s\leftarrow P$ and then a sample of $K(s)$, pushing a law forward, taking the law of the prefix $s_{\le i}$, and the expectation $\mathbf E_{s\leftarrow P}[g(s)]$.
--
--   The **statistical distance** of two laws is
--
--   $$\mathrm{SD}(P,Q)=\frac12\sum_{x}|P(x)-Q(x)|.$$
--
--   These objects carry every probability statement of the mission.
--
--   **Formalization Note** A law is the published `RegevRecon.Law` on strings, with its bind, map, expectation and probability predicate. The sum in $\\mathrm{SD}$ runs over the union of the two finite supports, so no summability convention enters and no junk value of an infinite sum can occur.
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), §2, p.11

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_RegevRecon_Law

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity

/-- A finitely supported mass function on bit strings: the distributions of Arnon, Mazor, Pass,
Silbak, *Does Witness Indistinguishability Require Cryptography?*, STOC 2027 submission manuscript
(sha256 3f78ec3d…), §2, p.11, all of which arise from finitely many uniform coins. It is the published `RegevRecon.Law` on strings. -/
abbrev Law := RegevRecon.Law Str

/-- The law of `f(r)` for `r ← {0,1}^m` (§2, p.11: "let x ← S denote that x is drawn uniformly from
S"; "When we omit r_P, r_V, they are sampled uniformly and independently", §2.3, p.13).
`coinLaw m f = Σ_r 2^{−m} δ_{f(r)}`. -/
noncomputable def coinLaw (m : ℕ) (f : Str → Str) : Law :=
  RegevRecon.Law.ofWeights (fun _ : Fin m → Bool => (1 : ℝ) / 2 ^ m) fun r => f (List.ofFn r)

/-- `s ← P`, then a sample of `K s`. -/
noncomputable def bindLaw (P : Law) (K : Str → Law) : Law :=
  RegevRecon.Law.bind P K

/-- The law of `g(s)` for `s ← P`. -/
noncomputable def mapLaw (g : Str → Str) (P : Law) : Law :=
  RegevRecon.Law.map g P

/-- The law of the prefix `s_{≤i}` (§2, p.11) for `s ← P`. -/
noncomputable def prefixLaw (P : Law) (i : ℕ) : Law :=
  mapLaw (List.take i) P

/-- `E_{s←P}[g(s)]`. -/
noncomputable def expect (P : Law) (g : Str → ℝ) : ℝ :=
  RegevRecon.Law.expect P g

/-- `P` is a probability distribution over `{0,1}^m`. -/
def IsLawOn (P : Law) (m : ℕ) : Prop :=
  RegevRecon.Law.IsProb P ∧ ∀ s ∈ P.support, s.length = m

/-- **Statistical distance** (§2, p.11): `SD(P, Q) = ½ Σ_x |P(x) − Q(x)|`. Only points of the two
finite supports contribute to the sum, so no summability convention enters. -/
noncomputable def SD (P Q : Law) : ℝ :=
  (1 / 2) * ∑ s ∈ P.support ∪ Q.support, |P s - Q s|

end WICanon


