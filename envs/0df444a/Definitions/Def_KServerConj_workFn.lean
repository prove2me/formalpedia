-- Prove2me | Definitions.Def_KServerConj_workFn
-- name    : KServerConj_workFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:51.6952+00:00
-- url     : https://prove2.me/theorems/02bcd2fc-df37-4782-99c5-223990d16773
-- title:
--   Offline schedules and the work function $w_t$
-- statement:
--   Fix a (pseudo)metric space $(M,d)$, a number of servers $k$, an initial configuration $C_0$ and requests $r_1,r_2,\dots\in M$. An **offline schedule** serving the first $t$ requests is a sequence of configurations $S_0=C_0,S_1,\dots,S_t$, each $S_s$ ($1\le s\le t$) a set of $k$ points containing the request $r_s$.
--
--   The **work function** $w_t$ maps a configuration $X$ to the minimum (offline) cost to serve the first $t$ requests and then move to $X$:
--
--   $$w_t(X)=\inf\Big\{\sum_{s=1}^t D(S_{s-1},S_s)+D(S_t,X)\ :\ S\ \text{an offline schedule serving } r_1,\dots,r_t\Big\}.$$
--
--   In particular $w_0(X)=D(C_0,X)$. The work function records, for every configuration, the cheapest way the past could have ended there; the Work Function Algorithm and its whole analysis are phrased through it.
--
--   **Formalization Note** Requests are a sequence $r:\mathbb N\to M$ with the paper's times $1,\dots,t$; $r_0$ is never used. The work function is defined from offline schedules, as in the paper's definition, and not by the dynamic-programming recurrence (2), which is a milestone. The set of costs is bounded below by $0$ and is nonempty when $k\ge1$ and $|C_0|=k$. The value is meaningful for $|X|=k$, which is how the mission uses it.
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §1.1, p.2 (pdf p.3)

import Mathlib
import Definitions.Def_KServerConj_confDist

namespace KServerConj

/-- An **offline schedule** serving the first `t` requests, Coester, Koutsoupias, Zbysiński,
*The k-server conjecture is true*, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…),
§1.1, printed pp.1–2 (PDF pp.2–3): it starts in the initial configuration `S 0 = C₀`, and at each
time `1 ≤ s ≤ t` it occupies a configuration `S s` of `k` points containing the request `r s`.

**Formalization Note.** Requests are `r : ℕ → M` with the paper's 1-based times `r 1, …, r t`; the
value `r 0` is never used. Values `S s` for `s > t` are unconstrained and do not enter any cost. -/
def IsSchedule {M : Type*} (k : ℕ) (C₀ : Finset M) (r : ℕ → M) (t : ℕ) (S : ℕ → Finset M) :
    Prop :=
  S 0 = C₀ ∧ ∀ s, 1 ≤ s → s ≤ t → (S s).card = k ∧ r s ∈ S s

/-- **The work function**, Coester, Koutsoupias, Zbysiński, *The k-server conjecture is true*,
arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §1.1, printed p.2 (PDF p.3):

"The work function is the function w_t that maps a configuration X to the minimum (offline) cost to
serve the first t requests and then move to configuration X."

`workFn k C₀ r t X` is the infimum, over all offline schedules `S` serving `r 1, …, r t` from `C₀`
(`IsSchedule`), of `∑_{s=1}^t D(S (s-1), S s) + D(S t, X)`.

**Formalization Note.** The work function is defined from offline schedules, as in the paper's
sentence, not by the recurrence (2), which is a milestone of the mission. The set of costs is
bounded below by `0`; it is nonempty when `1 ≤ k` and `C₀.card = k` (one server can always be
moved to the request). The value is meaningful for configurations `X` with `X.card = k`, which is
how every statement of the mission uses it; for `t = 0` it is `D(C₀, X)`. -/
noncomputable def workFn {M : Type*} [PseudoMetricSpace M] (k : ℕ) (C₀ : Finset M) (r : ℕ → M)
    (t : ℕ) (X : Finset M) : ℝ :=
  sInf {c | ∃ S : ℕ → Finset M, IsSchedule k C₀ r t S ∧
    c = (∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s)) + confDist (S t) X}

end KServerConj


