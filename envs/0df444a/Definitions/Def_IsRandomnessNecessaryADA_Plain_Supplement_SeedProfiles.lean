-- Prove2me | Definitions.Def_IsRandomnessNecessaryADA_Plain_Supplement_SeedProfiles
-- name    : IsRandomnessNecessaryADA_Plain_Supplement_SeedProfiles
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:22:31.586633+00:00
-- url     : https://prove2.me/theorems/33287484-4acb-4f8f-a6be-66fcf4c19cbb
-- title:
--   Seed-indexed response profiles along threshold paths
-- statement:
--   Let $m$ be a mechanism on $[N]\times[M]$ with a $b$-bit private tape, let $r$ specify support locations, and let $h$ be a fixed list of past Boolean query tables. For a changed row $i$ and current table $q$, define the response profile with one coordinate for every ordered row-sample avoiding $i$ and every private tape:
--
--   $$V_i^h(q)_{s,\sigma}=\mathbf1\{m_\sigma(S_r(s),\operatorname{replay}(m_\sigma,S_r(s),h),q)\ge1/2\},\quad(s,\sigma)\in([N]\setminus\{i\})^n\times\{0,1\}^b.$$
--
--   Every candidate replays its own real answers using the same seed for replay and the next response. Eliminated candidates are included. The profile has $2^b(N-1)^n$ coordinates when $N\ge1$; with $h$ and $r_{-i}$ fixed it uses no $r_i$. The agreement predicate requires equality of these full profiles at every adjacent step of a published threshold path. It defines the event without claiming that any coupling achieves it. Published Boolean lifting and the weak threshold $a\ge1/2$ are reused.
-- source:
--   Edith Cohen, Haim Kaplan, Yishay Mansour, Shay Sapir, Uri Stemmer, Eliad Tsfadia, Is Randomness Necessary for Adaptive Data Analysis?, STOC 2027 submission #267 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/267.pdf, §4.5, p.15 (PDF p.15); Definitions 2.1–2.2, pp.7–8; supporting conventions §§3–4.4, pp.8–14.

import Definitions.Def_IsRandomnessNecessaryADA_Plain_Supplement_SeedProtocol
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Tables

set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Supplement

/-- Section 4.5, p.15: all avoiding-row samples and ALL private seeds, even
eliminated candidates. Past query tables are fixed, candidate answers are replayed. -/
noncomputable def seededResponseProfile {N M n b : ℕ}
    (m : SeedMechanism (Fin N × Fin M) n b) (r : Locations N M)
    (h : List (Table N M)) (i : Fin N) (q : Table N M) :
    ((Fin n → {j : Fin N // j ≠ i}) × PrivateSeed b) → Bool :=
  fun c =>
    let S := rowSample r (fun t => (c.1 t).val)
    responseBit (m c.2 S (replayQueries (m c.2) S (h.map liftQuery)) (liftQuery q))

/-- Simultaneous agreement along the actual threshold path, for every private seed. -/
noncomputable def seededProfilesAgree {N M n b : ℕ}
    (m : SeedMechanism (Fin N × Fin M) n b) (r : Locations N M)
    (h : List (Table N M)) (p : ThresholdPath N)
    (Q : Fin (p.length + 1) → Table N M) : Prop :=
  ∀ t : Fin p.length,
    seededResponseProfile m r h (p.change t) (Q t.castSucc) =
      seededResponseProfile m r h (p.change t) (Q t.succ)

end IsRandomnessNecessaryADA.Plain.Supplement


